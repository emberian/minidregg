use minidregg_inference_scheduler::{core::*, digest};
use std::collections::BTreeMap;

fn config() -> Config {
    let model = Model {
        context: 4096,
        max_output: 512,
        tools: true,
        input_us: 10,
        output_us: 100,
    };
    let backend = Backend {
        pool: "members".into(),
        group: "gpu-a".into(),
        endpoint: "http://127.0.0.1:9001/v1/chat/completions".into(),
        models: BTreeMap::from([("coder".into(), model)]),
    };
    Config {
        version: 1,
        max_terminal_receipts: 1000000,
        max_receipt_bytes: 8 * 1024 * 1024 * 1024,
        max_jobs: 100,
        max_queued_per_principal: 4,
        max_active_per_principal: 2,
        lease_ms: 1000,
        groups: BTreeMap::from([("gpu-a".into(), 1), ("gpu-b".into(), 1)]),
        controllers: [("a1", "alice"), ("a2", "alice"), ("b", "bob"), ("z", "zoe")]
            .into_iter()
            .map(|(id, principal)| {
                (
                    id.into(),
                    Registration {
                        uid: 1000,
                        principal: principal.into(),
                        pool: "members".into(),
                    },
                )
            })
            .collect(),
        backends: BTreeMap::from([
            ("a".into(), backend.clone()),
            ("alias-a".into(), backend),
            (
                "b".into(),
                Backend {
                    pool: "members".into(),
                    group: "gpu-b".into(),
                    endpoint: "http://127.0.0.1:9002/v1/chat/completions".into(),
                    models: BTreeMap::from([(
                        "plain".into(),
                        Model {
                            context: 8192,
                            max_output: 1024,
                            tools: false,
                            input_us: 10,
                            output_us: 100,
                        },
                    )]),
                },
            ),
        ]),
    }
}
fn job(name: &str) -> Request {
    Request {
        id: digest(name.as_bytes()),
        request_digest: digest(format!("body-{name}").as_bytes()),
        model: "coder".into(),
        max_input: 100,
        max_output: 20,
        tools: true,
        allowed_endpoints: vec![
            "http://127.0.0.1:9001/v1/chat/completions".into(),
            "http://127.0.0.1:9002/v1/chat/completions".into(),
        ],
        queue_deadline_ms: 10_000,
    }
}
fn enqueue(core: &mut Core, cfg: &Config, controller: &str, name: &str) -> Request {
    let request = job(name);
    core.enqueue(cfg, controller, request.clone(), 0).unwrap();
    request
}
fn lease(core: &Core, controller: &str, request: &Request) -> u64 {
    match core.inspect(controller, &request.id).unwrap().state {
        State::Placed { lease, .. } => lease,
        other => panic!("expected placement, got {other:?}"),
    }
}
fn state(core: &Core, controller: &str, request: &Request) -> State {
    core.inspect(controller, &request.id).unwrap().state
}

#[test]
fn backend_aliases_share_one_physical_slot() {
    let cfg = config();
    let mut core = Core::new(&cfg).unwrap();
    let a = enqueue(&mut core, &cfg, "a1", "first");
    let b = enqueue(&mut core, &cfg, "b", "second");
    assert!(matches!(state(&core, "a1", &a), State::Placed { .. }));
    assert_eq!(state(&core, "b", &b), State::Queued);
    core.finish("a1", &a.id, lease(&core, "a1", &a), Outcome::NotSent, 1)
        .unwrap();
    core.schedule(&cfg, 1).unwrap();
    assert!(matches!(state(&core, "b", &b), State::Placed { .. }));
}

#[test]
fn extra_controllers_do_not_multiply_principal_slots_or_queue() {
    let mut cfg = config();
    cfg.groups.insert("gpu-a".into(), 2);
    cfg.max_active_per_principal = 1;
    cfg.max_queued_per_principal = 1;
    let mut core = Core::new(&cfg).unwrap();
    let a = enqueue(&mut core, &cfg, "a1", "alice-active");
    let waiting = enqueue(&mut core, &cfg, "a2", "alice-waiting");
    let b = enqueue(&mut core, &cfg, "b", "bob-active");
    assert!(matches!(state(&core, "a1", &a), State::Placed { .. }));
    assert_eq!(state(&core, "a2", &waiting), State::Queued);
    assert!(matches!(state(&core, "b", &b), State::Placed { .. }));
    assert!(core
        .enqueue(&cfg, "a1", job("alice-over-limit"), 0)
        .unwrap_err()
        .contains("principal queue"));
}

#[test]
fn queued_principals_share_service_across_controllers() {
    let cfg = config();
    let mut core = Core::new(&cfg).unwrap();
    let blocker = enqueue(&mut core, &cfg, "z", "blocker");
    let a1 = enqueue(&mut core, &cfg, "a1", "alice-one");
    let a2 = enqueue(&mut core, &cfg, "a2", "alice-two");
    let b = enqueue(&mut core, &cfg, "b", "bob-one");
    core.finish(
        "z",
        &blocker.id,
        lease(&core, "z", &blocker),
        Outcome::NotSent,
        1,
    )
    .unwrap();
    core.schedule(&cfg, 1).unwrap();
    let first = lease(&core, "a1", &a1);
    core.dispatch("a1", &a1.id, first, "attempt-a".into(), 1)
        .unwrap();
    core.finish("a1", &a1.id, first, Outcome::Ended, 101)
        .unwrap();
    core.schedule(&cfg, 101).unwrap();
    assert!(matches!(state(&core, "b", &b), State::Placed { .. }));
    assert_eq!(state(&core, "a2", &a2), State::Queued);
}

#[test]
fn incompatible_context_tools_output_and_pool_are_refused() {
    let cfg = config();
    for (name, request) in [
        (
            "context",
            Request {
                max_input: 4090,
                ..job("context")
            },
        ),
        (
            "output",
            Request {
                max_output: 513,
                ..job("output")
            },
        ),
        (
            "tools",
            Request {
                model: "plain".into(),
                ..job("tools")
            },
        ),
        (
            "unknown-model",
            Request {
                model: "unknown".into(),
                ..job("unknown-model")
            },
        ),
        (
            "overflow",
            Request {
                max_input: u32::MAX,
                ..job("overflow")
            },
        ),
        (
            "endpoint-pin",
            Request {
                allowed_endpoints: vec![
                    "https://not-this-backend.example/v1/chat/completions".into()
                ],
                ..job("endpoint-pin")
            },
        ),
    ] {
        let mut core = Core::new(&cfg).unwrap();
        assert!(
            core.enqueue(&cfg, "a1", request, 0).is_err(),
            "accepted {name}"
        );
        assert!(core.jobs.is_empty());
    }
    let mut isolated = cfg.clone();
    isolated.controllers.get_mut("a1").unwrap().pool = "private".into();
    let mut core = Core::new(&isolated).unwrap();
    assert!(core.enqueue(&isolated, "a1", job("wrong-pool"), 0).is_err());
}

#[test]
fn occupied_host_does_not_block_an_independent_host() {
    let cfg = config();
    let mut core = Core::new(&cfg).unwrap();
    let a = enqueue(&mut core, &cfg, "a1", "host-a");
    let blocked = enqueue(&mut core, &cfg, "b", "blocked-on-a");
    let independent = Request {
        model: "plain".into(),
        tools: false,
        ..job("host-b")
    };
    core.enqueue(&cfg, "b", independent.clone(), 0).unwrap();
    assert_eq!(state(&core, "b", &blocked), State::Queued);
    assert!(matches!(state(&core, "a1", &a), State::Placed { group, .. } if group == "gpu-a"));
    assert!(
        matches!(state(&core, "b", &independent), State::Placed { group, .. } if group == "gpu-b")
    );
}

#[test]
fn cancellation_of_queued_work_is_final_but_sent_work_keeps_capacity() {
    let cfg = config();
    let mut core = Core::new(&cfg).unwrap();
    let active = enqueue(&mut core, &cfg, "a1", "active");
    let queued = enqueue(&mut core, &cfg, "b", "queued");
    core.cancel("b", &queued.id).unwrap();
    assert!(matches!(
        state(&core, "b", &queued),
        State::Terminal {
            outcome: Outcome::Cancelled,
            ..
        }
    ));
    assert!(core
        .finish("b", &queued.id, 0, Outcome::Cancelled, 1)
        .is_err());
    let ticket = lease(&core, "a1", &active);
    core.dispatch("a1", &active.id, ticket, "provider-send".into(), 1)
        .unwrap();
    core.cancel("a1", &active.id).unwrap();
    assert!(matches!(
        state(&core, "a1", &active),
        State::Dispatched {
            stop_requested: true,
            ..
        }
    ));
    let later = enqueue(&mut core, &cfg, "b", "later");
    core.finish("a1", &active.id, ticket, Outcome::Uncertain, 2)
        .unwrap();
    core.schedule(&cfg, 9000).unwrap();
    assert_eq!(state(&core, "b", &later), State::Queued);
    assert!(matches!(
        state(&core, "a1", &active),
        State::Uncertain { .. }
    ));
    core.finish("a1", &active.id, ticket, Outcome::Ended, 9001)
        .unwrap();
    core.schedule(&cfg, 9001).unwrap();
    assert!(matches!(state(&core, "b", &later), State::Placed { .. }));
}

#[test]
fn restart_requeues_unsent_placement_but_quarantines_dispatched_attempt() {
    let cfg = config();
    let mut core = Core::new(&cfg).unwrap();
    let unsent = enqueue(&mut core, &cfg, "a1", "unsent");
    let old_ticket = lease(&core, "a1", &unsent);
    let sent = Request {
        model: "plain".into(),
        tools: false,
        ..job("sent")
    };
    core.enqueue(&cfg, "b", sent.clone(), 0).unwrap();
    let sent_ticket = lease(&core, "b", &sent);
    core.dispatch(
        "b",
        &sent.id,
        sent_ticket,
        "exact-upstream-attempt".into(),
        1,
    )
    .unwrap();
    let mut recovered: Core = serde_json::from_slice(&serde_json::to_vec(&core).unwrap()).unwrap();
    recovered.recover(&cfg).unwrap();
    assert_eq!(state(&recovered, "a1", &unsent), State::Queued);
    assert!(
        matches!(state(&recovered, "b", &sent), State::Uncertain { lease, attempt, .. } if lease == sent_ticket && attempt == "exact-upstream-attempt")
    );
    recovered.schedule(&cfg, 2).unwrap();
    assert_ne!(lease(&recovered, "a1", &unsent), old_ticket);
    assert!(recovered
        .dispatch("a1", &unsent.id, old_ticket, "stale-attempt".into(), 3)
        .is_err());
    assert!(recovered
        .dispatch(
            "b",
            &sent.id,
            sent_ticket,
            "exact-upstream-attempt".into(),
            3
        )
        .is_err());
    let mut changed = cfg.clone();
    changed.groups.insert("gpu-a".into(), 2);
    assert!(recovered.recover(&changed).is_err());
}

#[test]
fn retained_identity_rejects_changed_content_and_other_controller() {
    let cfg = config();
    let mut core = Core::new(&cfg).unwrap();
    let request = enqueue(&mut core, &cfg, "a1", "identity");
    let original = serde_json::to_value(&core).unwrap();
    core.enqueue(&cfg, "a1", request.clone(), 1).unwrap();
    assert_eq!(serde_json::to_value(&core).unwrap(), original);
    assert!(core.enqueue(&cfg, "a2", request.clone(), 1).is_err());
    assert!(core.inspect("a2", &request.id).is_err());
    for changed in [
        Request {
            request_digest: digest(b"changed-body"),
            ..request.clone()
        },
        Request {
            max_output: 21,
            ..request.clone()
        },
        Request {
            allowed_endpoints: vec!["http://127.0.0.1:9001/v1/chat/completions".into()],
            ..request.clone()
        },
    ] {
        assert!(core.enqueue(&cfg, "a1", changed, 1).is_err());
    }
    core.enqueue(
        &cfg,
        "a1",
        Request {
            queue_deadline_ms: 11_000,
            ..request.clone()
        },
        1,
    )
    .unwrap();
    assert_eq!(serde_json::to_value(&core).unwrap(), original);
    // Reconnecting cannot extend the first durable queue deadline.
    let mut waiting = Core::new(&cfg).unwrap();
    let blocker = enqueue(&mut waiting, &cfg, "z", "deadline-blocker");
    let blocker_lease = lease(&waiting, "z", &blocker);
    waiting
        .dispatch("z", &blocker.id, blocker_lease, "holds-capacity".into(), 0)
        .unwrap();
    waiting.enqueue(&cfg, "a1", request.clone(), 0).unwrap();
    waiting
        .enqueue(
            &cfg,
            "a1",
            Request {
                queue_deadline_ms: 11_000,
                ..request.clone()
            },
            1,
        )
        .unwrap();
    assert_eq!(
        waiting
            .inspect("a1", &request.id)
            .unwrap()
            .request
            .queue_deadline_ms,
        10_000
    );
    waiting.schedule(&cfg, 10_000).unwrap();
    assert!(matches!(
        state(&waiting, "a1", &request),
        State::Terminal {
            outcome: Outcome::Expired,
            ..
        }
    ));
}

#[test]
fn exact_dispatch_and_terminal_replays_do_not_double_charge() {
    let cfg = config();
    let mut core = Core::new(&cfg).unwrap();
    let request = enqueue(&mut core, &cfg, "a1", "replay");
    let ticket = lease(&core, "a1", &request);
    core.dispatch("a1", &request.id, ticket, "attempt".into(), 1)
        .unwrap();
    assert!(core
        .dispatch("a1", &request.id, ticket, "attempt".into(), 2)
        .is_err());
    assert!(core
        .dispatch("a1", &request.id, ticket, "different-attempt".into(), 2)
        .is_err());
    core.finish("a1", &request.id, ticket, Outcome::Ended, 10)
        .unwrap();
    let ended = serde_json::to_value(&core).unwrap();
    core.finish("a1", &request.id, ticket, Outcome::Ended, 500)
        .unwrap();
    assert_eq!(serde_json::to_value(&core).unwrap(), ended);
    assert!(core
        .finish("a1", &request.id, ticket + 1, Outcome::Ended, 500)
        .is_err());
    assert!(core
        .finish("a1", &request.id, ticket, Outcome::NotSent, 500)
        .is_err());
    assert_eq!(serde_json::to_value(&core).unwrap(), ended);
}

#[test]
fn blocked_large_request_does_not_hide_small_same_model_on_another_host() {
    let mut cfg = config();
    cfg.backends.get_mut("b").unwrap().models.insert(
        "coder".into(),
        Model {
            context: 256,
            max_output: 64,
            tools: true,
            input_us: 10,
            output_us: 100,
        },
    );
    let mut core = Core::new(&cfg).unwrap();
    let blocker = Request {
        max_input: 1000,
        ..job("large-host-blocker")
    };
    core.enqueue(&cfg, "z", blocker, 0).unwrap();
    let big = Request {
        max_input: 1000,
        ..job("large-alice")
    };
    core.enqueue(&cfg, "a1", big.clone(), 0).unwrap();
    let small = enqueue(&mut core, &cfg, "a2", "small-alice");
    assert_eq!(state(&core, "a1", &big), State::Queued);
    assert!(matches!(state(&core, "a2", &small), State::Placed { group, .. } if group == "gpu-b"));
}

#[test]
fn old_unsent_guard_cannot_release_new_placement_or_dispatch_after_restart() {
    let cfg = config();
    let mut core = Core::new(&cfg).unwrap();
    let request = enqueue(&mut core, &cfg, "a1", "old-guard");
    let old = lease(&core, "a1", &request);
    core.recover(&cfg).unwrap();
    core.schedule(&cfg, 1).unwrap();
    let fresh = lease(&core, "a1", &request);
    assert_ne!(old, fresh);
    let placed = serde_json::to_value(&core).unwrap();
    core.finish("a1", &request.id, old, Outcome::NotSent, 2)
        .unwrap();
    assert_eq!(serde_json::to_value(&core).unwrap(), placed);
    assert!(core
        .finish("a1", &request.id, old + 1000, Outcome::NotSent, 2)
        .is_err());
    core.dispatch("a1", &request.id, fresh, "new-send".into(), 2)
        .unwrap();
    let dispatched = serde_json::to_value(&core).unwrap();
    core.finish("a1", &request.id, old, Outcome::NotSent, 3)
        .unwrap();
    assert_eq!(serde_json::to_value(&core).unwrap(), dispatched);
    assert!(core
        .finish("a1", &request.id, old, Outcome::Ended, 3)
        .is_err());
    let competing = enqueue(&mut core, &cfg, "b", "still-blocked");
    assert_eq!(state(&core, "b", &competing), State::Queued);
}

#[test]
fn idle_principal_returns_at_current_service_floor_without_catchup_burst() {
    let cfg = config();
    let mut core = Core::new(&cfg).unwrap();
    let initial = enqueue(&mut core, &cfg, "a1", "alice-before-idle");
    let ticket = lease(&core, "a1", &initial);
    core.dispatch("a1", &initial.id, ticket, "initial".into(), 0)
        .unwrap();
    core.finish("a1", &initial.id, ticket, Outcome::Ended, 1)
        .unwrap();

    let long = enqueue(&mut core, &cfg, "b", "bob-long");
    let ticket = lease(&core, "b", &long);
    core.dispatch("b", &long.id, ticket, "long".into(), 1)
        .unwrap();
    let short = enqueue(&mut core, &cfg, "b", "bob-short");
    core.finish("b", &long.id, ticket, Outcome::Ended, 101)
        .unwrap();
    core.schedule(&cfg, 101).unwrap();
    let ticket = lease(&core, "b", &short);
    core.dispatch("b", &short.id, ticket, "short".into(), 101)
        .unwrap();
    let b_wait = enqueue(&mut core, &cfg, "b", "bob-waiting");
    let a_return = enqueue(&mut core, &cfg, "a1", "alice-return");
    let a_more = enqueue(&mut core, &cfg, "a2", "alice-extra-controller");
    core.finish("b", &short.id, ticket, Outcome::Ended, 102)
        .unwrap();
    core.schedule(&cfg, 102).unwrap();
    // Either Alice or Bob may win a tie, but a returning idle account must
    // never get two consecutive catch-up slots ahead of already waiting Bob.
    if matches!(state(&core, "a1", &a_return), State::Placed { .. }) {
        let ticket = lease(&core, "a1", &a_return);
        core.dispatch("a1", &a_return.id, ticket, "return".into(), 102)
            .unwrap();
        core.finish("a1", &a_return.id, ticket, Outcome::Ended, 103)
            .unwrap();
        core.schedule(&cfg, 103).unwrap();
    }
    assert!(matches!(state(&core, "b", &b_wait), State::Placed { .. }));
    assert_eq!(state(&core, "a2", &a_more), State::Queued);
}

#[test]
fn refundable_estimate_is_not_the_joining_principals_service_floor() {
    let mut cfg = config();
    for backend in cfg.backends.values_mut() {
        if let Some(model) = backend.models.get_mut("coder") {
            model.context = 1_000_000;
            model.max_output = 100_000;
            model.input_us = 10_000;
            model.output_us = 10_000;
        }
    }
    let mut core = Core::new(&cfg).unwrap();
    let expensive = Request {
        max_input: 100_000,
        max_output: 100_000,
        ..job("large-estimate-fast-finish")
    };
    core.enqueue(&cfg, "a1", expensive.clone(), 0).unwrap();
    let ticket = lease(&core, "a1", &expensive);
    core.dispatch("a1", &expensive.id, ticket, "fast-upstream".into(), 0)
        .unwrap();
    let backlog = enqueue(&mut core, &cfg, "a2", "alice-backlog");
    let newcomer = enqueue(&mut core, &cfg, "b", "bob-joins-during-reservation");
    assert_eq!(state(&core, "b", &newcomer), State::Queued);
    // Only 1 ms of physical service occurred. Bob must not inherit Alice's
    // refundable 2-billion-microsecond estimate as permanent service debt.
    core.finish("a1", &expensive.id, ticket, Outcome::Ended, 1)
        .unwrap();
    core.schedule(&cfg, 1).unwrap();
    assert!(matches!(state(&core, "b", &newcomer), State::Placed { .. }));
    assert_eq!(state(&core, "a2", &backlog), State::Queued);
}

#[test]
fn selected_population_concurrency_pairs_share_principals_and_preserve_held_slots() {
    for (population, concurrency) in [(2, 1), (5, 4), (20, 4), (100, 16)] {
        let mut cfg = config();
        cfg.max_jobs = population * 2 + 1;
        cfg.max_queued_per_principal = 1;
        cfg.max_active_per_principal = 1;
        cfg.groups.insert("gpu-a".into(), concurrency);
        cfg.controllers.clear();
        for member in 0..population {
            for controller in 0..2 {
                cfg.controllers.insert(
                    format!("subject-{member}-controller-{controller}"),
                    Registration {
                        uid: 1000,
                        principal: format!("actual-subject-{}", 500 + member),
                        pool: "members".into(),
                    },
                );
            }
        }
        let mut core = Core::new(&cfg).unwrap();
        let mut jobs = vec![];
        for member in 0..population {
            let controller = format!("subject-{member}-controller-0");
            let request = enqueue(
                &mut core,
                &cfg,
                &controller,
                &format!("population-{population}-member-{member}"),
            );
            jobs.push((controller, request));
        }
        let (controller, held) = &jobs[0];
        let ticket = lease(&core, controller, held);
        core.dispatch(controller, &held.id, ticket, "unknown-response".into(), 1)
            .unwrap();
        core.finish(controller, &held.id, ticket, Outcome::Uncertain, 2)
            .unwrap();
        let extra_controller = "subject-0-controller-1";
        let extra = enqueue(
            &mut core,
            &cfg,
            extra_controller,
            &format!("population-{population}-extra-controller"),
        );
        assert_eq!(state(&core, extra_controller, &extra), State::Queued);
        assert!(core
            .enqueue(
                &cfg,
                controller,
                job(&format!("population-{population}-over-limit")),
                2
            )
            .unwrap_err()
            .contains("principal queue"));
        if concurrency == 1 {
            // A held physical slot cannot magically serve another member. An
            // independent host still works under the same population limit.
            core.cancel(&jobs[1].0, &jobs[1].1.id).unwrap();
            let independent = Request {
                model: "plain".into(),
                tools: false,
                ..job("independent-population")
            };
            core.enqueue(&cfg, &jobs[1].0, independent.clone(), 2)
                .unwrap();
            assert!(
                matches!(state(&core, &jobs[1].0, &independent), State::Placed { group, .. } if group == "gpu-b")
            );
        } else {
            let mut completed = 0;
            while completed < population - 1 {
                let mut progressed = false;
                for (controller, request) in jobs.iter().skip(1) {
                    if let State::Placed { lease, .. } = state(&core, controller, request) {
                        core.finish(controller, &request.id, lease, Outcome::NotSent, 3)
                            .unwrap();
                        completed += 1;
                        progressed = true;
                    }
                }
                core.schedule(&cfg, 3).unwrap();
                assert!(
                    progressed,
                    "held member blocked others at {population}/{concurrency}"
                );
                assert!(matches!(
                    state(&core, &jobs[0].0, held),
                    State::Uncertain { .. }
                ));
                assert_eq!(state(&core, extra_controller, &extra), State::Queued);
                let occupied = core
                    .jobs
                    .values()
                    .filter(|job| {
                        matches!(
                            job.state,
                            State::Placed { .. }
                                | State::Dispatched { .. }
                                | State::Uncertain { .. }
                        )
                    })
                    .count();
                assert!(occupied <= concurrency);
            }
        }
    }
}
