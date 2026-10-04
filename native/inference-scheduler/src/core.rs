use crate::{digest, Result};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub version: u32,
    /// Bound for nonterminal work, independent of lifetime completions.
    pub max_jobs: usize,
    #[serde(default = "default_receipts")]
    pub max_terminal_receipts: usize,
    #[serde(default = "default_receipt_bytes")]
    pub max_receipt_bytes: u64,
    pub max_queued_per_principal: usize,
    pub max_active_per_principal: usize,
    pub lease_ms: u64,
    pub groups: BTreeMap<String, usize>,
    pub controllers: BTreeMap<String, Registration>,
    pub backends: BTreeMap<String, Backend>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Registration {
    pub uid: u32,
    /// Root-owned mapping; never chosen by the model or request.
    pub principal: String,
    pub pool: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Backend {
    pub pool: String,
    pub group: String,
    pub endpoint: String,
    pub models: BTreeMap<String, Model>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Model {
    pub context: u32,
    pub max_output: u32,
    pub tools: bool,
    /// Conservative configured scheduling cost, not a monetary tariff.
    pub input_us: u32,
    pub output_us: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Request {
    /// Domain/task/generation/operation + exact body digest, derived by controller.
    pub id: String,
    pub request_digest: String,
    pub model: String,
    pub max_input: u32,
    pub max_output: u32,
    pub tools: bool,
    pub queue_deadline_ms: u64,
    pub allowed_endpoints: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "kebab-case", deny_unknown_fields)]
pub enum State {
    Queued,
    Placed {
        lease: u64,
        backend: String,
        endpoint: String,
        group: String,
        expires_ms: u64,
        estimated_us: u64,
    },
    Dispatched {
        lease: u64,
        backend: String,
        group: String,
        attempt: String,
        started_ms: u64,
        estimated_us: u64,
        stop_requested: bool,
    },
    Uncertain {
        lease: u64,
        backend: String,
        group: String,
        attempt: String,
        started_ms: u64,
        estimated_us: u64,
    },
    Terminal {
        outcome: Outcome,
        lease: Option<u64>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Outcome {
    /// Physical execution finished; says nothing about Mini settlement/delivery.
    Ended,
    /// Caller knows no upstream send occurred.
    NotSent,
    /// External effect or physical stop is unresolved. Capacity stays occupied.
    Uncertain,
    Cancelled,
    Expired,
    Drained,
    /// The operator attested that the physical execution is over (the lease
    /// holder is gone and the backend was stopped or checked). Frees the slot;
    /// a late report from the old holder is then a no-op.
    OperatorResolved,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Job {
    pub controller: String,
    pub principal: String,
    pub pool: String,
    pub order: u64,
    pub request: Request,
    pub state: State,
    /// Old placements proven unsent at broker restart; never release a newer lease.
    pub superseded_unsent: BTreeSet<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Core {
    pub version: u32,
    pub config_digest: String,
    pub jobs: BTreeMap<String, Job>,
    #[serde(default)]
    pub archived_receipts: usize,
    #[serde(default)]
    pub archived_bytes: u64,
    #[serde(default)]
    pub archived_drained: usize,
    pub service_us: BTreeMap<String, u64>,
    pub next: u64,
    pub virtual_floor: u64,
    #[serde(default)]
    pub draining: bool,
}

/// Finite crash/restart history per unsent request. All guards remain exact;
/// exhaustion terminalizes only that definitely-unsent placement as NotSent.
pub const MAX_UNSENT_LEASE_GUARDS: usize = 1024;

fn text(value: &str) -> bool {
    !value.is_empty() && value.len() <= 256 && !value.chars().any(char::is_control)
}
fn hash(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|v| v.is_ascii_hexdigit() && !v.is_ascii_uppercase())
}

fn default_receipts() -> usize {
    1_000_000
}
fn default_receipt_bytes() -> u64 {
    8 * 1024 * 1024 * 1024
}

impl Config {
    pub fn validate(&self) -> Result<()> {
        if self.version != 1
            || self.max_jobs == 0
            || self.max_jobs > 100_000
            || self.max_terminal_receipts < self.max_jobs
            || self.max_terminal_receipts > 100_000_000
            || self.max_receipt_bytes < 128 * 1024
            || self.max_queued_per_principal == 0
            || self.max_active_per_principal == 0
            || !(100..=300_000).contains(&self.lease_ms)
            || self.groups.is_empty()
            || self.controllers.is_empty()
            || self.backends.is_empty()
        {
            return Err("invalid scheduler configuration bounds".into());
        }
        for (name, slots) in &self.groups {
            if !text(name) || *slots == 0 || *slots > 1024 {
                return Err("invalid capacity group".into());
            }
        }
        for (name, controller) in &self.controllers {
            if !text(name) || !text(&controller.principal) || !text(&controller.pool) {
                return Err("invalid controller registration".into());
            }
        }
        for (name, backend) in &self.backends {
            if !text(name)
                || !text(&backend.pool)
                || !self.groups.contains_key(&backend.group)
                || backend.models.is_empty()
                || !endpoint(&backend.endpoint)
            {
                return Err("invalid backend or endpoint".into());
            }
            for (name, model) in &backend.models {
                if !text(name)
                    || model.context == 0
                    || model.max_output == 0
                    || model.max_output > model.context
                    || model.input_us == 0
                    || model.output_us == 0
                {
                    return Err("invalid model capacity/cost".into());
                }
            }
        }
        Ok(())
    }
    pub fn fingerprint(&self) -> String {
        // Archive resource policy can be increased without changing identity or
        // physical placement under retained leases.
        let mut value = serde_json::to_value(self).expect("serializable config");
        value
            .as_object_mut()
            .unwrap()
            .remove("max_terminal_receipts");
        value.as_object_mut().unwrap().remove("max_receipt_bytes");
        digest(&serde_json::to_vec(&value).expect("serializable config"))
    }
}

fn endpoint(value: &str) -> bool {
    let safe = !value.contains(['\r', '\n', '#', '@', '?']) && value.len() <= 2048;
    let Some((scheme, rest)) = value.split_once("://") else {
        return false;
    };
    let authority = rest.split('/').next().unwrap_or_default();
    safe && !authority.is_empty()
        && (scheme == "https"
            || scheme == "http"
                && (authority.starts_with("127.0.0.1:") || authority.starts_with("[::1]:")))
}

impl Core {
    pub fn new(config: &Config) -> Result<Self> {
        config.validate()?;
        Ok(Self {
            version: 1,
            config_digest: config.fingerprint(),
            jobs: BTreeMap::new(),
            archived_receipts: 0,
            archived_bytes: 0,
            archived_drained: 0,
            service_us: BTreeMap::new(),
            next: 1,
            virtual_floor: 0,
            draining: false,
        })
    }
    fn serial(&mut self) -> Result<u64> {
        let value = self.next;
        self.next = self
            .next
            .checked_add(1)
            .ok_or("scheduler sequence exhausted")?;
        Ok(value)
    }
    pub fn enqueue(
        &mut self,
        config: &Config,
        controller: &str,
        request: Request,
        now: u64,
    ) -> Result<()> {
        // The direct core API has the same request-body bound as the socket.
        // Together with the bounded old-lease set, every terminal receipt fits
        // the archive reservation made before accepting work.
        if serde_json::to_vec(&request)
            .map_err(|e| e.to_string())?
            .len()
            > crate::MAX_FRAME
        {
            return Err("scheduler request exceeds frame bound".into());
        }
        if !hash(&request.id)
            || !hash(&request.request_digest)
            || !text(&request.model)
            || request.max_input == 0
            || request.max_output == 0
            || request.allowed_endpoints.is_empty()
            || request.allowed_endpoints.len() > 64
            || request
                .allowed_endpoints
                .iter()
                .any(|value| !endpoint(value))
        {
            return Err("invalid job identity or bounds".into());
        }
        if let Some(old) = self.jobs.get(&request.id) {
            let mut exact = request.clone();
            exact.queue_deadline_ms = old.request.queue_deadline_ms;
            return if old.controller == controller && old.request == exact {
                Ok(())
            } else {
                Err("job identity conflicts with retained request".into())
            };
        }
        if self.draining {
            return Err("scheduler-draining".into());
        }
        let registration = config
            .controllers
            .get(controller)
            .ok_or("unregistered controller")?;
        if request.queue_deadline_ms <= now {
            return Err("queue deadline elapsed".into());
        }
        if self
            .jobs
            .values()
            .filter(|job| !matches!(job.state, State::Terminal { .. }))
            .count()
            >= config.max_jobs
        {
            return Err("active job capacity exhausted".into());
        }
        let count = self
            .jobs
            .values()
            .filter(|job| {
                job.principal == registration.principal && matches!(job.state, State::Queued)
            })
            .count();
        if count >= config.max_queued_per_principal {
            return Err("principal queue is full".into());
        }
        if !config
            .backends
            .values()
            .any(|backend| eligible(backend, &registration.pool, &request))
        {
            return Err("no backend supports pool/model/context/tools".into());
        }
        let order = self.serial()?;
        // A new or previously idle principal joins at the current virtual clock,
        // not zero: creating another controller does not create another principal.
        self.advance_floor();
        let was_active = self.jobs.values().any(|job| {
            job.principal == registration.principal && !matches!(job.state, State::Terminal { .. })
        });
        let service = self
            .service_us
            .entry(registration.principal.clone())
            .or_insert(self.virtual_floor);
        if !was_active {
            *service = (*service).max(self.virtual_floor);
        }
        self.jobs.insert(
            request.id.clone(),
            Job {
                controller: controller.into(),
                principal: registration.principal.clone(),
                pool: registration.pool.clone(),
                order,
                request,
                state: State::Queued,
                superseded_unsent: BTreeSet::new(),
            },
        );
        self.schedule(config, now)
    }

    pub fn schedule(&mut self, config: &Config, now: u64) -> Result<()> {
        let mut credits = Vec::new();
        for job in self.jobs.values_mut() {
            match &job.state {
                State::Queued if job.request.queue_deadline_ms <= now => {
                    job.state = State::Terminal {
                        outcome: Outcome::Expired,
                        lease: None,
                    }
                }
                State::Placed {
                    expires_ms,
                    estimated_us,
                    lease,
                    ..
                } if *expires_ms <= now => {
                    credits.push((job.principal.clone(), *estimated_us));
                    job.state = State::Terminal {
                        outcome: Outcome::Expired,
                        lease: Some(*lease),
                    };
                }
                _ => {}
            }
        }
        for (principal, amount) in credits {
            self.credit(&principal, amount);
        }
        if self.draining {
            return Ok(());
        }
        loop {
            self.advance_floor();
            let mut occupied = BTreeMap::<String, usize>::new();
            let mut active = BTreeMap::<String, usize>::new();
            for job in self.jobs.values() {
                if let Some(group) = group(&job.state) {
                    *occupied.entry(group.into()).or_default() += 1;
                    *active.entry(job.principal.clone()).or_default() += 1;
                }
            }
            let mut choices = Vec::new();
            let mut seen = BTreeSet::new();
            let mut waiting: Vec<_> = self
                .jobs
                .values()
                .filter(|job| matches!(job.state, State::Queued))
                .collect();
            waiting.sort_by_key(|job| job.order);
            for job in waiting {
                let family = (
                    job.principal.clone(),
                    job.pool.clone(),
                    job.request.model.clone(),
                );
                if seen.contains(&family)
                    || active.get(&job.principal).copied().unwrap_or(0)
                        >= config.max_active_per_principal
                {
                    continue;
                }
                for (name, backend) in &config.backends {
                    if eligible(backend, &job.pool, &job.request)
                        && occupied.get(&backend.group).copied().unwrap_or(0)
                            < config.groups[&backend.group]
                    {
                        seen.insert(family.clone());
                        let model = &backend.models[&job.request.model];
                        let cost = (u64::from(job.request.max_input) * u64::from(model.input_us))
                            .checked_add(
                                u64::from(job.request.max_output) * u64::from(model.output_us),
                            )
                            .ok_or("scheduling cost overflows")?;
                        choices.push((
                            self.service_us.get(&job.principal).copied().unwrap_or(0),
                            job.order,
                            cost,
                            name.clone(),
                            job.request.id.clone(),
                        ));
                    }
                }
            }
            choices.sort();
            let Some((_, _, cost, backend_name, id)) = choices.into_iter().next() else {
                break;
            };
            let lease = self.serial()?;
            let backend = &config.backends[&backend_name];
            let job = self.jobs.get_mut(&id).expect("chosen job");
            let service = self.service_us.entry(job.principal.clone()).or_default();
            *service = service
                .checked_add(cost)
                .ok_or("virtual service exhausted")?;
            job.state = State::Placed {
                lease,
                backend: backend_name,
                endpoint: backend.endpoint.clone(),
                group: backend.group.clone(),
                expires_ms: now
                    .saturating_add(config.lease_ms)
                    .min(job.request.queue_deadline_ms),
                estimated_us: cost,
            };
        }
        Ok(())
    }

    pub fn inspect(&self, controller: &str, id: &str) -> Result<Job> {
        let job = self.jobs.get(id).ok_or("unknown job")?;
        if job.controller != controller {
            return Err("job belongs to another controller".into());
        }
        Ok(job.clone())
    }

    pub fn dispatch(
        &mut self,
        controller: &str,
        id: &str,
        lease: u64,
        attempt: String,
        now: u64,
    ) -> Result<()> {
        if !text(&attempt) {
            return Err("invalid provider attempt identity".into());
        }
        let old = self.inspect(controller, id)?;
        let state = match old.state {
            State::Placed {
                lease: actual,
                backend,
                group,
                expires_ms,
                estimated_us,
                ..
            } if lease == actual && now < expires_ms => State::Dispatched {
                lease,
                backend,
                group,
                attempt,
                started_ms: now,
                estimated_us,
                stop_requested: false,
            },

            _ => return Err("placement is not dispatchable; reconcile exact lease".into()),
        };
        self.jobs.get_mut(id).unwrap().state = state;
        Ok(())
    }

    pub fn finish(
        &mut self,
        controller: &str,
        id: &str,
        lease: u64,
        outcome: Outcome,
        now: u64,
    ) -> Result<()> {
        let old = self.inspect(controller, id)?;
        if old.superseded_unsent.contains(&lease) {
            return if outcome == Outcome::NotSent {
                Ok(())
            } else {
                Err("superseded unsent lease cannot report execution".into())
            };
        }
        let (estimated, elapsed, next) = match old.state {
            State::Placed {
                lease: actual,
                estimated_us,
                ..
            } if actual == lease && outcome == Outcome::NotSent => (
                estimated_us,
                0,
                State::Terminal {
                    outcome,
                    lease: Some(lease),
                },
            ),
            State::Dispatched {
                lease: actual,
                backend,
                group,
                attempt,
                started_ms,
                estimated_us,
                ..
            }
            | State::Uncertain {
                lease: actual,
                backend,
                group,
                attempt,
                started_ms,
                estimated_us,
            } if actual == lease
                && matches!(
                    outcome,
                    Outcome::Ended | Outcome::NotSent | Outcome::Uncertain
                ) =>
            {
                if outcome == Outcome::Uncertain {
                    self.jobs.get_mut(id).unwrap().state = State::Uncertain {
                        lease,
                        backend,
                        group,
                        attempt,
                        started_ms,
                        estimated_us,
                    };
                    return Ok(());
                }
                (
                    estimated_us,
                    if outcome == Outcome::NotSent {
                        0
                    } else {
                        now.saturating_sub(started_ms).saturating_mul(1000)
                    },
                    State::Terminal {
                        outcome,
                        lease: Some(lease),
                    },
                )
            }
            State::Terminal {
                outcome: saved,
                lease: Some(actual),
            } if actual == lease
                && (saved == outcome
                    || saved == Outcome::OperatorResolved
                        && matches!(
                            outcome,
                            Outcome::Ended | Outcome::NotSent | Outcome::Uncertain
                        )
                    || outcome == Outcome::NotSent
                        && matches!(
                            saved,
                            Outcome::Expired | Outcome::Cancelled | Outcome::Drained
                        )) =>
            {
                return Ok(())
            }
            _ => return Err("completion does not match an active placement".into()),
        };
        self.complete(id, old.principal, estimated, elapsed, next);
        Ok(())
    }

    fn complete(&mut self, id: &str, principal: String, estimated: u64, elapsed: u64, next: State) {
        self.credit(&principal, estimated);
        let service = self.service_us.entry(principal).or_default();
        *service = service.saturating_add(elapsed);
        let completed_service = *service;
        self.jobs.get_mut(id).unwrap().state = next;
        if self
            .jobs
            .values()
            .all(|job| matches!(job.state, State::Terminal { .. }))
        {
            self.virtual_floor = self.virtual_floor.max(completed_service);
        }
    }

    /// Operator `resolve`: a sent or uncertain job whose lease holder will never
    /// report (it died, its controller was retired) holds its group slot forever.
    /// The operator attests the physical execution is over; the slot is freed
    /// and the elapsed wall time is charged to the principal as service.
    pub fn resolve(&mut self, id: &str, now: u64) -> Result<()> {
        let old = self.jobs.get(id).ok_or("resolve: no live job with that id")?.clone();
        let (lease, started_ms, estimated_us) = match old.state {
            State::Dispatched { lease, started_ms, estimated_us, .. }
            | State::Uncertain { lease, started_ms, estimated_us, .. } => (lease, started_ms, estimated_us),
            State::Terminal { outcome: Outcome::OperatorResolved, .. } => return Ok(()),
            _ => return Err("resolve applies only to dispatched or uncertain work; cancel or drain the rest".into()),
        };
        let elapsed = now.saturating_sub(started_ms).saturating_mul(1000);
        self.complete(id, old.principal, estimated_us, elapsed, State::Terminal {
            outcome: Outcome::OperatorResolved,
            lease: Some(lease),
        });
        Ok(())
    }

    pub fn cancel(&mut self, controller: &str, id: &str) -> Result<()> {
        let old = self.inspect(controller, id)?;
        let next = match old.state {
            State::Queued => State::Terminal {
                outcome: Outcome::Cancelled,
                lease: None,
            },
            State::Placed {
                estimated_us,
                lease,
                ..
            } => {
                self.credit(&old.principal, estimated_us);
                State::Terminal {
                    outcome: Outcome::Cancelled,
                    lease: Some(lease),
                }
            }
            State::Dispatched {
                lease,
                backend,
                group,
                attempt,
                started_ms,
                estimated_us,
                ..
            } => State::Dispatched {
                lease,
                backend,
                group,
                attempt,
                started_ms,
                estimated_us,
                stop_requested: true,
            },
            _ => return Ok(()),
        };
        self.jobs.get_mut(id).unwrap().state = next;
        Ok(())
    }

    /// Drain stops admission and relinquishes only definitely-unsent placements.
    /// Running/uncertain work is neither killed nor declared complete.
    pub fn set_draining(&mut self, enabled: bool) {
        self.draining = enabled;
        if !enabled {
            return;
        }
        let mut credits = Vec::new();
        for job in self.jobs.values_mut() {
            match job.state {
                State::Queued => {
                    job.state = State::Terminal {
                        outcome: Outcome::Drained,
                        lease: None,
                    }
                }
                State::Placed {
                    lease,
                    estimated_us,
                    ..
                } => {
                    credits.push((job.principal.clone(), estimated_us));
                    job.state = State::Terminal {
                        outcome: Outcome::Drained,
                        lease: Some(lease),
                    };
                }
                _ => {}
            }
        }
        for (principal, amount) in credits {
            self.credit(&principal, amount);
        }
    }

    fn advance_floor(&mut self) {
        let mut reserved = BTreeMap::<String, u64>::new();
        let mut active = BTreeSet::new();
        for job in self
            .jobs
            .values()
            .filter(|job| !matches!(job.state, State::Terminal { .. }))
        {
            active.insert(job.principal.clone());
            if let State::Placed { estimated_us, .. }
            | State::Dispatched { estimated_us, .. }
            | State::Uncertain { estimated_us, .. } = &job.state
            {
                let value = reserved.entry(job.principal.clone()).or_default();
                *value = value.saturating_add(*estimated_us);
            }
        }
        // New members join committed service, not a speculative reservation that
        // may be refunded after a fast call. Otherwise they inherit another
        // member's huge estimate while that member's backlog receives the refund.
        let next = active
            .iter()
            .map(|principal| {
                self.service_us
                    .get(principal)
                    .copied()
                    .unwrap_or(0)
                    .saturating_sub(reserved.get(principal).copied().unwrap_or(0))
            })
            .min();
        if let Some(next) = next {
            self.virtual_floor = self.virtual_floor.max(next);
        }
    }

    fn credit(&mut self, principal: &str, amount: u64) {
        let service = self.service_us.entry(principal.into()).or_default();
        *service = service.saturating_sub(amount);
    }

    pub fn recover(&mut self, config: &Config) -> Result<()> {
        if self.version != 1 || self.config_digest != config.fingerprint() {
            return Err(
                "scheduler state/config version differs; drain and migrate explicitly".into(),
            );
        }
        let mut credits = Vec::new();
        for job in self.jobs.values_mut() {
            job.state = match job.state.clone() {
                State::Placed {
                    estimated_us,
                    lease,
                    ..
                } => {
                    credits.push((job.principal.clone(), estimated_us));
                    if job.superseded_unsent.len() >= MAX_UNSENT_LEASE_GUARDS
                        && !job.superseded_unsent.contains(&lease)
                    {
                        // This placement never crossed the send boundary. Retire
                        // only this exhausted retry history, retaining all old
                        // guards and this final exact lease. Other members keep
                        // receiving; an explicit fresh request can be admitted.
                        State::Terminal {
                            outcome: Outcome::NotSent,
                            lease: Some(lease),
                        }
                    } else {
                        job.superseded_unsent.insert(lease);
                        State::Queued
                    }
                }
                State::Dispatched {
                    lease,
                    backend,
                    group,
                    attempt,
                    started_ms,
                    estimated_us,
                    ..
                } => State::Uncertain {
                    lease,
                    backend,
                    group,
                    attempt,
                    started_ms,
                    estimated_us,
                },
                state => state,
            };
        }
        for (principal, cost) in credits {
            self.credit(&principal, cost);
        }
        Ok(())
    }
}

fn group(state: &State) -> Option<&str> {
    match state {
        State::Placed { group, .. }
        | State::Dispatched { group, .. }
        | State::Uncertain { group, .. } => Some(group),
        _ => None,
    }
}

fn eligible(backend: &Backend, pool: &str, request: &Request) -> bool {
    backend.pool == pool
        && request.allowed_endpoints.contains(&backend.endpoint)
        && backend.models.get(&request.model).is_some_and(|model| {
            request
                .max_input
                .checked_add(request.max_output)
                .is_some_and(|tokens| tokens <= model.context)
                && request.max_output <= model.max_output
                && (!request.tools || model.tools)
        })
}
