use mini_sdk::app_interface::Declaration;
use serde_json::json;
#[test]
fn native_gogs_encodes_declared_call_and_refuses_bad_input() {
    let d = Declaration::load(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    let p = d
        .prepare(
            "issue.create",
            &json!({"owner":"alice","repo":"one","title":"typed","body":"hi"}),
            &json!({}),
        )
        .unwrap();
    assert_eq!(p.path, "api/v1/repos/alice/one/issues");
    assert_eq!(
        serde_json::from_slice::<serde_json::Value>(&p.body).unwrap(),
        json!({"title":"typed","body":"hi"})
    );
    assert!(d
        .prepare(
            "issue.create",
            &json!({"owner":"../bob","repo":"one","title":"typed","body":"hi"}),
            &json!({})
        )
        .is_err());
}
#[test]
fn native_dav_binary_and_uncertain_writes() {
    let d = Declaration::load(include_bytes!("../../../apps/interfaces/davros.json")).unwrap();
    let p = d
        .prepare(
            "file.put",
            &json!({"path":"dir/a.bin","contentBase64":"AP8="}),
            &json!({}),
        )
        .unwrap();
    assert_eq!(p.body, vec![0, 255]);
    assert!(d.decode(&p, 500, &[], b"bad").unwrap_err().uncertain);
    let p = d
        .prepare("file.get", &json!({"path":"dir/a.bin"}), &json!({}))
        .unwrap();
    assert_eq!(
        d.decode(&p, 200, &[], &[0, 255]).unwrap(),
        json!({"contentBase64":"AP8="})
    );
}

fn binding() -> mini_sdk::app_interface::SessionBinding {
    mini_sdk::app_interface::SessionBinding {
        package_id: "aede44cf19129337aae68b6993324574".into(),
        subject: "7".into(),
        app: "8".into(),
        generation: "0".into(),
        session: "9".into(),
        session_generation: "0".into(),
    }
}
#[test]
fn executor_retains_receipt_and_never_replays_uninterpretable_write() {
    use mini_sdk::app_interface::NativeReply;
    let d = Declaration::load(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    let mut calls = 0;
    let e = d.execute(
        "repo.create",
        &json!({"name":"hello","description":""}),
        &json!({}),
        &binding(),
        |_, _| {
            calls += 1;
            Ok(NativeReply {
                status: 201,
                headers: vec![("content-type".into(), "application/json".into())],
                body: b"{}".to_vec(),
                receipt: json!({"exact":"native"}),
            })
        },
    );
    assert_eq!(calls, 1);
    assert!(e.outcome.unwrap_err().uncertain);
    assert_eq!(e.receipts, vec![json!({"exact":"native"})]);
}
#[test]
fn preparation_uses_result_token_and_scoped_app_cookie() {
    use mini_sdk::app_interface::NativeReply;
    let mut d: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    d["auth"]["appCookies"] = json!("retain");
    d["operations"]["token"] = json!({"internal":true,"description":"token","input":{"type":"object","additionalProperties":false},"output":{"type":"object","properties":{"token":{"type":"string"}},"required":["token"]},"write":false,"binding":{"protocol":"http","method":"GET","path":["token"],"status":[200],"decode":"json"}});
    d["operations"]["edit"] = json!({"description":"edit","input":{"type":"object","additionalProperties":false},"output":{"type":"string"},"write":true,"prepare":[{"id":"csrf","op":"token","args":{}}],"binding":{"protocol":"http","method":"POST","path":["edit"],"form":{"token":{"result":["csrf","token"]},"text":"a & b"},"status":[200],"decode":"text"}});
    let d = Declaration::load(&serde_json::to_vec(&d).unwrap()).unwrap();
    assert!(!d.tools().unwrap().iter().any(|t| t["operation"] == "token"));
    let mut calls = 0;
    let e = d.execute("edit", &json!({}), &json!({}), &binding(), |b, p| {
        assert_eq!(b.subject, "7");
        calls += 1;
        Ok(if calls == 1 {
            NativeReply {
                status: 200,
                headers: vec![
                    ("content-type".into(), "application/json".into()),
                    ("set-cookie".into(), "sid=member; HttpOnly".into()),
                ],
                body: br#"{"token":"secret"}"#.to_vec(),
                receipt: json!({"read":true}),
            }
        } else {
            assert_eq!(p.body, b"text=a%20%26%20b&token=secret");
            assert!(p
                .ordered_headers
                .contains(&("cookie".into(), "sid=member".into())));
            NativeReply {
                status: 200,
                headers: vec![],
                body: b"edited".to_vec(),
                receipt: json!({"write":true}),
            }
        })
    });
    assert_eq!(e.outcome.unwrap(), json!("edited"));
    assert_eq!(e.receipts.len(), 2);
    assert_eq!(calls, 2);
}

#[test]
fn declaration_refuses_schema_constraints_it_cannot_enforce() {
    let mut d: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    d["operations"]["repo.create"]["input"]["not"] = json!({"required":["name"]});
    assert_eq!(
        Declaration::load(&serde_json::to_vec(&d).unwrap())
            .unwrap_err()
            .name,
        "schema-keyword-unsupported"
    );
}

#[test]
fn native_generic_multipart_cookie_expression_and_json_lines() {
    use mini_sdk::app_interface::NativeReply;
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["operations"]["upload"] = json!({"description":"upload","input":{"type":"object","properties":{},"additionalProperties":false},"output":{"type":"array","items":{"type":"object"}},"write":true,"binding":{"protocol":"http","method":"POST","path":["upload"],"status":[200],"decode":"json-lines","multipart":[{"name":"file","filename":"a.bin","contentType":"application/octet-stream","base64":"AP8="},{"name":"title","text":"hello"}]}});
    let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
    let e = d.execute("upload", &json!({}), &json!({}), &binding(), |_, p| {
        assert!(p.body.windows(2).any(|w| w == [0, 255]));
        assert!(p
            .ordered_headers
            .iter()
            .any(|(k, v)| k == "content-type" && v.starts_with("multipart/form-data; boundary=")));
        Ok(NativeReply {
            status: 200,
            headers: vec![],
            body: b"{\"id\":1}\n{\"id\":2}\n".to_vec(),
            receipt: json!({"native":"exact"}),
        })
    });
    assert_eq!(e.outcome.unwrap(), json!([{"id":1},{"id":2}]));
    assert!(mini_sdk::app_interface::resolve(
        &json!({"cookie":"csrf"}),
        &json!({}),
        &json!({"csrf":"caller-forged"}),
        &json!({})
    )
    .is_err());
}

#[test]
fn declaration_digest_matches_contract_unicode_escaping() {
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["description"] = json!("é💖\u{7f}");
    let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
    assert_eq!(
        d.sha256,
        "917da2077e2421276b725d74c73dbc1bc5fd9e0e838cd3f497d9040ee2bfaba4"
    );
}

#[test]
fn native_ddp_authenticates_with_server_identity_and_waits_for_updated() {
    use mini_sdk::app_interface::NativeReply;
    let d = Declaration::load(include_bytes!("../../../apps/interfaces/wekan.json")).unwrap();
    let mut b = binding();
    b.package_id = d.package_id.clone();
    let mut mutations = 0;
    let e = d.execute(
        "board.create",
        &json!({"title":"typed"}),
        &json!({"operationId":"controller-operation","rendezvousSeed":"12".repeat(32),"nowMs":42}),
        &b,
        |_, p| {
            assert_eq!(p.method, "CONVERSATION");
            assert_eq!(p.path, "websocket");
            let q: serde_json::Value = serde_json::from_slice(&p.body).unwrap();
            let mut frames = vec![];
            let mut http = None;
            match q["op"].as_str().unwrap() {
                "open" | "close" => {}
                "send" => {
                    let m: serde_json::Value =
                        serde_json::from_str(q["text"].as_str().unwrap()).unwrap();
                    if m["msg"] == "connect" {
                        frames.push(json!({"msg":"connected","session":"app-session"}).to_string());
                    } else if m["msg"] == "method" {
                        mutations += 1;
                        assert_eq!(m["params"][0]["members"][0]["userId"], "server-member");
                        assert_eq!(m["params"][0]["_id"], m["id"]);
                        frames.push(
                            json!({"msg":"result","id":m["id"],"result":m["id"]}).to_string(),
                        );
                    }
                }
                "rendezvous" => {
                    let m: serde_json::Value =
                        serde_json::from_str(q["text"].as_str().unwrap()).unwrap();
                    assert_eq!(m["method"], "loginWithSandstorm");
                    assert_eq!(
                        q["http"]["bodyHex"],
                        mini_sdk::hex::encode(m["params"][0].as_str().unwrap().as_bytes())
                    );
                    http = Some(204);
                    frames.push(json!({"msg":"updated","methods":[m["id"]]}).to_string());
                    frames.push(
                        json!({"msg":"result","id":m["id"],"result":{"userId":"server-member"}})
                            .to_string(),
                    );
                }
                "receive" => {
                    assert_eq!(q["condition"]["msg"], "updated");
                    frames.push(
                        json!({"msg":"updated","methods":[q["condition"]["id"]]}).to_string(),
                    );
                }
                _ => panic!("unexpected native conversation descriptor"),
            }
            let mut response =
                json!({"version":1,"channel":q["channel"],"op":q["op"],"frames":frames});
            if let Some(s) = http {
                response["httpStatus"] = json!(s)
            }
            Ok(NativeReply {
                status: 200,
                headers: vec![],
                body: serde_json::to_vec(&response).unwrap(),
                receipt: json!({"native":"retained"}),
            })
        },
    );
    assert_eq!(mutations, 1);
    assert!(e.outcome.unwrap()["id"].is_string());
    assert_eq!(e.receipts.len(), 6);
}

#[test]
fn caldav_report_does_not_require_resource_type() {
    let mut d: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/davros.json")).unwrap();
    d["operations"]["events"] = json!({"description":"events","input":{"type":"object"},"output":{"type":"array","items":{"type":"object","properties":{"href":{"type":"string"},"etag":{"type":"string"},"calendarData":{"type":"string"}},"required":["href","etag","calendarData"],"additionalProperties":false}},"write":false,"binding":{"protocol":"http","method":"REPORT","path":["dav/"],"decode":"caldav-multistatus","status":[207]}});
    let d = Declaration::load(&serde_json::to_vec(&d).unwrap()).unwrap();
    let p = d.prepare("events", &json!({}), &json!({})).unwrap();
    let xml=br#"<d:multistatus xmlns:d="DAV:" xmlns:c="urn:ietf:params:xml:ns:caldav"><d:response><d:href>/event.ics</d:href><d:propstat><d:prop><d:getetag>"a"</d:getetag><c:calendar-data>BEGIN:VCALENDAR</c:calendar-data></d:prop><d:status>HTTP/1.1 200 OK</d:status></d:propstat><d:propstat><d:prop><d:resourcetype/></d:prop><d:status>HTTP/1.1 404 Not Found</d:status></d:propstat></d:response></d:multistatus>"#;
    assert_eq!(
        d.decode(&p, 207, &[], xml).unwrap(),
        json!([{"href":"/event.ics","etag":"\"a\"","calendarData":"BEGIN:VCALENDAR"}])
    );
}
#[test]
fn readonly_await_retries_only_declared_transient_statuses() {
    use mini_sdk::app_interface::NativeReply;
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["qualification"] = json!([{"id":"repo","op":"repo.create","args":{"name":"x","description":""}},{"id":"me","op":"user.read","args":{},"assert":[{"path":["login"],"equals":"member"}],"await":{"attempts":3,"intervalSeconds":0,"retryStatuses":[503]}}]);
    let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
    let mut calls = 0;
    let mut reads = 0;
    let e = d.qualify(&json!({}), &binding(), |_, p| {
        calls += 1;
        if p.method == "POST" {
            return Ok(NativeReply {
                status: 201,
                headers: vec![("content-type".into(), "application/json".into())],
                body: br#"{"id":1,"name":"x","owner":{"id":1,"login":"member"}}"#.to_vec(),
                receipt: json!({"native":calls}),
            });
        }
        reads += 1;
        Ok(NativeReply {
            status: if reads == 1 { 503 } else { 200 },
            headers: vec![("content-type".into(), "application/json".into())],
            body: br#"{"id":1,"login":"member"}"#.to_vec(),
            receipt: json!({"native":calls}),
        })
    });
    assert_eq!(calls, 3);
    assert!(e.outcome.is_ok());
    assert_eq!(e.receipts.len(), 3);
}

#[test]
fn postmutation_cookie_refusal_is_uncertain_but_default_omit_ignores_it() {
    use mini_sdk::app_interface::NativeReply;
    for retain in [false, true] {
        let mut v: serde_json::Value =
            serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
        if retain {
            v["auth"]["appCookies"] = json!("retain")
        }
        let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
        let e = d.execute(
            "repo.create",
            &json!({"name":"x","description":""}),
            &json!({}),
            &binding(),
            |_, _| {
                Ok(NativeReply {
                    status: 201,
                    headers: vec![
                        ("content-type".into(), "application/json".into()),
                        (
                            "set-cookie".into(),
                            "__Host-mini_spk_session=forged; Path=/".into(),
                        ),
                    ],
                    body: br#"{"id":1,"name":"x","owner":{"id":1,"login":"owner"}}"#.to_vec(),
                    receipt: json!({"exact":"committed"}),
                })
            },
        );
        assert_eq!(e.receipts.len(), 1);
        if retain {
            let err = e.outcome.unwrap_err();
            assert_eq!(err.name, "app-cookie-reserved");
            assert!(err.uncertain)
        } else {
            assert!(e.outcome.is_ok())
        }
    }
}

#[test]
fn declaration_digest_matches_contract_numeric_normalization() {
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["number"] = serde_json::from_str("5e-7").unwrap();
    assert_eq!(
        Declaration::load(&serde_json::to_vec(&v).unwrap())
            .unwrap()
            .sha256,
        "3064a2deefcb7380ef493ad97241ef6284ce167ffa75944167ad4eb4d73b4176"
    );
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["number"] = serde_json::from_str("1e16").unwrap();
    assert_eq!(
        Declaration::load(&serde_json::to_vec(&v).unwrap())
            .unwrap()
            .sha256,
        "75c8e38ca7cb6d620e7e8acef955fdaf7ee757cd4bcfcc41ea43c536e3ee418e"
    );
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["number"] = serde_json::from_str("100000.0").unwrap();
    assert_eq!(
        Declaration::load(&serde_json::to_vec(&v).unwrap())
            .unwrap()
            .sha256,
        "756d7c74fb948808e52500faec393130895a715a980df7f0f379174431499295"
    );
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["number"] = serde_json::from_str("-0.0").unwrap();
    assert_eq!(
        Declaration::load(&serde_json::to_vec(&v).unwrap())
            .unwrap()
            .sha256,
        "4563f556447a18181911e9efcd9940c93075900f897cfc6a4fc33b6cc9dca3fa"
    );
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["number"] = serde_json::from_str("1.2345678901234567e30").unwrap();
    assert_eq!(
        Declaration::load(&serde_json::to_vec(&v).unwrap())
            .unwrap()
            .sha256,
        "ede046763257196f30e988101622270948ceb0549f066608f83083272b5d52a5"
    );
}

#[test]
fn qualification_refuses_missing_write_readback_before_any_dispatch() {
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["qualification"] = json!([{"id":"me","op":"user.read","args":{}}]);
    let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
    let e = d.qualify(&json!({}), &binding(), |_, _| panic!("must not dispatch"));
    assert_eq!(
        e.outcome.unwrap_err().name,
        "qualification-write-readback-absent"
    );
    assert!(e.receipts.is_empty());
}

#[test]
fn generic_json_conversation_collects_correlated_terminals_in_any_order() {
    use mini_sdk::app_interface::NativeReply;
    for reverse in [false, true] {
        let mut v: serde_json::Value =
            serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
        v["operations"]["execute"] = json!({"description":"execute","input":{"type":"object"},"output":{"type":"object"},"write":true,"binding":{"protocol":"conversation","wire":"json-v1","path":["channels"],"steps":[{"send":{"header":{"msg_id":{"context":"operationId"}},"content":"code"}},{"receiveAll":[{"id":"reply","where":[{"path":["parent"],"equals":{"context":"operationId"}},{"path":["kind"],"equals":"reply"}]},{"id":"idle","where":[{"path":["parent"],"equals":{"context":"operationId"}},{"path":["kind"],"equals":"idle"}]}]}],"result":{"reply":{"result":["reply","value"]},"idle":{"result":["idle","kind"]}}}});
        let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
        let mut sends = 0;
        let e = d.execute(
            "execute",
            &json!({}),
            &json!({"operationId":"fresh"}),
            &binding(),
            |_, p| {
                let q: serde_json::Value = serde_json::from_slice(&p.body).unwrap();
                let mut frames = vec![];
                if q["op"] == "send" {
                    sends += 1;
                    frames = vec![
                        json!({"parent":"other","kind":"reply","value":0}).to_string(),
                        json!({"parent":"fresh","kind":"reply","value":42}).to_string(),
                        json!({"parent":"fresh","kind":"idle"}).to_string(),
                    ];
                    if reverse {
                        frames.reverse();
                    }
                }
                Ok(NativeReply {
                    status: 200,
                    headers: vec![],
                    body: json!({"version":1,"channel":q["channel"],"op":q["op"],"frames":frames})
                        .to_string()
                        .into_bytes(),
                    receipt: json!({"exact":true}),
                })
            },
        );
        assert_eq!(sends, 1);
        assert_eq!(e.outcome.unwrap(), json!({"reply":42,"idle":"idle"}));
        assert_eq!(e.receipts.len(), 3);
    }
}
#[test]
fn bound_tool_projection_rejects_collisions_and_reserved_qualify() {
    let d = Declaration::load(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    assert_eq!(
        d.bound_tools("my_gogs").unwrap()[0]["name"],
        "mini_app_my_gogs_comment_create"
    );
    assert!(mini_sdk::app_interface::bound_tool_name("bad-name", "a").is_err());
    assert!(mini_sdk::app_interface::bound_tool_name("ok", "qualify").is_err());
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["operations"]["repo_create"] = v["operations"]["repo.create"].clone();
    assert_eq!(
        Declaration::load(&serde_json::to_vec(&v).unwrap())
            .unwrap_err()
            .name,
        "operation-tool-name-collision"
    );
}

#[test]
fn conversation_preflight_refuses_duplicate_and_forward_captures() {
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    for steps in [
        json!([{"send":{"result":["future"]}},{"id":"future","receive":{}}]),
        json!([{"id":"same","receive":{}},{"id":"same","receive":{}}]),
    ] {
        v["operations"]["macro"] = json!({"description":"macro","input":{"type":"object"},"output":{},"write":true,"binding":{"protocol":"conversation","wire":"json-v1","path":["ws"],"steps":steps,"result":true}});
        assert!(Declaration::load(&serde_json::to_vec(&v).unwrap()).is_err());
    }
}

#[test]
fn generic_missing_terminal_is_uncertain_without_replaying_send() {
    use mini_sdk::app_interface::NativeReply;
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["operations"]["execute"] = json!({"description":"execute","input":{"type":"object"},"output":{"type":"object"},"write":true,"binding":{"protocol":"conversation","wire":"json-v1","path":["channels"],"steps":[{"send":{"date":{"context":"nowIso"}}},{"id":"reply","receive":{"where":[{"path":["kind"],"equals":"reply"}]}}],"result":{"result":["reply"]}}});
    let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
    let mut sends = 0;
    let e = d.execute(
        "execute",
        &json!({}),
        &json!({"operationId":"fixed","nowMs":0}),
        &binding(),
        |_, p| {
            let q: serde_json::Value = serde_json::from_slice(&p.body).unwrap();
            if q["op"] == "send" {
                sends += 1;
                assert_eq!(
                    serde_json::from_str::<serde_json::Value>(q["text"].as_str().unwrap()).unwrap()
                        ["date"],
                    "1970-01-01T00:00:00.000Z"
                );
            }
            Ok(NativeReply {
                status: 200,
                headers: vec![],
                body: json!({"version":1,"channel":q["channel"],"op":q["op"],"frames":[]})
                    .to_string()
                    .into_bytes(),
                receipt: json!({"exact":true}),
            })
        },
    );
    assert_eq!(sends, 1);
    assert!(e.outcome.unwrap_err().uncertain);
    assert!(e.receipts.len() > 2);
}

#[test]
fn sandforms_credential_resume_uses_private_admitted_http_then_server_identity() {
    use mini_sdk::app_interface::NativeReply;
    let d = Declaration::load(include_bytes!("../../../apps/interfaces/sandforms.json")).unwrap();
    let mut b = binding();
    b.package_id = d.package_id.clone();
    let mut credentials = 0;
    let mut mutations = 0;
    let e = d.execute(
        "questions.create",
        &json!({"text":"Question?","required":true}),
        &json!({"operationId":"sandforms-call"}),
        &b,
        |bound, p| {
            assert_eq!(bound.subject, "7");
            if p.method == "GET" {
                credentials += 1;
                assert_eq!(p.path, ".sandstorm-credentials");
                return Ok(NativeReply {
                    status: 200,
                    headers: vec![("content-type".into(), "application/json".into())],
                    body: br#"{"token":"private-resume"}"#.to_vec(),
                    receipt: json!({"private":"credential-receipt"}),
                });
            }
            let q: serde_json::Value = serde_json::from_slice(&p.body).unwrap();
            let mut frames = vec![];
            if q["op"] == "send" {
                let m: serde_json::Value =
                    serde_json::from_str(q["text"].as_str().unwrap()).unwrap();
                if m["msg"] == "connect" {
                    frames.push(json!({"msg":"connected"}).to_string())
                } else {
                    let result = if m["method"] == "login" {
                        assert_eq!(m["params"], json!([{"resume":"private-resume"}]));
                        json!({"id":"server-user"})
                    } else {
                        mutations += 1;
                        assert_eq!(m["method"], "Prompts.create");
                        json!("prompt-id")
                    };
                    frames.push(json!({"msg":"updated","methods":[m["id"]]}).to_string());
                    frames.push(json!({"msg":"result","id":m["id"],"result":result}).to_string());
                }
            }
            Ok(NativeReply {
                status: 200,
                headers: vec![],
                body: json!({"version":1,"channel":q["channel"],"op":q["op"],"frames":frames})
                    .to_string()
                    .into_bytes(),
                receipt: json!({"private":"native-receipt"}),
            })
        },
    );
    assert_eq!(credentials, 1);
    assert_eq!(mutations, 1);
    assert_eq!(e.outcome.unwrap(), json!("prompt-id"));
    assert_eq!(e.receipts.len(), 6);
}
#[test]
fn ddp_absolute_deadline_stops_after_incomplete_mutation_without_replay() {
    use mini_sdk::app_interface::NativeReply;
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/sandforms.json")).unwrap();
    v["limits"]["seconds"] = json!(1);
    let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
    let mut b = binding();
    b.package_id = d.package_id.clone();
    let mut mutations = 0;
    let start = std::time::Instant::now();
    let e = d.execute(
        "questions.create",
        &json!({"text":"Question?","required":true}),
        &json!({"operationId":"bounded-call"}),
        &b,
        |_, p| {
            if p.method == "GET" {
                return Ok(NativeReply {
                    status: 200,
                    headers: vec![("content-type".into(), "application/json".into())],
                    body: br#"{"token":"private"}"#.to_vec(),
                    receipt: json!({"native":true}),
                });
            }
            let q: serde_json::Value = serde_json::from_slice(&p.body).unwrap();
            if let Some(ms) = q["deadlineMs"].as_u64() {
                assert!(ms <= 1000)
            }
            let mut frames = vec![];
            if q["op"] == "send" {
                let m: serde_json::Value =
                    serde_json::from_str(q["text"].as_str().unwrap()).unwrap();
                if m["msg"] == "connect" {
                    frames.push(json!({"msg":"connected"}).to_string())
                } else if m["method"] == "login" {
                    frames.push(
                        json!({"msg":"result","id":m["id"],"result":{"id":"member"}}).to_string(),
                    );
                    frames.push(json!({"msg":"updated","methods":[m["id"]]}).to_string());
                } else {
                    mutations += 1;
                    std::thread::sleep(std::time::Duration::from_millis(1050));
                }
            }
            Ok(NativeReply {
                status: 200,
                headers: vec![],
                body: json!({"version":1,"channel":q["channel"],"op":q["op"],"frames":frames})
                    .to_string()
                    .into_bytes(),
                receipt: json!({"native":true}),
            })
        },
    );
    assert_eq!(mutations, 1);
    let error = e.outcome.unwrap_err();
    assert_eq!(error.name, "ddp-deadline");
    assert!(error.uncertain);
    assert!(start.elapsed() < std::time::Duration::from_secs(3));
    assert!(e.receipts.len() >= 5);
}

#[test]
fn complete_curated_inventory_loads_and_projects_native_tools() {
    let checked_in = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../apps/interfaces");
    let mut entries = Vec::new();
    for entry in std::fs::read_dir(checked_in).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "json") {
            let bytes = std::fs::read(&path).unwrap();
            let source: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
            if source["format"] == "mini-app-interface-v1" {
                entries.push((path.display().to_string(), bytes, None));
            }
        }
    }
    assert!(!entries.is_empty(), "checked-in declaration inventory is empty");
    if let Some(dir) = std::env::var_os("MINI_ALL_INTERFACES") {
        let dir = std::path::PathBuf::from(dir);
        let manifest: serde_json::Value =
            serde_json::from_slice(&std::fs::read(dir.join("manifest.json")).unwrap()).unwrap();
        assert!(!manifest.as_object().unwrap().is_empty());
        for (name, meta) in manifest.as_object().unwrap() {
            entries.push((name.clone(), std::fs::read(dir.join(name)).unwrap(),
                Some(meta["interfaceDigest"].clone())));
        }
    }
    for (name, bytes, digest) in entries {
        let d = Declaration::load(&bytes).unwrap_or_else(|e| panic!("{name}: {}", e.name));
        if let Some(digest) = digest {
            assert_eq!(d.sha256, digest, "{name} digest parity");
        }
        let tools = d
            .bound_tools("member_app")
            .unwrap_or_else(|e| panic!("{name}: {}", e.name));
        let source: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        let expected = source["operations"]
            .as_object()
            .unwrap()
            .values()
            .filter(|op| op["internal"] != true)
            .count();
        assert_eq!(tools.len(), expected, "{name} public tools");
        for tool in tools {
            assert!(tool["name"]
                .as_str()
                .unwrap()
                .starts_with("mini_app_member_app_"));
            assert!(tool["inputSchema"].is_object());
            assert_eq!(tool["_meta"]["interfaceDigest"], d.sha256);
        }
    }
}

#[test]
fn schema_object_property_bound_refuses_before_dispatch() {
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["operations"]["repo.create"]["input"]["maxProperties"] = json!(1);
    let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
    let e = d.execute(
        "repo.create",
        &json!({"name":"x","description":""}),
        &json!({}),
        &binding(),
        |_, _| panic!("bound refused before dispatch"),
    );
    assert_eq!(e.outcome.unwrap_err().name, "input-schema");
    assert!(e.receipts.is_empty());
}

#[test]
fn readonly_and_compound_qualification_gates_preserve_correlated_results() {
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["operations"]["hit"] = json!({"description":"hit","input":{"type":"object"},"output":{"type":"object"},"write":true,"binding":{"protocol":"conversation","wire":"json-v1","path":["ws"],"steps":[{"send":{"request":"beacon"}},{"id":"hit","receive":{"where":[{"path":["id"],"equals":"mine"}]}}],"result":{"result":["hit"]}}});
    v["qualification"] =
        json!([{"id":"hit","op":"hit","args":{},"assert":[{"path":["id"],"equals":"mine"}]}]);
    let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
    let e = d.qualify(&json!({"operationId":"correlated"}), &binding(), |_, p| {
        let q: serde_json::Value = serde_json::from_slice(&p.body).unwrap();
        let frames = if q["op"] == "send" {
            vec![json!({"id":"mine"}).to_string()]
        } else {
            vec![]
        };
        Ok(mini_sdk::app_interface::NativeReply {
            status: 200,
            headers: vec![],
            body: json!({"version":1,"channel":q["channel"],"op":q["op"],"frames":frames})
                .to_string()
                .into_bytes(),
            receipt: json!({"private":true}),
        })
    });
    assert_eq!(e.outcome.unwrap()["hit"]["id"], "mine");
}

#[test]
fn generic_absolute_deadline_bounds_open_and_forbids_cleanup_after_mutation() {
    use mini_sdk::app_interface::NativeReply;
    let mut v: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../../apps/interfaces/gogs.json")).unwrap();
    v["limits"]["seconds"] = json!(1);
    v["operations"]["macro"] = json!({"description":"macro","input":{"type":"object"},"output":{"type":"object"},"write":true,"binding":{"protocol":"conversation","wire":"json-v1","path":["ws"],"steps":[{"send":{"request":"write"}},{"http":{"protocol":"http","method":"GET","path":["read"],"status":[200],"decode":"json"},"id":"read"}],"result":{"result":["read"]}}});
    let d = Declaration::load(&serde_json::to_vec(&v).unwrap()).unwrap();
    let start = std::time::Instant::now();
    let mut callbacks = vec![];
    let e = d.execute(
        "macro",
        &json!({}),
        &json!({"operationId":"one-deadline"}),
        &binding(),
        |_, p| {
            assert!(
                start.elapsed() < std::time::Duration::from_secs(1),
                "no callback after absolute deadline"
            );
            let q: serde_json::Value = serde_json::from_slice(&p.body).unwrap();
            callbacks.push(q["op"].as_str().unwrap().to_owned());
            if q["op"] == "open" {
                assert!(q["deadlineMs"].as_u64().unwrap() <= 1000)
            }
            if q["op"] == "send" {
                std::thread::sleep(std::time::Duration::from_millis(1050));
            }
            Ok(NativeReply {
                status: 200,
                headers: vec![],
                body: json!({"version":1,"channel":q["channel"],"op":q["op"],"frames":[]})
                    .to_string()
                    .into_bytes(),
                receipt: json!({"private":"exact-native"}),
            })
        },
    );
    assert_eq!(callbacks, vec!["open", "send"]);
    let error = e.outcome.unwrap_err();
    assert_eq!(error.name, "conversation-deadline");
    assert!(error.uncertain);
    assert_eq!(e.receipts.len(), 2);
}

/// A qualification step whose `args` has one member named like a binding form (`{"path": ...}`,
/// Davros's directory.create) is an object of bindings, never the `path` form: the first step must
/// reach the dispatcher (it was refused declaration-invalid before it did).
#[test]
fn a_one_member_args_object_named_path_is_not_the_path_binding_form() {
    use mini_sdk::app_interface::NativeReply;
    let d = Declaration::load(include_bytes!("../../../apps/interfaces/davros.json")).unwrap();
    let mut b = binding();
    b.package_id = d.package_id.clone();
    let mut first: Option<(String, String)> = None;
    let e = d.qualify(&json!({"runId":"run1"}), &b, |_, p| {
        first.get_or_insert((p.method.clone(), p.path.clone()));
        Ok(NativeReply { status: 201, headers: vec![], body: vec![], receipt: json!({"native":1}) })
    });
    assert_eq!(first, Some(("MKCOL".into(), "dav/run1".into())), "{:?}", e.outcome);
}
