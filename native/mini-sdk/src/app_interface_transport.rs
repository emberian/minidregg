//! Closed conversation carriers and protocol codecs; all I/O uses current native admission.
use super::*;

impl Declaration {
    fn conversation<F>(
        &self,
        name: &str,
        binding: &SessionBinding,
        path: &str,
        descriptor: Value,
        mutation: bool,
        dispatch: &mut F,
        receipts: &mut Vec<Value>,
    ) -> Result<Value>
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        self.conversation_at(
            name, binding, path, "", descriptor, mutation, dispatch, receipts,
        )
    }
    fn conversation_at<F>(
        &self,
        name: &str,
        binding: &SessionBinding,
        path: &str,
        query: &str,
        descriptor: Value,
        mutation: bool,
        dispatch: &mut F,
        receipts: &mut Vec<Value>,
    ) -> Result<Value>
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        let body = serde_json::to_vec(&descriptor)
            .map_err(|_| refuse("conversation-descriptor-invalid"))?;
        if body.len() > 65536 {
            return Err(refuse("body-over-bound"));
        }
        let call = PreparedCall {
            method: "CONVERSATION".into(),
            path: path.into(),
            query: query.into(),
            ordered_headers: vec![("content-type".into(), "application/json".into())],
            body,
            declaration_sha256: self.sha256.clone(),
            package_id: self.package_id.clone(),
            operation: name.into(),
            write: mutation,
        };
        let reply = dispatch(binding, &call)?;
        receipts.push(reply.receipt);
        let result = (|| {
            if reply.status != 200 {
                return Err(refuse("conversation-http-refused"));
            }
            if reply.body.len() > 1048576 {
                return Err(refuse("reply-over-bound"));
            }
            let v: Value = serde_json::from_slice(&reply.body)
                .map_err(|_| refuse("conversation-response-invalid"))?;
            if v["version"] != 1
                || v["channel"] != descriptor["channel"]
                || v["op"] != descriptor["op"]
                || !v["frames"]
                    .as_array()
                    .is_some_and(|a| a.iter().all(Value::is_string))
            {
                return Err(refuse("conversation-response-mismatch"));
            }
            Ok(v)
        })();
        result.map_err(|mut e: Refusal| {
            e.uncertain |= mutation;
            e
        })
    }
    fn ddp_frames<F>(
        &self,
        name: &str,
        binding: &SessionBinding,
        path: &str,
        channel: &str,
        reply: &Value,
        state: &mut crate::app_interface_ddp::DdpState,
        dispatch: &mut F,
        receipts: &mut Vec<Value>,
    ) -> Result<()>
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        for frame in reply["frames"]
            .as_array()
            .ok_or_else(|| refuse("conversation-response-invalid"))?
        {
            if let Some(pong) = state.frame(
                string(frame)?,
                number(&self.value["limits"]["snapshotDocuments"])? as usize,
            )? {
                let text = serde_json::to_string(&pong).map_err(|_| refuse("ddp-frame-invalid"))?;
                self.conversation(
                    name,
                    binding,
                    path,
                    json!({"version":1,"op":"send","channel":channel,"text":text}),
                    false,
                    dispatch,
                    receipts,
                )?;
            }
        }
        Ok(())
    }
    pub(super) fn execute_ddp<F>(
        &self,
        name: &str,
        args: &Value,
        context: &Value,
        binding: &SessionBinding,
        dispatch: &mut F,
        receipts: &mut Vec<Value>,
    ) -> Result<Value>
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        let op = self.operation(name)?;
        let b = &op["binding"];
        let auth = &self.value["auth"];
        let auth_kind = string(&auth["kind"])?;
        if !matches!(auth_kind, "sandstorm-ddp-rendezvous" | "credential-resume") {
            return Err(refuse("auth-protocol-unsupported"));
        }
        let seconds = number(&self.value["limits"]["seconds"])?.min(300);
        if seconds == 0 {
            return Err(refuse("ddp-deadline-invalid"));
        }
        let end = std::time::Instant::now() + std::time::Duration::from_secs(seconds);
        // One fixed budget covers credentials, open, connect, login, application
        // frames and close. Per-receive budgets only attenuate this deadline.
        let original_dispatch = dispatch;
        let mut bounded_dispatch = |binding: &SessionBinding, call: &PreparedCall| {
            let left = end
                .checked_duration_since(std::time::Instant::now())
                .filter(|d| !d.is_zero())
                .ok_or_else(|| Refusal {
                    name: "ddp-deadline".into(),
                    uncertain: false,
                })?;
            let mut call = call.clone();
            if call.method == "CONVERSATION" {
                let mut descriptor: Value = serde_json::from_slice(&call.body)
                    .map_err(|_| refuse("conversation-descriptor-invalid"))?;
                if descriptor.get("deadlineMs").is_some() {
                    let ms = left.as_millis().min(30000).max(1) as u64;
                    descriptor["deadlineMs"] =
                        json!(descriptor["deadlineMs"].as_u64().unwrap_or(ms).min(ms));
                    call.body = serde_json::to_vec(&descriptor)
                        .map_err(|_| refuse("conversation-descriptor-invalid"))?;
                }
            }
            original_dispatch(binding, &call)
        };
        let dispatch = &mut bounded_dispatch;
        let seed = if auth_kind == "sandstorm-ddp-rendezvous" {
            let seed = context["rendezvousSeed"]
                .as_str()
                .ok_or_else(|| refuse("controller-rendezvous-seed-required"))?;
            if seed.len() != 64
                || !seed
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            {
                return Err(refuse("controller-rendezvous-seed-invalid"));
            }
            seed
        } else {
            ""
        };
        let serial = receipts.len();
        let root_id = context["operationId"]
            .as_str()
            .ok_or_else(|| refuse("controller-operation-id-required"))?;
        let id = format!(
            "{:x}",
            Sha256::digest(format!("mini/ddp/op/v1/{root_id}/{serial}/{name}"))
        );
        let channel = channel_name(&format!("mini/ddp/channel/v1/{root_id}/{serial}/{name}"));
        let token = format!(
            "{:x}",
            Sha256::digest(format!("mini/ddp/auth/v1/{seed}/{id}"))
        );
        let path = string(&auth["websocket"])?.trim_start_matches('/');
        let mut state = crate::app_interface_ddp::DdpState::default();
        let open=self.conversation(name,binding,path,json!({"version":1,"op":"open","channel":channel,"protocol":"ddp-v1","maxFrames":64,"maxBytes":65536,"deadlineMs":30000}),false,dispatch,receipts)?;
        let mut sent_mutation = false;
        let result=(||{
            self.ddp_frames(name,binding,path,&channel,&open,&mut state,dispatch,receipts)?;
            let connect=json!({"msg":"connect","version":"1","support":["1"]}).to_string();
            let reply=self.conversation(name,binding,path,json!({"version":1,"op":"send","channel":channel,"text":connect}),false,dispatch,receipts)?;
            self.ddp_frames(name,binding,path,&channel,&reply,&mut state,dispatch,receipts)?;
            if !state.connected{
                let reply=self.conversation(name,binding,path,json!({"version":1,"op":"receive","channel":channel,"condition":{"msg":"any"},"maxFrames":64,"maxBytes":65536,"deadlineMs":30000}),false,dispatch,receipts)?;
                self.ddp_frames(name,binding,path,&channel,&reply,&mut state,dispatch,receipts)?;
                if !state.connected{return Err(refuse("ddp-connect-incomplete"))}
            }
            let login_id=format!("login-{id}");
            let reply=if auth_kind=="credential-resume"{
                let credentials=PreparedCall{method:"GET".into(),path:string(&auth["credentialsPath"])?.trim_start_matches('/').into(),query:String::new(),ordered_headers:vec![],body:vec![],declaration_sha256:self.sha256.clone(),package_id:self.package_id.clone(),operation:name.into(),write:false};
                let reply=dispatch(binding,&credentials)?;receipts.push(reply.receipt);
                if reply.status!=200||!reply.headers.iter().any(|(k,v)|k.eq_ignore_ascii_case("content-type")&&v.to_ascii_lowercase().contains("json")){return Err(refuse("auth-credentials-refused"))}
                if reply.body.len() as u64>number(&self.value["limits"]["replyBytes"])?{return Err(refuse("reply-over-bound"))}
                let credentials:Value=serde_json::from_slice(&reply.body).map_err(|_|refuse("auth-credentials-invalid"))?;
                let resume=credentials[string(&auth["tokenField"])?].as_str().filter(|s|!s.is_empty()&&s.len()<=4096).ok_or_else(||refuse("auth-credentials-invalid"))?;
                let login=json!({"msg":"method","method":auth["method"],"id":login_id,"params":[{"resume":resume}]}).to_string();
                self.conversation(name,binding,path,json!({"version":1,"op":"send","channel":channel,"text":login}),false,dispatch,receipts)?
            }else{
                let login=json!({"msg":"method","method":auth["method"],"id":login_id,"params":[token]}).to_string();
                let reply=self.conversation(name,binding,path,json!({"version":1,"op":"rendezvous","channel":channel,"text":login,"http":{"method":"POST","path":string(&auth["postPath"])?.trim_start_matches('/'),"query":"","headers":[{"name":"content-type","value":auth["contentType"]}],"bodyHex":crate::hex::encode(token.as_bytes())},"maxFrames":64,"maxBytes":65536,"deadlineMs":30000}),false,dispatch,receipts)?;
                if reply["httpStatus"]!=204{return Err(refuse("auth-rendezvous-refused"))}reply
            };
            self.ddp_frames(name,binding,path,&channel,&reply,&mut state,dispatch,receipts)?;
            let login=self.ddp_finish(name,binding,path,&channel,&login_id,&mut state,false,dispatch,receipts)?;
            let uid=login[string(&auth["userIdField"])?].as_str().filter(|s|!s.is_empty()).ok_or_else(||refuse("auth-member-required"))?;
            let mut local=context.clone();local["userId"]=json!(uid);local["operationId"]=json!(id);
            let params=resolve(&b["params"],args,&local,&Value::Null)?;
            match string(&b["kind"])?{
                "method"=>{
                    let frame=json!({"msg":"method","method":b["method"],"id":id,"params":params}).to_string();
                    let reply=self.conversation(name,binding,path,json!({"version":1,"op":"send","channel":channel,"text":frame}),op["write"]==true,dispatch,receipts)?;
                    sent_mutation=op["write"]==true;
                    self.ddp_frames(name,binding,path,&channel,&reply,&mut state,dispatch,receipts)?;
                    let value=self.ddp_finish(name,binding,path,&channel,&id,&mut state,sent_mutation,dispatch,receipts)?;
                    if b["result"]=="insert-id" {if value!=id{return Err(refuse("ddp-insert-id-mismatch"))}Ok(json!({"id":id}))}else if b["result"]=="json"{Ok(value)}else{Err(refuse("ddp-result-unsupported"))}
                },
                "snapshot"=>{
                    let frame=json!({"msg":"sub","id":id,"name":b["publication"],"params":params}).to_string();
                    let reply=self.conversation(name,binding,path,json!({"version":1,"op":"send","channel":channel,"text":frame}),false,dispatch,receipts)?;
                    self.ddp_frames(name,binding,path,&channel,&reply,&mut state,dispatch,receipts)?;
                    let collections=b["collections"].as_array().ok_or_else(||refuse("declaration-invalid"))?.iter().map(|v|string(v).map(str::to_owned)).collect::<Result<Vec<_>>>()?;
                    if let Some(value)=state.snapshot(&id,&collections)?{return Ok(value)}
                    let reply=self.conversation(name,binding,path,json!({"version":1,"op":"receive","channel":channel,"condition":{"msg":"ready","id":id},"maxFrames":64,"maxBytes":65536,"deadlineMs":30000}),false,dispatch,receipts)?;
                    self.ddp_frames(name,binding,path,&channel,&reply,&mut state,dispatch,receipts)?;
                    state.snapshot(&id,&collections)?.ok_or_else(||refuse("ddp-publication-incomplete"))
                },_=>Err(refuse("ddp-kind-unsupported")),
            }
        })().map_err(|mut e|{if sent_mutation&&e.name!="ddp-method-refused"{e.uncertain=true;}e});
        // A close is a fresh admitted operation, never a replay of any method.
        let close = self.conversation(
            name,
            binding,
            path,
            json!({"version":1,"op":"close","channel":channel}),
            false,
            dispatch,
            receipts,
        );
        match result {
            Err(e) => Err(e),
            Ok(v) => {
                close.map_err(|mut e: Refusal| {
                    e.uncertain |= sent_mutation;
                    e
                })?;
                Ok(v)
            }
        }
    }
    fn ddp_finish<F>(
        &self,
        name: &str,
        binding: &SessionBinding,
        path: &str,
        channel: &str,
        id: &str,
        state: &mut crate::app_interface_ddp::DdpState,
        mutation: bool,
        dispatch: &mut F,
        receipts: &mut Vec<Value>,
    ) -> Result<Value>
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        if let Some(v) = state.method_result(id)? {
            return Ok(v);
        }
        // Both result and updated are required; receive preserves all intervening
        // frames, so either order and a combined frame batch are accepted.
        for _ in 0..64 {
            if let Some(v) = state.method_result(id)? {
                return Ok(v);
            }
            let msg = state.method_waiting_for(id);
            let reply=self.conversation(name,binding,path,json!({"version":1,"op":"receive","channel":channel,"condition":{"msg":msg,"id":id},"maxFrames":64,"maxBytes":65536,"deadlineMs":30000}),mutation,dispatch,receipts)?;
            self.ddp_frames(
                name, binding, path, channel, &reply, state, dispatch, receipts,
            )?;
        }
        state.method_result(id)?.ok_or_else(|| Refusal {
            name: "ddp-method-incomplete".into(),
            uncertain: mutation,
        })
    }
}

#[derive(Clone)]
struct Packet {
    event: Option<String>,
    value: Value,
}
struct Wire {
    kind: String,
    opened: bool,
    connected: bool,
    ping_interval: std::time::Duration,
    last_ping: std::time::Instant,
}
impl Wire {
    fn new(kind: &str) -> Result<Self> {
        if !matches!(kind, "json-v1" | "socket.io-eio3" | "socket.io-eio4") {
            return Err(refuse("conversation-wire-unsupported"));
        }
        Ok(Self {
            kind: kind.into(),
            opened: kind == "json-v1",
            connected: kind == "json-v1",
            ping_interval: std::time::Duration::from_secs(25),
            last_ping: std::time::Instant::now(),
        })
    }
    fn frame(&mut self, text: &str) -> Result<(Option<Packet>, Vec<String>)> {
        if self.kind == "json-v1" {
            return Ok((
                Some(Packet {
                    event: None,
                    value: serde_json::from_str(text)
                        .map_err(|_| refuse("conversation-json-invalid"))?,
                }),
                vec![],
            ));
        }
        if let Some(open) = text.strip_prefix('0') {
            if self.opened {
                return Err(refuse("socketio-duplicate-open"));
            }
            let open: Value =
                serde_json::from_str(open).map_err(|_| refuse("socketio-open-invalid"))?;
            if !open["sid"].is_string() {
                return Err(refuse("socketio-open-invalid"));
            }
            let interval = open["pingInterval"]
                .as_u64()
                .filter(|n| *n > 0 && *n <= 300000)
                .ok_or_else(|| refuse("socketio-open-invalid"))?;
            self.ping_interval = std::time::Duration::from_millis(interval);
            self.opened = true;
            return Ok((
                None,
                if self.kind == "socket.io-eio4" {
                    vec!["40".into()]
                } else {
                    vec![]
                },
            ));
        }
        if !self.opened {
            return Err(refuse("socketio-frame-before-open"));
        }
        if text == "2" {
            return Ok((None, vec!["3".into()]));
        }
        if text == "3" {
            return Ok((None, vec![]));
        }
        if text == "40" || text.starts_with("40{") {
            self.connected = true;
            return Ok((None, vec![]));
        }
        if text.starts_with("44") || text == "1" || text == "41" {
            return Err(refuse("socketio-connection-refused"));
        }
        if let Some(text) = text.strip_prefix("42") {
            if !self.connected {
                return Err(refuse("socketio-event-before-connect"));
            }
            let packet: Value =
                serde_json::from_str(text).map_err(|_| refuse("socketio-event-invalid"))?;
            let values = packet
                .as_array()
                .filter(|a| !a.is_empty())
                .ok_or_else(|| refuse("socketio-event-invalid"))?;
            let event = values[0]
                .as_str()
                .ok_or_else(|| refuse("socketio-event-invalid"))?;
            return Ok((
                Some(Packet {
                    event: Some(event.into()),
                    value: Value::Array(values[1..].to_vec()),
                }),
                vec![],
            ));
        }
        Err(refuse("socketio-frame-unsupported"))
    }
    fn emit(&self, event: &str, args: Value) -> Result<String> {
        if self.kind == "json-v1" || !self.connected {
            return Err(refuse("socketio-not-connected"));
        }
        let mut payload = vec![json!(event)];
        payload.extend(
            args.as_array()
                .ok_or_else(|| refuse("conversation-args-invalid"))?
                .iter()
                .cloned(),
        );
        Ok(format!(
            "42{}",
            serde_json::to_string(&payload).map_err(|_| refuse("conversation-json-invalid"))?
        ))
    }
    fn heartbeat(&mut self) -> Option<String> {
        if self.kind == "socket.io-eio3" && self.last_ping.elapsed() >= self.ping_interval {
            self.last_ping = std::time::Instant::now();
            Some("2".into())
        } else {
            None
        }
    }
}
const APP_REFUSED: &str = "app-refused: ";

/// The frames a step received but did not match, counted by event: "(unmatched: user_joined x1)".
fn unmatched(queue: &std::collections::VecDeque<Packet>) -> String {
    let mut seen = std::collections::BTreeMap::<String, usize>::new();
    for packet in queue {
        *seen.entry(packet.event.clone().unwrap_or_else(|| "message".into())).or_default() += 1;
    }
    let seen: Vec<_> = seen.iter().map(|(e, n)| format!("{e} x{n}")).collect();
    format!("(unmatched: {})", if seen.is_empty() { "nothing".into() } else { seen.join(", ") })
}

/// A queued frame that a pending receive's `refuseOn` names (the app's own rejection of the awaited
/// result, e.g. WBO's `mutation_rejected` for this clientMutationId) ends the step at once with the
/// app's reason, instead of polling until the step's bound.
fn app_refusal(
    pending: &[Value],
    queue: &std::collections::VecDeque<Packet>,
    args: &Value,
    context: &Value,
    results: &Value,
) -> Result<Option<Refusal>> {
    for condition in pending {
        let Some(refusals) = condition.get("refuseOn").and_then(Value::as_array) else { continue };
        for packet in queue {
            for refusal in refusals {
                if check_packet(packet, refusal, args, context, results)? {
                    let reason = lookup(&packet.value, &refusal["reason"])
                        .ok()
                        .map(|v| v.as_str().map(str::to_owned).unwrap_or_else(|| v.to_string()))
                        .unwrap_or_else(|| "no reason given".into());
                    let reason: String = reason.chars().filter(|c| !c.is_control()).take(200).collect();
                    return Ok(Some(refuse(&format!("{APP_REFUSED}{reason}"))));
                }
            }
        }
    }
    Ok(None)
}

fn check_packet(
    packet: &Packet,
    condition: &Value,
    args: &Value,
    context: &Value,
    results: &Value,
) -> Result<bool> {
    if let Some(event) = condition.get("event") {
        if packet.event.as_deref() != event.as_str() {
            return Ok(false);
        }
    }
    if let Some(checks) = condition.get("where") {
        for check in checks
            .as_array()
            .ok_or_else(|| refuse("conversation-check-invalid"))?
        {
            let got = lookup(&packet.value, &check["path"]);
            if check["exists"] == true {
                if got.is_err() {
                    return Ok(false);
                }
                continue;
            }
            let Ok(got) = got else { return Ok(false) };
            if let Some(expected) = check.get("equals") {
                if *got != resolve(expected, args, context, results)? {
                    return Ok(false);
                }
            } else if let Some(expected) = check.get("contains") {
                let expected = resolve(expected, args, context, results)?;
                if !got.as_array().is_some_and(|a| {
                    a.iter().any(|v| {
                        if expected.is_object() {
                            matches_fields(v, &expected)
                        } else {
                            *v == expected
                        }
                    })
                }) {
                    return Ok(false);
                }
            } else {
                return Err(refuse("conversation-check-invalid"));
            }
        }
    }
    Ok(true)
}

impl Declaration {
    pub(super) fn execute_conversation<F>(
        &self,
        name: &str,
        args: &Value,
        context: &Value,
        binding: &SessionBinding,
        dispatch: &mut F,
        receipts: &mut Vec<Value>,
        cookies: &mut CookieJar,
    ) -> Result<Value>
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        let op = self.operation(name)?;
        let b = &op["binding"];
        let kind = string(&b["wire"])?;
        let mut wire = Wire::new(kind)?;
        let path = path(&b["path"], args)?;
        let q = resolve(
            b.get("query").unwrap_or(&json!({})),
            args,
            context,
            &json!({}),
        )?;
        let mut query = q
            .as_object()
            .ok_or_else(|| refuse("query-invalid"))?
            .iter()
            .map(|(k, v)| Ok(format!("{}={}", percent(k), percent(&scalar(v)?))))
            .collect::<Result<Vec<_>>>()?;
        if kind != "json-v1" {
            if q.get("EIO").is_some() || q.get("transport").is_some() {
                return Err(refuse("socketio-query-reserved"));
            }
            query.push(format!(
                "EIO={}",
                if kind == "socket.io-eio3" { 3 } else { 4 }
            ));
            query.push("transport=websocket".into());
        }
        let query = query.join("&");
        let root = context["operationId"]
            .as_str()
            .ok_or_else(|| refuse("controller-operation-id-required"))?;
        let channel = channel_name(&format!(
            "mini/conversation/v1/{root}/{name}/{}",
            receipts.len()
        ));
        let seconds = number(&self.value["limits"]["seconds"])?.min(300);
        if seconds == 0 {
            return Err(refuse("conversation-deadline-invalid"));
        }
        let end = std::time::Instant::now() + std::time::Duration::from_secs(seconds);
        // This one boundary covers open, protocol control sends, HTTP steps,
        // receives and cleanup. Helpers cannot reset or bypass the budget.
        let original_dispatch = dispatch;
        let mut bounded_dispatch = |binding: &SessionBinding, call: &PreparedCall| {
            let left = end
                .checked_duration_since(std::time::Instant::now())
                .filter(|d| !d.is_zero())
                .ok_or_else(|| refuse("conversation-deadline"))?;
            let mut call = call.clone();
            if call.method == "CONVERSATION" {
                let mut descriptor: Value = serde_json::from_slice(&call.body)
                    .map_err(|_| refuse("conversation-descriptor-invalid"))?;
                if let Some(existing) = descriptor.get("deadlineMs") {
                    let remaining = left.as_millis().min(30000).max(1) as u64;
                    descriptor["deadlineMs"] =
                        json!(existing.as_u64().unwrap_or(remaining).min(remaining));
                    call.body = serde_json::to_vec(&descriptor)
                        .map_err(|_| refuse("conversation-descriptor-invalid"))?;
                }
            }
            original_dispatch(binding, &call)
        };
        let dispatch = &mut bounded_dispatch;
        let open=self.conversation_at(name,binding,&path,&query,json!({"version":1,"op":"open","channel":channel,"protocol":kind,"maxFrames":64,"maxBytes":65536,"deadlineMs":30000}),false,dispatch,receipts)?;
        let mut queue = std::collections::VecDeque::new();
        let mut results = json!({});
        let mut mutated = false;
        let result = (|| {
            self.generic_frames(
                name, binding, &path, &query, &channel, &open, &mut wire, &mut queue, dispatch,
                receipts,
            )?;
            for _ in 0..64 {
                if wire.connected {
                    break;
                }
                self.generic_receive(
                    name, binding, &path, &query, &channel, end, &mut wire, &mut queue, dispatch,
                    receipts,
                )?;
            }
            if !wire.connected {
                return Err(refuse("socketio-connect-incomplete"));
            }
            for step in b["steps"]
                .as_array()
                .ok_or_else(|| refuse("declaration-invalid"))?
            {
                if std::time::Instant::now() >= end {
                    return Err(refuse("conversation-deadline"));
                }
                if let Some(v) = step.get("send") {
                    if kind != "json-v1" {
                        return Err(refuse("conversation-wire-step-mismatch"));
                    }
                    let text = serde_json::to_string(&resolve(v, args, context, &results)?)
                        .map_err(|_| refuse("conversation-json-invalid"))?;
                    let reply = self.conversation_at(
                        name,
                        binding,
                        &path,
                        &query,
                        json!({"version":1,"op":"send","channel":channel,"text":text}),
                        op["write"] == true,
                        dispatch,
                        receipts,
                    )?;
                    mutated |= op["write"] == true;
                    self.generic_frames(
                        name, binding, &path, &query, &channel, &reply, &mut wire, &mut queue,
                        dispatch, receipts,
                    )?;
                } else if let Some(event) = step.get("emit") {
                    let text = wire.emit(
                        string(event)?,
                        resolve(&step["args"], args, context, &results)?,
                    )?;
                    let reply = self.conversation_at(
                        name,
                        binding,
                        &path,
                        &query,
                        json!({"version":1,"op":"send","channel":channel,"text":text}),
                        op["write"] == true,
                        dispatch,
                        receipts,
                    )?;
                    mutated |= op["write"] == true;
                    self.generic_frames(
                        name, binding, &path, &query, &channel, &reply, &mut wire, &mut queue,
                        dispatch, receipts,
                    )?;
                } else if let Some(http) = step.get("http") {
                    let mut local = results.clone();
                    local["__mini_cookie_jar"] =
                        json!(cookies.for_path(&super::path(&http["path"], args)?)?);
                    let mut call = self.encode_http_binding(
                        name,
                        http,
                        op["write"] == true,
                        args,
                        context,
                        &local,
                    )?;
                    // Merge only eligible app cookies; protected member identity is transport-owned.
                    let scoped = cookies.for_path(&call.path)?;
                    if self.value["auth"]["appCookies"] == "retain" && !scoped.is_empty() {
                        merge_cookie_header(&mut call.ordered_headers, &scoped)?;
                    }
                    let reply = dispatch(binding, &call)?;
                    mutated |= op["write"] == true;
                    receipts.push(reply.receipt);
                    let synthetic =
                        json!({"binding":http,"write":op["write"],"internal":op["internal"]});
                    let value = self.decode_http_binding(
                        &synthetic,
                        reply.status,
                        &reply.headers,
                        &reply.body,
                    )?;
                    if self.value["auth"]["appCookies"] == "retain" {
                        cookies.retain(&reply.headers, &call.path)?;
                    }
                    capture(&mut results, string(&step["id"])?, value)?;
                } else {
                    let conditions: Vec<Value> = if let Some(receive) = step.get("receive") {
                        let mut v = receive.clone();
                        v["id"] = step["id"].clone();
                        vec![v]
                    } else {
                        step["receiveAll"]
                            .as_array()
                            .ok_or_else(|| refuse("conversation-step-invalid"))?
                            .clone()
                    };
                    let mut pending = conditions;
                    for _ in 0..64 {
                        let mut i = 0;
                        while i < pending.len() {
                            let c = &pending[i];
                            let mut matched = None;
                            for (index, packet) in queue.iter().enumerate() {
                                if check_packet(packet, c, args, context, &results)? {
                                    matched = Some(index);
                                    break;
                                }
                            }
                            if let Some(index) = matched {
                                let packet = queue.remove(index).unwrap();
                                capture(&mut results, string(&c["id"])?, packet.value)?;
                                pending.remove(i);
                            } else {
                                i += 1
                            }
                        }
                        if pending.is_empty() {
                            break;
                        }
                        if let Some(refusal) = app_refusal(&pending, &queue, args, context, &results)? {
                            return Err(refusal);
                        }
                        // A poll that fails (deadline, channel budget) still says what did arrive.
                        if let Err(mut e) = self.generic_receive(
                            name, binding, &path, &query, &channel, end, &mut wire, &mut queue,
                            dispatch, receipts,
                        ) {
                            e.name = format!("{} {}", e.name, unmatched(&queue));
                            return Err(e);
                        }
                    }
                    if !pending.is_empty() {
                        // Name what did arrive, so the refusal says why the awaited frame never matched.
                        return Err(refuse(&format!("conversation-terminal-incomplete {}", unmatched(&queue))));
                    }
                }
            }
            resolve(&b["result"], args, context, &results)
        })()
        .map_err(|mut e: Refusal| {
            // An app refusal names this very mutation's rejection (`refuseOn`): decided, not uncertain.
            if !e.name.starts_with(APP_REFUSED) {
                e.uncertain |= mutated;
            }
            e
        });
        let close = self.conversation_at(
            name,
            binding,
            &path,
            &query,
            json!({"version":1,"op":"close","channel":channel}),
            false,
            dispatch,
            receipts,
        );
        match result {
            Err(e) => Err(e),
            Ok(value) => {
                close.map_err(|mut e| {
                    e.uncertain |= mutated;
                    e
                })?;
                Ok(value)
            }
        }
    }
    fn generic_frames<F>(
        &self,
        name: &str,
        binding: &SessionBinding,
        path: &str,
        query: &str,
        channel: &str,
        reply: &Value,
        wire: &mut Wire,
        queue: &mut std::collections::VecDeque<Packet>,
        dispatch: &mut F,
        receipts: &mut Vec<Value>,
    ) -> Result<()>
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        let mut replies = std::collections::VecDeque::from([reply.clone()]);
        let mut count = 0;
        while let Some(reply) = replies.pop_front() {
            for text in reply["frames"]
                .as_array()
                .ok_or_else(|| refuse("conversation-response-invalid"))?
            {
                count += 1;
                if count > 64 {
                    return Err(refuse("conversation-frame-over-bound"));
                }
                let (packet, sends) = wire.frame(string(text)?)?;
                if let Some(packet) = packet {
                    queue.push_back(packet);
                }
                if queue.len() > 64
                    || queue
                        .iter()
                        .map(|p| p.value.to_string().len())
                        .sum::<usize>()
                        > 65536
                {
                    return Err(refuse("conversation-buffer-over-bound"));
                }
                for text in sends {
                    replies.push_back(self.conversation_at(
                        name,
                        binding,
                        path,
                        query,
                        json!({"version":1,"op":"send","channel":channel,"text":text}),
                        false,
                        dispatch,
                        receipts,
                    )?);
                }
            }
        }
        Ok(())
    }
    fn generic_receive<F>(
        &self,
        name: &str,
        binding: &SessionBinding,
        path: &str,
        query: &str,
        channel: &str,
        end: std::time::Instant,
        wire: &mut Wire,
        queue: &mut std::collections::VecDeque<Packet>,
        dispatch: &mut F,
        receipts: &mut Vec<Value>,
    ) -> Result<()>
    where
        F: FnMut(&SessionBinding, &PreparedCall) -> Result<NativeReply>,
    {
        if let Some(text) = wire.heartbeat() {
            let reply = self.conversation_at(
                name,
                binding,
                path,
                query,
                json!({"version":1,"op":"send","channel":channel,"text":text}),
                false,
                dispatch,
                receipts,
            )?;
            self.generic_frames(
                name, binding, path, query, channel, &reply, wire, queue, dispatch, receipts,
            )?;
        }
        let remaining = end
            .checked_duration_since(std::time::Instant::now())
            .ok_or_else(|| refuse("conversation-deadline"))?;
        let ms = remaining.as_millis().min(1000).max(1) as u64;
        let reply=self.conversation_at(name,binding,path,query,json!({"version":1,"op":"receive","channel":channel,"condition":{"msg":"any"},"maxFrames":64,"maxBytes":65536,"deadlineMs":ms}),false,dispatch,receipts)?;
        self.generic_frames(
            name, binding, path, query, channel, &reply, wire, queue, dispatch, receipts,
        )
    }
}
fn capture(results: &mut Value, id: &str, value: Value) -> Result<()> {
    if results.get(id).is_some() {
        return Err(refuse("conversation-capture-duplicate"));
    }
    results[id] = value;
    Ok(())
}
fn merge_cookie_header(
    headers: &mut Vec<(String, String)>,
    cookies: &std::collections::BTreeMap<String, String>,
) -> Result<()> {
    let mut pairs = cookies.clone();
    if let Some(i) = headers
        .iter()
        .position(|(k, _)| k.eq_ignore_ascii_case("cookie"))
    {
        for pair in headers.remove(i).1.split(';') {
            let (k, v) = pair
                .trim()
                .split_once('=')
                .ok_or_else(|| refuse("app-cookie-invalid"))?;
            if pairs.insert(k.into(), v.into()).is_some() {
                return Err(refuse("app-cookie-duplicate"));
            }
        }
    }
    if !pairs.is_empty() {
        headers.push((
            "cookie".into(),
            pairs
                .iter()
                .map(|(k, v)| format!("{k}={v}"))
                .collect::<Vec<_>>()
                .join("; "),
        ));
    }
    Ok(())
}

pub(super) fn validate_binding(b: &Value) -> Result<()> {
    let protocol = string(&b["protocol"])?;
    let allowed: &[&str] = match protocol {
        "http" => &[
            "protocol",
            "method",
            "path",
            "decode",
            "status",
            "headers",
            "query",
            "json",
            "text",
            "base64",
            "form",
            "multipart",
            "cookies",
            "acceptedContentTypes",
            "fragment",
            "responseHeaders",
            "emptyValue",
        ],
        "ddp" => &[
            "protocol",
            "kind",
            "method",
            "publication",
            "params",
            "collections",
            "result",
        ],
        "conversation" => &["protocol", "wire", "path", "query", "steps", "result"],
        _ => return Err(refuse("binding-protocol-unsupported")),
    };
    if b.as_object()
        .is_none_or(|o| o.keys().any(|k| !allowed.contains(&k.as_str())))
    {
        return Err(refuse("binding-key-unknown"));
    }
    if protocol != "conversation" {
        return Ok(());
    }
    let wire = string(&b["wire"])?;
    Wire::new(wire)?;
    let steps = b["steps"]
        .as_array()
        .filter(|a| !a.is_empty() && a.len() <= 64)
        .ok_or_else(|| refuse("conversation-step-invalid"))?;
    let mut ids = std::collections::BTreeSet::new();
    for step in steps {
        let o = step
            .as_object()
            .ok_or_else(|| refuse("conversation-step-invalid"))?;
        let keys: Vec<_> = o.keys().map(String::as_str).collect();
        let terminals = if o.contains_key("send") {
            if keys != ["send"] || wire != "json-v1" {
                return Err(refuse("conversation-step-invalid"));
            }
            vec![]
        } else if o.contains_key("emit") {
            if keys != ["args", "emit"] || wire == "json-v1" {
                return Err(refuse("conversation-step-invalid"));
            }
            vec![]
        } else if o.contains_key("http") {
            if keys != ["http", "id"] {
                return Err(refuse("conversation-step-invalid"));
            }
            validate_binding(&step["http"])?;
            vec![&step["id"]]
        } else if o.contains_key("receive") {
            if keys != ["id", "receive"] {
                return Err(refuse("conversation-step-invalid"));
            }
            let mut receive = step["receive"].clone();
            if let Some(refusals) = receive.as_object_mut().and_then(|o| o.remove("refuseOn")) {
                let refusals = refusals
                    .as_array()
                    .filter(|a| !a.is_empty() && a.len() <= 8)
                    .ok_or_else(|| refuse("conversation-check-invalid"))?
                    .clone();
                for mut refusal in refusals {
                    let reason = refusal.as_object_mut().and_then(|o| o.remove("reason"));
                    if !reason.as_ref().and_then(Value::as_array).is_some_and(|a| {
                        a.len() <= 32 && a.iter().all(|v| v.is_string() || v.as_u64().is_some())
                    }) || refusal.get("where").is_none()
                    {
                        return Err(refuse("conversation-check-invalid"));
                    }
                    validate_condition(&refusal, wire)?;
                }
            }
            validate_condition(&receive, wire)?;
            vec![&step["id"]]
        } else if o.contains_key("receiveAll") {
            if keys != ["receiveAll"] {
                return Err(refuse("conversation-step-invalid"));
            }
            let all = step["receiveAll"]
                .as_array()
                .filter(|a| !a.is_empty() && a.len() <= 32)
                .ok_or_else(|| refuse("conversation-step-invalid"))?;
            for c in all {
                validate_condition(c, wire)?;
            }
            all.iter().map(|c| &c["id"]).collect()
        } else {
            return Err(refuse("conversation-step-invalid"));
        };
        validate_refs(step, &ids)?;
        for id in terminals {
            let id = string(id)?;
            if id.is_empty()
                || id.len() > 64
                || !id.as_bytes()[0].is_ascii_alphabetic()
                || !id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
                || !ids.insert(id.to_owned())
            {
                return Err(refuse("conversation-capture-invalid-or-duplicate"));
            }
        }
    }
    validate_refs(&b["result"], &ids)
}
fn validate_condition(c: &Value, wire: &str) -> Result<()> {
    let o = c
        .as_object()
        .ok_or_else(|| refuse("conversation-check-invalid"))?;
    if o.keys()
        .any(|k| !matches!(k.as_str(), "id" | "event" | "where"))
        || (wire == "json-v1" && c.get("event").is_some())
        || (wire != "json-v1" && !c["event"].is_string())
    {
        return Err(refuse("conversation-check-invalid"));
    }
    if let Some(checks) = c.get("where") {
        let checks = checks
            .as_array()
            .filter(|a| a.len() <= 32)
            .ok_or_else(|| refuse("conversation-check-invalid"))?;
        for check in checks {
            let o = check
                .as_object()
                .ok_or_else(|| refuse("conversation-check-invalid"))?;
            if o.len() != 2
                || !check["path"].as_array().is_some_and(|a| {
                    a.len() <= 32 && a.iter().all(|v| v.is_string() || v.as_u64().is_some())
                })
                || ["equals", "exists", "contains"]
                    .iter()
                    .filter(|k| o.contains_key(**k))
                    .count()
                    != 1
                || o.keys()
                    .any(|k| !matches!(k.as_str(), "path" | "equals" | "exists" | "contains"))
            {
                return Err(refuse("conversation-check-invalid"));
            }
            if o.contains_key("exists") && check["exists"] != true {
                return Err(refuse("conversation-check-invalid"));
            }
        }
    }
    Ok(())
}
fn validate_refs(v: &Value, ids: &std::collections::BTreeSet<String>) -> Result<()> {
    if let Some(o) = v.as_object() {
        let reserved = [
            "arg",
            "context",
            "result",
            "concat",
            "path",
            "sha256",
            "cookie",
            "csv",
            "jsonStringify",
        ];
        if o.keys().any(|k| reserved.contains(&k.as_str())) && o.len() != 1 {
            // Path bindings and receive checks are closed structural objects,
            // rather than expression objects.
            let structural = (o.contains_key("path")
                && (o.contains_key("equals")
                    || o.contains_key("contains")
                    || o.contains_key("exists")))
                || (o.contains_key("arg") && o.contains_key("encoding"))
                || o.contains_key("protocol");
            if !structural {
                return Err(refuse("binding-expression-key-invalid"));
            }
        }
        if let Some(path) = o.get("result") {
            if o.len() == 1 {
                let p = path
                    .as_array()
                    .filter(|a| !a.is_empty())
                    .ok_or_else(|| refuse("result-binding-invalid"))?;
                if !p[0].as_str().is_some_and(|s| ids.contains(s)) {
                    return Err(refuse("result-binding-forward-or-unknown"));
                }
                return Ok(());
            }
        }
        for value in o.values() {
            validate_refs(value, ids)?;
        }
    } else if let Some(a) = v.as_array() {
        for value in a {
            validate_refs(value, ids)?;
        }
    }
    Ok(())
}

/// A hosted channel id: the Host's `identifier` shape is at most 64 of [A-Za-z0-9_-]. `mini-` plus a full
/// SHA-256 in hex is 69, so the first 32 hex digits (128 bits) are kept: 37 characters.
fn channel_name(seed: &str) -> String {
    format!("mini-{}", &format!("{:x}", Sha256::digest(seed))[..32])
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn a_channel_id_fits_the_hosts_identifier_shape() {
        let id = channel_name("mini/conversation/v1/43/cards.read/0");
        assert!(id.len() <= 64 && id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_'), "{id}");
        assert_ne!(id, channel_name("mini/conversation/v1/43/cards.read/1"));
    }
    #[test]
    fn source_derived_data_frames_use_native_codec_and_correlation() {
        let fixture: Value =
            serde_json::from_str(include_str!("../tests/fixtures/data-conversations.json"))
                .unwrap();
        for case in fixture["cases"].as_array().unwrap() {
            let mut wire = Wire::new(case["wire"].as_str().unwrap()).unwrap();
            let mut packets = vec![];
            for frame in case["frames"].as_array().unwrap() {
                let (packet, _) = wire.frame(frame.as_str().unwrap()).unwrap();
                if let Some(packet) = packet {
                    packets.push(packet)
                }
            }
            if case["name"].as_str().unwrap().starts_with("notebook") {
                let mut found = std::collections::BTreeSet::new();
                for (id, kind) in [("reply", "execute_reply"), ("idle", "status")] {
                    let mut checks = vec![
                        json!({"path":["parent_header","msg_id"],"equals":"operation-1"}),
                        json!({"path":["header","msg_type"],"equals":kind}),
                    ];
                    if id == "idle" {
                        checks.push(json!({"path":["content","execution_state"],"equals":"idle"}))
                    }
                    let cond = json!({"where":checks});
                    if packets.iter().any(|p| {
                        check_packet(p, &cond, &json!({}), &json!({}), &json!({})).unwrap()
                    }) {
                        found.insert(id);
                    }
                }
                if case.get("expectedMissing").is_some() {
                    assert!(found.len() < 2);
                    for missing in case["expectedMissing"].as_array().unwrap() {
                        assert!(!found.contains(missing.as_str().unwrap()))
                    }
                } else {
                    assert_eq!(found.len(), 2)
                }
            } else if let Some(condition) = case.get("match") {
                assert!(packets.iter().any(|p| check_packet(
                    p,
                    condition,
                    &json!({}),
                    &json!({}),
                    &json!({})
                )
                .unwrap()))
            } else {
                assert_eq!(packets[0].value["args"], case["httpCookie"]["token"]);
                let op = json!({"projection":{"collection":"library","where":{},"values":true}});
                let result = json!({"library":packets[1].value["args"]});
                assert_eq!(
                    project(&op, result, &json!({}), &json!({}), &json!({})).unwrap(),
                    case["expectedProjection"]
                );
            }
        }
    }
}
