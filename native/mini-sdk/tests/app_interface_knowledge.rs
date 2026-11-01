//! Source-derived package frames, not recorded live app captures.
use mini_sdk::app_interface::{Declaration, NativeReply, SessionBinding};
use serde_json::{json, Value};

fn binding(package: &str) -> SessionBinding {
    SessionBinding { package_id: package.into(), subject: "7".into(), app: "8".into(),
        generation: "0".into(), session: "9".into(), session_generation: "0".into() }
}
fn reply(q: &Value, frames: Vec<String>) -> NativeReply {
    NativeReply { status: 200, headers: vec![], body: serde_json::to_vec(&json!({
        "version":1,"channel":q["channel"],"op":q["op"],"frames":frames})).unwrap(),
        receipt: json!({"native":"fixture","op":q["op"]}) }
}
#[test]
fn wbo_native_write_acknowledged_and_independent_replay() {
    // WBO 2.18 joins by connecting with board and baselineSeq, replays the board's mutations on
    // join and broadcasts an accepted mutation back with its numeric create form (frames derived
    // from server/socket/replay.mjs and apps/packages/wbo/qualify-writes/wbo-sio.py).
    let d=Declaration::load(include_bytes!("../../../apps/interfaces/wbo.json")).unwrap();
    let b=binding("d3b06718d12bc377db7b494679440b91");
    let mut item=Value::Null; let mut sends=0;
    let result=d.execute("rectangle.write",&json!({"board":"human","id":"owned","color":"#123456","size":10,"opacity":1,"x":10,"y":10,"x2":120,"y2":90}),&json!({"operationId":"wbo-write"}),&b,|session,p| {
        assert_eq!(session.subject,"7");
        if p.method=="GET" {
            assert_eq!(p.path,"boards/human.svg");
            return Ok(NativeReply{status:200,headers:vec![],body:vec![],receipt:json!({"op":"pin"})});
        }
        assert_eq!(p.method,"CONVERSATION");
        assert!(p.query.contains("EIO=4") && p.query.contains("board=human") && p.query.contains("baselineSeq=0"), "{}", p.query);
        let q:Value=serde_json::from_slice(&p.body).unwrap();
        let mut frames=vec![];
        if q["op"]=="open" { frames.push(r#"0{"sid":"s","pingInterval":25000}"#.into()); }
        if q["op"]=="send" {
            let text=q["text"].as_str().unwrap();
            if text=="40" {frames.push("40".into()); frames.push(r#"42["broadcast",{"type":0,"fromSeq":0,"seq":0,"_children":[]}]"#.into());}
            else {
                let v:Value=serde_json::from_str(text.strip_prefix("42").unwrap()).unwrap();
                assert_eq!(v[0],"broadcast");
                item=v[1].clone(); sends+=1;
                assert_eq!(item["tool"],3); assert_eq!(item["type"],1); assert_eq!(item["clientMutationId"],"owned");
                frames.push(format!("42{}",json!(["broadcast",{"seq":1,"mutation":item}])));
            }
        }
        Ok(reply(&q,frames))
    });
    assert_eq!(result.outcome.unwrap(),json!({"delivery":"acknowledged","id":"owned"}));
    assert_eq!(sends,1);
    let result=d.execute("board.read",&json!({"board":"human"}),&json!({"operationId":"wbo-read"}),&b,|_,p| {
        let q:Value=serde_json::from_slice(&p.body).unwrap();
        let frames=if q["op"]=="open" {vec![r#"0{"sid":"r","pingInterval":25000}"#.into()]}
        else if q["text"]=="40" {vec!["40".into(),format!("42{}",json!(["broadcast",{"type":0,"fromSeq":0,"seq":1,"_children":[item]}]))]}
        else {vec![]}; Ok(reply(&q,frames))
    });
    let values=result.outcome.unwrap();assert_eq!(values[0]["id"],"owned");assert_eq!(values[0]["x2"],120);
}
#[test]
fn wbo_rejected_write_is_named_at_once_and_decided() {
    // WBO rejects a write with `mutation_rejected {reason, clientMutationId}` (server/socket/broadcasts.mjs
    // emitMutationRejected) and never echoes it; the ack step's refuseOn ends the step on that frame.
    let d=Declaration::load(include_bytes!("../../../apps/interfaces/wbo.json")).unwrap();
    let b=binding("d3b06718d12bc377db7b494679440b91");
    let mut receives=0;
    let result=d.execute("rectangle.write",&json!({"board":"human","id":"owned","color":"#123456","size":10,"opacity":1,"x":10,"y":10,"x2":120,"y2":90}),&json!({"operationId":"wbo-write"}),&b,|_,p| {
        if p.method=="GET" {
            return Ok(NativeReply{status:200,headers:vec![],body:vec![],receipt:json!({"op":"pin"})});
        }
        let q:Value=serde_json::from_slice(&p.body).unwrap();
        let mut frames=vec![];
        if q["op"]=="open" { frames.push(r#"0{"sid":"s","pingInterval":25000}"#.into()); }
        if q["op"]=="receive" { receives+=1; }
        if q["op"]=="send" {
            let text=q["text"].as_str().unwrap();
            if text=="40" {frames.push("40".into()); frames.push(r#"42["broadcast",{"type":0,"fromSeq":0,"seq":0,"_children":[]}]"#.into());}
            else {
                frames.push(r#"42["mutation_rejected",{"reason":"other","clientMutationId":"someone-else"}]"#.into());
                frames.push(r#"42["mutation_rejected",{"reason":"rate limit exceeded","clientMutationId":"owned"}]"#.into());
            }
        }
        Ok(reply(&q,frames))
    });
    let refusal=result.outcome.unwrap_err();
    assert_eq!(refusal.name,"app-refused: rate limit exceeded");
    assert!(!refusal.uncertain);
    assert_eq!(receives,0, "no poll after the rejection arrived");
}
#[test]
fn an_unmatched_conversation_names_what_did_arrive() {
    let d=Declaration::load(include_bytes!("../../../apps/interfaces/wbo.json")).unwrap();
    let b=binding("d3b06718d12bc377db7b494679440b91");
    let result=d.execute("board.read",&json!({"board":"human"}),&json!({"operationId":"wbo-read"}),&b,|_,p| {
        let q:Value=serde_json::from_slice(&p.body).unwrap();
        let frames=if q["op"]=="open" {vec![r#"0{"sid":"r","pingInterval":25000}"#.into()]}
        else if q["text"]=="40" {vec!["40".into(),r#"42["user_joined",{}]"#.into()]}
        else {vec![]}; Ok(reply(&q,frames))
    });
    let name=result.outcome.unwrap_err().name;
    assert!(name.starts_with("conversation-terminal-incomplete (unmatched: user_joined x1"), "{name}");
}
#[test]
fn hummingbird_record_correlates_on_its_event_in_the_locations_stream() {
    // lib/metrics/locations.js pushes {city, region, country, latitude, longitude, event} per tracked
    // request every 500 ms; hits carry only the referer url, which the bridge never forwards.
    let d=Declaration::load(include_bytes!("../../../apps/interfaces/hummingbird.json")).unwrap();
    let b=binding("c7287dfbae2796cd283a32452d2395c7");
    let mut beacon=None;
    let result=d.execute("analytics.record",&json!({"event":"mini-qualify-7"}),&json!({"operationId":"hb"}),&b,|_,p| {
        if p.method=="GET" {
            assert!(p.ordered_headers.iter().all(|(k,_)| k!="referer"));
            beacon=Some(p.query.clone());
            return Ok(NativeReply{status:200,headers:vec![],body:vec![],receipt:json!({"op":"beacon"})});
        }
        let q:Value=serde_json::from_slice(&p.body).unwrap();
        let mut frames=vec![];
        if q["op"]=="open" { frames.push(r#"0{"sid":"s","pingInterval":25000}"#.into()); }
        if q["op"]=="send" && q["text"]=="40" { frames.push("40".into()); }
        if q["op"]=="receive" && beacon.is_some() {
            frames.push(r#"42["hits",[{"timestamp":"2026-11-01T00:00:00.000Z"}]]"#.into());
            frames.push(r#"42["locations",[{"city":"","region":"C","country":"US","latitude":37.7,"longitude":-122.4,"event":"other"},{"city":"","region":"C","country":"US","latitude":37.7,"longitude":-122.4,"event":"mini-qualify-7"}]]"#.into());
        }
        Ok(reply(&q,frames))
    });
    assert_eq!(beacon.as_deref(), Some("event=mini-qualify-7"));
    let entries=result.outcome.unwrap();
    assert!(entries.as_array().unwrap().iter().any(|e| e["timestamp"].is_string()), "{entries}");
}
#[test]
fn scrumblr_native_room_and_matching_card_snapshot() {
    let d=Declaration::load(include_bytes!("../../../apps/interfaces/scrumblr.json")).unwrap();
    let result=d.execute("cards.read",&json!({"room":"/human"}),&json!({"operationId":"scrum-read"}),&binding("57fa8aab611f5e0ab656e73324d48879"),|_,p| {
        assert!(p.query.contains("EIO=4"));let q:Value=serde_json::from_slice(&p.body).unwrap();
        let frames=if q["op"]=="open" {vec![r#"0{"sid":"s","pingInterval":25000}"#.into()]}
        else if q["op"]=="send" && q["text"]=="40" {vec!["40".into()]}
        else if q["op"]=="send" {
            let v:Value=serde_json::from_str(q["text"].as_str().unwrap().strip_prefix("42").unwrap()).unwrap();
            assert_eq!(v[0],"message");
            if v[1]["action"]=="joinRoom" {assert_eq!(v[1]["data"],"/human");vec![r#"42["message",{"action":"roomAccept","data":""}]"#.into()]}
            else {assert_eq!(v[1]["action"],"initializeMe");vec![r#"42["message",{"action":"initColumns","data":[]}]"#.into(),r#"42["message",{"action":"initCards","data":[{"id":"owned","text":"typed"}]}]"#.into()]}
        } else {vec![]};Ok(reply(&q,frames))
    });
    assert_eq!(result.outcome.unwrap(),json!([{"id":"owned","text":"typed"}]));
}
#[test]
fn scrumblr_unknown_mutation_is_not_replayed() {
    let d=Declaration::load(include_bytes!("../../../apps/interfaces/scrumblr.json")).unwrap();let mut mutations=0;
    let result=d.execute("card.write",&json!({"room":"/human","id":"owned","text":"typed","colour":"yellow","x":58,"y":120,"rot":3}),&json!({"operationId":"scrum-unknown"}),&binding("57fa8aab611f5e0ab656e73324d48879"),|_,p| {
        let q:Value=serde_json::from_slice(&p.body).unwrap();
        let frames=if q["op"]=="open" {vec![r#"0{"sid":"s","pingInterval":25000}"#.into()]}
        else if q["op"]=="send" && q["text"]=="40" {vec!["40".into()]}
        else if q["op"]=="send" {
            let v:Value=serde_json::from_str(q["text"].as_str().unwrap().strip_prefix("42").unwrap()).unwrap();
            if v[1]["action"]=="joinRoom" {vec![r#"42["message",{"action":"roomAccept","data":""}]"#.into()]}
            else {mutations+=1;return Err(mini_sdk::app_interface::Refusal{name:"physical-reply-lost".into(),uncertain:true});}
        } else {vec![]};Ok(reply(&q,frames))
    });
    assert_eq!(mutations,1);assert!(result.outcome.unwrap_err().uncertain);
}
