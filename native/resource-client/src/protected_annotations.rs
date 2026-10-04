//! Annotation bindings over the shared immutable authored-fragment custody.
use super::*;
fn binding(annotation:&str,anchor:&Value)->Result<Vec<u8>>{
    Ok([&[2u8][..],&nat32(annotation)?,&nat32(text(anchor,"atom")?)?,&nat32(text(anchor,"revision")?)?].concat())
}
pub(super) fn seal(audience:&Audience,action:&mut Value,nonce:&[u8;32],store:&mut Store,writer:&SigningKey)->Result<()>{
    if action["type"]=="annotate"{
        let address=binding(text(action,"annotation")?,&json!({"atom":action["atom"],"revision":action["revision"]}))?;
        let plain=Zeroizing::new(crate::decode_hex(text(action,"body")?)?);
        action["body"]=json!({"type":"sealed","fragment":fragments::seal(audience,&address,nonce,&plain,store,writer)?});
    }else{
        if action["wrapping"]["type"]!="sealed"{return Err("only authored sealed annotations can be rewrapped".into());}
        action["wrapping"]=json!(fragments::rewrap(audience,&action["wrapping"]["fragment"],nonce,store,writer)?);
    }
    Ok(())
}
pub(super) fn open(object:&str,entry:&Value,store:&Store)->Result<Vec<u8>>{
    fragments::open(object,&binding(text(entry,"id")?,&entry["anchor"])? ,&entry["body"]["fragment"],store)
}
pub(super) fn epoch(body:&Value)->Result<u64>{fragments::epoch(&body["fragment"])}
