//! Protected text bindings over shared authored-fragment custody.
use super::*;
const SCHEMA:&[u8]=b"MINI/PROTECTED-AUTHORED-TEXT/v1";
pub(super) fn schema()->String{decimal(&Sha256::digest(SCHEMA))}
pub(super) fn is_kind(kind:&Value)->bool{kind["type"]=="sealedObject"&&kind["schema"]==schema()}
fn binding(atom:&str)->Result<Vec<u8>>{Ok([&[1u8][..],&nat32(atom)?].concat())}
pub(super) fn seal(audience:&Audience,action:&mut Value,nonce:&[u8;32],store:&mut Store,writer:&SigningKey)->Result<()>{
    if action["type"]=="rewrapAtom"{
        let before=&action["before"];
        if !is_kind(&before["kind"])||before["payload"]!=""||!before["tombstonedAt"].is_null(){return Err("only live authored text can be rewrapped".into());}
        action["wrapping"]=json!(fragments::rewrap(audience,&before["kind"]["fragment"],nonce,store,writer)?);
    }else{
        let plain=Zeroizing::new(private::decode_hex(text(action,"payload")?)?);
        let fragment=fragments::seal(audience,&binding(text(action,"atom")?)?,nonce,&plain,store,writer)?;
        action["kind"]=json!({"type":"sealedObject","schema":schema(),"fragment":fragment});
        action["payload"]=json!("");
    }
    Ok(())
}
pub(super) fn open(object:&str,entry:&Value,store:&Store)->Result<Vec<u8>>{
    if !is_kind(&entry["kind"])||entry["payload"]!=""{return Err("invalid authored-text source record".into());}
    fragments::open(object,&binding(text(entry,"id")?)?,&entry["kind"]["fragment"],store)
}
pub(super) fn epoch(kind:&Value)->Result<u64>{fragments::epoch(&kind["fragment"])}
