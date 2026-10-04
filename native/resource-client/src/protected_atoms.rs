//! Protected text bindings over shared authored-fragment custody.
//!
//! The binding names the VERSION of the atom a ciphertext is:
//!   tag (2) ‖ atom (32) ‖ seq (8) ‖ prev (32)
//! seq is 0 at create and the predecessor's seq + 1 at each edit; prev is the
//! kernel revision of the exact `before` record the edit replaces (zero at
//! create). The binding is in the fragment header and in the fragment operation
//! every open recomputes, so it cannot be altered without the open refusing. A
//! reader then checks it against the served record (`check_current`) and, with
//! history, against the version it last saw (`advance`): an earlier ciphertext
//! re-served at the same address does not open. Version-1 bindings (atom only)
//! refuse to load.
use super::*;
const SCHEMA:&[u8]=b"MINI/PROTECTED-AUTHORED-TEXT/v1";
const BINDING_TAG:u8=2;
const BINDING_LEN:usize=1+32+8+32;
pub(super) fn schema()->String{decimal(&Sha256::digest(SCHEMA))}
pub(super) fn is_kind(kind:&Value)->bool{kind["type"]=="sealedObject"&&kind["schema"]==schema()}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct Version{pub(super) seq:u64,pub(super) prev:[u8;32]}

fn binding(atom:&str,version:&Version)->Result<Vec<u8>>{
    Ok([&[BINDING_TAG][..],&nat32(atom)?,&version.seq.to_be_bytes(),&version.prev].concat())
}
fn parse(atom:&str,bytes:&[u8])->Result<Version>{
    if bytes.len()!=BINDING_LEN||bytes[0]!=BINDING_TAG||bytes[1..33]!=nat32(atom)?{
        return Err("authored fragment address differs".into());
    }
    let version=Version{seq:u64::from_be_bytes(bytes[33..41].try_into().expect("8 bytes")),
        prev:bytes[41..73].try_into().expect("32 bytes")};
    if (version.seq==0)!=(version.prev==[0;32]){return Err("authored fragment version is malformed".into());}
    Ok(version)
}
/// The version a protected atom's ciphertext claims to be.
pub(super) fn version_of(atom:&str,kind:&Value)->Result<Version>{
    parse(atom,&fragments::binding_of(&kind["fragment"],BINDING_LEN)?)
}
/// The version a fresh sealing of `action` takes.
fn next_version(action:&Value)->Result<Version>{
    if action["type"]!="editAtom"{return Ok(Version{seq:0,prev:[0;32]});}
    let before=&action["before"];
    let prev=nat32(text(before,"revision")?)?;
    if prev==[0;32]{return Err("an edit's predecessor revision cannot be zero".into());}
    let seq=if is_kind(&before["kind"]){
        version_of(text(action,"atom")?,&before["kind"])?.seq.checked_add(1).ok_or("atom version exhausted")?
    }else{1};
    Ok(Version{seq,prev})
}
pub(super) fn seal(audience:&Audience,action:&mut Value,nonce:&[u8;32],store:&mut Store,writer:&SigningKey)->Result<()>{
    if action["type"]=="rewrapAtom"{
        let before=&action["before"];
        if !is_kind(&before["kind"])||before["payload"]!=""||!before["tombstonedAt"].is_null(){return Err("only live authored text can be rewrapped".into());}
        action["wrapping"]=json!(fragments::rewrap(audience,&before["kind"]["fragment"],nonce,store,writer)?);
    }else{
        let plain=Zeroizing::new(crate::decode_hex(text(action,"payload")?)?);
        let version=next_version(action)?;
        let fragment=fragments::seal(audience,&binding(text(action,"atom")?,&version)?,nonce,&plain,store,writer)?;
        action["kind"]=json!({"type":"sealedObject","schema":schema(),"fragment":fragment});
        action["payload"]=json!("");
    }
    Ok(())
}
/// A live record's ciphertext must be the version its record says it is: the
/// creation (seq 0) exactly when the record was never edited. A struck line
/// keeps its last ciphertext under the strike's revision, so it is exempt.
pub(super) fn check_current(version:&Version,entry:&Value)->Result<()>{
    if !entry["tombstonedAt"].is_null(){return Ok(());}
    let edited=text(entry,"revision")?!=text(entry,"createdAt")?;
    if edited!=(version.seq!=0){
        return Err("authored text is not the version its atom record names: an earlier ciphertext was re-served".into());
    }
    Ok(())
}
/// A reader's retained version of one atom (`{seq, revision, digestHex}`) may
/// only move forward: a lower seq, the same seq with other bytes, or a next seq
/// whose predecessor is not the revision last seen all refuse. Returns the row
/// to retain when it advanced.
pub(super) fn advance(retained:Option<&Value>,version:&Version,entry:&Value,digest:&[u8;32])->Result<Option<Value>>{
    let row=json!({"seq":version.seq.to_string(),"revision":text(entry,"revision")?,"digestHex":crate::hex(digest)});
    let Some(retained)=retained else{return Ok(Some(row));};
    let seq:u64=text(retained,"seq")?.parse().map_err(|_|"retained atom version is not a decimal")?;
    if version.seq<seq{return Err("authored text rolled back below the version this reader already saw".into());}
    if version.seq==seq{
        if retained["digestHex"]!=row["digestHex"]{return Err("authored text equivocates: another ciphertext at a version this reader already saw".into());}
        return Ok(None);
    }
    if version.seq==seq+1&&version.prev!=nat32(text(retained,"revision")?)?{
        return Err("authored text's predecessor is not the version this reader last saw".into());
    }
    Ok(Some(row))
}
pub(super) fn open(object:&str,entry:&Value,store:&Store)->Result<Vec<u8>>{
    if !is_kind(&entry["kind"])||entry["payload"]!=""{return Err("invalid authored-text source record".into());}
    let atom=text(entry,"id")?;
    let version=version_of(atom,&entry["kind"])?;
    check_current(&version,entry)?;
    fragments::open(object,&binding(atom,&version)?,&entry["kind"]["fragment"],store)
}
pub(super) fn epoch(kind:&Value)->Result<u64>{fragments::epoch(&kind["fragment"])}
