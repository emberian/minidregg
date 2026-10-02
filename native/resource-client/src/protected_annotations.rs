//! Authored fragments have immutable signed ciphertext and a separately
//! source-guarded epoch-key wrapping. Membership maintenance never rewrites an
//! author's comment or borrows its original whole-document epoch key.
use super::*;
const FRAGMENT: &[u8]=b"MINI/PROTECTED-ANNOTATION-FRAGMENT/v1";
const WRAP: &[u8]=b"MINI/PROTECTED-ANNOTATION-WRAP/v1";
fn hash(parts:&[&[u8]])->[u8;32] {
    let mut h=Sha256::new();for part in parts{h.update(part);}h.finalize().into()
}
fn fragment_op(object:&[u8;32],annotation:&[u8;32],atom:&[u8;32],revision:&[u8;32],nonce:&[u8;32])->[u8;32] {
    hash(&[FRAGMENT,object,annotation,atom,revision,nonce])
}
fn wrap_op(object:&[u8;32],annotation:&[u8;32],cipher:&[u8],nonce:&[u8;32])->[u8;32] {
    hash(&[WRAP,object,annotation,&Sha256::digest(cipher),nonce])
}
fn message(record:&[u8])->Result<(Context,[u8;32])> {
    let h=MESSAGE_FRAME.len();
    if !record.starts_with(MESSAGE_FRAME) || record.len()<h+32+8+32*4+24+16+64 {
        return Err("invalid annotation message".into());
    }
    let array=|bytes:&[u8]|->Result<[u8;32]>{bytes.try_into().map_err(|_|"invalid annotation binding".into())};
    let object=array(&record[h..h+32])?;let epoch=u64::from_be_bytes(record[h+32..h+40].try_into().unwrap());
    Ok((Context{object,epoch,transition:array(&record[h+40..h+72])?,operation:array(&record[h+72..h+104])?,law:array(&record[h+104..h+136])?},array(&record[h+136..h+168])?))
}
fn fragment<'a>(object:&str,annotation:&str,anchor:&Value,bytes:&'a[u8])->Result<(Context,[u8;32],&'a[u8])> {
    let h=FRAGMENT.len();
    if !bytes.starts_with(FRAGMENT)||bytes.len()<h+128{return Err("invalid authored fragment".into());}
    let aid=nat32(annotation)?;
    let atom=nat32(text(anchor,"atom")?)?;let revision=nat32(text(anchor,"revision")?)?;
    if bytes[h..h+32]!=aid||bytes[h+32..h+64]!=atom||bytes[h+64..h+96]!=revision {
        return Err("authored fragment address or anchor differs".into());
    }
    let nonce:[u8;32]=bytes[h+96..h+128].try_into().unwrap();
    let record=&bytes[h+128..];let (context,writer)=message(record)?;
    if context.object!=nat32(object)?||context.operation!=fragment_op(&context.object,&aid,&atom,&revision,&nonce){return Err("authored fragment context differs".into());}
    Ok((context,writer,record))
}
fn wrap(audience:&Audience,annotation:&[u8;32],cipher:&[u8],nonce:&[u8;32],key:&[u8;32],store:&mut Store,writer:&SigningKey)->Result<Vec<u8>> {
    let context=Context{object:audience.anchor.object,epoch:audience.anchor.epoch,transition:audience.anchor.transition,
        law:audience.law,operation:wrap_op(&audience.anchor.object,annotation,cipher,nonce)};
    let record=store.prepare(&audience.anchor,&context,writer,key)?;
    Ok([WRAP,annotation,nonce,&record].concat())
}
fn key(object:&str,annotation:&str,cipher:&[u8],wrapping:&[u8],store:&Store)->Result<Zeroizing<[u8;32]>> {
    let h=WRAP.len();let aid=nat32(annotation)?;
    if !wrapping.starts_with(WRAP)||wrapping.len()<h+64||wrapping[h..h+32]!=aid{return Err("annotation wrap address differs".into());}
    let nonce:[u8;32]=wrapping[h+32..h+64].try_into().unwrap();let record=&wrapping[h+64..];
    let (context,writer)=message(record)?;
    if context.object!=nat32(object)?||context.operation!=wrap_op(&context.object,&aid,cipher,&nonce){return Err("annotation wrap context differs".into());}
    let epoch_key=store.historical_key(&AdmittedAnchor{object:context.object,epoch:context.epoch,transition:context.transition,active:false})?;
    let bytes=Zeroizing::new(object_messages::open(&context,&epoch_key,&writer,record)?);
    Ok(Zeroizing::new(bytes.as_slice().try_into().map_err(|_|"invalid fragment key")?))
}
pub(super) fn seal(audience:&Audience,action:&mut Value,nonce:&[u8;32],store:&mut Store,writer:&SigningKey)->Result<()> {
    let annotation=nat32(text(action,"annotation")?)?;
    if action["type"]=="annotate" {
        let atom=nat32(text(action,"atom")?)?;let revision=nat32(text(action,"revision")?)?;
        let context=Context{object:audience.anchor.object,epoch:audience.anchor.epoch,transition:audience.anchor.transition,law:audience.law,
            operation:fragment_op(&audience.anchor.object,&annotation,&atom,&revision,nonce)};
        let plain=Zeroizing::new(private::decode_hex(text(action,"body")?)?);
        let (key,record)=store.prepare_fragment(&audience.anchor,&context,writer,&plain)?;
        let cipher=[FRAGMENT,&annotation,&atom,&revision,nonce,&record].concat();
        let wrapping=wrap(audience,&annotation,&cipher,nonce,&key,store,writer)?;
        action["body"]=json!({"type":"sealed","ciphertext":crate::hex(&cipher),"wrapping":crate::hex(&wrapping)});
    } else {
        let body=&action["wrapping"];
        if body["type"]!="sealed"{return Err("only authored sealed annotations can be rewrapped".into());}
        let cipher=private::decode_hex(text(body,"ciphertext")?)?;
        let old=private::decode_hex(text(body,"wrapping")?)?;
        let key=key(&audience.object,text(action,"annotation")?,&cipher,&old,store)?;
        action["wrapping"]=json!(crate::hex(&wrap(audience,&annotation,&cipher,nonce,&key,store,writer)?));
    }
    Ok(())
}
pub(super) fn open(object:&str,entry:&Value,store:&Store)->Result<Vec<u8>> {
    let body=&entry["body"];let cipher=private::decode_hex(text(body,"ciphertext")?)?;
    let wrapping=private::decode_hex(text(body,"wrapping")?)?;let annotation=text(entry,"id")?;
    let (context,writer,record)=fragment(object,annotation,&entry["anchor"],&cipher)?;
    let key=key(object,annotation,&cipher,&wrapping,store)?;
    object_messages::open(&context,&key,&writer,record)
}
pub(super) fn epoch(body:&Value)->Result<u64> {
    let bytes=private::decode_hex(text(body,"wrapping")?)?;
    let h=WRAP.len();if !bytes.starts_with(WRAP)||bytes.len()<h+64{return Err("invalid annotation wrap".into());}
    Ok(message(&bytes[h+64..])?.0.epoch)
}
