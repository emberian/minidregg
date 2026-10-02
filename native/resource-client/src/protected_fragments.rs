//! Immutable authenticated authored payloads and separately journaled epoch wraps.
use super::*;
const FRAGMENT:&[u8]=b"MINI/PROTECTED-AUTHORED-FRAGMENT/v1";
const WRAP:&[u8]=b"MINI/PROTECTED-AUTHORED-WRAP/v1";
fn hash(parts:&[&[u8]])->[u8;32]{let mut h=Sha256::new();for p in parts{h.update(p);}h.finalize().into()}
fn fragment_op(object:&[u8;32],binding:&[u8],nonce:&[u8;32])->[u8;32]{hash(&[FRAGMENT,object,binding,nonce])}
fn wrap_op(object:&[u8;32],cipher:&[u8],nonce:&[u8;32])->[u8;32]{hash(&[WRAP,object,&Sha256::digest(cipher),nonce])}
fn message(record:&[u8])->Result<(Context,[u8;32])>{
    let h=MESSAGE_FRAME.len();
    if !record.starts_with(MESSAGE_FRAME)||record.len()<h+32+8+32*4+24+16+64{return Err("invalid authored-fragment message".into());}
    let array=|bytes:&[u8]|->Result<[u8;32]>{bytes.try_into().map_err(|_|"invalid fragment binding".into())};
    Ok((Context{object:array(&record[h..h+32])?,epoch:u64::from_be_bytes(record[h+32..h+40].try_into().unwrap()),
      transition:array(&record[h+40..h+72])?,operation:array(&record[h+72..h+104])?,law:array(&record[h+104..h+136])?},array(&record[h+136..h+168])?))
}
fn key(object:&str,fragment:&Value,store:&Store)->Result<Zeroizing<[u8;32]>>{
    let cipher=private::decode_hex(text(fragment,"ciphertext")?)?;
    let wrapping=private::decode_hex(text(fragment,"wrapping")?)?;let h=WRAP.len();
    if !wrapping.starts_with(WRAP)||wrapping.len()<h+32{return Err("invalid fragment wrapping".into());}
    let nonce:[u8;32]=wrapping[h..h+32].try_into().unwrap();let record=&wrapping[h+32..];
    let (context,writer)=message(record)?;
    if context.object!=nat32(object)?||context.operation!=wrap_op(&context.object,&cipher,&nonce){return Err("fragment wrapping context differs".into());}
    let epoch_key=store.historical_key(&AdmittedAnchor{object:context.object,epoch:context.epoch,transition:context.transition,active:false})?;
    let bytes=Zeroizing::new(object_messages::open(&context,&epoch_key,&writer,record)?);
    Ok(Zeroizing::new(bytes.as_slice().try_into().map_err(|_|"invalid fragment key")?))
}
fn wrap(audience:&Audience,cipher:&[u8],nonce:&[u8;32],key:&[u8;32],store:&mut Store,writer:&SigningKey)->Result<Vec<u8>>{
    let context=Context{object:audience.anchor.object,epoch:audience.anchor.epoch,transition:audience.anchor.transition,
      law:audience.law,operation:wrap_op(&audience.anchor.object,cipher,nonce)};
    let record=store.prepare(&audience.anchor,&context,writer,key)?;
    Ok([WRAP,nonce,&record].concat())
}
pub(super) fn seal(audience:&Audience,binding:&[u8],nonce:&[u8;32],plain:&[u8],store:&mut Store,writer:&SigningKey)->Result<Value>{
    let context=Context{object:audience.anchor.object,epoch:audience.anchor.epoch,transition:audience.anchor.transition,law:audience.law,
      operation:fragment_op(&audience.anchor.object,binding,nonce)};
    let (key,record)=store.prepare_fragment(&audience.anchor,&context,writer,plain)?;
    let cipher=[FRAGMENT,binding,nonce,&record].concat();let wrapping=wrap(audience,&cipher,nonce,&key,store,writer)?;
    // Source normalizes these placeholders from the authenticated receiving actor.
    let author=json!({"subject":"0","capabilityKind":"object","capability":"0"});
    Ok(json!({"ciphertext":crate::hex(&cipher),"wrapping":crate::hex(&wrapping),
      "author":author,"operation":"0","wrappedBy":author,"wrappedAt":"0"}))
}
pub(super) fn rewrap(audience:&Audience,fragment:&Value,nonce:&[u8;32],store:&mut Store,writer:&SigningKey)->Result<String>{
    let cipher=private::decode_hex(text(fragment,"ciphertext")?)?;
    let key=key(&audience.object,fragment,store)?;
    Ok(crate::hex(&wrap(audience,&cipher,nonce,&key,store,writer)?))
}
pub(super) fn open(object:&str,binding:&[u8],fragment:&Value,store:&Store)->Result<Vec<u8>>{
    let bytes=private::decode_hex(text(fragment,"ciphertext")?)?;let h=FRAGMENT.len()+binding.len();
    if !bytes.starts_with(FRAGMENT)||bytes.len()<h+32||bytes[FRAGMENT.len()..h]!=*binding{return Err("authored fragment address differs".into());}
    let nonce:[u8;32]=bytes[h..h+32].try_into().unwrap();let record=&bytes[h+32..];let (context,writer)=message(record)?;
    if context.object!=nat32(object)?||context.operation!=fragment_op(&context.object,binding,&nonce){return Err("authored fragment context differs".into());}
    object_messages::open(&context,&*key(object,fragment,store)?,&writer,record)
}
pub(super) fn epoch(fragment:&Value)->Result<u64>{
    let bytes=private::decode_hex(text(fragment,"wrapping")?)?;let h=WRAP.len();
    if !bytes.starts_with(WRAP)||bytes.len()<h+32{return Err("invalid fragment wrapping".into());}
    Ok(message(&bytes[h+32..])?.0.epoch)
}
