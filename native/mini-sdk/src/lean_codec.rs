//! The runtime check that makes Lean the encoder of record: dlopen the Lean archive that carries
//! `Kernel.Contracts.Intents` and call its exports.
//!
//! `libminidregg-intents.so` is built by `lean-codec/build.sh` (the compiled objects of
//! `Kernel.Contracts.Intents` and its import closure, a C shim for runtime initialisation and
//! `ByteArray` marshalling, the toolchain's shared runtime). [`LeanCodec::load`] initialises it and
//! binds `minidregg_intent_encode` and `minidregg_intent_id_preimage`; each takes the intent's JSON
//! spelling as UTF-8 and answers one status byte, then the bytes (`1`) or a UTF-8 refusal (`0`).
//! `tests/lean_codec.rs` holds this crate's encoder to those answers on every row of
//! `golden/intents.json`. Lean initialises on the loading thread; every later call must be on it.
use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::path::Path;

use crate::{Error, Result};

type Obj = *mut c_void;

const RTLD_NOW: c_int = 2;
const RTLD_GLOBAL: c_int = 0x100;

pub struct LeanCodec {
    bytes_new: unsafe extern "C" fn(*const u8, usize) -> Obj,
    bytes_len: unsafe extern "C" fn(Obj) -> usize,
    bytes_ptr: unsafe extern "C" fn(Obj) -> *const u8,
    dec: unsafe extern "C" fn(Obj),
    encode: unsafe extern "C" fn(Obj) -> Obj,
    id_preimage: unsafe extern "C" fn(Obj) -> Obj,
}

/// What Lean answered: the canonical bytes, or its named refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Answer {
    Bytes(Vec<u8>),
    Refused(String),
}

fn symbol<T: Copy>(handle: *mut c_void, name: &str) -> Result<T> {
    let c = CString::new(name).map_err(|_| Error("symbol name".into()))?;
    // SAFETY: `handle` is a live dlopen handle; the caller names a function symbol of type `T`.
    let p = unsafe { libc::dlsym(handle, c.as_ptr()) };
    if p.is_null() {
        return Err(Error(format!("the intent library has no symbol {name}")));
    }
    // SAFETY: `T` is a function pointer type of the pointer's width.
    Ok(unsafe { std::mem::transmute_copy::<*mut c_void, T>(&p) })
}

impl LeanCodec {
    /// Load and initialise the library on the calling thread.
    pub fn load(lib: &Path) -> Result<LeanCodec> {
        let c = CString::new(lib.as_os_str().as_encoded_bytes()).map_err(|_| Error("library path".into()))?;
        // SAFETY: a NUL-terminated path; the handle is used only through `symbol`.
        let handle = unsafe { libc::dlopen(c.as_ptr(), RTLD_NOW | RTLD_GLOBAL) };
        if handle.is_null() {
            // SAFETY: dlerror returns a thread-local NUL-terminated string or null.
            let e = unsafe { libc::dlerror() };
            let why = if e.is_null() { "unknown".into() } else { unsafe { CStr::from_ptr(e as *const c_char) }.to_string_lossy().into_owned() };
            return Err(Error(format!("cannot load the intent library {}: {why}", lib.display())));
        }
        let init: unsafe extern "C" fn() -> c_int = symbol(handle, "mdi_init")?;
        // SAFETY: the shim's initialiser, called once on this thread.
        if unsafe { init() } != 0 {
            return Err(Error("the intent library's Lean initialisation failed".into()));
        }
        Ok(LeanCodec {
            bytes_new: symbol(handle, "mdi_bytes_new")?,
            bytes_len: symbol(handle, "mdi_bytes_len")?,
            bytes_ptr: symbol(handle, "mdi_bytes_ptr")?,
            dec: symbol(handle, "mdi_dec")?,
            encode: symbol(handle, "minidregg_intent_encode")?,
            id_preimage: symbol(handle, "minidregg_intent_id_preimage")?,
        })
    }

    fn call(&self, export: unsafe extern "C" fn(Obj) -> Obj, spelling: &[u8]) -> Result<Answer> {
        // SAFETY: `export` consumes its owned argument and returns an owned ByteArray; the reply is
        // copied out before it is released.
        let reply = unsafe {
            let reply = export((self.bytes_new)(spelling.as_ptr(), spelling.len()));
            let bytes = std::slice::from_raw_parts((self.bytes_ptr)(reply), (self.bytes_len)(reply)).to_vec();
            (self.dec)(reply);
            bytes
        };
        match reply.split_first() {
            Some((1, bytes)) => Ok(Answer::Bytes(bytes.to_vec())),
            Some((0, why)) => Ok(Answer::Refused(String::from_utf8_lossy(why).into_owned())),
            _ => Err(Error("the intent export answered without a status byte".into())),
        }
    }

    /// `Kernel.Contracts.Intents.encodeSpelling`: the canonical intent bytes of a JSON spelling.
    pub fn encode(&self, spelling: &str) -> Result<Answer> {
        self.call(self.encode, spelling.as_bytes())
    }

    /// `Kernel.Contracts.Intents.idPreimageSpelling`: `DREGG/CONTRACT/INTENT-ID/v1 ‖ bytes`.
    pub fn id_preimage(&self, spelling: &str) -> Result<Answer> {
        self.call(self.id_preimage, spelling.as_bytes())
    }
}
