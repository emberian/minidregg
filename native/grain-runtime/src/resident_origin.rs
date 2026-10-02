//! Source-owned causal identity for admitted resident prompts.
use crate::*;
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all="camelCase",deny_unknown_fields)]
pub(crate) struct ResidentPromptOrigin {
    pub(crate) resident_prompt_id:String,
    pub(crate) prompt_sha256:String,
    pub(crate) prompt_operation_id:u64,
    pub(crate) session_id:Option<String>,
}
pub(crate) fn valid_digest(s:&str)->bool {
    s.len()==64 && s.bytes().all(|c|c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}
pub(crate) fn validate(id:&str, digest:&str, prompt:&str)->Result<()> {
    if !valid_digest(id) || !valid_digest(digest) || sha256_bytes(prompt.as_bytes())? != digest {
        return Err("resident prompt identity or exact text digest is invalid".into());
    }
    Ok(())
}
impl ResidentPromptOrigin {
    pub(crate) fn archive(&self,state:&Path,stage:&str)->Result<()> {
        let record=json!({"type":"mini-resident-prompt-origin-v1","stage":stage,"origin":self});
        if stage=="admitted" {
            write_new(&state.join(format!("resident-origin-id-{}.json",self.resident_prompt_id)),
                &serde_json::to_vec_pretty(&record).map_err(|e|e.to_string())?)?;
        }
        write_new(&state.join(format!("resident-origin-{:016}.{stage}.json",self.prompt_operation_id)),
            &serde_json::to_vec_pretty(&record).map_err(|e|e.to_string())?)
    }
    pub(crate) fn is_current(&self,id:&str,digest:&str,first_operation:u64)->bool {
        self.resident_prompt_id==id && self.prompt_sha256==digest
            && self.prompt_operation_id>=first_operation && self.prompt_operation_id>0
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn exact_text_and_both_ids_are_required(){
        let id="a".repeat(64);let text="current assignment";let digest=sha256_bytes(text.as_bytes()).unwrap();
        assert!(validate(&id,&digest,text).is_ok());
        assert!(validate(&id,&digest,"other assignment").is_err());
        assert!(validate("bad",&digest,text).is_err());
        assert!(validate(&id,&"A".repeat(64),text).is_err());
    }
    #[test] fn previous_identical_prompt_cannot_claim_new_dispatch(){
        let origin=ResidentPromptOrigin{resident_prompt_id:"a".repeat(64),prompt_sha256:"b".repeat(64),
            prompt_operation_id:94,session_id:Some("retained".into())};
        assert!(origin.is_current(&origin.resident_prompt_id,&origin.prompt_sha256,94));
        assert!(!origin.is_current(&origin.resident_prompt_id,&origin.prompt_sha256,95));
        assert!(!origin.is_current(&"c".repeat(64),&origin.prompt_sha256,94));
    }
}
