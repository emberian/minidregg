//! Signed member request used only to provision a fresh controller. It carries
//! no bearer, endpoint, filesystem path or authority to change a running task.
use super::*;
use ring::signature::{Ed25519KeyPair, KeyPair, UnparsedPublicKey, ED25519};
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Choice {
    pub owner: Owner,
    pub runner: String,
    pub task: String,
    pub provider: String,
    pub model: String,
    pub table_sha256: String,
    pub signature: String,
}
impl Choice {
    pub fn body(&self) -> Value {
        json!({"type":"mini-provider-choice-v1", "owner":{"subject":self.owner.subject,"publicKey":self.owner.public_key},
            "runner":self.runner,"task":self.task,"provider":self.provider,"model":self.model,"tableSha256":self.table_sha256})
    }
    fn signing_bytes(&self) -> Vec<u8> {
        let mut out = b"mini/provider-choice/v1\0".to_vec();
        for part in [
            &self.owner.subject,
            &self.owner.public_key,
            &self.runner,
            &self.task,
            &self.provider,
            &self.model,
            &self.table_sha256,
        ] {
            out.extend_from_slice(&(part.len() as u32).to_le_bytes());
            out.extend_from_slice(part.as_bytes());
        }
        out
    }
    pub fn to_json(&self) -> Value {
        let mut value = self.body();
        value["signature"] = json!(self.signature);
        value
    }
    pub fn signed(
        owner: Owner,
        runner: &str,
        task: &str,
        provider: &str,
        model: &str,
        table: &ProviderTable,
        seed: &[u8; 32],
    ) -> Result<Self, String> {
        let choice =
            Self::signed_for_catalogue(owner, runner, task, provider, model, &table.sha256, seed)?;
        choice.validate_route(table)?;
        Ok(choice)
    }
    pub fn signed_for_catalogue(
        owner: Owner,
        runner: &str,
        task: &str,
        provider: &str,
        model: &str,
        table_sha256: &str,
        seed: &[u8; 32],
    ) -> Result<Self, String> {
        let key = Ed25519KeyPair::from_seed_unchecked(seed)
            .map_err(|_| "member signing key unavailable")?;
        if hex(key.public_key().as_ref()) != owner.public_key {
            return Err("member choice signing key differs from owner".into());
        }
        let mut choice = Self {
            owner,
            runner: runner.into(),
            task: task.into(),
            provider: provider.into(),
            model: model.into(),
            table_sha256: table_sha256.into(),
            signature: String::new(),
        };
        choice.signature = hex(key.sign(&choice.signing_bytes()).as_ref());
        Self::from_json(&choice.to_json())
    }
    pub fn from_json(value: &Value) -> Result<Self, String> {
        object_keys(
            value,
            &[
                "type",
                "owner",
                "runner",
                "task",
                "provider",
                "model",
                "tableSha256",
                "signature",
            ],
            "provider choice",
        )?;
        if value["type"] != "mini-provider-choice-v1" {
            return Err("unknown provider choice version".into());
        }
        let owner = value.get("owner").ok_or("provider choice owner absent")?;
        object_keys(owner, &["subject", "publicKey"], "provider choice owner")?;
        let choice = Self {
            owner: Owner::new(
                string(owner, "subject", "choice owner")?,
                string(owner, "publicKey", "choice owner")?,
            )?,
            runner: string(value, "runner", "choice")?.into(),
            task: string(value, "task", "choice")?.into(),
            provider: string(value, "provider", "choice")?.into(),
            model: string(value, "model", "choice")?.into(),
            table_sha256: string(value, "tableSha256", "choice")?.into(),
            signature: string(value, "signature", "choice")?.into(),
        };
        decimal(&choice.runner, "choice runner")?;
        decimal(&choice.task, "choice task")?;
        provider_name(&choice.provider)?;
        if choice.model.is_empty()
            || choice.model.len() > 256
            || choice.model.chars().any(char::is_control)
        {
            return Err("invalid choice model".into());
        }
        if choice.table_sha256.len() != 64 || choice.signature.len() != 128 {
            return Err("invalid choice digest or signature width".into());
        }
        UnparsedPublicKey::new(&ED25519, unhex(&choice.owner.public_key)?)
            .verify(&choice.signing_bytes(), &unhex(&choice.signature)?)
            .map_err(|_| "provider choice signature refused")?;
        Ok(choice)
    }
    pub fn validate_route(&self, table: &ProviderTable) -> Result<(), String> {
        decimal(&self.runner, "choice runner")?;
        decimal(&self.task, "choice task")?;
        if self.table_sha256 != table.sha256 {
            return Err("provider catalogue changed; choose the route again".into());
        }
        if table.select(&self.model, Some(&self.provider))?.credential != CredentialSource::User {
            return Err("member BYOK choice needs a user credential route".into());
        }
        Ok(())
    }
    pub fn digest(&self) -> String {
        hex(&Sha256::digest(
            serde_json::to_vec(&self.to_json()).expect("choice JSON"),
        ))
    }
}
impl CredentialStore {
    pub fn choose(&self, choice: &Choice, table: &ProviderTable) -> Result<(), String> {
        let checked = Choice::from_json(&choice.to_json())?;
        checked.validate_route(table)?;
        self.choice_grant(&checked)?;
        let dir = self.directory(Namespace::Owner(&checked.owner), false)?;
        let _lock = provider_lock(&dir, &format!("choice-{}", checked.task))?;
        replace_private(
            &dir.join(format!("choice-{}.json", checked.task)),
            &serde_json::to_vec_pretty(&checked.to_json()).map_err(|_| "choice encode failed")?,
        )
    }
    pub fn selected(
        &self,
        owner: &Owner,
        runner: &str,
        task: &str,
        table: &ProviderTable,
    ) -> Result<Choice, String> {
        decimal(task, "choice task")?;
        let dir = self.directory(Namespace::Owner(owner), false)?;
        let value = read_record(&dir.join(format!("choice-{task}.json")), "provider choice")?
            .ok_or("no member provider choice for this task")?;
        let choice = Choice::from_json(&value)?;
        if &choice.owner != owner || choice.runner != runner || choice.task != task {
            return Err("provider choice names another member or task".into());
        }
        choice.validate_route(table)?;
        self.choice_grant(&choice)?;
        Ok(choice)
    }
    /// Check without spending a daily call. Current height/output limits are
    /// still checked during every native reservation, including after a queue.
    fn choice_grant(&self, choice: &Choice) -> Result<(), String> {
        let dir = self.directory(Namespace::Owner(&choice.owner), false)?;
        private_dir_check(&dir, "credential namespace")?;
        let _lock = provider_lock(&dir, &choice.provider)?;
        let g = self
            .grants(&dir, &choice.provider)?
            .into_iter()
            .find(|g| g.runner == choice.runner)
            .ok_or("choice requires a runner grant")?;
        if g.model.as_deref() != Some(&choice.model) {
            return Err("choice requires an exact model-scoped grant".into());
        }
        if self
            .secret(Namespace::Owner(&choice.owner), &choice.provider)?
            .is_none()
        {
            return Err("choice requires enrolled sealed custody".into());
        }
        Ok(())
    }
}
