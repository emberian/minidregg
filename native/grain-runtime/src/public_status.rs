//! The plain SSH connector uses the same allowlisted state projection as
//! framed clients. Private configuration/custody never enters its response.
use serde_json::Value;
pub(crate) fn project(journal:&Value,shared_apps:usize)->Value{
    let mut value=crate::terminal::state(journal,0,0,shared_apps);
    let object=value.as_object_mut().expect("source state projection object");
    object.remove("attachmentId");object.remove("requestId");
    object.insert("type".into(),Value::String("mini-grain-status-v1".into()));value
}
#[cfg(test)]
mod tests{
    use super::*;
    use serde_json::json;
    #[test]
    fn plain_status_projects_without_private_configuration_or_custody(){
        let journal=json!({"connection":"detached","binding":{"config":{"custodyKey":"/private/key","providerKey":"secret","hostSocket":"/private/operator.sock"}},"providerAttempt":{"request":"private prompt"},"nextOperationId":10});
        let value=project(&journal,2);let text=value.to_string();
        for private in ["/private","secret","private prompt","binding","providerAttempt","nextOperationId"]{assert!(!text.contains(private),"{private}");}
        assert_eq!(value["type"],"mini-grain-status-v1");assert_eq!(value["registeredSharedApplicationCount"],2);
        assert!(value.get("attachmentId").is_none());assert!(value.get("requestId").is_none());
        assert_eq!(value.as_object().unwrap().len(),6);
    }
}
