//! Generic consumer for source-authored Objective Bend surfaces. Lean owns the
//! canonical Surface codec. This adapter accepts its JSON projection; it never
//! evaluates source, opens a resource, prepares an intent or confers authority.
use super::*;

const MAX_NODES: usize = 1024;
const MAX_LABEL_BYTES: usize = 16384;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Intent {
    artifact: String,
    export_name: String,
    program: String,
    instance: String,
    expected_root: String,
    arguments: String,
}

#[derive(Clone, Debug)]
struct Node {
    tag: usize,
    slot: usize,
    label: String,
    children: Vec<usize>,
}

#[derive(Clone, Debug)]
pub(crate) struct Surface {
    artifact: String,
    export_name: String,
    nodes: Vec<Node>,
    root: usize,
    intents: Vec<Intent>,
}

/// Supplied by the signed observation adapter, never parsed from Surface.
/// The retained value is precisely the projection already admitted for this
/// viewer, including locked/refused/unavailable states and source revisions.
pub(crate) struct AdmittedObservation {
    pub(crate) projection: Value,
}

/// Supplied by actual native preparation, never by source-controlled JSON.
/// Rendering exposes an exact custody handle only when every binding matches.
pub(crate) struct PreparedIntent {
    pub(crate) binding: Intent,
    pub(crate) operation: Value,
}

/// Actual accepted execution/source attribution, supplied separately from the
/// returned authored Surface. A returned label cannot impersonate this origin.
pub(crate) struct AcceptedOrigin {
    pub(crate) artifact: String,
    pub(crate) export_name: String,
}

fn exact(value: &Value, keys: &[&str]) -> Result<()> {
    let object = value.as_object().ok_or("surface record must be an object")?;
    if object.len() != keys.len() || keys.iter().any(|key| !object.contains_key(*key)) {
        return Err(format!("surface record requires exactly {}", keys.join(", ")).into());
    }
    Ok(())
}

fn string(value: &Value, key: &str) -> Result<String> {
    let text = member(value, key)?;
    if text.len() > MAX_LABEL_BYTES || text.contains('\0') {
        return Err(format!("surface {key} exceeds its bound or contains NUL").into());
    }
    Ok(text.to_owned())
}

fn decimal(value: &Value, key: &str) -> Result<String> {
    let text = string(value, key)?;
    field_decimal(&text, key)?;
    Ok(text)
}

fn index(value: &Value, key: &str) -> Result<usize> {
    decimal(value, key)?.parse().map_err(|_| format!("surface {key} is not a bounded index").into())
}

impl Intent {
    pub(crate) fn parse(value: &Value) -> Result<Self> {
        exact(value, &["artifact", "exportName", "program", "instance", "expectedRoot", "arguments"])?;
        let export_name = string(value, "exportName")?;
        if export_name.is_empty() { return Err("surface export name is empty".into()); }
        let arguments = string(value, "arguments")?;
        if !mini_sdk::hex::is_lower(&arguments) || arguments.len() % 2 != 0 {
            return Err("surface arguments must be exact lowercase hex".into());
        }
        Ok(Self { artifact: decimal(value, "artifact")?, export_name,
            program: decimal(value, "program")?, instance: decimal(value, "instance")?,
            expected_root: decimal(value, "expectedRoot")?, arguments })
    }
}

impl Surface {
    /// Node indices address earlier nodes, so no authored mount can create a
    /// recursive renderer loop. The entire structure is checked before output.
    pub(crate) fn parse(value: &Value) -> Result<Self> {
        exact(value, &["artifact", "exportName", "nodes", "root", "intents"])?;
        let export_name = string(value, "exportName")?;
        if export_name.is_empty() { return Err("surface export name is empty".into()); }
        let raw_nodes = value["nodes"].as_array().ok_or("surface nodes must be an array")?;
        let raw_intents = value["intents"].as_array().ok_or("surface intents must be an array")?;
        if raw_nodes.is_empty() || raw_nodes.len() > MAX_NODES || raw_intents.len() > MAX_NODES {
            return Err("surface exceeds node/intent bound".into());
        }
        let intents = raw_intents.iter().map(Intent::parse).collect::<Result<Vec<_>>>()?;
        let mut nodes = Vec::with_capacity(raw_nodes.len());
        for (position, value) in raw_nodes.iter().enumerate() {
            exact(value, &["tag", "slot", "label", "children"])?;
            let tag = index(value, "tag")?;
            let slot = index(value, "slot")?;
            let raw_children = value["children"].as_array().ok_or("surface children must be an array")?;
            if tag > 4 || raw_children.len() > MAX_NODES || (tag == 3 && slot >= intents.len()) {
                return Err("surface node tag, action slot or child count is invalid".into());
            }
            let mut children = Vec::with_capacity(raw_children.len());
            for child in raw_children {
                let text = child.as_str().ok_or("surface child must be a decimal index")?;
                field_decimal(text, "surface child")?;
                let child: usize = text.parse().map_err(|_| "surface child index exceeds bound")?;
                if child >= position { return Err("surface children must precede their parent".into()); }
                children.push(child);
            }
            nodes.push(Node { tag, slot, label: string(value, "label")?, children });
        }
        let root = index(value, "root")?;
        if root >= nodes.len() { return Err("surface root is absent".into()); }
        Ok(Self { artifact: decimal(value, "artifact")?, export_name, nodes, root, intents })
    }

    /// Observations and prepared intents come through separate native channels.
    /// No surface key can supply their contents or turn an action on. These
    /// projected nodes contain plain data, never authored HTML or script URLs.
    pub(crate) fn project(&self, origin: &AcceptedOrigin, observations: &[AdmittedObservation], prepared: &[PreparedIntent]) -> Result<Value> {
        if self.artifact != origin.artifact || self.export_name != origin.export_name {
            return Err("surface origin differs from the actual accepted source export".into());
        }
        if self.nodes.iter().any(|n| matches!(n.tag, 1 | 2) && n.slot >= observations.len()) {
            return Err("surface refers to an observation that was not admitted".into());
        }
        let nodes = self.nodes.iter().map(|node| {
            let mut result = json!({"tag": node.tag.to_string(), "label": node.label, "children": node.children.iter().map(usize::to_string).collect::<Vec<_>>()});
            if matches!(node.tag, 1 | 2) {
                result["observation"] = observations[node.slot].projection.clone();
            } else if node.tag == 3 {
                let binding = &self.intents[node.slot];
                match prepared.iter().find(|candidate| candidate.binding == *binding) {
                    Some(candidate) => { result["state"] = json!("prepared"); result["operation"] = candidate.operation.clone(); }
                    None => { result["state"] = json!("unprepared"); }
                }
            }
            result
        }).collect::<Vec<_>>();
        Ok(json!({"artifact": self.artifact, "exportName": self.export_name, "root": self.root.to_string(), "nodes": nodes}))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn intent() -> Value { json!({"artifact":"1","exportName":"close","program":"2","instance":"3","expectedRoot":"4","arguments":"00"}) }
    fn surface() -> Value { json!({"artifact":"1","exportName":"board","root":"2","intents":[intent()],"nodes":[
        {"tag":"1","slot":"0","label":"Source","children":[]},
        {"tag":"3","slot":"0","label":"Close","children":[]},
        {"tag":"4","slot":"0","label":"Board","children":["0","1"]}]}) }
    fn origin() -> AcceptedOrigin { AcceptedOrigin { artifact: "1".into(), export_name: "board".into() } }
    #[test]
    fn authored_enabled_or_observation_is_refused() {
        let mut value = surface(); value["nodes"][1]["enabled"] = json!(true);
        assert!(Surface::parse(&value).is_err());
        let mut value = surface(); value["nodes"][0]["observation"] = json!({"private":"forged"});
        assert!(Surface::parse(&value).is_err());
    }
    #[test]
    fn native_projection_and_every_action_binding_are_preserved() {
        let source = Surface::parse(&surface()).unwrap();
        let observed = vec![AdmittedObservation { projection: json!({"state":"locked","revision":"9"}) }];
        let mut binding = Intent::parse(&intent()).unwrap(); binding.expected_root = "5".into();
        let stale = vec![PreparedIntent { binding, operation: json!({"id":"stale"}) }];
        let view = source.project(&origin(), &observed, &stale).unwrap();
        assert_eq!(view["nodes"][0]["observation"], observed[0].projection);
        assert_eq!(view["nodes"][1]["state"], "unprepared");
        let prepared = vec![PreparedIntent { binding: Intent::parse(&intent()).unwrap(), operation: json!({"id":"actual-native-custody"}) }];
        assert_eq!(source.project(&origin(), &observed, &prepared).unwrap()["nodes"][1]["operation"], prepared[0].operation);
        assert!(source.project(&origin(), &[], &prepared).is_err());
        let mut wrong_origin = origin(); wrong_origin.artifact = "9".into();
        assert!(source.project(&wrong_origin, &observed, &prepared).is_err());
    }
    #[test]
    fn authored_cycle_and_unknown_node_fail_before_projection() {
        let mut value = surface(); value["nodes"][0]["children"] = json!(["2"]);
        assert!(Surface::parse(&value).is_err());
        let mut value = surface(); value["nodes"][0]["tag"] = json!("8");
        assert!(Surface::parse(&value).is_err());
    }
}
