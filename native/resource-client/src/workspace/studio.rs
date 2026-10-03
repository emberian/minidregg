//! Source packages are ordinary module documents plus a local composition draft.
//! This discovery/custody index grants no read, publication or execution rights.
//! Preview snapshots use fresh authenticated document openings, never old text.
use super::*;
use std::collections::BTreeSet;
#[path = "studio_preview.rs"]
mod preview;
pub(crate) fn preview_available() -> bool { preview::available() }
pub(crate) fn source_preview(root:&Path, workspace:&Value, id:&str, snapshot:&str, edition:&str) -> Result<Value> { preview::run(root,workspace,id,snapshot,edition) }
pub(crate) fn source_preview_result(root:&Path, workspace:&Value, id:&str, snapshot:&str, run:&str) -> Result<Value> { preview::load(root,workspace,id,snapshot,run) }
pub(crate) fn source_preview_runs(root:&Path, workspace:&Value, id:&str, snapshot:&str) -> Result<Vec<Value>> { preview::runs(root,workspace,id,snapshot) }

const TYPE: &str = "mini-studio-package-draft-v1";
const MAX_MANIFEST: usize = 192 * 1024;
const MAX_PROJECT: usize = 256 * 1024;
const MAX_SOURCE: usize = 4 * 1024 * 1024;

#[derive(Clone, Debug)]
pub(crate) struct Import {
    pub alias: String,
    pub module: usize,
}
#[derive(Clone, Debug)]
pub(crate) struct Module {
    pub name: String,
    pub reference: String,
    pub imports: Vec<Import>,
}
#[derive(Clone, Debug)]
pub(crate) struct Manifest {
    pub entry_module: usize,
    pub entry_definition: String,
    pub modules: Vec<Module>,
}

fn exact(value: &Value, keys: &[&str]) -> Result<()> {
    let map = value
        .as_object()
        .ok_or("source manifest record must be an object")?;
    if map.len() != keys.len() || keys.iter().any(|key| !map.contains_key(*key)) {
        return Err(format!(
            "source manifest requires exactly {}",
            keys.join(", ")
        ));
    }
    Ok(())
}
fn label(value: &Value, key: &str, empty: bool) -> Result<String> {
    let text = member(value, key)?;
    if text.len() > 16384 || text.contains('\0') || (!empty && text.is_empty()) {
        return Err(format!("invalid source {key}"));
    }
    Ok(text.into())
}
fn index(value: &Value, key: &str) -> Result<usize> {
    let text = member(value, key)?;
    field_decimal(text, key)?;
    text.parse()
        .map_err(|_| format!("source {key} exceeds the module bound"))
}
impl Manifest {
    pub(crate) fn parse(value: &Value) -> Result<Self> {
        if serde_json::to_vec_pretty(value)
            .map_err(|e| e.to_string())?
            .len()
            > MAX_MANIFEST
        {
            return Err("source composition exceeds its bound".into());
        }
        exact(value, &["entryModule", "entryDefinition", "modules"])?;
        let raw = value["modules"]
            .as_array()
            .ok_or("source modules must be an ordered array")?;
        if raw.is_empty() || raw.len() > 256 {
            return Err("source packages require 1 to 256 modules".into());
        }
        let mut names = BTreeSet::new();
        let mut modules: Vec<Module> = Vec::with_capacity(raw.len());
        for (position, record) in raw.iter().enumerate() {
            exact(record, &["name", "reference", "imports"])?;
            let name = label(record, "name", false)?;
            if !names.insert(name.clone()) {
                return Err("source module names must be distinct".into());
            }
            let reference = label(record, "reference", false)?;
            validate_name(&reference)?;
            let raw_imports = record["imports"]
                .as_array()
                .ok_or("module imports must be an array")?;
            if raw_imports.len() > 256 {
                return Err("module import bound exceeded".into());
            }
            let mut aliases = BTreeSet::new();
            let mut imports = Vec::new();
            for edge in raw_imports {
                exact(edge, &["alias", "module"])?;
                let alias = label(edge, "alias", true)?;
                let module = index(edge, "module")?;
                if module >= position {
                    return Err("imports must select an earlier module".into());
                }
                if alias.is_empty() && modules[module].name != "Base" {
                    return Err("only Base may have an empty import alias".into());
                }
                if !aliases.insert(alias.clone()) {
                    return Err("module import aliases must be distinct".into());
                }
                imports.push(Import { alias, module });
            }
            modules.push(Module {
                name,
                reference,
                imports,
            });
        }
        let entry_module = index(value, "entryModule")?;
        if entry_module >= modules.len() {
            return Err("entry module is absent".into());
        }
        Ok(Self {
            entry_module,
            entry_definition: label(value, "entryDefinition", false)?,
            modules,
        })
    }
    pub(crate) fn json(&self) -> Value {
        json!({"entryModule":self.entry_module.to_string(),"entryDefinition":self.entry_definition,
            "modules":self.modules.iter().map(|m| json!({"name":m.name,"reference":m.reference,
                "imports":m.imports.iter().map(|i| json!({"alias":i.alias,"module":i.module.to_string()})).collect::<Vec<_>>()})).collect::<Vec<_>>()})
    }
}
/// Authored fields of ObjectiveBendPartialAuthor.partial-input.v1. Package and
/// partialCorePath are supplied later by the actual captured source producer.
/// This validates the bounded shape; reflection/linking determine its meaning.
pub(crate) fn declaration(value: &Value) -> Result<Value> {
    exact(
        value,
        &["directParents", "ancestorOrder", "required", "provided"],
    )?;
    for key in ["directParents", "ancestorOrder"] {
        let ids = value[key]
            .as_array()
            .ok_or("prototype parents must be ordered arrays")?;
        if ids.len() > 256 {
            return Err("prototype parent bound exceeded".into());
        }
        for id in ids {
            let text = id
                .as_str()
                .ok_or("prototype identity must be a decimal string")?;
            field_decimal(text, "prototype identity")?;
            if text.len() > 80 {
                return Err("prototype identity exceeds its bound".into());
            }
        }
    }
    for key in ["required", "provided"] {
        let entries = value[key]
            .as_array()
            .ok_or("prototype entries must be arrays")?;
        if entries.len() > 256 {
            return Err("prototype entry bound exceeded".into());
        }
        for entry in entries {
            if key == "required" {
                exact(entry, &["scope", "selector", "typeEntry"])?;
                if !matches!(member(entry, "scope")?, "finalSelf" | "priorSuper") {
                    return Err("unknown prototype requirement scope".into());
                }
                label(entry, "selector", false)?;
                label(entry, "typeEntry", false)?;
            } else {
                exact(entry, &["selector", "entry", "captures"])?;
                label(entry, "selector", false)?;
                label(entry, "entry", false)?;
                let captures = entry["captures"]
                    .as_array()
                    .ok_or("prototype captures must be source entry names")?;
                if captures.len() > 256 {
                    return Err("prototype capture bound exceeded".into());
                }
                for capture in captures {
                    let text = capture
                        .as_str()
                        .ok_or("prototype capture must name a source entry")?;
                    if text.is_empty() || text.len() > 16384 || text.contains('\0') {
                        return Err("invalid source capture entry".into());
                    }
                }
            }
        }
    }
    if serde_json::to_vec_pretty(value)
        .map_err(|e| e.to_string())?
        .len()
        > MAX_MANIFEST
    {
        return Err("prototype declaration exceeds its bound".into());
    }
    Ok(value.clone())
}
pub(crate) fn empty_declaration() -> Value {
    json!({"directParents":[],"ancestorOrder":[],"required":[],"provided":[]})
}
fn token() -> Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut bytes))
        .map_err(|e| e.to_string())?;
    Ok(hex(&bytes))
}
fn directory(root: &Path, id: &str) -> Result<PathBuf> {
    if id.len() != 32
        || !id
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
    {
        return Err("invalid source workspace identity".into());
    }
    Ok(root.join("studio-packages").join(id))
}
fn save_state(path: &Path, value: &Value, old: Option<&Value>) -> Result<()> {
    if serde_json::to_vec_pretty(value)
        .map_err(|e| e.to_string())?
        .len()
        > MAX_PROJECT
    {
        return Err(
            "source workspace custody index exceeds its bound; existing drafts remain retained"
                .into(),
        );
    }
    atomic_json(path, value, old)
}
pub(crate) fn load(root: &Path, workspace: &Value, id: &str) -> Result<Value> {
    let dir = directory(root, id)?;
    private_dir(&dir)?;
    let value = bounded_json_limit(&dir.join("draft.json"), MAX_PROJECT as u64)?;
    if value["type"] != TYPE
        || value["id"] != id
        || value["subject"] != member(workspace, "subject")?
    {
        return Err("source workspace does not belong to this member".into());
    }
    Manifest::parse(&value["manifest"])?;
    if let Some(prototype) = value.get("prototype") {
        declaration(prototype)?;
    }
    Ok(value)
}
pub(crate) fn create(
    root: &Path,
    workspace: &Value,
    title: &str,
    manifest: &Value,
) -> Result<Value> {
    let manifest = Manifest::parse(manifest)?;
    if title.is_empty() || title.len() > 16384 || title.contains('\0') {
        return Err("invalid source workspace title".into());
    }
    let parent = root.join("studio-packages");
    if !parent.exists() {
        make_private_dir(&parent)?;
    }
    private_dir(&parent)?;
    let id = token()?;
    let dir = directory(root, &id)?;
    make_private_dir(&dir)?;
    let value = json!({"type":TYPE,"id":id,"subject":member(workspace,"subject")?,"title":title,
        "revision":"0","manifest":manifest.json(),"prototype":empty_declaration(),"editors":[],"snapshots":[]});
    save_state(&dir.join("draft.json"), &value, None)?;
    Ok(value)
}
pub(crate) fn save_manifest(
    root: &Path,
    workspace: &Value,
    id: &str,
    revision: &str,
    manifest: &Value,
) -> Result<Value> {
    let old = load(root, workspace, id)?;
    if member(&old, "revision")? != revision {
        return Err("this package composition changed; your submitted manifest is retained in this page, copy or reconcile it with the current workspace".into());
    }
    let manifest = Manifest::parse(manifest)?;
    let mut value = old.clone();
    value["manifest"] = manifest.json();
    save_composition(root, id, revision, &old, value)
}
fn save_composition(
    root: &Path,
    id: &str,
    revision: &str,
    old: &Value,
    mut value: Value,
) -> Result<Value> {
    let generation = revision
        .parse::<u64>()
        .map_err(|_| "invalid source workspace revision")?
        .checked_add(1)
        .ok_or("source workspace revision exhausted")?;
    value["revision"] = json!(generation.to_string());
    let dir = directory(root, id)?;
    let history = dir.join(format!("composition-{generation}.json"));
    let prior = json!({"manifest":old["manifest"],"prototype":old.get("prototype").cloned().unwrap_or_else(empty_declaration)});
    if history.exists() {
        if bounded_json_limit(&history, MAX_PROJECT as u64)? != prior {
            return Err("composition history differs; retain and reconcile this draft".into());
        }
    } else {
        atomic_json(&history, &prior, None)?;
    }
    save_state(&dir.join("draft.json"), &value, Some(old))?;
    Ok(value)
}
pub(crate) fn save_declaration(
    root: &Path,
    workspace: &Value,
    id: &str,
    revision: &str,
    prototype: &Value,
) -> Result<Value> {
    let old = load(root, workspace, id)?;
    if member(&old, "revision")? != revision {
        return Err("composition changed; your authored declaration remains retained".into());
    }
    let mut value = old.clone();
    value["prototype"] = declaration(prototype)?;
    save_composition(root, id, revision, &old, value)
}
/// Apply a bounded composition operation to the member's selected revision.
/// Source document identities are retained; changing imports creates no rights.
pub(crate) fn compose(
    root: &Path,
    workspace: &Value,
    id: &str,
    revision: &str,
    change: &Value,
) -> Result<Value> {
    let old = load(root, workspace, id)?;
    if member(&old, "revision")? != revision {
        return Err(
            "composition changed; reconcile your retained operation with its current revision"
                .into(),
        );
    }
    let mut manifest = Manifest::parse(&old["manifest"])?;
    match member(change, "operation")? {
        "add-module" => {
            exact(change, &["operation", "name", "reference"])?;
            manifest.modules.push(Module {
                name: label(change, "name", false)?,
                reference: label(change, "reference", false)?,
                imports: Vec::new(),
            });
        }
        "entry" => {
            exact(change, &["operation", "module", "definition"])?;
            manifest.entry_module = index(change, "module")?;
            manifest.entry_definition = label(change, "definition", false)?;
        }
        "add-import" => {
            exact(change, &["operation", "module", "dependency", "alias"])?;
            let module = index(change, "module")?;
            let dependency = index(change, "dependency")?;
            manifest
                .modules
                .get_mut(module)
                .ok_or("source module is absent")?
                .imports
                .push(Import {
                    alias: label(change, "alias", true)?,
                    module: dependency,
                });
        }
        "remove-import" => {
            exact(change, &["operation", "module", "import"])?;
            let module = index(change, "module")?;
            let edge = index(change, "import")?;
            let imports = &mut manifest
                .modules
                .get_mut(module)
                .ok_or("source module is absent")?
                .imports;
            if edge >= imports.len() {
                return Err("selected import is absent".into());
            }
            imports.remove(edge);
        }
        _ => return Err("unknown source composition operation".into()),
    }
    save_manifest(root, workspace, id, revision, &manifest.json())
}
/// Historical composition is custody metadata, not permission to reopen source.
pub(crate) fn manifest_version(
    root: &Path,
    workspace: &Value,
    id: &str,
    revision: &str,
) -> Result<Value> {
    let current = load(root, workspace, id)?;
    field_decimal(revision, "revision")?;
    let selected = revision
        .parse::<u64>()
        .map_err(|_| "invalid composition revision")?;
    let generation = member(&current, "revision")?
        .parse::<u64>()
        .map_err(|_| "invalid composition revision")?;
    if selected > generation {
        return Err("composition revision is absent".into());
    }
    let composition = if selected == generation {
        json!({"manifest":current["manifest"],"prototype":current.get("prototype").cloned().unwrap_or_else(empty_declaration)})
    } else {
        let directory = directory(root, id)?;
        let path = directory.join(format!("composition-{}.json", selected + 1));
        if path.exists() {
            bounded_json_limit(&path, MAX_PROJECT as u64)?
        } else {
            json!({"manifest":bounded_json_limit(&directory.join(format!("manifest-{}.json",selected+1)),MAX_MANIFEST as u64)?,"prototype":empty_declaration()})
        }
    };
    Manifest::parse(&composition["manifest"])?;
    declaration(&composition["prototype"])?;
    Ok(
        json!({"package":id,"revision":revision,"title":current["title"],"manifest":composition["manifest"],"prototype":composition["prototype"]}),
    )
}
/// Fork only the composition. Both workspaces continue to address ordinary
/// documents; every source opening and edit uses current document authority.
pub(crate) fn fork(
    root: &Path,
    workspace: &Value,
    id: &str,
    revision: &str,
    title: &str,
) -> Result<Value> {
    let selected = manifest_version(root, workspace, id, revision)?;
    let created = create(root, workspace, title, &selected["manifest"])?;
    let mut value = created.clone();
    value["forkOf"] = json!({"package":id,"revision":revision});
    value["prototype"] = selected["prototype"].clone();
    save_state(
        &directory(root, member(&value, "id")?)?.join("draft.json"),
        &value,
        Some(&created),
    )?;
    Ok(value)
}
/// Submitted composition text is retained before validation/CAS, so malformed
/// or stale drafts survive reload without changing the selected package.
pub(crate) fn retain_submission(
    root: &Path,
    workspace: &Value,
    id: &str,
    revision: &str,
    text: &str,
) -> Result<String> {
    load(root, workspace, id)?;
    if text.len() > MAX_MANIFEST || text.contains('\0') {
        return Err("source composition exceeds its bound".into());
    }
    let submission = token()?;
    let value = json!({"type":"mini-studio-manifest-submission-v1","package":id,"subject":member(workspace,"subject")?,"id":submission,"revision":revision,"text":text});
    atomic_json(
        &directory(root, id)?.join(format!("submission-{submission}.json")),
        &value,
        None,
    )?;
    Ok(submission)
}
pub(crate) fn submission(
    root: &Path,
    workspace: &Value,
    id: &str,
    submission: &str,
) -> Result<Value> {
    load(root, workspace, id)?;
    directory(root, submission)?;
    let value = bounded_json_limit(
        &directory(root, id)?.join(format!("submission-{submission}.json")),
        (MAX_MANIFEST * 2) as u64,
    )?;
    if value["type"] != "mini-studio-manifest-submission-v1"
        || value["package"] != id
        || value["id"] != submission
        || value["subject"] != member(workspace, "subject")?
    {
        return Err("source draft does not belong to this package/member".into());
    }
    Ok(value)
}
pub(crate) fn projects(root: &Path, workspace: &Value) -> Result<Vec<Value>> {
    let parent = root.join("studio-packages");
    if !parent.exists() {
        return Ok(Vec::new());
    }
    private_dir(&parent)?;
    let mut values = Vec::new();
    for entry in fs::read_dir(parent).map_err(|e| e.to_string())?.take(256) {
        let entry = entry.map_err(|e| e.to_string())?;
        if let Some(id) = entry.file_name().to_str() {
            if let Ok(value) = load(root, workspace, id) {
                values.push(value);
            }
        }
    }
    Ok(values)
}
/// Opening source editing uses the same per-tab signed base and durable operation
/// as ordinary doc editing. A fresh current read gates even a retained draft.
pub(crate) fn editor(
    root: &Path,
    workspace: &Value,
    id: &str,
    module: usize,
    fresh: bool,
) -> Result<web_author::Edit> {
    let old = load(root, workspace, id)?;
    let manifest = Manifest::parse(&old["manifest"])?;
    let selected = manifest
        .modules
        .get(module)
        .ok_or("source module is absent")?;
    let (read, _) = read_rendered(root, workspace, &selected.reference, None)?;
    content_page(&read.view, &selected.reference)?;
    if !fresh {
        if let Some(existing) = old["editors"].as_array().and_then(|list| {
            list.iter()
                .rev()
                .find(|e| e["name"] == selected.name && e["reference"] == selected.reference)
        }) {
            return web_author::load(
                root,
                workspace,
                &selected.reference,
                member(existing, "edit")?,
            );
        }
    }
    let edit = web_author::open(root, workspace, &selected.reference)?;
    let mut value = old.clone();
    value["editors"]
        .as_array_mut()
        .ok_or("invalid source editor index")?
        .push(json!({"name":selected.name,"reference":selected.reference,"edit":edit.id}));
    save_state(&directory(root, id)?.join("draft.json"), &value, Some(&old))?;
    Ok(edit)
}
/// Capture saved module source from fresh authenticated openings at one head.
/// Files are immutable custody for the real canonical package producer; their
/// paths/digests are never interpreted as installation or source acceptance.
pub(crate) fn snapshot(root: &Path, workspace: &Value, id: &str) -> Result<Value> {
    let old = load(root, workspace, id)?;
    let manifest = Manifest::parse(&old["manifest"])?;
    let mut coordinate = None;
    let mut opened = Vec::new();
    let mut total = 0usize;
    for module in &manifest.modules {
        let (read, _) = read_rendered(root, workspace, &module.reference, None)?;
        content_page(&read.view, &module.reference)?;
        let challenge = bounded_json(&read.attempt.join("challenge.json"))?;
        check_read_coordinates(coordinate.as_ref(), &challenge)?;
        if coordinate.is_none() {
            coordinate = Some(challenge.clone());
        }
        let seen = seen_read_value(&module.reference, &read, &challenge);
        let bytes = pull_text(&seen)?;
        total = total
            .checked_add(bytes.len())
            .ok_or("source byte bound exceeded")?;
        if total > MAX_SOURCE {
            return Err("sealed source byte bound exceeded".into());
        }
        std::str::from_utf8(&bytes)
            .map_err(|_| "source is not UTF8; keep this module in the byte editor")?;
        opened.push((bytes,json!({"name":module.name,"reference":module.reference,"cellRoot":read.view["cell"]["root"],"height":challenge["height"],"authorityRoot":challenge["authorityRoot"],"readAttempt":read.attempt,"referenceBinding":reference(root,&module.reference)?})));
    }
    if load(root, workspace, id)?["revision"] != old["revision"] {
        return Err("package composition changed during source capture".into());
    }
    let snapshot_id = token()?;
    let dir = directory(root, id)?.join(&snapshot_id);
    make_private_dir(&dir)?;
    let mut modules = Vec::new();
    let mut sources = Vec::new();
    for (index, (bytes, source)) in opened.into_iter().enumerate() {
        let path = dir.join(format!("module-{index}.bend"));
        private_file(&path, &bytes)?;
        let module = &manifest.modules[index];
        modules.push(json!({"name":module.name,"sourcePath":path,"imports":module.imports.iter().map(|i|json!({"alias":i.alias,"module":i.module.to_string()})).collect::<Vec<_>>() }));
        sources.push(source);
    }
    let input = json!({"schema":"dregg.bend.package-input.v1","entryModule":manifest.entry_module.to_string(),"entryDefinition":manifest.entry_definition,"modules":modules});
    private_file(
        &dir.join("package-input.json"),
        &serde_json::to_vec(&input).map_err(|e| e.to_string())?,
    )?;
    let capture = json!({"type":"mini-studio-source-capture-v1","id":snapshot_id,"package":id,"subject":member(workspace,"subject")?,"revision":old["revision"],"entryModule":manifest.entry_module.to_string(),"entryDefinition":manifest.entry_definition,"prototype":old.get("prototype").cloned().unwrap_or_else(empty_declaration),"sources":sources,"coordinate":coordinate,"producer":"unavailable","publication":"unavailable"});
    atomic_json(&dir.join("capture.json"), &capture, None)?;
    let mut value = old.clone();
    value["snapshots"]
        .as_array_mut()
        .ok_or("invalid source snapshot index")?
        .push(json!({"id":capture["id"],"revision":capture["revision"],"count":manifest.modules.len().to_string()}));
    save_state(&directory(root, id)?.join("draft.json"), &value, Some(&old))?;
    Ok(capture)
}

pub(crate) fn capture(root: &Path, workspace: &Value, id: &str, snapshot: &str) -> Result<Value> {
    load(root, workspace, id)?;
    directory(root, snapshot)?;
    let value = bounded_json_limit(
        &directory(root, id)?.join(snapshot).join("capture.json"),
        1024 * 1024,
    )?;
    if value["type"] != "mini-studio-source-capture-v1"
        || value["package"] != id
        || value["id"] != snapshot
        || value["subject"] != member(workspace, "subject")?
    {
        return Err("source capture does not belong to this package/member".into());
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn source_composition_preserves_stale_operation_and_historical_fork() {
        let root = std::env::temp_dir().join(format!("mini-studio-{}", token().unwrap()));
        make_private_dir(&root).unwrap();
        let workspace = json!({"subject":"7"});
        let first = json!({"entryModule":"0","entryDefinition":"remember","modules":[
            {"name":"Notebook","reference":"notebook-source","imports":[]}]});
        let project = create(&root, &workspace, "Notebook", &first).unwrap();
        let id = member(&project, "id").unwrap();
        let retained =
            retain_submission(&root, &workspace, id, "0", "my earlier authored draft").unwrap();
        compose(
            &root,
            &workspace,
            id,
            "0",
            &json!({"operation":"add-module","name":"Review","reference":"review-source"}),
        )
        .unwrap();
        assert!(compose(
            &root,
            &workspace,
            id,
            "0",
            &json!({"operation":"entry","module":"1","definition":"review"})
        )
        .is_err());
        assert_eq!(
            submission(&root, &workspace, id, &retained).unwrap()["text"],
            "my earlier authored draft"
        );
        assert_eq!(
            manifest_version(&root, &workspace, id, "0").unwrap()["manifest"],
            first
        );
        let forked = fork(&root, &workspace, id, "0", "Earlier notebook").unwrap();
        assert_eq!(forked["manifest"], first);
        assert_eq!(forked["forkOf"], json!({"package":id,"revision":"0"}));
        assert_eq!(
            load(&root, &workspace, id).unwrap()["manifest"]["modules"]
                .as_array()
                .unwrap()
                .len(),
            2
        );
        fs::remove_dir_all(&root).unwrap();
    }
    #[test]
    fn source_manifest_rejects_forward_imports_and_authored_authority() {
        let good = json!({"entryModule":"1","entryDefinition":"remember","modules":[
            {"name":"Base","reference":"base-source","imports":[]},
            {"name":"Notebook","reference":"notebook-source","imports":[{"alias":"","module":"0"}]}]});
        assert!(Manifest::parse(&good).is_ok());
        let mut bad = good.clone();
        bad["modules"][1]["imports"][0]["module"] = json!("1");
        assert!(Manifest::parse(&bad).is_err());
        let mut bad = good;
        bad["modules"][1]["enabled"] = json!(true);
        assert!(Manifest::parse(&bad).is_err());
    }
}
