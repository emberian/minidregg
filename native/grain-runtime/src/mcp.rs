//! Stdio MCP edge. This process has no Mini signing key; each call is sent to
//! the separately supervised controller over an owner-only Unix socket.
use serde_json::{json, Value};
use std::fs;
use std::io::{self, BufRead, Read, Write};
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::mpsc::{self, Receiver, Sender, SyncSender};
use std::sync::{Arc, RwLock};
use std::thread;
use std::time::{Duration, Instant};

const MAX_WORKER_WALL: Duration = Duration::from_secs(1800);
const MCP_DELIVERY_GRACE: Duration = Duration::from_secs(10);
const MAX_PROXY_WAIT: Duration = Duration::from_secs(1810);

pub struct BrokerRequest {
    pub name: String,
    pub arguments: Value,
    pub prompt_epoch: u64,
    pub reply: Sender<Value>,
}

pub struct BrokerEndpoint {
    pub requests: Receiver<BrokerRequest>,
    stop: Arc<AtomicBool>,
    path: PathBuf,
    socket_identity: (u64, u64),
    prompt_epoch: Arc<AtomicU64>,
    catalog: Arc<RwLock<ToolCatalog>>,
}

impl BrokerEndpoint {
    pub fn activate_prompt(&self) {
        self.prompt_epoch.store(1, Ordering::SeqCst);
    }

    pub fn deactivate_prompt(&self) {
        self.prompt_epoch.store(0, Ordering::SeqCst);
    }

    pub fn replace_catalog(&self, catalog: ToolCatalog) -> Result<(), String> {
        *self
            .catalog
            .write()
            .map_err(|_| "MCP catalog lock poisoned")? = catalog;
        Ok(())
    }
}

impl Drop for BrokerEndpoint {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::SeqCst);
        if let Ok(meta) = fs::symlink_metadata(&self.path) {
            if meta.file_type().is_socket() && (meta.dev(), meta.ino()) == self.socket_identity {
                let _ = fs::remove_file(&self.path);
            }
        }
    }
}

#[derive(Clone, Default)]
pub struct ToolCatalog {
    pub birth_families: Vec<String>,
    pub application_families: Vec<String>,
    pub session_families: Vec<String>,
    pub applications: Vec<String>,
    pub api_applications: Vec<String>,
}

pub fn start_broker(
    path: &Path,
    worker_wall: Duration,
    catalog: ToolCatalog,
) -> Result<BrokerEndpoint, String> {
    if worker_wall.is_zero() || worker_wall > MAX_WORKER_WALL {
        return Err("MCP broker worker wall time must be 1..1800 seconds".into());
    }
    let response_timeout = worker_wall + MCP_DELIVERY_GRACE;
    let listener = UnixListener::bind(path).map_err(|e| format!("MCP broker bind: {e}"))?;
    fs::set_permissions(path, fs::Permissions::from_mode(0o600))
        .map_err(|e| format!("MCP broker mode: {e}"))?;
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    let socket_identity = (meta.dev(), meta.ino());
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let (tx, rx) = mpsc::sync_channel(8);
    let stop = Arc::new(AtomicBool::new(false));
    let active = Arc::new(AtomicUsize::new(0));
    let prompt_epoch = Arc::new(AtomicU64::new(0));
    let thread_stop = stop.clone();
    let thread_epoch = prompt_epoch.clone();
    let catalog = Arc::new(RwLock::new(catalog));
    let broker_catalog = catalog.clone();
    thread::spawn(move || {
        while !thread_stop.load(Ordering::SeqCst) {
            match listener.accept() {
                Ok((stream, _)) => {
                    if active.fetch_add(1, Ordering::SeqCst) >= 8 {
                        active.fetch_sub(1, Ordering::SeqCst);
                        continue;
                    }
                    let tx = tx.clone();
                    let active = active.clone();
                    let epoch = thread_epoch.clone();
                    let catalog = catalog.clone();
                    thread::spawn(move || {
                        serve_broker_connection(stream, tx, epoch, response_timeout, catalog);
                        active.fetch_sub(1, Ordering::SeqCst);
                    });
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    thread::sleep(Duration::from_millis(20))
                }
                Err(_) => break,
            }
        }
    });
    Ok(BrokerEndpoint {
        requests: rx,
        stop,
        path: path.to_path_buf(),
        socket_identity,
        prompt_epoch,
        catalog: broker_catalog,
    })
}

fn serve_broker_connection(
    mut stream: UnixStream,
    tx: SyncSender<BrokerRequest>,
    epoch: Arc<AtomicU64>,
    response_timeout: Duration,
    catalog: Arc<RwLock<ToolCatalog>>,
) {
    if stream
        .set_write_timeout(Some(Duration::from_secs(5)))
        .is_err()
    {
        return;
    }
    let mut line = String::new();
    if io::BufReader::new(
        DeadlineRead {
            stream: &mut stream,
            deadline: Instant::now() + Duration::from_secs(5),
        }
        .take(65_537),
    )
    .read_line(&mut line)
    .is_err()
        || line.is_empty()
        || line.len() > 65_536
        || !line.ends_with('\n')
    {
        return;
    }
    let Ok(req) = serde_json::from_str::<Value>(&line) else {
        return;
    };
    let Some(name) = req.get("name").and_then(Value::as_str) else {
        return;
    };
    // MCP initialization asks for this before the prompt epoch is active.
    // It carries only validated operator-selected names, never grant paths,
    // private policy bytes, resource IDs, or custody credentials.
    if name == "__catalog" && req.get("arguments") == Some(&json!({})) {
        let Ok(snapshot) = catalog.read() else {
            let _ = writeln!(
                stream,
                "{}",
                json!({"isError":true,"text":"MCP catalog unavailable"})
            );
            return;
        };
        let _ = writeln!(
            stream,
            "{}",
            json!({"type":"mini-grain-tool-catalog-v2",
                "birthFamilies":snapshot.birth_families,
                "applicationFamilies":snapshot.application_families,
                "sessionFamilies":snapshot.session_families,
                "applications":snapshot.applications,
                "apiApplications":snapshot.api_applications})
        );
        return;
    }
    let prompt_epoch = epoch.load(Ordering::SeqCst);
    let (reply_tx, reply_rx) = mpsc::channel();
    if tx
        .try_send(BrokerRequest {
            name: name.to_owned(),
            arguments: req.get("arguments").cloned().unwrap_or(Value::Null),
            prompt_epoch,
            reply: reply_tx,
        })
        .is_err()
    {
        let _ = writeln!(
            stream,
            "{}",
            json!({"isError":true,"text":"broker queue is full"})
        );
        return;
    }
    let response = reply_rx.recv_timeout(response_timeout).unwrap_or_else(|_| {
        json!({"isError":true,"text":"tool delivery timed out or reply was lost; outcome unknown"})
    });
    let _ = writeln!(stream, "{response}");
}

fn call_controller(path: &Path, name: &str, arguments: Value) -> Value {
    call_controller_with_timeout(path, name, arguments, MAX_PROXY_WAIT)
}

fn catalog_names(reply: &Value, field: &str, max: usize) -> Result<Vec<String>, String> {
    let names = reply
        .get(field)
        .and_then(Value::as_array)
        .ok_or_else(|| format!("controller MCP {field} absent"))?;
    if names.len() > max {
        return Err(format!("controller MCP {field} exceeds bound"));
    }
    let mut result = Vec::with_capacity(names.len());
    for value in names {
        let name = value.as_str().ok_or("MCP catalog entry is not a name")?;
        if name.is_empty()
            || name.len() > 64
            || !name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
            || result.iter().any(|prior| prior == name)
        {
            return Err(format!("controller MCP {field} has an invalid name"));
        }
        result.push(name.to_owned());
    }
    Ok(result)
}

fn catalog_from_reply(reply: &Value) -> Result<ToolCatalog, String> {
    if reply.get("type").and_then(Value::as_str) != Some("mini-grain-tool-catalog-v2") {
        return Err("controller MCP catalog unavailable".into());
    }
    let catalog = ToolCatalog {
        birth_families: catalog_names(reply, "birthFamilies", 8)?,
        application_families: catalog_names(reply, "applicationFamilies", 8)?,
        session_families: catalog_names(reply, "sessionFamilies", 8)?,
        applications: catalog_names(reply, "applications", 64)?,
        api_applications: catalog_names(reply, "apiApplications", 16)?,
    };
    if catalog
        .applications
        .iter()
        .chain(&catalog.api_applications)
        .any(|name| !name.ends_with("-app"))
    {
        return Err("controller MCP application selector is not a named app".into());
    }
    Ok(catalog)
}

fn tools_for_catalog(catalog: &ToolCatalog) -> Value {
    let mut tools = vec![
        json!({"name":"mini_grain_status","description":"Read the signed Mini task resource",
            "inputSchema":{"type":"object","properties":{}}}),
        json!({"name":"mini_read_resource","description":"Read one operator-named Mini resource with signed delegated observe authority",
            "inputSchema":{"type":"object","properties":{"name":{"type":"string"}},"required":["name"],"additionalProperties":false}}),
        json!({"name":"mini_publish","description":"Atomically settle a delegated grain allowance and publish Mini resource targets. Success returns a historical signed publication receipt; current content requires a fresh signed read.",
            "inputSchema":{"type":"object","properties":{"publications":{"type":"array","items":{"type":"object"}}},"required":["publications"]}}),
    ];
    if !catalog.birth_families.is_empty() {
        tools.push(json!({"name":"mini_create_resource",
            "description":"Create one resource in an operator-approved family through Mini's signed, budgeted composite birth. The family selects fixed factory, payer, tariff, policy and bounded ID namespace; the model supplies no IDs or capabilities. Success returns a historical birth receipt. Later reads and writes require fresh Mini admission.",
            "inputSchema":{"type":"object","properties":{"family":{"type":"string","enum":catalog.birth_families}},"required":["family"],"additionalProperties":false}}));
    }
    if !catalog.application_families.is_empty() {
        tools.push(json!({"name":"mini_create_application",
            "description":"Create one operator-approved application, package manifest, and snapshot manifest through Mini's signed, budgeted current-authority birth. The family fixes all target and capability namespaces; this returns a historical receipt, not a live use grant.",
            "inputSchema":{"type":"object","properties":{"family":{"type":"string","enum":catalog.application_families}},"required":["family"],"additionalProperties":false}}));
    }
    if !catalog.session_families.is_empty() {
        let description = if catalog.applications.is_empty() {
            "Name returned by a confirmed Mini application birth in this grain".to_owned()
        } else {
            format!("Name returned by a confirmed Mini application birth in this grain. Known names: {}", catalog.applications.join(", "))
        };
        // Hermes may cache its first tools/list for an ACP session. A dynamic
        // enum here would exclude apps created later in the same session.
        let application_selector = json!({"type":"string","maxLength":64,
            "pattern":"^[A-Za-z0-9-]+-app$","description":description});
        tools.push(json!({"name":"mini_create_application_session",
            "description":"Create a Mini-governed application session and descriptor for one named, already confirmed local application. Mini rechecks current authority and the app owner grant before birth; this receipt is not a dispatch permit.",
            "inputSchema":{"type":"object","properties":{
                "family":{"type":"string","enum":catalog.session_families},
                "application":application_selector},
                "required":["family","application"],"additionalProperties":false}}));
    }
    if !catalog.api_applications.is_empty() {
        tools.push(json!({"name":"mini_gitweb_read",
            "description":"Read one bounded UTF-8 file from a named Mini GitWeb app through fresh authorized Git smart-HTTP requests.",
            "inputSchema":{"type":"object","properties":{
                "application":{"type":"string","enum":catalog.api_applications},
                "path":{"type":"string","maxLength":256}},
                "required":["application","path"],"additionalProperties":false}}));
        tools.push(json!({"name":"mini_gitweb_edit",
            "description":"Edit a bounded text file, commit, push, and verify the remote ref in one named Mini GitWeb app. Every Git HTTP request receives a fresh Mini dispatch and settlement. An uncertain push is retained and never retried automatically.",
            "inputSchema":{"type":"object","properties":{
                "application":{"type":"string","enum":catalog.api_applications},
                "path":{"type":"string","maxLength":256},
                "content":{"type":"string","maxLength":8192},
                "message":{"type":"string","maxLength":256}},
                "required":["application","path","content","message"],
                "additionalProperties":false}}));
        tools.push(json!({"name":"mini_application_api",
            "description":"Call one operator-pinned resident application API session. A fresh Mini agent dispatch permit and separate purse settlement are required for every call. The model chooses only the named app and bounded ordinary HTTP input. Path is relative to the signed /repo.git/ API prefix (for example git-receive-pack or info/refs); do not include that prefix in the path.",
            "inputSchema":{"type":"object","properties":{
                "application":{"type":"string","enum":catalog.api_applications},
                "method":{"type":"string","enum":["GET","HEAD","POST","PUT","PATCH","DELETE"]},
                "path":{"type":"string","maxLength":8192},
                "query":{"type":"string","maxLength":8192},
                "headers":{"type":"array","maxItems":128,"items":{"type":"object","properties":{"name":{"type":"string"},"value":{"type":"string"}},"required":["name","value"],"additionalProperties":false}},
                "bodyHex":{"type":"string","maxLength":49152}},
                "required":["application","method","path","query","headers","bodyHex"],
                "additionalProperties":false}}));
    }
    json!({"tools":tools})
}

fn public_tool_name(name: &str) -> bool {
    !name.starts_with("__")
}

fn call_controller_with_timeout(
    path: &Path,
    name: &str,
    arguments: Value,
    response_timeout: Duration,
) -> Value {
    let result = (|| -> Result<Value, String> {
        let mut stream = UnixStream::connect(path).map_err(|e| e.to_string())?;
        stream
            .set_write_timeout(Some(Duration::from_secs(5)))
            .map_err(|e| e.to_string())?;
        writeln!(stream, "{}", json!({"name":name,"arguments":arguments}))
            .map_err(|e| e.to_string())?;
        let mut line = String::new();
        io::BufReader::new(DeadlineRead {
            stream: &mut stream,
            deadline: Instant::now() + response_timeout,
        })
        .take(16_777_217)
        .read_line(&mut line)
        .map_err(|e| e.to_string())?;
        if line.len() > 16_777_216 || !line.ends_with('\n') {
            return Err("controller reply exceeds 16 MiB".into());
        }
        serde_json::from_str(&line).map_err(|e| e.to_string())
    })();
    result.unwrap_or_else(|e| {
        json!({"isError":true,"text":format!("Mini tool delivery timed out or reply unavailable; outcome unknown: {e}")})
    })
}

struct DeadlineRead<'a> {
    stream: &'a mut UnixStream,
    deadline: Instant,
}

impl Read for DeadlineRead<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "MCP reply deadline exceeded",
            ));
        }
        self.stream.set_read_timeout(Some(remaining))?;
        self.stream.read(buf)
    }
}

pub fn serve_stdio(path: &Path) -> Result<(), String> {
    if !path.is_absolute() {
        return Err("MCP broker socket must be absolute".into());
    }
    let stdin = io::stdin();
    let mut input = stdin.lock();
    let mut stdout = io::stdout().lock();
    loop {
        let mut line = String::new();
        input
            .by_ref()
            .take(65_537)
            .read_line(&mut line)
            .map_err(|e| e.to_string())?;
        if line.is_empty() {
            break;
        }
        if line.len() > 65_536 || !line.ends_with('\n') {
            return Err("MCP frame exceeds 64 KiB".into());
        }
        let msg: Value = serde_json::from_str(&line).map_err(|e| e.to_string())?;
        let Some(id) = msg.get("id") else {
            continue;
        };
        let method = msg.get("method").and_then(Value::as_str).unwrap_or("");
        let result = match method {
            "initialize" => json!({"protocolVersion":msg.pointer("/params/protocolVersion")
                .and_then(Value::as_str).unwrap_or("2025-06-18"),
                "capabilities":{"tools":{}},
                "serverInfo":{"name":"mini-grain","version":"0.1.0"}}),
            "ping" => json!({}),
            "tools/list" => {
                let catalog = call_controller(path, "__catalog", json!({}));
                match catalog_from_reply(&catalog) {
                    Ok(catalog) => tools_for_catalog(&catalog),
                    Err(reason) => json!({"tools":[],"catalogError":reason}),
                }
            }
            "tools/call" => {
                let name = msg
                    .pointer("/params/name")
                    .and_then(Value::as_str)
                    .unwrap_or("");
                let arguments = msg
                    .pointer("/params/arguments")
                    .cloned()
                    .unwrap_or(Value::Null);
                let response = if !public_tool_name(name) {
                    json!({"isError":true,"text":"internal Mini broker operation is unavailable to MCP callers"})
                } else if matches!(name, "mini_gitweb_read" | "mini_gitweb_edit") {
                    let catalog = call_controller(path, "__catalog", json!({}));
                    match catalog_from_reply(&catalog).and_then(|catalog| {
                        let application = arguments
                            .get("application")
                            .and_then(Value::as_str)
                            .ok_or("GitWeb application selector absent")?;
                        if !catalog
                            .api_applications
                            .iter()
                            .any(|name| name == application)
                        {
                            return Err(
                                "GitWeb application is not in the current controller catalog"
                                    .into(),
                            );
                        }
                        let mut forward = |request| {
                            let result = call_controller(path, "__mini_gitweb_http_raw", request);
                            if result.get("isError").and_then(Value::as_bool) != Some(false) {
                                return Err(result
                                    .get("text")
                                    .and_then(Value::as_str)
                                    .unwrap_or("GitWeb HTTP outcome unavailable")
                                    .to_owned());
                            }
                            serde_json::from_str(
                                result
                                    .get("text")
                                    .and_then(Value::as_str)
                                    .ok_or("GitWeb HTTP response absent")?,
                            )
                            .map_err(|_| "GitWeb HTTP response malformed".to_owned())
                        };
                        if name == "mini_gitweb_read" {
                            crate::gitweb_worker::read(&arguments, &mut forward)
                        } else {
                            crate::gitweb_worker::edit(&arguments, &mut forward)
                        }
                    }) {
                        Ok(value) => json!({"isError":false,"text":value.to_string()}),
                        Err(error) => json!({"isError":true,"text":error}),
                    }
                } else {
                    call_controller(path, name, arguments)
                };
                json!({"content":[{"type":"text","text":response.get("text").and_then(Value::as_str).unwrap_or("tool returned no text")}],
                    "isError":response.get("isError").and_then(Value::as_bool).unwrap_or(true)})
            }
            _ => json!({"error":format!("unsupported MCP method {method}")}),
        };
        let response = json!({"jsonrpc":"2.0","id":id,"result":result});
        writeln!(stdout, "{response}")
            .and_then(|_| stdout.flush())
            .map_err(|e| e.to_string())?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;

    #[test]
    fn internal_broker_names_are_not_public_mcp_tools() {
        assert!(!public_tool_name("__mini_gitweb_http_raw"));
        assert!(!public_tool_name("__catalog"));
        assert!(public_tool_name("mini_gitweb_edit"));
        assert!(public_tool_name("mini_application_api"));
    }

    static NEXT_SOCKET: AtomicUsize = AtomicUsize::new(1);

    #[test]
    fn application_api_catalog_exposes_only_operator_selected_route_names() {
        let absent = tools_for_catalog(&ToolCatalog::default());
        assert!(absent["tools"]
            .as_array()
            .unwrap()
            .iter()
            .all(|tool| tool["name"] != "mini_application_api"));
        let listed = tools_for_catalog(&ToolCatalog {
            api_applications: vec!["workroom-app".into()],
            ..ToolCatalog::default()
        });
        let api = listed["tools"]
            .as_array()
            .unwrap()
            .iter()
            .find(|tool| tool["name"] == "mini_application_api")
            .unwrap();
        assert_eq!(
            api["inputSchema"]["properties"]["application"]["enum"],
            json!(["workroom-app"])
        );
        assert_eq!(api["inputSchema"]["additionalProperties"], false);
        assert!(api["inputSchema"]["properties"].get("ticket").is_none());
    }

    #[test]
    fn birth_catalog_lists_only_named_confirmed_routes_before_prompt() {
        let (mut client, broker) = UnixStream::pair().unwrap();
        let (tx, rx) = mpsc::sync_channel(1);
        let epoch = Arc::new(AtomicU64::new(0));
        let worker = thread::spawn(move || {
            serve_broker_connection(
                broker,
                tx,
                epoch,
                Duration::from_secs(1),
                Arc::new(RwLock::new(ToolCatalog {
                    birth_families: vec!["note".into()],
                    application_families: vec!["office".into()],
                    session_families: vec!["office-web".into()],
                    applications: vec!["office-0-app".into()],
                    api_applications: vec![],
                })),
            );
        });
        writeln!(client, "{}", json!({"name":"__catalog","arguments":{}})).unwrap();
        let mut reply = String::new();
        io::BufReader::new(&client).read_line(&mut reply).unwrap();
        worker.join().unwrap();
        assert!(rx.try_recv().is_err());
        let catalog = catalog_from_reply(&serde_json::from_str(&reply).unwrap()).unwrap();
        let tools = tools_for_catalog(&catalog);
        let birth = tools["tools"]
            .as_array()
            .unwrap()
            .iter()
            .find(|tool| tool["name"] == "mini_create_resource")
            .unwrap();
        assert_eq!(
            birth["inputSchema"]["properties"]["family"]["enum"],
            json!(["note"])
        );
        assert_eq!(birth["inputSchema"]["additionalProperties"], false);
        let application = tools["tools"]
            .as_array()
            .unwrap()
            .iter()
            .find(|tool| tool["name"] == "mini_create_application")
            .unwrap();
        assert_eq!(
            application["inputSchema"]["properties"]["family"]["enum"],
            json!(["office"])
        );
        let session = tools["tools"]
            .as_array()
            .unwrap()
            .iter()
            .find(|tool| tool["name"] == "mini_create_application_session")
            .unwrap();
        assert!(session["inputSchema"]["properties"]["application"]
            .get("enum")
            .is_none());
        assert!(
            session["inputSchema"]["properties"]["application"]["description"]
                .as_str()
                .unwrap()
                .contains("office-0-app")
        );
        assert!(tools_for_catalog(&ToolCatalog::default())["tools"]
            .as_array()
            .unwrap()
            .iter()
            .all(|tool| tool["name"] != "mini_create_resource"));
        let no_app = ToolCatalog {
            applications: vec![],
            ..catalog
        };
        let session_before_app = tools_for_catalog(&no_app)["tools"]
            .as_array()
            .unwrap()
            .iter()
            .find(|tool| tool["name"] == "mini_create_application_session")
            .unwrap()
            .clone();
        assert_eq!(
            session_before_app["inputSchema"]["properties"]["application"]["type"],
            "string"
        );
        assert!(
            session_before_app["inputSchema"]["properties"]["application"]
                .get("enum")
                .is_none()
        );
        assert!(
            catalog_from_reply(&json!({"type":"mini-grain-tool-catalog-v2",
            "birthFamilies":["note","note"],"applicationFamilies":[],
            "sessionFamilies":[],"applications":[]}))
            .is_err()
        );
        assert!(
            catalog_from_reply(&json!({"type":"mini-grain-tool-catalog-v2",
            "birthFamilies":[],"applicationFamilies":["office"],
            "sessionFamilies":["office-web"],"applications":["8401"]}))
            .is_err()
        );
    }

    #[test]
    fn same_broker_lists_new_confirmed_app_after_catalog_refresh() {
        let socket = std::env::temp_dir().join(format!(
            "mini-mcp-catalog-{}-{}",
            std::process::id(),
            NEXT_SOCKET.fetch_add(1, Ordering::SeqCst)
        ));
        let broker = start_broker(
            &socket,
            Duration::from_secs(1),
            ToolCatalog {
                application_families: vec!["office".into()],
                session_families: vec!["office-web".into()],
                ..ToolCatalog::default()
            },
        )
        .unwrap();
        let listed = || {
            let mut stream = UnixStream::connect(&socket).unwrap();
            writeln!(stream, "{}", json!({"name":"__catalog","arguments":{}})).unwrap();
            let mut reply = String::new();
            io::BufReader::new(&stream).read_line(&mut reply).unwrap();
            tools_for_catalog(&catalog_from_reply(&serde_json::from_str(&reply).unwrap()).unwrap())
        };
        let initial = listed();
        let session = initial["tools"]
            .as_array()
            .unwrap()
            .iter()
            .find(|tool| tool["name"] == "mini_create_application_session")
            .unwrap();
        assert!(session["inputSchema"]["properties"]["application"]
            .get("enum")
            .is_none());
        broker
            .replace_catalog(ToolCatalog {
                application_families: vec!["office".into()],
                session_families: vec!["office-web".into()],
                applications: vec!["office-0-app".into()],
                ..ToolCatalog::default()
            })
            .unwrap();
        let updated = listed();
        let session = updated["tools"]
            .as_array()
            .unwrap()
            .iter()
            .find(|tool| tool["name"] == "mini_create_application_session")
            .unwrap();
        assert!(session["inputSchema"]["properties"]["application"]
            .get("enum")
            .is_none());
        assert!(
            session["inputSchema"]["properties"]["application"]["description"]
                .as_str()
                .unwrap()
                .contains("office-0-app")
        );
        drop(broker);
        assert!(!socket.exists());
    }

    #[test]
    fn broker_deadline_reports_unknown_delivery_without_claiming_settlement() {
        let (mut client, broker) = UnixStream::pair().unwrap();
        client
            .set_read_timeout(Some(Duration::from_secs(1)))
            .unwrap();
        let (tx, rx) = mpsc::sync_channel(1);
        let epoch = Arc::new(AtomicU64::new(1));
        let worker = thread::spawn(move || {
            serve_broker_connection(
                broker,
                tx,
                epoch,
                Duration::from_millis(30),
                Arc::new(RwLock::new(ToolCatalog::default())),
            );
        });
        writeln!(client, "{}", json!({"name":"mini_publish","arguments":{}})).unwrap();
        let request = rx.recv_timeout(Duration::from_secs(1)).unwrap();
        assert_eq!(request.prompt_epoch, 1);
        let mut reply = String::new();
        io::BufReader::new(&client).read_line(&mut reply).unwrap();
        let value: Value = serde_json::from_str(&reply).unwrap();
        assert_eq!(value["isError"], true);
        assert!(value["text"].as_str().unwrap().contains("outcome unknown"));
        worker.join().unwrap();
        assert!(request.reply.send(json!({"isError":false})).is_err());
    }

    #[test]
    fn proxy_read_has_total_deadline_and_preserves_unknown_outcome() {
        let socket = std::env::temp_dir().join(format!(
            "mini-mcp-timeout-{}-{}",
            std::process::id(),
            NEXT_SOCKET.fetch_add(1, Ordering::SeqCst)
        ));
        let listener = UnixListener::bind(&socket).unwrap();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut request = String::new();
            io::BufReader::new(&stream).read_line(&mut request).unwrap();
            assert!(request.contains("mini_publish"));
            stream.write_all(b"{\"isError\":").unwrap();
            thread::sleep(Duration::from_millis(100));
        });
        let result = call_controller_with_timeout(
            &socket,
            "mini_publish",
            json!({}),
            Duration::from_millis(30),
        );
        assert_eq!(result["isError"], true);
        assert!(result["text"].as_str().unwrap().contains("outcome unknown"));
        server.join().unwrap();
        fs::remove_file(socket).unwrap();
    }
}
