//! Shell access to declaration schemas and the SAME native controller tools as Hermes.
use crate::{Args, Result};
use mini_sdk::app_interface::Declaration;
use serde_json::{json, Value};
use std::path::{Path, PathBuf};
use std::process::Command;

fn read(path: &Path) -> Result<Vec<u8>> {
    let meta = std::fs::symlink_metadata(path).map_err(|e| format!("interface file: {e}"))?;
    if !meta.is_file() || meta.len() > 4 * 1024 * 1024 {
        return Err("interface-file-bound".into());
    }
    std::fs::read(path).map_err(|e| e.to_string())
}
fn value(path: &Path) -> Result<Value> {
    serde_json::from_slice(&read(path)?).map_err(|e| e.to_string())
}
pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args.required("action")?;
    let declaration = PathBuf::from(args.required("declaration")?);
    let d = Declaration::load(&read(&declaration)?).map_err(|e| e.to_string())?;
    match action.to_str() {
        Some("tools") => {
            args.finish()?;
            crate::print_json(&json!(d.tools().map_err(|e| e.to_string())?))
        }
        Some("prepare") => {
            let op = args.required("operation")?.to_string_lossy().into_owned();
            let input = value(&PathBuf::from(args.required("args")?))?;
            let context = args
                .optional("context")
                .map(PathBuf::from)
                .map(|p| value(&p))
                .transpose()?
                .unwrap_or(json!({}));
            args.finish()?;
            let p = d
                .prepare(&op, &input, &context)
                .map_err(|e| e.to_string())?;
            crate::print_json(
                &json!({"method":p.method,"path":p.path,"query":p.query,"headers":p.ordered_headers.iter().map(|(k,v)|json!({"name":k,"value":v})).collect::<Vec<_>>(),"bodyHex":mini_sdk::hex::encode(&p.body),"packageId":p.package_id,"interfaceSha256":p.declaration_sha256,"operation":p.operation}),
            )
        }
        Some("call" | "qualify") => {
            let qualification = action == "qualify";
            let op = if qualification {
                "qualify".to_owned()
            } else {
                args.required("operation")?.to_string_lossy().into_owned()
            };
            let input = value(&PathBuf::from(args.required("args")?))?;
            let tool = args.required("tool")?.to_string_lossy().into_owned();
            let alias = args.required("attachment")?.to_string_lossy().into_owned();
            let expected = if qualification {
                mini_sdk::app_interface::qualification_tool_name(&alias)
            } else {
                mini_sdk::app_interface::bound_tool_name(&alias, &op)
            }
            .map_err(|e| e.to_string())?;
            if tool != expected {
                return Err("typed-tool-operation-mismatch".into());
            }
            let runtime = PathBuf::from(args.required("runtime")?);
            let socket = PathBuf::from(args.required("controller-socket")?);
            let attempt = PathBuf::from(args.required("dir")?);
            args.finish()?;
            // Schema validation without executing preparations or exposing tokens.
            let spec = if qualification {
                json!({"nativeQualification":true})
            } else {
                d.validate_input(&op, &input).map_err(|e| e.to_string())?;
                d.tools()
                    .map_err(|e| e.to_string())?
                    .into_iter()
                    .find(|v| v["operation"] == op)
                    .ok_or("operation-unknown-or-internal")?
            };
            if !runtime.is_absolute() || !socket.is_absolute() || !attempt.is_absolute() {
                return Err("call paths must be absolute".into());
            }
            if tool.is_empty() || !tool.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
                return Err("typed-tool-name-invalid".into());
            }
            std::fs::create_dir(&attempt)
                .map_err(|e| format!("new interface attempt required: {e}"))?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                std::fs::set_permissions(&attempt, std::fs::Permissions::from_mode(0o700))
                    .map_err(|e| e.to_string())?;
            }
            let id =
                mini_sdk::hex::encode(&mini_sdk::random::bytes::<16>().map_err(|e| e.to_string())?);
            let input_path = attempt.join("arguments.json");
            let mut input = if qualification {
                json!({"context":input})
            } else {
                input
            };
            input
                .as_object_mut()
                .ok_or("input-schema")?
                .insert("_miniInterfaceDigest".into(), json!(d.sha256));
            crate::create_private(
                &input_path,
                &serde_json::to_vec(&input).map_err(|e| e.to_string())?,
            )?;
            crate::create_private(&attempt.join("request.json"),&serde_json::to_vec(&json!({"requestId":id,"controllerSocket":socket,"runtime":runtime,"tool":tool,"operation":op,"packageId":d.package_id,"interfaceSha256":d.sha256,"toolSchema":spec})).map_err(|e|e.to_string())?)?;
            let output = Command::new(&runtime)
                .arg("tool")
                .arg(&socket)
                .arg("hard")
                .arg(&id)
                .arg(&tool)
                .arg(&input_path)
                .output()
                .map_err(|e| format!("controller tool spawn: {e}; retained request {id}"))?;
            crate::create_private(&attempt.join("controller-stdout.json"), &output.stdout)?;
            crate::create_private(&attempt.join("controller-stderr.txt"), &output.stderr)?;
            // Never reissue on lost reply. The retained ID is the recovery identity.
            if output.stdout.is_empty() {
                return Err(format!(
                    "dispatch-uncertain: inspect with {} tool-result {} {}; attempt {}",
                    runtime.display(),
                    socket.display(),
                    id,
                    attempt.display()
                ));
            }
            let reply: Value = serde_json::from_slice(&output.stdout).map_err(|_| {
                format!(
                    "dispatch-uncertain: controller reply retained in {}",
                    attempt.display()
                )
            })?;
            crate::print_json(&json!({"requestId":id,"attempt":attempt,"controllerResult":reply}))?;
            if output.status.success() {
                Ok(())
            } else {
                Err(format!(
                    "typed-call-refused-or-uncertain: native result retained in {}",
                    attempt.display()
                ))
            }
        }
        _ => Err("app-interface --action must be tools, prepare, call or qualify".into()),
    }
}
