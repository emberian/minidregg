use crate::{api_session_capnp, grain_capnp, identity_capnp, util_capnp, web_session_capnp};
use capnp::traits::HasTypeId;
use capnp_rpc::{rpc_twoparty_capnp, twoparty, RpcSystem};
use futures::AsyncReadExt;
use tokio::net::UnixStream;
use tokio_util::compat::TokioAsyncReadCompatExt;

/// Values placed on Sandstorm's wire after the Mini controller has admitted
/// this exact request. These values carry no authorization proof themselves.
#[derive(Clone, Debug)]
pub struct SessionParameters {
    pub identity_id: [u8; 32],
    pub display_name: String,
    pub preferred_handle: String,
    pub permissions: Vec<bool>,
    pub tab_id: Vec<u8>,
    pub base_path: String,
    pub user_agent: String,
    pub acceptable_languages: Vec<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ViewInfo {
    pub app_title: String,
    /// Stable wire indexes are their positions in this vector.
    pub permissions: Vec<PermissionDefinition>,
    /// Stable wire role IDs are their positions in this vector.
    pub roles: Vec<RoleDefinition>,
    /// Proxy UiView attenuation metadata, not an authorization decision.
    pub denied_permissions: Vec<bool>,
    /// Compatibility summary; use `permissions` for complete metadata.
    pub permission_names: Vec<String>,
    /// Compatibility summary; use `roles` for definitions/default bits.
    pub role_count: u32,
}

#[derive(Debug, PartialEq, Eq)]
pub struct LocalizedText {
    pub default_text: String,
    pub localizations: Vec<(String, String)>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct PermissionDefinition {
    pub name: String,
    pub title: LocalizedText,
    pub description: LocalizedText,
    pub obsolete: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct RoleDefinition {
    pub title: LocalizedText,
    pub verb_phrase: LocalizedText,
    pub description: LocalizedText,
    /// Raw PermissionSet bit list, whose wire length may differ from definitions.
    pub permissions: Vec<bool>,
    pub obsolete: bool,
    /// Legacy `RoleAssignment.none` may refer to a role with this flag.
    pub default: bool,
}

fn bounded_text(value: capnp::text::Reader<'_>, maximum: usize) -> capnp::Result<String> {
    let value = value.to_str()?;
    if value.len() > maximum {
        return Err(capnp::Error::failed("ViewInfo text exceeds bound".into()));
    }
    Ok(value.to_owned())
}

fn localized(value: util_capnp::localized_text::Reader<'_>) -> capnp::Result<LocalizedText> {
    let default_text = bounded_text(value.get_default_text()?, 4096)?;
    let entries = value.get_localizations()?;
    bounded_len(entries.len() as usize, 32, "localizations")?;
    let mut localizations = Vec::with_capacity(entries.len() as usize);
    for item in entries.iter() {
        localizations.push((
            bounded_text(item.get_locale()?, 128)?,
            bounded_text(item.get_text()?, 4096)?,
        ));
    }
    Ok(LocalizedText {
        default_text,
        localizations,
    })
}

#[derive(Debug, PartialEq, Eq)]
pub struct InlineResponse {
    pub status: u16,
    pub mime_type: String,
    pub body: Vec<u8>,
}

struct MinimalSandstormApi;
impl grain_capnp::sandstorm_api::Server<capnp::data::Owned> for MinimalSandstormApi {}

struct MinimalSessionContext;
impl grain_capnp::session_context::Server for MinimalSessionContext {}

struct ProfileIdentity {
    display_name: String,
    preferred_handle: String,
}
impl identity_capnp::identity::Server for ProfileIdentity {
    async fn get_profile(
        self: capnp::capability::Rc<Self>,
        _: identity_capnp::identity::GetProfileParams,
        mut results: identity_capnp::identity::GetProfileResults,
    ) -> capnp::Result<()> {
        let mut profile = results.get().init_profile();
        profile
            .reborrow()
            .init_display_name()
            .set_default_text(self.display_name.as_str());
        profile.set_preferred_handle(self.preferred_handle.as_str());
        Ok(())
    }
}

struct RejectingResponseStream;
impl crate::util_capnp::byte_stream::Server for RejectingResponseStream {}

fn reader_options() -> capnp::message::ReaderOptions {
    capnp::message::ReaderOptions {
        traversal_limit_in_words: Some(2 * 1024 * 1024), // 16 MiB traversal ceiling
        nesting_limit: 64,
    }
}

fn bounded_len(value: usize, maximum: usize, field: &str) -> capnp::Result<u32> {
    if value > maximum {
        return Err(capnp::Error::failed(format!(
            "{field} exceeds SPK RPC transport bound"
        )));
    }
    u32::try_from(value).map_err(|_| capnp::Error::failed(format!("{field} is too large")))
}

/// The supervisor side of one already-connected Sandstorm fd3 socketpair.
///
/// The caller must drive the returned RPC system on a Tokio LocalSet for as
/// long as the app is alive. The app's fd3 end runs as the two-party CLIENT;
/// this side is SERVER, exports SandstormApi, and bootstraps its UiView.
pub struct SupervisorConnection {
    view: grain_capnp::ui_view::Client,
}

impl SupervisorConnection {
    pub fn from_connected_stream(
        stream: UnixStream,
    ) -> (Self, RpcSystem<rpc_twoparty_capnp::Side>) {
        let (reader, writer) = stream.compat().split();
        let network = twoparty::VatNetwork::new(
            futures::io::BufReader::new(reader),
            futures::io::BufWriter::new(writer),
            rpc_twoparty_capnp::Side::Server,
            reader_options(),
        );
        let api: grain_capnp::sandstorm_api::Client<capnp::data::Owned> =
            capnp_rpc::new_client(MinimalSandstormApi);
        let mut rpc = RpcSystem::new(Box::new(network), Some(api.client));
        let view = rpc.bootstrap(rpc_twoparty_capnp::Side::Client);
        (Self { view }, rpc)
    }

    pub async fn get_view_info(&self) -> capnp::Result<ViewInfo> {
        let reply = self.view.get_view_info_request().send().promise.await?;
        let info = reply.get()?;
        let app_title = bounded_text(info.get_app_title()?.get_default_text()?, 4096)?;
        let raw_permissions = info.get_permissions()?;
        let raw_roles = info.get_roles()?;
        bounded_len(
            raw_permissions.len() as usize,
            4096,
            "permission definitions",
        )?;
        bounded_len(raw_roles.len() as usize, 4096, "role definitions")?;
        let mut names = std::collections::HashSet::new();
        let mut permissions = Vec::with_capacity(raw_permissions.len() as usize);
        for item in raw_permissions.iter() {
            let name = bounded_text(item.get_name()?, 256)?;
            if !name.starts_with(|c: char| c.is_ascii_alphabetic())
                || !name.chars().all(|c| c.is_ascii_alphanumeric())
                || !names.insert(name.clone())
            {
                return Err(capnp::Error::failed(
                    "invalid or duplicate permission name".into(),
                ));
            }
            permissions.push(PermissionDefinition {
                name,
                title: localized(item.get_title()?)?,
                description: localized(item.get_description()?)?,
                obsolete: item.get_obsolete(),
            });
        }
        let mut roles = Vec::with_capacity(raw_roles.len() as usize);
        let mut defaults = 0;
        for item in raw_roles.iter() {
            let bits = item.get_permissions()?;
            bounded_len(bits.len() as usize, 4096, "role permission bits")?;
            let default = item.get_default();
            if default {
                defaults += 1;
            }
            roles.push(RoleDefinition {
                title: localized(item.get_title()?)?,
                verb_phrase: localized(item.get_verb_phrase()?)?,
                description: localized(item.get_description()?)?,
                permissions: bits.iter().collect(),
                obsolete: item.get_obsolete(),
                default,
            });
        }
        if defaults > 1 {
            return Err(capnp::Error::failed(
                "multiple default roles are ambiguous".into(),
            ));
        }
        let denied = info.get_denied_permissions()?;
        bounded_len(denied.len() as usize, 4096, "denied permission bits")?;
        let permission_names = permissions.iter().map(|p| p.name.clone()).collect();
        Ok(ViewInfo {
            app_title,
            permissions,
            roles,
            denied_permissions: denied.iter().collect(),
            permission_names,
            role_count: raw_roles.len(),
        })
    }

    pub async fn new_web_session(
        &self,
        params: &SessionParameters,
    ) -> capnp::Result<web_session_capnp::web_session::Client> {
        self.new_session(params, false).await
    }

    pub async fn new_api_session(
        &self,
        params: &SessionParameters,
    ) -> capnp::Result<web_session_capnp::web_session::Client> {
        self.new_session(params, true).await
    }

    async fn new_session(
        &self,
        params: &SessionParameters,
        api: bool,
    ) -> capnp::Result<web_session_capnp::web_session::Client> {
        let permission_count = bounded_len(params.permissions.len(), 4096, "permissions")?;
        let language_count = bounded_len(params.acceptable_languages.len(), 32, "languages")?;
        bounded_len(params.display_name.len(), 1024, "display name")?;
        bounded_len(params.preferred_handle.len(), 256, "preferred handle")?;
        bounded_len(params.tab_id.len(), 256, "tab ID")?;
        bounded_len(params.base_path.len(), 8192, "base path")?;
        bounded_len(params.user_agent.len(), 4096, "user agent")?;
        for language in &params.acceptable_languages {
            bounded_len(language.len(), 256, "language")?;
        }
        let mut request = self.view.new_session_request();
        {
            let mut body = request.get();
            let mut user = body.reborrow().init_user_info();
            user.reborrow()
                .init_display_name()
                .set_default_text(params.display_name.as_str());
            user.set_preferred_handle(params.preferred_handle.as_str());
            user.set_identity_id(&params.identity_id);
            let identity: identity_capnp::identity::Client =
                capnp_rpc::new_client(ProfileIdentity {
                    display_name: params.display_name.clone(),
                    preferred_handle: params.preferred_handle.clone(),
                });
            user.set_identity(identity);
            let mut permissions = user.init_permissions(permission_count);
            for (index, allowed) in params.permissions.iter().enumerate() {
                permissions.set(index as u32, *allowed);
            }
            let context: grain_capnp::session_context::Client =
                capnp_rpc::new_client(MinimalSessionContext);
            body.set_context(context);
            body.set_tab_id(&params.tab_id);
            if api {
                body.set_session_type(api_session_capnp::api_session::Client::TYPE_ID);
                let _: api_session_capnp::api_session::params::Builder<'_> =
                    body.init_session_params().init_as();
            } else {
                body.set_session_type(web_session_capnp::web_session::Client::TYPE_ID);
                let mut web: web_session_capnp::web_session::params::Builder<'_> =
                    body.init_session_params().init_as();
                web.set_base_path(params.base_path.as_str());
                web.set_user_agent(params.user_agent.as_str());
                let mut languages = web.init_acceptable_languages(language_count);
                for (index, language) in params.acceptable_languages.iter().enumerate() {
                    languages.set(index as u32, language.as_str());
                }
            }
        }
        let reply = request.send().promise.await?;
        let session = reply.get()?.get_session()?;
        Ok(web_session_capnp::web_session::Client {
            client: session.client,
        })
    }

    /// A first typed WebSession operation. Streaming responses fail closed until
    /// the application body-stream adapter is connected to durable dispatch.
    pub async fn get_inline(
        session: &web_session_capnp::web_session::Client,
        path: &str,
        max_body_bytes: usize,
    ) -> capnp::Result<InlineResponse> {
        use web_session_capnp::web_session::response::{self, content};
        bounded_len(path.len(), 8192, "request path")?;
        let mut request = session.get_request();
        {
            let mut body = request.get();
            body.set_path(path);
            body.set_ignore_body(false);
            let mut context = body.init_context();
            let stream: crate::util_capnp::byte_stream::Client =
                capnp_rpc::new_client(RejectingResponseStream);
            context.set_response_stream(stream);
        }
        let reply = request.send().promise.await?;
        match reply
            .get()?
            .which()
            .map_err(|e| capnp::Error::failed(e.to_string()))?
        {
            response::Which::Content(value) => {
                let status = match value
                    .get_status_code()
                    .map_err(|e| capnp::Error::failed(e.to_string()))?
                {
                    response::SuccessCode::Ok => 200,
                    response::SuccessCode::Created => 201,
                    response::SuccessCode::Accepted => 202,
                    response::SuccessCode::NoContent => 204,
                    response::SuccessCode::PartialContent => 206,
                    response::SuccessCode::MultiStatus => 207,
                    response::SuccessCode::NotModified => 304,
                };
                let mime_type = value.get_mime_type()?.to_str()?.to_owned();
                let body = match value
                    .get_body()
                    .which()
                    .map_err(|e| capnp::Error::failed(e.to_string()))?
                {
                    content::body::Which::Bytes(bytes) => bytes?.to_vec(),
                    content::body::Which::Stream(_) => {
                        return Err(capnp::Error::unimplemented(
                            "streaming response body is not connected".into(),
                        ))
                    }
                };
                if body.len() > max_body_bytes {
                    return Err(capnp::Error::failed(
                        "app response exceeds caller bound".into(),
                    ));
                }
                Ok(InlineResponse {
                    status,
                    mime_type,
                    body,
                })
            }
            _ => Err(capnp::Error::unimplemented(
                "response variant is not mapped".into(),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use capnp_rpc::rpc_twoparty_capnp::Side;
    use std::{cell::RefCell, rc::Rc};

    #[derive(Default)]
    struct Observed {
        identity_id: Vec<u8>,
        permissions: Vec<bool>,
        session_type: u64,
        base_path: String,
        api_sessions: u32,
        identity_profile: String,
        paths: Vec<String>,
        posts: Vec<(String, Vec<u8>, String, String)>,
        view_fault: u8,
    }

    struct FakeApp(Rc<RefCell<Observed>>);
    impl grain_capnp::ui_view::Server for FakeApp {
        async fn get_view_info(
            self: capnp::capability::Rc<Self>,
            _: grain_capnp::ui_view::GetViewInfoParams,
            mut results: grain_capnp::ui_view::GetViewInfoResults,
        ) -> capnp::Result<()> {
            let mut info = results.get();
            info.reborrow()
                .init_app_title()
                .set_default_text("Actual app");
            let mut permissions = info.reborrow().init_permissions(2);
            let mut read = permissions.reborrow().get(0);
            read.set_name("read");
            read.reborrow().init_title().set_default_text("Read");
            read.reborrow()
                .init_description()
                .set_default_text("See tasks");
            let mut edit = permissions.reborrow().get(1);
            edit.set_name(if self.0.borrow().view_fault == 1 {
                "read"
            } else {
                "edit"
            });
            edit.set_obsolete(true);
            let mut title = edit.reborrow().init_title();
            title.set_default_text("Edit");
            let mut localized = title.init_localizations(1);
            localized.reborrow().get(0).set_locale("fr");
            localized.get(0).set_text("Modifier");
            edit.init_description().set_default_text("Change tasks");
            let mut roles = info.reborrow().init_roles(2);
            let mut viewer = roles.reborrow().get(0);
            viewer.reborrow().init_title().set_default_text("Viewer");
            viewer
                .reborrow()
                .init_verb_phrase()
                .set_default_text("can view");
            viewer
                .reborrow()
                .init_description()
                .set_default_text("Read only");
            viewer.set_default(true);
            viewer.init_permissions(2).set(0, true);
            let mut editor = roles.get(1);
            editor.reborrow().init_title().set_default_text("Editor");
            editor
                .reborrow()
                .init_verb_phrase()
                .set_default_text("can edit");
            editor
                .reborrow()
                .init_description()
                .set_default_text("Full task editing");
            editor.set_obsolete(true);
            if self.0.borrow().view_fault == 2 {
                editor.set_default(true);
            }
            let mut bits = editor.init_permissions(2);
            bits.set(0, true);
            bits.set(1, true);
            info.init_denied_permissions(2).set(1, true);
            Ok(())
        }

        async fn new_session(
            self: capnp::capability::Rc<Self>,
            params: grain_capnp::ui_view::NewSessionParams,
            mut results: grain_capnp::ui_view::NewSessionResults,
        ) -> capnp::Result<()> {
            let params = params.get()?;
            let user = params.get_user_info()?;
            let profile_reply = user
                .get_identity()?
                .get_profile_request()
                .send()
                .promise
                .await?;
            let profile_name = profile_reply
                .get()?
                .get_profile()?
                .get_display_name()?
                .get_default_text()?
                .to_str()?
                .to_owned();
            {
                let mut seen = self.0.borrow_mut();
                seen.identity_id = user.get_identity_id()?.to_vec();
                seen.permissions = user.get_permissions()?.iter().collect();
                seen.session_type = params.get_session_type();
                seen.identity_profile = profile_name;
                if seen.session_type == api_session_capnp::api_session::Client::TYPE_ID {
                    let _: api_session_capnp::api_session::params::Reader<'_> =
                        params.get_session_params().get_as()?;
                    seen.api_sessions += 1;
                } else {
                    let web: web_session_capnp::web_session::params::Reader<'_> =
                        params.get_session_params().get_as()?;
                    seen.base_path = web.get_base_path()?.to_str()?.to_owned();
                }
            }
            let web: web_session_capnp::web_session::Client =
                capnp_rpc::new_client(FakeWebSession(self.0.clone()));
            results
                .get()
                .set_session(grain_capnp::ui_session::Client { client: web.client });
            Ok(())
        }
    }
    impl grain_capnp::main_view::Server<capnp::data::Owned> for FakeApp {}

    struct FakeWebSession(Rc<RefCell<Observed>>);
    impl grain_capnp::ui_session::Server for FakeWebSession {}
    impl web_session_capnp::web_session::Server for FakeWebSession {
        async fn get(
            self: capnp::capability::Rc<Self>,
            params: web_session_capnp::web_session::GetParams,
            mut results: web_session_capnp::web_session::GetResults,
        ) -> capnp::Result<()> {
            let path = params.get()?.get_path()?.to_str()?.to_owned();
            if path == "stream" || path == "overflow" {
                let sink = params.get()?.get_context()?.get_response_stream()?;
                let bytes: &'static [u8] = if path == "overflow" {
                    b"too many bytes"
                } else {
                    b"streamed body"
                };
                tokio::task::spawn_local(async move {
                    let mut write = sink.write_request();
                    write.get().set_data(bytes);
                    write.send().await.unwrap();
                    let _ = sink.done_request().send().promise.await;
                });
                let mut content = results.get().init_content();
                content.set_status_code(web_session_capnp::web_session::response::SuccessCode::Ok);
                content.set_mime_type("text/plain");
                let handle: crate::util_capnp::handle::Client = capnp_rpc::new_client(FakeHandle);
                content.init_body().set_stream(handle);
                return Ok(());
            }
            self.0.borrow_mut().paths.push(path);
            let mut content = results.get().init_content();
            content.set_status_code(web_session_capnp::web_session::response::SuccessCode::Ok);
            content.set_mime_type("text/plain");
            content.init_body().set_bytes(b"from packaged app");
            Ok(())
        }

        async fn post(
            self: capnp::capability::Rc<Self>,
            params: web_session_capnp::web_session::PostParams,
            mut results: web_session_capnp::web_session::PostResults,
        ) -> capnp::Result<()> {
            let params = params.get()?;
            let context = params.get_context()?;
            let cookie = context.get_cookies()?.get(0);
            let header = context.get_additional_headers()?.get(0);
            let content = params.get_content()?;
            self.0.borrow_mut().posts.push((
                params.get_path()?.to_str()?.to_owned(),
                content.get_content()?.to_vec(),
                format!(
                    "{}={}",
                    cookie.get_key()?.to_str()?,
                    cookie.get_value()?.to_str()?
                ),
                format!(
                    "{}={}",
                    header.get_name()?.to_str()?,
                    header.get_value()?.to_str()?
                ),
            ));
            let mut response = results.get();
            let mut headers = response.reborrow().init_additional_headers(1);
            headers.reborrow().get(0).set_name("x-sandstorm-app-test");
            headers.get(0).set_value("kept");
            let mut content = response.init_content();
            content.set_status_code(web_session_capnp::web_session::response::SuccessCode::Created);
            content.set_mime_type("application/json");
            content.init_body().set_bytes(br#"{"ok":true}"#);
            Ok(())
        }

        async fn delete(
            self: capnp::capability::Rc<Self>,
            _: web_session_capnp::web_session::DeleteParams,
            mut results: web_session_capnp::web_session::DeleteResults,
        ) -> capnp::Result<()> {
            let mut err = results.get().init_client_error();
            err.set_status_code(
                web_session_capnp::web_session::response::ClientErrorCode::Forbidden,
            );
            err.set_description_html("<p>denied</p>");
            Ok(())
        }
    }

    struct FakeHandle;
    impl crate::util_capnp::handle::Server for FakeHandle {}

    #[tokio::test(flavor = "current_thread")]
    async fn two_party_fd3_bootstrap_session_and_web_get() {
        tokio::task::LocalSet::new()
            .run_until(async {
                let (host_fd, app_fd) = UnixStream::pair().unwrap();
                let observed = Rc::new(RefCell::new(Observed::default()));
                let main: grain_capnp::main_view::Client<capnp::data::Owned> =
                    capnp_rpc::new_client(FakeApp(observed.clone()));
                let (reader, writer) = app_fd.compat().split();
                let network = twoparty::VatNetwork::new(
                    futures::io::BufReader::new(reader),
                    futures::io::BufWriter::new(writer),
                    Side::Client,
                    reader_options(),
                );
                let mut app_rpc = RpcSystem::new(Box::new(network), Some(main.client));
                let api: grain_capnp::sandstorm_api::Client<capnp::data::Owned> =
                    app_rpc.bootstrap(Side::Server);
                let app_task = tokio::task::spawn_local(app_rpc);

                let (host, host_rpc) = SupervisorConnection::from_connected_stream(host_fd);
                let host_task = tokio::task::spawn_local(host_rpc);
                assert!(api
                    .deprecated_publish_request()
                    .send()
                    .promise
                    .await
                    .is_err());

                let info = host.get_view_info().await.unwrap();
                assert_eq!(info.app_title, "Actual app");
                assert_eq!(info.permission_names, ["read", "edit"]);
                assert_eq!(info.role_count, 2);
                assert_eq!(info.denied_permissions, [false, true]);
                assert_eq!(info.permissions[1].title.localizations, [("fr".into(), "Modifier".into())]);
                assert!(info.permissions[1].obsolete);
                assert_eq!(info.roles[0].permissions, [true, false]);
                assert!(info.roles[0].default);
                assert_eq!(info.roles[1].permissions, [true, true]);
                assert!(info.roles[1].obsolete);
                let source = crate::permission_schema_source_bytes(&info, 7).unwrap();
                let value: serde_json::Value = serde_json::from_slice(&source).unwrap();
                assert_eq!(value["version"], "7");
                assert_eq!(value["permissions"][0]["name"], "read");
                assert_eq!(value["permissions"][1]["obsolete"], true);
                assert_eq!(value["roles"][0]["permissions"], serde_json::json!([true, false]));
                assert_eq!(value["roles"][0]["default"], true);
                assert_eq!(value["denied"], serde_json::json!([false, true]));
                let pinned_source: serde_json::Value = serde_json::from_str(include_str!(
                    "../tests/fixtures/permission-schema-source-v1.json"
                ))
                .unwrap();
                assert_eq!(value, pinned_source);
                observed.borrow_mut().view_fault = 1;
                assert!(host.get_view_info().await.is_err());
                observed.borrow_mut().view_fault = 2;
                assert!(host.get_view_info().await.is_err());
                observed.borrow_mut().view_fault = 0;

                let params = SessionParameters {
                    identity_id: [7; 32],
                    display_name: "Ada".into(),
                    preferred_handle: "ada".into(),
                    permissions: vec![true, false],
                    tab_id: vec![9, 8, 7],
                    base_path: "https://grain.example/i/test".into(),
                    user_agent: "Mini test".into(),
                    acceptable_languages: vec!["en".into()],
                };
                let session = host.new_web_session(&params).await.unwrap();
                let response = SupervisorConnection::get_inline(&session, "todos", 1024)
                    .await
                    .unwrap();
                assert_eq!(response.status, 200);
                assert_eq!(response.mime_type, "text/plain");
                assert_eq!(response.body, b"from packaged app");
                {
                    let seen = observed.borrow();
                    assert_eq!(seen.identity_id, vec![7; 32]);
                    assert_eq!(seen.permissions, [true, false]);
                    assert_eq!(
                        seen.session_type,
                        web_session_capnp::web_session::Client::TYPE_ID
                    );
                    assert_eq!(seen.base_path, "https://grain.example/i/test");
                    assert_eq!(seen.identity_profile, "Ada");
                    assert_eq!(seen.paths, ["todos"]);
                }
                let api_session = host.new_api_session(&params).await.unwrap();
                let api_response =
                    SupervisorConnection::get_inline(&api_session, "api/todos", 1024)
                        .await
                        .unwrap();
                assert_eq!(api_response.body, b"from packaged app");
                {
                    let seen = observed.borrow();
                    assert_eq!(seen.api_sessions, 1);
                    assert_eq!(
                        seen.session_type,
                        api_session_capnp::api_session::Client::TYPE_ID
                    );
                    assert_eq!(seen.paths, ["todos", "api/todos"]);
                }
                use crate::web::{dispatch_web, Body, Cookie, Header, Method, RequestContext, WebRequest, WebResult};
                use std::time::Duration;
                let post = WebRequest {
                    method: Method::Post,
                    path_and_query: "todos?from=app%20view&n=2".into(),
                    context: RequestContext {
                        cookies: vec![Cookie { name: "session".into(), value: "abc".into() }],
                        additional_headers: vec![Header { name: "x-sandstorm-app-test".into(), value: "yes".into() }],
                        ..Default::default()
                    },
                    body: Some(Body { mime_type: "application/json".into(), encoding: String::new(), bytes: br#"{"task":"write"}"#.to_vec() }),
                };
                let reply = dispatch_web(&session, &post, 1024, Duration::from_secs(5)).await.unwrap();
                assert_eq!(reply.headers, [Header { name: "x-sandstorm-app-test".into(), value: "kept".into() }]);
                assert!(matches!(reply.result, WebResult::Content { status: 201, body, .. } if body == br#"{"ok":true}"#));
                assert_eq!(observed.borrow().posts, [("todos?from=app%20view&n=2".into(), br#"{"task":"write"}"#.to_vec(), "session=abc".into(), "x-sandstorm-app-test=yes".into())]);
                let delete = WebRequest { method: Method::Delete, path_and_query: "todos/1".into(), context: RequestContext::default(), body: None };
                let reply = dispatch_web(&session, &delete, 1024, Duration::from_secs(5)).await.unwrap();
                assert!(matches!(reply.result, WebResult::ClientError { status: 403, html, .. } if html == "<p>denied</p>"));
                let get = |path: &str| WebRequest { method: Method::Get, path_and_query: path.into(), context: RequestContext::default(), body: None };
                let reply = dispatch_web(&session, &get("stream"), 64, Duration::from_secs(5)).await.unwrap();
                assert!(matches!(reply.result, WebResult::Content { body, .. } if body == b"streamed body"));
                assert!(dispatch_web(&session, &get("overflow"), 4, Duration::from_secs(5)).await.is_err());
                let mut forbidden = post.clone();
                forbidden.context.additional_headers[0].name = "authorization".into();
                assert!(dispatch_web(&session, &forbidden, 1024, Duration::from_secs(5)).await.is_err());
                host_task.abort();
                app_task.abort();
            })
            .await;
    }
}
