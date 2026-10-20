//! User MCP server management, ported from `core/mcp/mcp-command.ts`. The
//! global `mcpServers` setting is read and written through the settings
//! manager.

use std::collections::{BTreeMap, HashMap};
use std::path::Path;

use anyhow::{bail, Context, Result};

use crate::config::get_agent_dir;
use eukhe_core::auth::AuthStorageBackend;
use eukhe_core::mcp::{parse_user_servers, EnvRef, McpServerConfig, McpServerDiagnostic};
use eukhe_core::settings::SettingsManager;

/// Built-in MCP integrations that reserve their server name
/// (`BUILTIN_MCP_CATALOG` in packages/ai/src/mcp/catalog.ts).
pub const BUILTIN_MCP_CATALOG: &[&str] = &["linear", "notion"];

const NAME_PATTERN: fn(&str) -> bool = is_valid_server_name;

fn is_valid_server_name(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) if first.is_ascii_alphanumeric() => {}
        _ => return false,
    }
    let rest = chars.count();
    rest <= 63
        && name[1..]
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
}

fn is_valid_env_name(value: &str) -> bool {
    let mut chars = value.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Drop the `mcp:<name>` credential from auth.json under the auth storage
/// lock, mirroring `AuthStorage.removeVerified`: the TS product serializes the
/// current document and writes it back inside `withLock`, so a concurrent TS
/// credential refresh and a Rust credential drop never race on the file.
fn drop_server_credentials(agent_dir: &Path, name: &str) -> Result<()> {
    if BUILTIN_MCP_CATALOG.contains(&name) {
        return Ok(());
    }
    let backend = eukhe_core::auth::FileAuthStorageBackend::new(agent_dir.join("auth.json"));
    backend
        .with_lock(&mut |current| {
            let mut auth: serde_json::Value =
                serde_json::from_str(current.as_deref().unwrap_or("{}"))
                    .context("parsing auth.json")?;
            let Some(object) = auth.as_object_mut() else {
                bail!("auth.json must contain a JSON object");
            };
            if object.remove(&format!("mcp:{name}")).is_none() {
                return Ok(((), None));
            }
            Ok((
                (),
                Some(serde_json::to_string_pretty(&auth).context("serializing auth.json")?),
            ))
        })
        .context("updating auth.json")?;
    Ok(())
}

/// Run an `mcp <add|list|get|remove>` command; the returned message is printed
/// by the caller, and errors are printed as `Error: <message>` with exit 1.
pub fn run_mcp_management_command(args: &[String]) -> Result<String> {
    let cwd = std::env::current_dir().context("resolving the current directory")?;
    run_mcp_command(args, &cwd, &get_agent_dir())
}

/// [`run_mcp_management_command`] over the settings of `cwd` and
/// `agent_dir`.
fn run_mcp_command(args: &[String], cwd: &Path, agent_dir: &Path) -> Result<String> {
    let action = args.first().map(String::as_str).unwrap_or_default();
    match action {
        "list" => {
            require_count(args, 1, "mcp list")?;
            let settings = SettingsManager::create(cwd, agent_dir);
            let (servers, diagnostics) = global_mcp_servers(&settings, agent_dir)?;
            Ok(format_mcp_server_list(&servers, &diagnostics))
        }
        "get" => {
            require_count(args, 2, "mcp get <name>")?;
            let name = validate_name(&args[1])?;
            let settings = SettingsManager::create(cwd, agent_dir);
            let (servers, diagnostics) = global_mcp_servers(&settings, agent_dir)?;
            if let Some(config) = servers.get(name) {
                return Ok(format!("{name}: {}", config.server_type()));
            }
            if let Some(diagnostic) = diagnostics.iter().find(|entry| entry.name == name) {
                bail!("{diagnostic}");
            }
            bail!("MCP server \"{name}\" was not found.");
        }
        "remove" => {
            require_count(args, 2, "mcp remove <name>")?;
            let name = validate_name(&args[1])?;
            let mut settings = SettingsManager::create(cwd, agent_dir);
            if let Some(error) = settings.global_load_error() {
                bail!("{}: {error}", agent_dir.join("settings.json").display());
            }
            if !settings.remove_global_mcp_server(name)? {
                bail!("MCP server \"{name}\" was not found.");
            }
            drop_server_credentials(agent_dir, name)?;
            Ok(format!("Removed MCP server \"{name}\"."))
        }
        "add" => {
            let (name, config, force) = parse_mcp_add_args(&args[1..])?;
            let mut settings = SettingsManager::create(cwd, agent_dir);
            let (servers, diagnostics) = global_mcp_servers(&settings, agent_dir)?;
            let replaced = servers.contains_key(name)
                || diagnostics.iter().any(|diagnostic| diagnostic.name == name);
            if replaced && !force {
                bail!("MCP server \"{name}\" already exists. Use --force to replace it.");
            }
            drop_server_credentials(agent_dir, name)?;
            settings.set_global_mcp_server(name, &serde_json::to_value(&config)?)?;
            Ok(format!(
                "{} MCP server \"{name}\".",
                if replaced { "Replaced" } else { "Added" }
            ))
        }
        _ => bail!("Usage: mcp <add|list|get|remove>."),
    }
}

/// The global `mcpServers` entries: each good one, and one diagnostic for
/// each one that does not parse.
///
/// # Errors
///
/// The global settings.json cannot be read or parsed, or its `mcpServers`
/// is not a JSON object.
fn global_mcp_servers(
    settings: &SettingsManager,
    agent_dir: &Path,
) -> Result<(HashMap<String, McpServerConfig>, Vec<McpServerDiagnostic>)> {
    let path = agent_dir.join("settings.json");
    if let Some(error) = settings.global_load_error() {
        bail!("{}: {error}", path.display());
    }
    match settings.global_raw().and_then(|raw| raw.get("mcpServers")) {
        None | Some(serde_json::Value::Null) => Ok((HashMap::new(), Vec::new())),
        Some(serde_json::Value::Object(servers)) => Ok(parse_user_servers(servers)),
        Some(
            serde_json::Value::Bool(_)
            | serde_json::Value::Number(_)
            | serde_json::Value::String(_)
            | serde_json::Value::Array(_),
        ) => bail!(
            "{}: the mcpServers setting must be a JSON object",
            path.display()
        ),
    }
}

/// One line per server, by name: the type of each good entry, and the
/// parse error of each entry that does not parse.
fn format_mcp_server_list(
    servers: &HashMap<String, McpServerConfig>,
    diagnostics: &[McpServerDiagnostic],
) -> String {
    let mut lines: BTreeMap<&str, String> = servers
        .iter()
        .map(|(name, config)| (name.as_str(), format!("{name}: {}", config.server_type())))
        .collect();
    lines.extend(diagnostics.iter().map(|diagnostic| {
        (
            diagnostic.name.as_str(),
            format!("{}: invalid entry ({})", diagnostic.name, diagnostic.error),
        )
    }));
    if lines.is_empty() {
        return "No user-configured MCP servers.".to_string();
    }
    lines.into_values().collect::<Vec<_>>().join("\n")
}

fn require_count(args: &[String], count: usize, usage: &str) -> Result<()> {
    if args.len() != count {
        bail!("Usage: {usage}");
    }
    Ok(())
}

fn validate_name(name: &str) -> Result<&str> {
    if NAME_PATTERN(name) {
        Ok(name)
    } else {
        bail!("MCP server names must be 1-64 letters, numbers, underscores, or hyphens and start with a letter or number.")
    }
}

fn parse_mcp_add_args(args: &[String]) -> Result<(&str, McpServerConfig, bool)> {
    let name = validate_name(args.first().map_or("", String::as_str))?;
    if BUILTIN_MCP_CATALOG.contains(&name) {
        bail!("MCP server name \"{name}\" is reserved for a built-in integration.");
    }
    let separator = args.iter().position(|arg| arg == "--");
    let option_args = &args[1..separator.unwrap_or(args.len())];
    let command_args: &[String] = separator.map_or(&[], |sep| &args[sep + 1..]);
    let mut url: Option<String> = None;
    let mut bearer_token_env_var: Option<String> = None;
    let mut oauth = false;
    let mut force = false;
    let mut cwd: Option<String> = None;
    let mut env: HashMap<String, EnvRef> = HashMap::new();
    let mut seen_options: Vec<&str> = Vec::new();

    let mut index = 0;
    while index < option_args.len() {
        let option = option_args[index].as_str();
        if option != "--env" && seen_options.contains(&option) {
            bail!("Duplicate MCP add option: {option}");
        }
        seen_options.push(option);
        if option == "--oauth" || option == "--force" {
            if option == "--oauth" {
                oauth = true;
            } else {
                force = true;
            }
            index += 1;
            continue;
        }
        if option != "--url"
            && option != "--bearer-token-env-var"
            && option != "--cwd"
            && option != "--env"
        {
            bail!("Unknown MCP add option: {option}");
        }
        let Some(value) = option_args.get(index + 1).filter(|v| !v.is_empty()) else {
            bail!("{option} requires a value.");
        };
        match option {
            "--url" => url = Some(value.clone()),
            "--bearer-token-env-var" => {
                bearer_token_env_var = Some(validate_env_name(value, option)?);
            }
            "--cwd" => cwd = Some(value.clone()),
            _ => {
                let equals = value.find('=').filter(|&e| e > 0 && e < value.len() - 1);
                let Some(equals) = equals else {
                    bail!("--env must use CHILD=SOURCE, where both sides are environment variable names.");
                };
                let child = validate_env_name(&value[..equals], "--env child")?;
                let source = validate_env_name(&value[equals + 1..], "--env source")?;
                if env.contains_key(child.as_str()) {
                    bail!("Duplicate child environment variable: {child}");
                }
                env.insert(child, EnvRef { env: Some(source) });
            }
        }
        index += 2;
    }

    if separator.is_some() {
        if url.is_some() || bearer_token_env_var.is_some() || oauth {
            bail!("Stdio MCP servers cannot use HTTP options.");
        }
        let command = command_args.first().filter(|c| !c.trim().is_empty());
        let Some(command) = command else {
            bail!("A command is required after --.");
        };
        return Ok((
            name,
            McpServerConfig::Stdio {
                command: command.clone(),
                args: (!command_args[1..].is_empty()).then(|| command_args[1..].to_vec()),
                cwd,
                env: (!env.is_empty()).then_some(env),
                enabled: None,
                enabled_tools: None,
                disabled_tools: None,
                startup_timeout_ms: None,
                call_timeout_ms: None,
            },
            force,
        ));
    }

    if cwd.is_some() || !env.is_empty() {
        bail!("--cwd and --env require a stdio command after --.");
    }
    let Some(url) = url else {
        bail!("Use --url <url> for HTTP or -- <command> [args...] for stdio.");
    };
    if bearer_token_env_var.is_some() && oauth {
        bail!("--oauth and --bearer-token-env-var cannot be combined.");
    }
    Ok((
        name,
        McpServerConfig::Http {
            url: validate_http_url(&url)?,
            headers: None,
            bearer_token_env_var,
            oauth: oauth.then_some(true),
            enabled: None,
            enabled_tools: None,
            disabled_tools: None,
            startup_timeout_ms: None,
            call_timeout_ms: None,
        },
        force,
    ))
}

fn validate_env_name(value: &str, option: &str) -> Result<String> {
    if is_valid_env_name(value) {
        Ok(value.to_string())
    } else {
        bail!("{option} requires an environment variable name.")
    }
}

fn validate_http_url(value: &str) -> Result<String> {
    // WHATWG-style checks matching `new URL(value)` in the TS product:
    // - no scheme, or an empty host after skipping extra slashes, fails to parse
    //   ("Invalid MCP URL: <value>");
    // - a parsed URL with a non-http(s) protocol, no hostname, or embedded
    //   credentials is rejected by the http(s) requirement instead.
    let Some((scheme, rest)) = split_scheme(value) else {
        bail!("Invalid MCP URL: {value}");
    };
    if !matches!(scheme, "http" | "https") {
        bail!("MCP URL must be an http(s) URL without embedded credentials.");
    }
    // The parser skips any extra slashes and backslashes after the scheme.
    let after_authority = rest
        .trim_start_matches(['/', '\\'])
        .split(['/', '?', '#'])
        .next()
        .unwrap_or("");
    let host = after_authority.rsplit('@').next().unwrap_or("");
    let host = host.split(':').next().unwrap_or("");
    if after_authority
        .rsplit_once('@')
        .is_some_and(|(user, _)| user.is_empty())
    {
        // `user@host` and `:pw@host` both carry credentials.
        bail!("MCP URL must be an http(s) URL without embedded credentials.");
    }
    if host.is_empty() {
        bail!("Invalid MCP URL: {value}");
    }
    if after_authority.contains('@') {
        bail!("MCP URL must be an http(s) URL without embedded credentials.");
    }
    // Normalize the way `url.toString()` does: lowercase scheme and host,
    // default path to "/".
    let authority = after_authority;
    let host_lower = authority.to_ascii_lowercase();
    let path = &rest[rest.find(authority).unwrap_or(0) + authority.len()..];
    let path = if path.is_empty() || path.starts_with('?') || path.starts_with('#') {
        format!("/{path}")
    } else {
        path.to_string()
    };
    Ok(format!("{scheme}://{host_lower}{path}"))
}

fn split_scheme(value: &str) -> Option<(&str, &str)> {
    let (scheme, rest) = value.split_once(':')?;
    if scheme.is_empty()
        || !scheme
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic())
    {
        return None;
    }
    if !scheme
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || c == '+' || c == '-' || c == '.')
    {
        return None;
    }
    Some((scheme, rest))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(ToString::to_string).collect()
    }

    /// A temp agent dir holding `settings` as its settings.json, and a
    /// project dir beside it.
    fn layout(settings: &str) -> (tempfile::TempDir, std::path::PathBuf, std::path::PathBuf) {
        let root = tempfile::tempdir().unwrap();
        let cwd = root.path().join("project");
        let agent_dir = root.path().join("agent");
        std::fs::create_dir_all(&cwd).unwrap();
        std::fs::create_dir_all(&agent_dir).unwrap();
        std::fs::write(agent_dir.join("settings.json"), settings).unwrap();
        (root, cwd, agent_dir)
    }

    /// `mcp add` builds the one `McpServerConfig` and writes its wire shape.
    #[test]
    fn add_args_build_the_settings_entry() {
        let args = strings(&["y", "--url", "https://example.com/mcp", "--oauth"]);
        let (name, config, force) = parse_mcp_add_args(&args).unwrap();
        assert_eq!(
            (name, serde_json::to_value(&config).unwrap(), force),
            (
                "y",
                serde_json::json!({"type": "http", "url": "https://example.com/mcp", "oauth": true}),
                false
            )
        );
        let args = strings(&["s", "--env", "A=B", "--", "run", "x"]);
        let (_, config, _) = parse_mcp_add_args(&args).unwrap();
        assert_eq!(
            serde_json::to_value(&config).unwrap(),
            serde_json::json!({
                "type": "stdio",
                "command": "run",
                "args": ["x"],
                "env": {"A": {"env": "B"}},
            })
        );
    }

    /// A settings.json that does not parse: `mcp add` fails and the file
    /// keeps every byte; `mcp list` fails too.
    #[test]
    fn add_refuses_a_settings_file_that_does_not_parse() {
        let content = "{\"theme\": \"x\",}";
        let (_root, cwd, agent_dir) = layout(content);
        let add = strings(&["add", "x", "--url", "https://e/mcp"]);
        assert!(run_mcp_command(&add, &cwd, &agent_dir).is_err());
        assert_eq!(
            std::fs::read_to_string(agent_dir.join("settings.json")).unwrap(),
            content
        );
        assert!(run_mcp_command(&strings(&["list"]), &cwd, &agent_dir).is_err());
        assert_eq!(
            std::fs::read_to_string(agent_dir.join("settings.json")).unwrap(),
            content
        );
    }

    /// One bad entry beside a good one: `mcp list` shows both, the bad one
    /// with its parse error.
    #[test]
    fn list_shows_good_servers_and_each_bad_entry() {
        let (_root, cwd, agent_dir) = layout(
            r#"{"mcpServers": {"good": {"type": "stdio", "command": "x"}, "bad": {"type": "http"}}}"#,
        );
        assert_eq!(
            run_mcp_command(&strings(&["list"]), &cwd, &agent_dir).unwrap(),
            "bad: invalid entry (missing field `url`)\ngood: stdio"
        );
    }

    #[test]
    fn name_patterns() {
        assert!(is_valid_server_name("a"));
        assert!(is_valid_server_name("A-b_9"));
        assert!(!is_valid_server_name(""));
        assert!(!is_valid_server_name("-abc"));
        assert!(!is_valid_server_name("a".repeat(65).as_str()));
    }

    #[test]
    fn http_url_validation() {
        assert!(validate_http_url("https://example.com/mcp").is_ok());
        assert!(validate_http_url("http://localhost:8080").is_ok());
        let err = validate_http_url("notaurl").unwrap_err().to_string();
        assert_eq!(err, "Invalid MCP URL: notaurl");
        let err = validate_http_url("ftp://example.com")
            .unwrap_err()
            .to_string();
        assert_eq!(
            err,
            "MCP URL must be an http(s) URL without embedded credentials."
        );
        let err = validate_http_url("http://u:p@example.com")
            .unwrap_err()
            .to_string();
        assert_eq!(
            err,
            "MCP URL must be an http(s) URL without embedded credentials."
        );
        let err = validate_http_url("http://").unwrap_err().to_string();
        assert_eq!(err, "Invalid MCP URL: http://");
        let err = validate_http_url("https:///").unwrap_err().to_string();
        assert_eq!(err, "Invalid MCP URL: https:///");
        assert_eq!(validate_http_url("http:///path").unwrap(), "http://path/");
    }
}
