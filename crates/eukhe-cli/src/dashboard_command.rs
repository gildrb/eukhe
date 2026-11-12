//! `dashboard`: serve the web dashboard on 127.0.0.1 and open it in the
//! browser. The tab chats with the session the CLI uses, browses the chat
//! memory, and controls the session. The URL's fragment holds the
//! pairing token (kept in the agent dir; `--rotate-token` replaces it).
//! `--no-open` only prints the URL; `--allow-host` names a host a
//! forwarder (`tailscale serve`) exposes the dashboard under. Runs in the
//! foreground until Ctrl+C.

use anyhow::Context;

/// Whether `dashboard` opens the browser.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Browser {
    Open,
    Skip,
}

/// The parsed `dashboard` arguments.
struct Args<'a> {
    daemon_socket: Option<&'a str>,
    port: eukhe_dashboard::Port,
    browser: Browser,
    /// Host names besides loopback the dashboard answers to, lowercase.
    allowed_hosts: Vec<String>,
    /// Whether the stored pairing token is replaced first.
    rotation: eukhe_dashboard::Rotation,
}

fn usage() -> String {
    format!(
        "Usage: {} dashboard [--port <port>] [--no-open] [--allow-host <name>]... [--rotate-token] [--daemon-socket <path>]",
        crate::config::APP_NAME
    )
}

/// Why the `dashboard` arguments do not parse; printed before the usage.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
enum DashboardUsageError {
    /// A flag that takes a value came last.
    #[error("{0} requires a value")]
    MissingValue(String),
    #[error("--port takes a port number (1-65535), not {0}")]
    Port(String),
    #[error("--allow-host takes a host name such as box.tail1234.ts.net, not {0}")]
    Host(String),
    #[error("unknown argument: {0}")]
    UnknownArgument(String),
}

fn parse_args(args: &[String]) -> Result<Args<'_>, DashboardUsageError> {
    let missing = |flag: &str| DashboardUsageError::MissingValue(flag.to_owned());
    let mut parsed = Args {
        daemon_socket: None,
        port: eukhe_dashboard::Port::Free,
        browser: Browser::Open,
        allowed_hosts: Vec::new(),
        rotation: eukhe_dashboard::Rotation::Keep,
    };
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--no-open" => parsed.browser = Browser::Skip,
            "--rotate-token" => parsed.rotation = eukhe_dashboard::Rotation::Rotate,
            "--port" => {
                let value = rest.next().ok_or_else(|| missing("--port"))?;
                let port = value
                    .parse::<u16>()
                    .ok()
                    .filter(|port| *port != 0)
                    .ok_or_else(|| DashboardUsageError::Port(value.clone()))?;
                parsed.port = eukhe_dashboard::Port::Fixed(port);
            }
            "--allow-host" => {
                let value = rest.next().ok_or_else(|| missing("--allow-host"))?;
                // A bare host name: no scheme, port, path, or brackets
                // (the port does not matter; the Origin check pins it).
                let valid = !value.is_empty()
                    && value
                        .chars()
                        .all(|char| char.is_ascii_alphanumeric() || matches!(char, '.' | '-'));
                if !valid {
                    return Err(DashboardUsageError::Host(value.clone()));
                }
                parsed.allowed_hosts.push(value.to_ascii_lowercase());
            }
            "--daemon-socket" | "--socket" => {
                parsed.daemon_socket = Some(rest.next().ok_or_else(|| missing(arg))?);
            }
            other => return Err(DashboardUsageError::UnknownArgument(other.to_owned())),
        }
    }
    Ok(parsed)
}

/// Run the `dashboard` command; returns the process exit code.
pub fn run_dashboard_command(args: &[String]) -> i32 {
    let args = match parse_args(args) {
        Ok(args) => args,
        Err(error) => {
            eprintln!("Error: {error}");
            eprintln!("{}", usage());
            return 2;
        }
    };
    let config = match dashboard_config(args.daemon_socket, args.allowed_hosts) {
        Ok(config) => config,
        Err(error) => {
            eprintln!("Error: {error:#}");
            return 1;
        }
    };
    if let Err(error) = tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_max_level(tracing::Level::INFO)
        .with_target(false)
        .try_init()
    {
        eprintln!("Error: could not start the dashboard log: {error}");
        return 1;
    }
    let runtime = match tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            eprintln!("Error: could not start the dashboard runtime: {error}");
            return 1;
        }
    };
    let launcher =
        match crate::interactive_mode::own_launcher(&config.socket_path, &config.new_session_cwd) {
            Ok(launcher) => launcher,
            Err(error) => {
                eprintln!("Error: {error:#}");
                return 1;
            }
        };
    let token = match eukhe_dashboard::pairing_token(&config.token_path, args.rotation) {
        Ok(token) => token,
        Err(error) => {
            eprintln!("Error: {error:#}");
            return 1;
        }
    };
    let served = runtime.block_on(async move {
        let listener = eukhe_dashboard::bind(args.port).await?;
        let fragment = format!("#token={}", token.secret_hex());
        let url = format!("http://{}/{fragment}", listener.local_addr()?);
        // stdout carries the one value a script captures: the URL. The
        // guidance around it is context and goes to stderr.
        println!("{url}");
        eprintln!("Serving on loopback only. Press Ctrl+C to stop.");
        eprintln!(
            "The {fragment} part pairs a browser: keep it private. Through a forwarder (porthmeus, tailscale serve), add it to the forwarder's URL. `--rotate-token` replaces it."
        );
        for host in &config.allowed_hosts {
            eprintln!("Also answering to {host} (through your forwarder): https://{host}/{fragment}");
        }
        if args.browser == Browser::Open {
            // The browser gets a private page that redirects to the URL:
            // the token stays out of the opener's process arguments.
            let opener = config.token_path.with_file_name("dashboard-open.html");
            eukhe_dashboard::opener_page(&opener, &url)?;
            eukhe_core::platform::browser::open_in_browser(&opener.display().to_string());
        }
        tokio::select! {
            served = eukhe_dashboard::serve(listener, config, launcher) => served,
            signal = tokio::signal::ctrl_c() => signal.context("wait for Ctrl+C"),
        }
    });
    match served {
        // Ctrl+C is how a foreground server is meant to stop: a clean exit
        // 0 on SIGINT.
        Ok(()) => 0,
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}

/// The dashboard configuration: the session dir the CLI uses, the daemon
/// socket, the home folder for new sessions (the gateway's default), and
/// the hosts `--allow-host` names.
fn dashboard_config(
    daemon_socket: Option<&str>,
    allowed_hosts: Vec<String>,
) -> anyhow::Result<eukhe_dashboard::DashboardConfig> {
    let agent_dir = crate::config::get_agent_dir();
    let home = eukhe_types::platform::home_dir().context("HOME is not set")?;
    let settings = eukhe_core::settings::SettingsManager::create(&home, &agent_dir);
    if let Some(error) = settings.global_load_error() {
        anyhow::bail!(
            "could not read {}: {error}",
            agent_dir.join("settings.json").display()
        );
    }
    let session_dir = eukhe_core::settings::resolve_session_dir(None, &settings, &agent_dir)?.path;
    let mut create_config = serde_json::Map::new();
    // Verification seam: sessions run this scripted faux model. The
    // product never sets it.
    if let Some(script) = std::env::var_os("EUKHE_FAUX_SCRIPT") {
        create_config.insert(
            "script".to_string(),
            serde_json::Value::String(script.to_string_lossy().to_string()),
        );
    }
    Ok(eukhe_dashboard::DashboardConfig {
        socket_path: eukhe_client::paths::resolve_daemon_socket_path(
            daemon_socket.map(std::path::Path::new),
        ),
        session_dir,
        new_session_cwd: home,
        create_config,
        allowed_hosts,
        token_path: agent_dir.join("dashboard-token"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_string()).collect()
    }

    #[test]
    fn arguments_parse_or_explain() {
        let args = strings(&[
            "--no-open",
            "--port",
            "8377",
            "--daemon-socket",
            "/tmp/d.sock",
            "--allow-host",
            "Box.Tail1234.ts.net",
            "--allow-host",
            "phone-proxy",
            "--rotate-token",
        ]);
        let parsed = parse_args(&args).unwrap();
        assert_eq!(
            (
                parsed.browser,
                parsed.port,
                parsed.daemon_socket,
                parsed.allowed_hosts,
                parsed.rotation
            ),
            (
                Browser::Skip,
                eukhe_dashboard::Port::Fixed(8377),
                Some("/tmp/d.sock"),
                vec!["box.tail1234.ts.net".to_string(), "phone-proxy".to_string()],
                eukhe_dashboard::Rotation::Rotate
            )
        );
        let parsed = parse_args(&[]).unwrap();
        assert_eq!(
            (
                parsed.browser,
                parsed.port,
                parsed.daemon_socket,
                parsed.allowed_hosts,
                parsed.rotation
            ),
            (
                Browser::Open,
                eukhe_dashboard::Port::Free,
                None,
                Vec::new(),
                eukhe_dashboard::Rotation::Keep
            )
        );
        let errors: Vec<String> = [
            strings(&["--port"]),
            strings(&["--port", "0"]),
            strings(&["--port", "http"]),
            strings(&["--open"]),
            strings(&["--allow-host"]),
            strings(&["--allow-host", "https://box.ts.net"]),
            strings(&["--allow-host", "box.ts.net:443"]),
        ]
        .iter()
        .map(|args| {
            parse_args(args)
                .err()
                .map_or_default(|error| error.to_string())
        })
        .collect();
        assert_eq!(
            errors,
            [
                "--port requires a value",
                "--port takes a port number (1-65535), not 0",
                "--port takes a port number (1-65535), not http",
                "unknown argument: --open",
                "--allow-host requires a value",
                "--allow-host takes a host name such as box.tail1234.ts.net, not https://box.ts.net",
                "--allow-host takes a host name such as box.tail1234.ts.net, not box.ts.net:443",
            ]
        );
    }
}
