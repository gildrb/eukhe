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

fn parse_args(args: &[String]) -> Result<Args<'_>, String> {
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
                let value = rest.next().ok_or("--port requires a value")?;
                let port = value
                    .parse::<u16>()
                    .ok()
                    .filter(|port| *port != 0)
                    .ok_or_else(|| {
                        format!("--port takes a port number (1-65535), not {value:?}")
                    })?;
                parsed.port = eukhe_dashboard::Port::Fixed(port);
            }
            "--allow-host" => {
                let value = rest.next().ok_or("--allow-host requires a value")?;
                // A bare host name: no scheme, port, path, or brackets
                // (the port does not matter; the Origin check pins it).
                let valid = !value.is_empty()
                    && value
                        .chars()
                        .all(|char| char.is_ascii_alphanumeric() || matches!(char, '.' | '-'));
                if !valid {
                    return Err(format!(
                        "--allow-host takes a host name such as box.tail1234.ts.net, not {value:?}"
                    ));
                }
                parsed.allowed_hosts.push(value.to_ascii_lowercase());
            }
            "--daemon-socket" | "--socket" => {
                parsed.daemon_socket = Some(rest.next().ok_or(format!("{arg} requires a value"))?);
            }
            other => return Err(format!("unknown argument {other:?}")),
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
            return 1;
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
    let launcher = crate::interactive_mode::CliLauncher {
        socket_path: config.socket_path.clone(),
        spawn_cwd: config.new_session_cwd.clone(),
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
        println!("eukhe dashboard: {url}");
        println!("Serving on loopback only. Press Ctrl+C to stop.");
        println!(
            "The {fragment} part pairs a browser: keep it private. Through a forwarder (poros, tailscale serve), add it to the forwarder's URL. `--rotate-token` replaces it."
        );
        for host in &config.allowed_hosts {
            println!("Also answering to {host} (through your forwarder): https://{host}/{fragment}");
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
    let session_dir = crate::config::get_session_dir_env_override()
        .or_else(|| settings.get_session_dir())
        .unwrap_or_else(|| agent_dir.join("sessions"));
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
        socket_path: crate::config::resolve_daemon_socket_path(daemon_socket),
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
        .map(|args| parse_args(args).err().unwrap_or_default())
        .collect();
        assert_eq!(
            errors,
            [
                "--port requires a value",
                "--port takes a port number (1-65535), not \"0\"",
                "--port takes a port number (1-65535), not \"http\"",
                "unknown argument \"--open\"",
                "--allow-host requires a value",
                "--allow-host takes a host name such as box.tail1234.ts.net, not \"https://box.ts.net\"",
                "--allow-host takes a host name such as box.tail1234.ts.net, not \"box.ts.net:443\"",
            ]
        );
    }
}
