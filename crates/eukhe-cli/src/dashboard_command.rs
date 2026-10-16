//! `dashboard`: serve the web dashboard on 127.0.0.1 and open it in the
//! browser. The tab chats with the session the CLI uses and browses the
//! chat memory. `--no-open` only prints the URL. Runs in the foreground
//! until Ctrl+C.

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
}

fn usage() -> String {
    format!(
        "Usage: {} dashboard [--port <port>] [--no-open] [--daemon-socket <path>]",
        crate::config::APP_NAME
    )
}

fn parse_args(args: &[String]) -> Result<Args<'_>, String> {
    let mut parsed = Args {
        daemon_socket: None,
        port: eukhe_dashboard::Port::Free,
        browser: Browser::Open,
    };
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--no-open" => parsed.browser = Browser::Skip,
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
    let config = match dashboard_config(args.daemon_socket) {
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
    let served = runtime.block_on(async move {
        let listener = eukhe_dashboard::bind(args.port).await?;
        let url = format!("http://{}/", listener.local_addr()?);
        println!("eukhe dashboard: {url}");
        println!("Serving on loopback only. Press Ctrl+C to stop.");
        if args.browser == Browser::Open {
            eukhe_core::platform::browser::open_in_browser(&url);
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
/// socket, and the home folder for new sessions (the gateway's default).
fn dashboard_config(
    daemon_socket: Option<&str>,
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
        ]);
        let parsed = parse_args(&args).unwrap();
        assert_eq!(
            (parsed.browser, parsed.port, parsed.daemon_socket),
            (
                Browser::Skip,
                eukhe_dashboard::Port::Fixed(8377),
                Some("/tmp/d.sock")
            )
        );
        let parsed = parse_args(&[]).unwrap();
        assert_eq!(
            (parsed.browser, parsed.port, parsed.daemon_socket),
            (Browser::Open, eukhe_dashboard::Port::Free, None)
        );
        let errors: Vec<String> = [
            strings(&["--port"]),
            strings(&["--port", "0"]),
            strings(&["--port", "http"]),
            strings(&["--open"]),
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
            ]
        );
    }
}
