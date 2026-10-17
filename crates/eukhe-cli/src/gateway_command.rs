//! `gateway`: run the Signal gateway. The phone's Signal messages go into
//! the session the CLI uses; the agent's replies go back. The settings come
//! from the global `gateway.signal` only. In a terminal it guides the setup
//! (link the phone) and starts the gateway service when one is installed.

use std::io::IsTerminal;
use std::path::PathBuf;

use anyhow::Context;

/// Where `eukhe gateway` runs: a terminal may answer setup questions; a
/// service may not.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Caller {
    Terminal,
    Service,
}

/// Run the `gateway` command; returns the process exit code.
pub fn run_gateway_command(args: &[String]) -> i32 {
    let app = crate::config::APP_NAME;
    let mut daemon_socket: Option<&str> = None;
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--daemon-socket" | "--socket" => {
                let Some(value) = rest.next() else {
                    eprintln!("Error: {arg} requires a value");
                    return 1;
                };
                daemon_socket = Some(value);
            }
            other => {
                eprintln!("Error: unknown argument {other:?}");
                eprintln!("Usage: {app} gateway [--daemon-socket <path>]");
                return 1;
            }
        }
    }
    let caller = if std::io::stdin().is_terminal() && std::io::stdout().is_terminal() {
        Caller::Terminal
    } else {
        Caller::Service
    };
    let config = match gateway_config(daemon_socket, caller) {
        Ok(config) => config,
        Err(error) => {
            eprintln!("Error: {error:#}");
            return 1;
        }
    };
    if caller == Caller::Terminal && eukhe_gateway::service_installed() {
        return match eukhe_gateway::restart_service() {
            Ok(()) => {
                println!(
                    "The gateway runs in the background as {}.",
                    config.signal.account
                );
                println!("Send a message to \"Note to Self\" in Signal.");
                println!("Log: journalctl --user -u eukhe-gateway -f");
                0
            }
            Err(error) => {
                eprintln!("Error: {error:#}");
                1
            }
        };
    }
    if let Err(error) = tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_max_level(tracing::Level::INFO)
        .with_target(false)
        .try_init()
    {
        eprintln!("Error: could not start the gateway log: {error}");
        return 1;
    }
    let runtime = match tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            eprintln!("Error: could not start the gateway runtime: {error}");
            return 1;
        }
    };
    let launcher = crate::interactive_mode::CliLauncher {
        socket_path: config.socket_path.clone(),
        spawn_cwd: config.new_session_cwd.clone(),
    };
    match runtime.block_on(eukhe_gateway::run(config, launcher)) {
        Ok(()) => 0,
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}

/// The gateway configuration from the global settings, the session-dir
/// overrides, and the daemon socket.
fn gateway_config(
    daemon_socket: Option<&str>,
    caller: Caller,
) -> anyhow::Result<eukhe_gateway::GatewayConfig> {
    let agent_dir = crate::config::get_agent_dir();
    let global_path = agent_dir.join("settings.json");
    let home = eukhe_types::platform::home_dir().context("HOME is not set")?;
    let settings = eukhe_core::settings::SettingsManager::create(&home, &agent_dir);
    if let Some(error) = settings.global_load_error() {
        anyhow::bail!("could not read {}: {error}", global_path.display());
    }
    let signal = settings.get_signal_gateway();
    let cli_path = signal.cli_path.as_deref().map_or_else(
        || PathBuf::from("signal-cli"),
        crate::config::expand_tilde_path,
    );
    let account = match signal.account.as_deref().map(str::trim) {
        Some("") => anyhow::bail!(
            "gateway.signal.account in {} is empty; set it to the signal-cli account or remove it",
            global_path.display()
        ),
        Some(account) => account.to_string(),
        None => linked_account(&cli_path, caller, &global_path)?,
    };
    let new_session_cwd = signal
        .cwd
        .as_deref()
        .map_or_else(|| home.clone(), crate::config::expand_tilde_path);
    let session_dir = crate::config::get_session_dir_env_override()
        .or_else(|| settings.get_session_dir())
        .unwrap_or_else(|| agent_dir.join("sessions"));
    Ok(eukhe_gateway::GatewayConfig {
        socket_path: crate::config::resolve_daemon_socket_path(daemon_socket),
        session_dir,
        new_session_cwd,
        signal: eukhe_gateway::SignalConfig {
            cli_path,
            account,
            allow: signal.allow.unwrap_or_default(),
        },
    })
}

/// The only account `signal-cli` has. With none, a terminal links the phone
/// first; a service stops with the step to take.
fn linked_account(
    cli_path: &std::path::Path,
    caller: Caller,
    global_path: &std::path::Path,
) -> anyhow::Result<String> {
    let mut accounts = eukhe_gateway::linked_accounts(cli_path)?;
    if accounts.is_empty() {
        match caller {
            Caller::Terminal => {
                eukhe_gateway::link_device(cli_path)?;
                accounts = eukhe_gateway::linked_accounts(cli_path)?;
            }
            Caller::Service => anyhow::bail!(
                "no Signal account is linked. Run `eukhe gateway` in a terminal and follow the steps"
            ),
        }
    }
    match accounts.as_slice() {
        [account] => Ok(account.clone()),
        [] => anyhow::bail!("signal-cli still lists no account after the link"),
        many => anyhow::bail!(
            "signal-cli has {} accounts ({}). Set gateway.signal.account in {}",
            many.len(),
            many.join(", "),
            global_path.display()
        ),
    }
}
