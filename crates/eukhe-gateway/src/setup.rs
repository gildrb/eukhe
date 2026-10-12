//! First-run setup in a terminal: find the linked `signal-cli` account, or
//! link this computer to the phone's Signal app (QR code), and start the
//! gateway service when one is installed.

use std::io::{BufRead, Write};
use std::path::Path;
use std::process::{Command, Stdio};

use anyhow::Context;
use serde::Deserialize;

/// The systemd user unit that `programs.eukhe.gateway` installs.
const SERVICE_UNIT: &str = "eukhe-gateway.service";

/// One `signal-cli -o json listAccounts` row.
#[derive(Deserialize)]
struct LinkedAccount {
    number: Option<String>,
    aci: Option<String>,
}

/// The accounts `signal-cli` has linked or registered: the number, or the
/// ACI of a numberless account.
///
/// # Errors
///
/// `signal-cli` is missing, fails, or prints rows without a number or ACI.
pub fn linked_accounts(cli_path: &Path) -> anyhow::Result<Vec<String>> {
    let output = Command::new(cli_path)
        .args(["-o", "json", "listAccounts"])
        .stdin(Stdio::null())
        .output()
        .with_context(|| {
            format!(
                "could not run {}. Install signal-cli: nix profile install nixpkgs#signal-cli",
                cli_path.display()
            )
        })?;
    if !output.status.success() {
        anyhow::bail!(
            "{} listAccounts failed ({}): {}",
            cli_path.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }
    let rows: Vec<LinkedAccount> = serde_json::from_slice(&output.stdout)
        .context("could not read the signal-cli listAccounts output")?;
    rows.into_iter()
        .map(|row| {
            row.number
                .or(row.aci)
                .context("signal-cli listed an account without a number or ACI")
        })
        .collect()
}

/// Link this computer to the phone's Signal app as a new device. Shows the
/// steps; `signal-cli link` prints the QR code and waits for the scan.
///
/// # Errors
///
/// The user cancels, or `signal-cli link` fails.
pub fn link_device(cli_path: &Path) -> anyhow::Result<()> {
    println!("No Signal account is linked. Link this computer to your phone:");
    println!("1. On the phone, open Signal > Settings > Linked devices > Link new device.");
    println!("2. Scan the QR code below.");
    println!("3. Send your messages to \"Note to Self\". The replies come back there.");
    if !confirm("Show the QR code now?")? {
        anyhow::bail!("setup cancelled");
    }
    let status = Command::new(cli_path)
        .args(["link", "-n", "eukhe"])
        .status()
        .with_context(|| format!("could not run {} link", cli_path.display()))?;
    if !status.success() {
        anyhow::bail!("{} link failed ({status})", cli_path.display());
    }
    println!("Linked.");
    Ok(())
}

/// Whether the systemd user service of the gateway is installed. `false`
/// where there is no systemd.
#[must_use]
pub fn service_installed() -> bool {
    Command::new("systemctl")
        .args(["--user", "cat", SERVICE_UNIT])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

/// Restart the gateway service so it picks up the linked account.
///
/// # Errors
///
/// `systemctl` cannot run or the restart fails.
pub fn restart_service() -> anyhow::Result<()> {
    let status = Command::new("systemctl")
        .args(["--user", "restart", SERVICE_UNIT])
        .status()
        .context("could not run systemctl")?;
    if !status.success() {
        anyhow::bail!("systemctl --user restart {SERVICE_UNIT} failed ({status})");
    }
    Ok(())
}

/// Ask a yes/no question on the terminal; Enter means yes.
fn confirm(question: &str) -> anyhow::Result<bool> {
    print!("{question} [Y/n] ");
    std::io::stdout()
        .flush()
        .context("could not write to the terminal")?;
    let mut answer = String::new();
    let read = std::io::stdin()
        .lock()
        .read_line(&mut answer)
        .context("could not read the answer")?;
    if read == 0 {
        return Ok(false);
    }
    Ok(matches!(
        answer.trim().to_ascii_lowercase().as_str(),
        "" | "y" | "yes"
    ))
}
