//! `eukhe tiny-models`: list the pinned local models with their install
//! state, and download them (`download <id>` or `download all`). The
//! download is the only traffic of the local models and runs only here;
//! every file is checked against its pinned size and sha256 before the
//! model is installed.

use std::io::IsTerminal;

use eukhe_tiny::{
    install_state, installed, CatalogModel, Downloaded, InstallState, ModelKind, Progress,
    TinyHome, CATALOG, HUGGING_FACE,
};

use crate::config::{get_agent_dir, APP_NAME};

/// Run the `tiny-models` command; returns the process exit code.
pub fn run_tiny_models_command(args: &[String]) -> i32 {
    let home = TinyHome::under(&get_agent_dir());
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match args.as_slice() {
        [] | ["list"] => {
            print_list(&home);
            0
        }
        ["download", "all"] => download_models(&home, CATALOG.iter().collect()),
        ["download", id] => {
            if let Some(model) = eukhe_tiny::find(id) {
                return download_models(&home, vec![model]);
            }
            let known: Vec<&str> = CATALOG.iter().map(|model| model.id).collect();
            eprintln!(
                "Error: unknown tiny model {id:?}; known: {}, or all",
                known.join(", ")
            );
            1
        }
        _ => {
            eprintln!("Usage: {APP_NAME} tiny-models [list | download <id|all>]");
            1
        }
    }
}

fn print_list(home: &TinyHome) {
    let rows: Vec<[String; 5]> = CATALOG
        .iter()
        .map(|model| {
            let kind = match model.kind {
                ModelKind::Text { .. } => "text",
                ModelKind::SpeechToText => "speech-to-text",
                ModelKind::TextToSpeech => "text-to-speech",
            };
            let roles: Vec<&str> = model.roles.iter().map(|role| role.id()).collect();
            let state = match install_state(home, model) {
                InstallState::Installed => "installed".to_owned(),
                InstallState::Missing => "missing".to_owned(),
                InstallState::Partial {
                    missing,
                    wrong_size,
                } => format!(
                    "incomplete ({} missing, {} wrong size)",
                    missing.len(),
                    wrong_size.len()
                ),
            };
            [
                model.id.to_owned(),
                kind.to_owned(),
                roles.join(","),
                megabytes(model.size()),
                state,
            ]
        })
        .collect();
    let header = ["ID", "KIND", "ROLES", "SIZE", "STATE"].map(str::to_owned);
    let mut widths = header.clone().map(|cell| cell.len());
    for row in &rows {
        for (width, cell) in widths.iter_mut().zip(row) {
            *width = (*width).max(cell.len());
        }
    }
    for row in std::iter::once(&header).chain(&rows) {
        let line: Vec<String> = row
            .iter()
            .zip(widths)
            .map(|(cell, width)| format!("{cell:<width$}"))
            .collect();
        println!("{}", line.join("  ").trim_end());
    }
    println!("Models dir: {}", home.models.display());
}

fn megabytes(bytes: u64) -> String {
    // Display only: the precision loss of the f64 is far below a tenth of a MB.
    #[allow(clippy::cast_precision_loss)]
    let megabytes = bytes as f64 / 1_000_000.0;
    format!("{megabytes:.1} MB")
}

/// Downloads `models` in order; stops at the first failure.
fn download_models(home: &TinyHome, models: Vec<&'static CatalogModel>) -> i32 {
    let runtime = match tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            eprintln!("Error: cannot start the async runtime: {error}");
            return 1;
        }
    };
    let terminal = std::io::stderr().is_terminal();
    for model in models {
        if installed(home, model) {
            eprintln!("{} is already installed", model.id);
            continue;
        }
        eprintln!(
            "Downloading {} ({}, {} files) from {HUGGING_FACE}",
            model.id,
            megabytes(model.size()),
            model.files.len()
        );
        let result = runtime.block_on(eukhe_tiny::download(
            home,
            model,
            HUGGING_FACE,
            &mut progress_printer(terminal),
        ));
        match result {
            Ok(Downloaded::Installed) => {
                eprintln!(
                    "{} installed in {}",
                    model.id,
                    home.model_dir(model.id).display()
                );
            }
            Ok(Downloaded::AlreadyInstalled) => eprintln!("{} is already installed", model.id),
            Err(error) => {
                if terminal {
                    eprintln!();
                }
                eprintln!("Error: {}: {error}", model.id);
                return 1;
            }
        }
    }
    0
}

/// Prints a per-file `received/total bytes` line (redrawn in place on a
/// terminal, at each whole percent) and the sha256 verification.
fn progress_printer(terminal: bool) -> impl FnMut(Progress) + Send {
    let mut last_percent: Option<u64> = None;
    move |event| match event {
        Progress::Receiving {
            file,
            received,
            total,
        } => {
            let percent = (received * 100).checked_div(total).unwrap_or(100);
            if terminal && last_percent != Some(percent) {
                last_percent = Some(percent);
                eprint!("\r  {file}: {received}/{total} bytes");
            }
        }
        Progress::Verified { file, sha256 } => {
            last_percent = None;
            let redraw = if terminal { "\r" } else { "" };
            eprintln!("{redraw}  {file}: sha256 {sha256} verified");
        }
    }
}
