//! `cli.ts` has no TS test; these pin the library port's command handling.

use std::io::Write;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::cli::run_cli;

#[derive(Clone, Default)]
struct Captured(Arc<Mutex<Vec<u8>>>);

impl Write for Captured {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .extend_from_slice(buf);
        Ok(buf.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl Captured {
    fn text(&self) -> String {
        String::from_utf8(
            self.0
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone(),
        )
        .expect("utf-8")
    }
}

async fn run(args: &[&str], input: &'static str) -> (Result<(), String>, String) {
    let output = Captured::default();
    let dir = tempfile::tempdir().expect("temp dir");
    let args: Vec<String> = args.iter().map(|arg| (*arg).to_owned()).collect();
    let result = run_cli(
        &args,
        Box::new(tokio::io::BufReader::new(input.as_bytes())),
        Box::new(output.clone()),
        &dir.path().join("auth.json"),
    )
    .await
    .map_err(|error| error.to_string());
    (result, output.text())
}

#[tokio::test]
async fn prints_usage_with_the_oauth_providers() {
    let (result, output) = run(&[], "").await;
    assert_eq!(result, Ok(()));
    assert!(
        output.starts_with("Usage: npx @earendil-works/pi-ai <command> [provider]\n\nCommands:\n")
    );
    assert!(output.contains(&format!("  {:<20} {}\n", "anthropic", "Anthropic")));
    assert!(!output.contains("  amazon-bedrock"));
}

#[tokio::test]
async fn lists_oauth_providers() {
    let (result, output) = run(&["list"], "").await;
    assert_eq!(result, Ok(()));
    assert!(output
        .lines()
        .any(|line| line == format!("{:<20} {}", "github-copilot", "GitHub Copilot")));
}

#[tokio::test]
async fn rejects_unknown_commands_and_providers() {
    assert_eq!(
        run(&["frobnicate"], "").await.0,
        Err("Unknown command: frobnicate".to_owned())
    );
    assert_eq!(
        run(&["login", "nope"], "").await.0,
        Err("Unknown provider: nope".to_owned())
    );
    let (result, output) = run(&["login"], "999\n").await;
    assert_eq!(result, Err("Unknown provider: ".to_owned()));
    assert!(output.contains("Enter number (1-"));
}
