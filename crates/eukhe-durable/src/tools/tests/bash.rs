//! `bash` and `powershell` cases of `test/tools.test.ts`.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{with_abort_signal, AbortController, AbortSignal, BACKGROUND_CONTEXT};
use futures::FutureExt;
use serde_json::json;

use super::support::{execute, native, read_file, run, temp_dir, FakeApi, HookedEnv};
use crate::env::{
    ExecCommand, ExecutionEnv, ExecutionError, ExecutionErrorCode, FileSystem, NativeExecutionEnv,
    NativeExecutionEnvOptions, OutputStream, ShellExecResult, ShellOutputInfo, ShellOutputSkip,
    ShellOutputWindow, TempFileOptions,
};
use crate::tools::{
    create_bash_tool, create_powershell_tool, BashPrepare, BashToolOptions, PowerShellToolOptions,
};
use crate::truncate::DEFAULT_MAX_LINES;

const STDOUT: ShellOutputInfo = ShellOutputInfo {
    stream: OutputStream::Stdout,
    skipped: None,
};

/// An environment where only the listed programs exist; it records each
/// command and prints `output`.
fn programs_env(
    installed: &[&str],
    output: &'static str,
    exit_code: i32,
) -> (
    Arc<dyn ExecutionEnv>,
    Arc<Mutex<Vec<ExecCommand>>>,
    tempfile::TempDir,
) {
    let dir = temp_dir();
    let commands = Arc::new(Mutex::new(Vec::new()));
    let installed: Vec<String> = installed
        .iter()
        .map(|program| (*program).to_owned())
        .collect();
    let mut env = HookedEnv::new(native(&dir));
    let recorded = Arc::clone(&commands);
    env.exec = Some(Arc::new(move |_inner, command, options, cx| {
        recorded
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(command.clone());
        let result = match command {
            ExecCommand::Argv(argv) if installed.contains(&argv[0]) => {
                if let Some(on_output) = &options.on_output {
                    on_output(output, cx, &STDOUT).unwrap();
                }
                Ok(ShellExecResult {
                    exit_code,
                    spill_path: None,
                })
            }
            ExecCommand::Argv(argv) => Err(ExecutionError::new(
                ExecutionErrorCode::SpawnError,
                format!("spawn {} ENOENT", argv[0]),
            )),
            ExecCommand::Shell(command) => Err(ExecutionError::new(
                ExecutionErrorCode::SpawnError,
                format!("spawn {command} ENOENT"),
            )),
        };
        futures::future::ready(result).boxed()
    }));
    (Arc::new(env), commands, dir)
}

#[tokio::test]
async fn runs_the_command_with_pwsh_as_one_argument_forcing_utf_8_output() {
    let (env, commands, _dir) = programs_env(&["pwsh"], "héllo\n", 0);
    let (result, api) = run(
        &create_powershell_tool(PowerShellToolOptions::default()),
        json!({ "command": "Write-Output 'héllo'" }),
        env,
    )
    .await;
    result.unwrap();
    assert_eq!(api.text(), "héllo\n");
    let expected: Vec<String> = [
        "pwsh",
        "-NoProfile",
        "-NonInteractive",
        "-ExecutionPolicy",
        "Bypass",
        "-Command",
        "try { [Console]::OutputEncoding=[System.Text.Encoding]::UTF8 } catch {}\nWrite-Output 'héllo'",
    ]
    .iter()
    .map(|arg| (*arg).to_owned())
    .collect();
    assert_eq!(
        *commands.lock().unwrap_or_else(PoisonError::into_inner),
        vec![ExecCommand::Argv(expected)]
    );
}

#[tokio::test]
async fn falls_back_to_windows_powershell_and_reports_the_last_start_failure() {
    let (env, commands, _dir) = programs_env(&["powershell"], "ok", 0);
    let options = PowerShellToolOptions {
        command_prefix: Some("$x = 1".to_owned()),
        ..PowerShellToolOptions::default()
    };
    let (result, api) = run(
        &create_powershell_tool(options),
        json!({ "command": "$x" }),
        env,
    )
    .await;
    result.unwrap();
    assert_eq!(api.text(), "ok");
    let commands = commands
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    let argvs: Vec<Vec<String>> = commands
        .into_iter()
        .map(|command| match command {
            ExecCommand::Argv(argv) => argv,
            ExecCommand::Shell(command) => vec![command],
        })
        .collect();
    assert_eq!(
        argvs
            .iter()
            .map(|argv| argv[0].as_str())
            .collect::<Vec<_>>(),
        ["pwsh", "powershell"]
    );
    assert!(argvs[1].last().unwrap().ends_with("\n$x = 1\n$x"));

    let (none, _, _dir) = programs_env(&[], "", 0);
    let (failed, _) = run(
        &create_powershell_tool(PowerShellToolOptions::default()),
        json!({ "command": "1" }),
        none,
    )
    .await;
    assert_eq!(failed.unwrap_err().to_string(), "spawn powershell ENOENT");
}

#[tokio::test]
async fn throws_on_a_nonzero_exit_after_streaming_the_output() {
    let (env, _, _dir) = programs_env(&["pwsh"], "partial", 3);
    let (failed, api) = run(
        &create_powershell_tool(PowerShellToolOptions::default()),
        json!({ "command": "exit 3" }),
        env,
    )
    .await;
    assert_eq!(
        failed.unwrap_err().to_string(),
        "Command exited with code 3"
    );
    assert_eq!(api.text(), "partial");
}

/// TS `runIf(process.platform === "win32")`: PowerShell is not part of the
/// supported Linux and macOS platforms, so the case is skipped like the TS
/// one there.
#[tokio::test]
#[ignore = "runs only on Windows in TS; PowerShell is not available on the supported platforms"]
async fn runs_real_powershell_with_utf_8_output() {
    let dir = temp_dir();
    let (result, api) = run(
        &create_powershell_tool(PowerShellToolOptions::default()),
        json!({ "command": "Write-Output ('h' + [char]0xe9 + 'llo'); exit 0" }),
        Arc::new(native(&dir)),
    )
    .await;
    result.unwrap();
    assert_eq!(api.text().trim(), "héllo");
}

#[tokio::test]
async fn passes_the_retained_window_to_the_environment_and_forwards_what_it_skipped() {
    let window = ShellOutputWindow {
        max_bytes: 4,
        max_lines: 1,
        min_interval_ms: 100.0,
        bytes_per_second: 1024.0,
    };
    let skipped = ShellOutputSkip {
        bytes: 6,
        newlines: 2,
        ends_with_newline: true,
    };
    let received = Arc::new(Mutex::new(None));
    let dir = temp_dir();
    let mut env = HookedEnv::new(native(&dir));
    let seen = Arc::clone(&received);
    env.exec = Some(Arc::new(move |_inner, _command, options, cx| {
        *seen.lock().unwrap_or_else(PoisonError::into_inner) = options.window;
        let info = ShellOutputInfo {
            stream: OutputStream::Stdout,
            skipped: Some(skipped),
        };
        if let Some(on_output) = &options.on_output {
            on_output("tail\n", cx, &info).unwrap();
        }
        futures::future::ready(Ok(ShellExecResult {
            exit_code: 0,
            spill_path: None,
        }))
        .boxed()
    }));
    let api = Arc::new(FakeApi {
        env: Some(Arc::new(env)),
        window: Some(window),
        output: Mutex::new(Vec::new()),
        diagnostics: Mutex::new(Vec::new()),
    });
    execute(
        &create_bash_tool(BashToolOptions::default()),
        json!({ "command": "anything" }),
        &api,
        &BACKGROUND_CONTEXT,
    )
    .await
    .unwrap();
    assert_eq!(
        *received.lock().unwrap_or_else(PoisonError::into_inner),
        Some(window)
    );
    assert_eq!(
        *api.output.lock().unwrap_or_else(PoisonError::into_inner),
        vec![("tail\n".to_owned(), Some(skipped))]
    );
}

#[tokio::test]
async fn streams_combined_stdout_and_stderr_and_returns_no_content_of_its_own() {
    let dir = temp_dir();
    let (result, api) = run(
        &create_bash_tool(BashToolOptions::default()),
        json!({ "command": "printf out; printf err >&2" }),
        Arc::new(native(&dir)),
    )
    .await;
    assert!(api.text().contains("out"));
    assert!(api.text().contains("err"));
    assert_eq!(result.unwrap().content, None);
}

#[tokio::test]
async fn throws_on_nonzero_exits_and_timeouts_after_streaming_the_output() {
    let dir = temp_dir();
    let env: Arc<dyn ExecutionEnv> = Arc::new(native(&dir));
    let tool = create_bash_tool(BashToolOptions::default());
    let (failed, api) = run(
        &tool,
        json!({ "command": "printf failed; exit 7" }),
        Arc::clone(&env),
    )
    .await;
    assert_eq!(
        failed.unwrap_err().to_string(),
        "Command exited with code 7"
    );
    assert_eq!(api.text(), "failed");
    let (slow, _) = run(&tool, json!({ "command": "sleep 2", "timeout": 0.01 }), env).await;
    assert_eq!(
        slow.unwrap_err().to_string(),
        "Command timed out after 0.01 seconds"
    );
}

const TRUNCATED_OUTPUT_LINES: u64 = DEFAULT_MAX_LINES + 1;

#[tokio::test]
async fn reports_the_spill_of_a_command_that_times_out() {
    let dir = temp_dir();
    let mut env = HookedEnv::new(native(&dir));
    env.exec = Some(Arc::new(|inner, _command, options, cx| {
        async move {
            let output = format!(
                "{}\n",
                (1..=TRUNCATED_OUTPUT_LINES)
                    .map(|index| format!("line-{index}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            );
            let options_temp = TempFileOptions {
                prefix: Some("timeout-".to_owned()),
                suffix: Some(".log".to_owned()),
            };
            let spill_path = inner.create_temp_file(options_temp, cx).await.unwrap();
            inner
                .write_file(&spill_path, output.as_bytes(), cx)
                .await
                .unwrap();
            if let Some(on_output) = &options.on_output {
                on_output(&output, cx, &STDOUT).unwrap();
            }
            let timeout = options
                .timeout
                .map_or_else(|| "undefined".to_owned(), |timeout| timeout.to_string());
            let mut error =
                ExecutionError::new(ExecutionErrorCode::Timeout, format!("timeout:{timeout}"));
            error.spill_path = Some(spill_path);
            Err(error)
        }
        .boxed()
    }));
    let env: Arc<dyn ExecutionEnv> = Arc::new(env);
    let (failed, api) = run(
        &create_bash_tool(BashToolOptions::default()),
        json!({ "command": "emit-output-then-time-out", "timeout": 0.05 }),
        Arc::clone(&env),
    )
    .await;
    assert_eq!(
        failed.unwrap_err().to_string(),
        "Command timed out after 0.05 seconds"
    );
    let reported = api.reported();
    let full_output_path = reported[0]
        .message
        .strip_prefix("Full output: ")
        .expect("spill diagnostic");
    let full_output = read_file(env.as_ref(), full_output_path).await;
    assert!(full_output.contains("line-1\nline-2"));
    assert!(full_output.contains(&format!(
        "line-{DEFAULT_MAX_LINES}\nline-{TRUNCATED_OUTPUT_LINES}"
    )));
}

#[tokio::test]
async fn prepares_command_cwd_and_an_explicit_environment_with_the_calls_api() {
    let dir = temp_dir();
    let env = Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: dir.path().to_string_lossy().into_owned(),
        shell_env: Some(BTreeMap::from([(
            "PI_BASH_PREPARE_INHERITED".to_owned(),
            "inherited".to_owned(),
        )])),
        ..NativeExecutionEnvOptions::default()
    }));
    env.create_dir(
        "workspace",
        crate::env::CreateDirOptions::default(),
        &BACKGROUND_CONTEXT,
    )
    .await
    .unwrap();
    let workspace = format!("{}/workspace", env.cwd());
    let controller = AbortController::new();
    let received_env = Arc::new(Mutex::new(None::<Arc<dyn ExecutionEnv>>));
    let received_signal = Arc::new(Mutex::new(None::<AbortSignal>));
    let prepare: BashPrepare = {
        let (received_env, received_signal, workspace) = (
            Arc::clone(&received_env),
            Arc::clone(&received_signal),
            workspace.clone(),
        );
        Arc::new(move |execution, api, call_cx| {
            *received_env.lock().unwrap_or_else(PoisonError::into_inner) = api.env();
            *received_signal
                .lock()
                .unwrap_or_else(PoisonError::into_inner) = call_cx.abort_signal();
            execution.cwd = workspace.clone();
            execution.env =
                BTreeMap::from([("PI_BASH_PREPARE_EXPLICIT".to_owned(), "explicit".to_owned())]);
            execution.inherit_env = false;
            execution.command.push_str(
                "\n: > prepared-cwd\nprintf '%s:%s:%s' \"$prefix\" \"${PI_BASH_PREPARE_INHERITED-}\" \"$PI_BASH_PREPARE_EXPLICIT\"",
            );
            execution.command.push_str("\nprintf ':%s' \"$PWD\"");
            futures::future::ready(Ok(())).boxed()
        })
    };
    let tool = create_bash_tool(BashToolOptions {
        command_prefix: Some("prefix=ready".to_owned()),
        prepare: Some(prepare),
    });
    let env_dyn: Arc<dyn ExecutionEnv> = Arc::clone(&env) as Arc<dyn ExecutionEnv>;
    let api = FakeApi::new(Some(Arc::clone(&env_dyn)));
    let cx = with_abort_signal(&controller.signal(), &BACKGROUND_CONTEXT);
    execute(&tool, json!({ "command": ":" }), &api, &cx)
        .await
        .unwrap();
    let seen_env = received_env
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .unwrap();
    assert!(Arc::ptr_eq(&seen_env, &env_dyn));
    assert!(received_signal
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .as_ref()
        .unwrap()
        .same(&cx.abort_signal().unwrap()));
    let pwd = format!(
        ":{}",
        env.canonical_path(&workspace, &BACKGROUND_CONTEXT)
            .await
            .unwrap()
    );
    assert_eq!(api.text(), format!("ready::explicit{pwd}"));
    assert!(env
        .exists(&format!("{workspace}/prepared-cwd"), &BACKGROUND_CONTEXT)
        .await
        .unwrap());
}

#[tokio::test]
async fn supports_command_prefixes() {
    let dir = temp_dir();
    let tool = create_bash_tool(BashToolOptions {
        command_prefix: Some("value=hello".to_owned()),
        prepare: None,
    });
    let (result, api) = run(
        &tool,
        json!({ "command": "printf $value" }),
        Arc::new(native(&dir)),
    )
    .await;
    result.unwrap();
    assert_eq!(api.text(), "hello");
}

#[tokio::test]
async fn streams_every_byte_and_spills_complete_output_beyond_the_default_limits() {
    let dir = temp_dir();
    let env: Arc<dyn ExecutionEnv> = Arc::new(native(&dir));
    let (result, api) = run(
        &create_bash_tool(BashToolOptions::default()),
        json!({ "command": "i=1; while [ $i -le 3000 ]; do echo line-$i; i=$((i + 1)); done" }),
        Arc::clone(&env),
    )
    .await;
    result.unwrap();
    let expected = (1..=3000).fold(String::new(), |mut text, index| {
        text.push_str("line-");
        text.push_str(&index.to_string());
        text.push('\n');
        text
    });
    assert_eq!(api.text(), expected);
    let reported = api.reported();
    let full_output_path = reported[0]
        .message
        .strip_prefix("Full output: ")
        .expect("spill diagnostic");
    assert_eq!(read_file(env.as_ref(), full_output_path).await, expected);
}

#[tokio::test]
async fn does_not_spill_output_within_the_limits() {
    let dir = temp_dir();
    let (result, api) = run(
        &create_bash_tool(BashToolOptions::default()),
        json!({ "command": "printf small" }),
        Arc::new(native(&dir)),
    )
    .await;
    result.unwrap();
    assert_eq!(api.reported(), Vec::new());
}
