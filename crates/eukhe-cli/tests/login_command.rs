//! `eukhe login` and `eukhe logout` as a host runs them: no terminal
//! (stdin a pipe or closed), a clean environment, an isolated agent dir,
//! and a fake OAuth endpoint (`EUKHE_XAI_AUTH_URL`). The device login
//! prints its code and polls; an API key comes from stdin or
//! `EUKHE_LOGIN_API_KEY`.

use std::io::{BufRead as _, BufReader, Read as _, Write as _};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::process::{Child, Command, Output, Stdio};
use std::sync::{mpsc, Arc, Mutex, PoisonError};
use std::time::Duration;

use serde_json::{json, Value};

/// How long one login may run before the test kills it.
const LOGIN_DEADLINE: Duration = Duration::from_secs(60);

/// The test's isolated home and agent dir.
struct World {
    dir: tempfile::TempDir,
}

impl World {
    fn new() -> World {
        let dir = tempfile::tempdir().expect("temp dir");
        std::fs::create_dir_all(dir.path().join("agent")).expect("agent dir");
        std::fs::create_dir_all(dir.path().join("tmp")).expect("tmp dir");
        World { dir }
    }

    fn agent_dir(&self) -> PathBuf {
        self.dir.path().join("agent")
    }

    /// `eukhe <args>` in a clean environment: stdin closed, output piped.
    fn eukhe(&self, args: &[&str]) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_eukhe"));
        command
            .args(args)
            .env_clear()
            .env("PATH", std::env::var_os("PATH").unwrap_or_default())
            .env("HOME", self.dir.path())
            .env("TMPDIR", self.dir.path().join("tmp"))
            .env("EUKHE_CODING_AGENT_DIR", self.agent_dir())
            .env("EUKHE_OFFLINE", "1")
            .current_dir(self.dir.path())
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        command
    }

    /// Run `eukhe <args>` with `stdin` piped in.
    fn run(&self, args: &[&str], stdin: &str) -> Output {
        let mut child = self
            .eukhe(args)
            .stdin(Stdio::piped())
            .spawn()
            .expect("eukhe starts");
        child
            .stdin
            .take()
            .expect("stdin")
            .write_all(stdin.as_bytes())
            .expect("write stdin");
        finish(child)
    }

    fn auth(&self) -> Value {
        std::fs::read_to_string(self.agent_dir().join("auth.json")).map_or(Value::Null, |text| {
            serde_json::from_str(&text).expect("auth.json")
        })
    }

    fn accounts(&self, provider: &str) -> Vec<Value> {
        self.auth()[provider]["accounts"]
            .as_array()
            .cloned()
            .unwrap_or_default()
    }

    /// `eukhe login --json`: the listing and its exit code.
    fn listing(&self) -> (Value, i32) {
        let output = self.run(&["login", "--json"], "");
        (
            serde_json::from_slice(&output.stdout).expect("listing JSON"),
            output.status.code().expect("exit code"),
        )
    }

    fn saved_to(&self) -> String {
        format!(
            "Credentials saved to {}",
            self.agent_dir().join("auth.json").display()
        )
    }
}

/// Wait for `child`; one still running at [`LOGIN_DEADLINE`] is killed
/// (its exit status then fails the test).
fn finish(child: Child) -> Output {
    let pid = nix::unistd::Pid::from_raw(i32::try_from(child.id()).expect("pid"));
    let (done_tx, done) = mpsc::channel::<()>();
    let watchdog = std::thread::spawn(move || {
        if done.recv_timeout(LOGIN_DEADLINE).is_err() {
            let _ = nix::sys::signal::kill(pid, nix::sys::signal::Signal::SIGKILL);
        }
    });
    let output = child.wait_with_output().expect("eukhe exits");
    let _ = done_tx.send(());
    watchdog.join().expect("watchdog");
    output
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// The one stdout line of a successful login.
fn one_line(output: &Output) -> String {
    let stdout = text(&output.stdout);
    assert_eq!(
        (output.status.code(), stdout.lines().count()),
        (Some(0), 1),
        "stdout: {stdout}\nstderr: {}",
        text(&output.stderr)
    );
    stdout.trim_end().to_owned()
}

fn row<'a>(listing: &'a Value, provider: &str, method: &str) -> &'a Value {
    listing["providers"]
        .as_array()
        .and_then(|rows| {
            rows.iter()
                .find(|row| row["provider"] == provider && row["method"] == method)
        })
        .unwrap_or_else(|| panic!("{provider} {method} is listed: {listing}"))
}

/// The listing's exit code: 0 when a provider is logged in, else 1.
fn listing_code(listing: &Value) -> i32 {
    let any = listing["providers"]
        .as_array()
        .is_some_and(|rows| rows.iter().any(|row| row["loggedIn"] == true));
    i32::from(!any)
}

#[test]
fn a_key_from_stdin_logs_in_and_logout_removes_it() {
    let world = World::new();
    let (before, code) = world.listing();
    assert_eq!(
        row(&before, "openai", "api_key"),
        &json!({ "provider": "openai", "name": "OpenAI", "method": "api_key", "loggedIn": false, "status": null })
    );
    assert_eq!(code, listing_code(&before));

    let line = one_line(&world.run(&["login", "openai"], "sk-from-stdin\n"));
    assert!(
        line.starts_with("Saved API key for OpenAI as ") && line.ends_with(&world.saved_to()),
        "{line}"
    );
    let accounts = world.accounts("openai");
    assert_eq!(
        (accounts.len(), &accounts[0]["type"], &accounts[0]["key"]),
        (1, &json!("api_key"), &json!("sk-from-stdin"))
    );
    let (after, code) = world.listing();
    assert_eq!(
        row(&after, "openai", "api_key"),
        &json!({ "provider": "openai", "name": "OpenAI", "method": "api_key", "loggedIn": true, "status": "configured" })
    );
    assert_eq!(code, 0);

    let logout = world.run(&["logout", "openai"], "");
    assert_eq!(logout.status.code(), Some(0), "{}", text(&logout.stderr));
    assert!(world.accounts("openai").is_empty());
}

/// The same key again replaces its account; another key adds one (an
/// API key's identity is its last 6 characters). An empty key fails.
#[test]
fn a_key_from_the_environment_follows_the_account_rules() {
    let world = World::new();
    let login = |key: &str| {
        let mut command = world.eukhe(&["login", "openai"]);
        command.env("EUKHE_LOGIN_API_KEY", key);
        finish(command.spawn().expect("eukhe starts"))
    };
    one_line(&login("sk-env-key-000001"));
    one_line(&login("sk-env-key-000001"));
    assert_eq!(world.accounts("openai").len(), 1);
    one_line(&login("sk-env-key-000002"));
    let keys: Vec<Value> = world
        .accounts("openai")
        .iter()
        .map(|account| account["key"].clone())
        .collect();
    assert_eq!(
        keys,
        vec![json!("sk-env-key-000001"), json!("sk-env-key-000002")]
    );

    let empty = world.run(&["login", "openai"], "\n");
    assert_eq!(empty.status.code(), Some(1));
    assert!(
        text(&empty.stderr).contains("API key cannot be empty"),
        "{}",
        text(&empty.stderr)
    );
}

#[test]
fn usage_errors_exit_2() {
    let world = World::new();
    for args in [
        &["login", "no-such-provider"][..],
        &["login", "openai", "anthropic"],
        &["login", "github-copilot", "--key"],
        &["login", "anthropic", "--device"],
        &["login", "--key"],
        &["login", "--bogus"],
        &["login", "anthropic", "--json"],
        &["logout"],
    ] {
        let output = world.run(args, "");
        assert_eq!(
            output.status.code(),
            Some(2),
            "{args:?}: {}",
            text(&output.stderr)
        );
    }
    assert!(
        world.accounts("openai").is_empty() && world.accounts("anthropic").is_empty(),
        "{}",
        world.auth()
    );
}

/// A fake HTTP endpoint: answers each request from `answer` (request line,
/// body) and records the bodies.
struct FakeServer {
    origin: String,
    bodies: Arc<Mutex<Vec<String>>>,
}

impl FakeServer {
    fn start(mut answer: impl FnMut(&str) -> (u16, String) + Send + 'static) -> FakeServer {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind fake server");
        let origin = format!(
            "http://127.0.0.1:{}",
            listener.local_addr().expect("addr").port()
        );
        let bodies: Arc<Mutex<Vec<String>>> = Arc::default();
        let recorded = Arc::clone(&bodies);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(mut stream) = stream else { return };
                let Some((request_line, body)) = read_request(&stream) else {
                    continue;
                };
                let (status, reply) = answer(&request_line);
                recorded
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(body);
                let _ = write!(
                    stream,
                    "HTTP/1.1 {status} X\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n{reply}",
                    reply.len()
                );
            }
        });
        FakeServer { origin, bodies }
    }

    fn bodies(&self) -> Vec<String> {
        self.bodies
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

/// One HTTP request: its request line and its body (by `content-length`).
fn read_request(stream: &TcpStream) -> Option<(String, String)> {
    let mut reader = BufReader::new(stream);
    let mut request_line = String::new();
    reader.read_line(&mut request_line).ok()?;
    let mut length = 0usize;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line).ok()? == 0 {
            return None;
        }
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some((name, value)) = line.split_once(':') {
            if name.eq_ignore_ascii_case("content-length") {
                length = value.trim().parse().ok()?;
            }
        }
    }
    let mut body = vec![0u8; length];
    reader.read_exact(&mut body).ok()?;
    Some((
        request_line.trim_end().to_owned(),
        String::from_utf8(body).ok()?,
    ))
}

/// The device login prints the verification URL and code, then polls the
/// token endpoint until the user approves.
#[test]
fn the_device_login_prints_the_code_and_polls() {
    let world = World::new();
    let mut polls = 0;
    let auth = FakeServer::start(move |request_line| {
        if request_line.starts_with("POST /oauth2/device/code ") {
            return (
                200,
                json!({
                    "device_code": "device-1",
                    "user_code": "ABCD-1234",
                    "verification_uri": "https://device.example/activate",
                    "expires_in": 600,
                    "interval": 1,
                })
                .to_string(),
            );
        }
        if !request_line.starts_with("POST /oauth2/token ") {
            return (404, String::new());
        }
        polls += 1;
        if polls == 1 {
            return (400, json!({ "error": "authorization_pending" }).to_string());
        }
        (
            200,
            json!({ "access_token": "xai-access", "refresh_token": "xai-refresh", "expires_in": 3600 })
                .to_string(),
        )
    });
    let mut command = world.eukhe(&["login", "xai", "--no-browser"]);
    command.env("EUKHE_XAI_AUTH_URL", &auth.origin);
    let output = finish(command.spawn().expect("eukhe starts"));
    let line = one_line(&output);
    assert!(
        line.starts_with("Logged in to xAI (Grok) as ") && line.ends_with(&world.saved_to()),
        "{line}"
    );
    let stderr = text(&output.stderr);
    assert!(
        stderr.contains("https://device.example/activate\nEnter code: ABCD-1234\n"),
        "{stderr}"
    );
    assert_eq!(auth.bodies().len(), 3, "the code request and two polls");
    let accounts = world.accounts("xai");
    assert_eq!(
        (accounts.len(), &accounts[0]["access"]),
        (1, &json!("xai-access"))
    );
}

/// `logout` takes a place or identity; a provider with several accounts
/// and none named lists them.
#[test]
fn logout_names_one_account() {
    let world = World::new();
    for key in ["sk-logout-key-111111", "sk-logout-key-222222"] {
        let mut command = world.eukhe(&["login", "openai"]);
        command.env("EUKHE_LOGIN_API_KEY", key);
        one_line(&finish(command.spawn().expect("eukhe starts")));
    }
    let unnamed = world.run(&["logout", "openai"], "");
    assert_eq!(unnamed.status.code(), Some(1), "{}", text(&unnamed.stderr));
    let second = world.run(&["logout", "openai", "2"], "");
    assert_eq!(second.status.code(), Some(0), "{}", text(&second.stderr));
    let keys: Vec<Value> = world
        .accounts("openai")
        .iter()
        .map(|account| account["key"].clone())
        .collect();
    assert_eq!(keys, vec![json!("sk-logout-key-111111")]);
}
