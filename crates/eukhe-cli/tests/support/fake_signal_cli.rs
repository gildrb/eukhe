//! A fake `signal-cli` for the gateway e2e tests, speaking what the
//! gateway speaks (`crates/eukhe-gateway/src/signal/rpc.rs`): the gateway
//! starts `<cliPath> -a <account> jsonRpc` and exchanges newline-delimited
//! JSON-RPC 2.0 over the child's stdio - its requests on the child's stdin
//! (`send`, `sendTyping`, `sendReceipt`), the answers by id and the
//! `receive` notifications (receive mode on-start: `params {envelope,
//! account}`) on its stdout.
//!
//! `cliPath` is a `/bin/sh` script (shell builtins only, so it runs under an
//! `env -i` PATH) that relays its stdin into one FIFO and a second FIFO into
//! its stdout, line by line; the test end serves both FIFOs. A plain line
//! loop on purpose: an earlier harness relayed a Unix socket into the
//! child's stdout pipe with `std::io::copy` (Linux takes its `splice` path
//! there), and the gateway never got the phone's first line: the socket's
//! queue was drained, the pipe stayed empty, so the gateway answered
//! nothing, not even a phone command. A read/write loop delivers each line.
//!
//! The phone side ([`FakeSignalCli::say`], [`FakeSignalCli::wait_reply`],
//! [`FakeSignalCli::settle_run`]) is what assertions use: send a text, wait
//! for the reply that contains X, and read every reply of the run once it
//! ended (to assert none contains Y).

#![allow(dead_code)] // each including test binary uses its own subset

use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

/// How long the phone waits for anything the gateway must do.
pub const WAIT: Duration = Duration::from_secs(90);

/// What the gateway asked `signal-cli` to do, in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Seen {
    /// `send`: a message to the phone.
    Sent { recipient: String, text: String },
    /// `sendTyping`: the typing indicator started (`stop` false) or stopped.
    Typing { stop: bool },
    /// `sendReceipt`: the read receipt of the phone message sent at
    /// `timestamp`.
    Receipt { timestamp: u64 },
    /// A method the fake does not implement (answered with JSON-RPC error
    /// -32601, as `signal-cli` answers an unknown method).
    Other { method: String },
}

#[derive(Default)]
struct State {
    seen: Vec<Seen>,
    /// The running child's stdout (the FIFO its relay reads); `None` while
    /// no child runs.
    to_gateway: Option<File>,
    /// Children that started (the gateway restarts one that exits).
    started: usize,
}

struct Shared {
    state: Mutex<State>,
    changed: Condvar,
}

impl Shared {
    fn lock(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Wait until `ready` returns a value, at most [`WAIT`]; `what` names
    /// the wait in the panic, with everything the gateway did.
    fn wait_for<T>(&self, what: &str, mut ready: impl FnMut(&State) -> Option<T>) -> T {
        let deadline = Instant::now() + WAIT;
        let mut state = self.lock();
        loop {
            if let Some(value) = ready(&state) {
                return value;
            }
            let left = deadline.saturating_duration_since(Instant::now());
            assert!(
                !left.is_zero(),
                "{what}: not within {WAIT:?}; the gateway did {:#?}",
                state.seen
            );
            state = self
                .changed
                .wait_timeout(state, left)
                .unwrap_or_else(PoisonError::into_inner)
                .0;
        }
    }
}

/// One phone message: where the gateway's log stood when it went out, and
/// its Signal timestamp (the id the gateway's read receipt names).
#[derive(Debug, Clone, Copy)]
pub struct Said {
    from: usize,
    timestamp: u64,
}

/// The test's end of the fake, and the phone of `sender`.
pub struct FakeSignalCli {
    /// The script `gateway.signal.cliPath` names.
    pub cli_path: PathBuf,
    account: String,
    sender: String,
    shared: Arc<Shared>,
    next_timestamp: Mutex<u64>,
}

impl Drop for FakeSignalCli {
    fn drop(&mut self) {
        // EOF on the child's stdout relay: a child the gateway left behind
        // ends with the test.
        self.shared.lock().to_gateway = None;
    }
}

impl FakeSignalCli {
    /// Make the FIFOs and the `cliPath` script in `dir` and serve them:
    /// `account` is the gateway's account, `sender` the phone (an allowed
    /// contact).
    pub fn start(dir: &Path, account: &str, sender: &str) -> FakeSignalCli {
        let from_gateway = dir.join("signal-cli.in");
        let to_gateway = dir.join("signal-cli.out");
        for fifo in [&from_gateway, &to_gateway] {
            nix::unistd::mkfifo(fifo.as_path(), nix::sys::stat::Mode::S_IRWXU)
                .expect("make a FIFO");
        }
        let cli_path = dir.join("signal-cli");
        std::fs::write(
            &cli_path,
            format!(
                "#!/bin/sh\n\
                 if [ \"$#\" -ne 3 ] || [ \"$1\" != -a ] || [ \"$2\" != '{account}' ] || [ \"$3\" != jsonRpc ]; then\n\
                 \techo \"fake signal-cli: unexpected arguments: $*\" >&2\n\
                 \texit 2\n\
                 fi\n\
                 while IFS= read -r line; do printf '%s\\n' \"$line\"; done <'{to}' &\n\
                 exec >'{from}'\n\
                 while IFS= read -r line; do printf '%s\\n' \"$line\"; done\n",
                to = to_gateway.display(),
                from = from_gateway.display(),
            ),
        )
        .expect("write the fake signal-cli");
        std::fs::set_permissions(&cli_path, std::fs::Permissions::from_mode(0o755))
            .expect("make the fake signal-cli executable");
        let shared = Arc::new(Shared {
            state: Mutex::default(),
            changed: Condvar::new(),
        });
        let served = Arc::clone(&shared);
        std::thread::spawn(move || loop {
            // Each child opens both FIFOs: its stdin relay the first, its
            // stdout relay the second; the opens pair up in that order.
            let Ok(requests) = File::open(&from_gateway) else {
                return;
            };
            let Ok(answers) = std::fs::OpenOptions::new().write(true).open(&to_gateway) else {
                return;
            };
            {
                let mut state = served.lock();
                state.to_gateway = Some(answers);
                state.started += 1;
            }
            served.changed.notify_all();
            serve(BufReader::new(requests), &served);
            served.lock().to_gateway = None;
        });
        FakeSignalCli {
            cli_path,
            account: account.to_owned(),
            sender: sender.to_owned(),
            shared,
            next_timestamp: Mutex::new(1_700_000_000_000),
        }
    }

    /// Wait until the gateway started `signal-cli`.
    pub fn wait_started(&self) {
        self.shared
            .wait_for("the gateway starts signal-cli", |state| {
                (state.started > 0).then_some(())
            });
    }

    /// Everything the gateway did so far.
    pub fn seen(&self) -> Vec<Seen> {
        self.shared.lock().seen.clone()
    }

    /// The phone sends `text` (a direct message to the account).
    pub fn say(&self, text: &str) -> Said {
        let timestamp = {
            let mut next = self
                .next_timestamp
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            *next += 1;
            *next
        };
        let notification = json!({
            "jsonrpc": "2.0",
            "method": "receive",
            "params": {
                "account": self.account,
                "envelope": {
                    "source": self.sender,
                    "sourceNumber": self.sender,
                    "sourceName": "Phone",
                    "sourceDevice": 1,
                    "timestamp": timestamp,
                    "dataMessage": {
                        "timestamp": timestamp,
                        "message": text,
                        "expiresInSeconds": 0,
                        "viewOnce": false,
                    },
                },
            },
        });
        let mut state = self.shared.lock();
        let from = state.seen.len();
        let stream = state
            .to_gateway
            .as_mut()
            .expect("signal-cli runs (wait_started first)");
        writeln!(stream, "{notification}").expect("deliver the phone message");
        Said { from, timestamp }
    }

    /// Wait for the first message to the phone after `said` that contains
    /// `needle`; its text.
    pub fn wait_reply(&self, said: &Said, needle: &str) -> String {
        self.shared
            .wait_for(&format!("a reply containing {needle:?}"), |state| {
                sent_texts(&state.seen[said.from..])
                    .find(|text| text.contains(needle))
                    .map(str::to_owned)
            })
    }

    /// Wait until the run `said` started has ended and every event the
    /// daemon sent by the end of a session read after it reached the phone;
    /// every message the phone got since `said`, in order.
    ///
    /// The run ended when the gateway stopped the typing indicator (it
    /// does at the run's `agent_end`). Messages of the run's end may still
    /// be on their way (the daemon sends them after `agent_end`): the phone
    /// then sends `/status`, whose session read the daemon answers after
    /// every event it sent before, and two blank messages (the gateway
    /// ignores them). Each phone message is handled whole before the next
    /// one starts, and its handling first relays the daemon events that
    /// came in, so the second blank message's read receipt means every
    /// event before the status read reached the phone. The status reply
    /// itself is left out.
    ///
    /// The end-of-run message of irreversible effects is not among them:
    /// the daemon's run service reports a run's end on its own time, after
    /// `agent_end`, so the status read can come first. A run that sends it
    /// waits for it ([`Self::wait_reply`]) before settling.
    pub fn settle_run(&self, said: &Said) -> Vec<String> {
        self.shared.wait_for("the run ends", |state| {
            state.seen[said.from..]
                .contains(&Seen::Typing { stop: true })
                .then_some(())
        });
        let status = self.say("/status");
        let first_blank = self.say(" ");
        let last_blank = self.say(" ");
        let seen = self.shared.wait_for("the barrier's read receipt", |state| {
            receipt_at(&state.seen, last_blank.timestamp).map(|at| state.seen[..at].to_vec())
        });
        let status_from = receipt_at(&seen, status.timestamp).expect("the status read receipt");
        let status_to =
            receipt_at(&seen, first_blank.timestamp).expect("the blank message's read receipt");
        let Some(status_at) = seen[status_from..status_to].iter().rposition(
            |seen| matches!(seen, Seen::Sent { text, .. } if text.starts_with("Session: ")),
        ) else {
            panic!("the /status reply: {seen:#?}");
        };
        let status_reply = status_from + status_at;
        seen.iter()
            .enumerate()
            .skip(said.from)
            .filter(|(at, _)| *at != status_reply)
            .filter_map(|(_, seen)| match seen {
                Seen::Sent { text, .. } => Some(text.clone()),
                Seen::Typing { .. } | Seen::Receipt { .. } | Seen::Other { .. } => None,
            })
            .collect()
    }

    /// [`Self::settle_run`], then assert no message of the run contains
    /// `needle`; the run's messages.
    pub fn assert_run_never_says(&self, said: &Said, needle: &str) -> Vec<String> {
        let replies = self.settle_run(said);
        assert!(
            !replies.iter().any(|text| text.contains(needle)),
            "no message of the run contains {needle:?}: {replies:#?}"
        );
        replies
    }
}

/// The texts of the `send` requests in `seen`.
fn sent_texts(seen: &[Seen]) -> impl Iterator<Item = &str> {
    seen.iter().filter_map(|seen| match seen {
        Seen::Sent { text, .. } => Some(text.as_str()),
        Seen::Typing { .. } | Seen::Receipt { .. } | Seen::Other { .. } => None,
    })
}

/// Where the read receipt of the phone message sent at `timestamp` is.
fn receipt_at(seen: &[Seen], timestamp: u64) -> Option<usize> {
    seen.iter()
        .position(|seen| *seen == Seen::Receipt { timestamp })
}

/// Answer one child's requests until its stdin relay closes.
fn serve(requests: BufReader<File>, shared: &Shared) {
    let mut timestamp = 1_800_000_000_000u64;
    for line in requests.lines() {
        let Ok(line) = line else { return };
        let request: Value = serde_json::from_str(&line)
            .unwrap_or_else(|error| panic!("the gateway wrote a non-JSON line ({error}): {line}"));
        assert_eq!(request["jsonrpc"], "2.0", "a JSON-RPC 2.0 request: {line}");
        let id = request["id"].clone();
        assert!(id.is_u64(), "a request with a numeric id: {line}");
        let params = &request["params"];
        let (seen, key, outcome) = match request["method"].as_str().unwrap_or_default() {
            "send" => {
                timestamp += 1;
                let recipient = params["recipient"][0].as_str().unwrap_or_default();
                (
                    Seen::Sent {
                        recipient: recipient.to_owned(),
                        text: params["message"].as_str().unwrap_or_default().to_owned(),
                    },
                    "result",
                    json!({ "timestamp": timestamp }),
                )
            }
            "sendTyping" => (
                Seen::Typing {
                    stop: params["stop"].as_bool().unwrap_or(false),
                },
                "result",
                json!({}),
            ),
            "sendReceipt" => (
                Seen::Receipt {
                    timestamp: params["targetTimestamp"][0].as_u64().unwrap_or_default(),
                },
                "result",
                json!({}),
            ),
            method => (
                Seen::Other {
                    method: method.to_owned(),
                },
                "error",
                json!({ "code": -32601, "message": "Method not implemented" }),
            ),
        };
        let mut answer = json!({ "jsonrpc": "2.0", "id": id });
        answer[key] = outcome;
        let mut state = shared.lock();
        state.seen.push(seen);
        shared.changed.notify_all();
        let Some(stream) = state.to_gateway.as_mut() else {
            return;
        };
        if writeln!(stream, "{answer}").is_err() {
            return;
        }
    }
}
