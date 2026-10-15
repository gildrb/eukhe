//! A supervisor wire client whose reader runs on its own thread: every
//! line lands in one ordered log the test waits on (responses by id,
//! session events by predicate), so no wait ever drops a frame another
//! wait needs, and a dead supervisor shows as a closed log, not a hang.

#![allow(dead_code)] // each including test binary uses its own subset

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[derive(Default)]
struct Lines {
    lines: Vec<Value>,
    closed: bool,
}

struct Shared {
    lines: Mutex<Lines>,
    changed: Condvar,
}

impl Shared {
    fn lock(&self) -> MutexGuard<'_, Lines> {
        self.lines.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

pub struct WireClient {
    writer: UnixStream,
    shared: Arc<Shared>,
    next_id: u64,
}

impl WireClient {
    /// Connect and read the hello.
    pub fn connect(socket: &Path) -> WireClient {
        let stream = UnixStream::connect(socket).expect("connect the supervisor");
        let reader = stream.try_clone().expect("clone the socket");
        let shared = Arc::new(Shared {
            lines: Mutex::new(Lines::default()),
            changed: Condvar::new(),
        });
        let feed = Arc::clone(&shared);
        std::thread::spawn(move || {
            let mut reader = BufReader::new(reader);
            loop {
                let mut line = String::new();
                match reader.read_line(&mut line) {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {
                        let Ok(value) = serde_json::from_str::<Value>(line.trim()) else {
                            continue;
                        };
                        feed.lock().lines.push(value);
                        feed.changed.notify_all();
                    }
                }
            }
            feed.lock().closed = true;
            feed.changed.notify_all();
        });
        let client = WireClient {
            writer: stream,
            shared,
            next_id: 0,
        };
        let hello = client.wait_line(Duration::from_secs(30), "the daemon hello", |line| {
            line["type"] == "daemon_hello"
        });
        assert_eq!(hello["type"], "daemon_hello");
        client
    }

    /// Send `command`; answers its id.
    pub fn send(&mut self, command: &Value) -> String {
        self.next_id += 1;
        let id = format!("c{}", self.next_id);
        let mut line = serde_json::to_string(&json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        }))
        .expect("serialize the command");
        line.push('\n');
        self.writer
            .write_all(line.as_bytes())
            .expect("send the command");
        id
    }

    /// Send `command` and wait for its response.
    pub fn request(&mut self, command: &Value, budget: Duration) -> Value {
        let id = self.send(command);
        self.response(&id, budget)
    }

    pub fn response(&self, id: &str, budget: Duration) -> Value {
        self.wait_line(budget, &format!("the response to {id}"), |line| {
            line["id"] == id && line["type"] == "response"
        })
    }

    /// The response to `id` if it already arrived.
    pub fn try_response(&self, id: &str) -> Option<Value> {
        self.shared
            .lock()
            .lines
            .iter()
            .find(|line| line["id"] == id && line["type"] == "response")
            .cloned()
    }

    /// Wait for the first line matching `probe`.
    pub fn wait_line(&self, budget: Duration, what: &str, probe: impl Fn(&Value) -> bool) -> Value {
        self.wait_line_from(0, budget, what, probe).1
    }

    /// Wait for the first line at or after `from` matching `probe`;
    /// answers its index and the line.
    pub fn wait_line_from(
        &self,
        from: usize,
        budget: Duration,
        what: &str,
        probe: impl Fn(&Value) -> bool,
    ) -> (usize, Value) {
        let deadline = Instant::now() + budget;
        let mut lines = self.shared.lock();
        loop {
            if let Some(index) = lines.lines.iter().skip(from).position(&probe) {
                return (from + index, lines.lines[from + index].clone());
            }
            assert!(!lines.closed, "the connection closed before {what}");
            let now = Instant::now();
            assert!(now < deadline, "{what} never arrived");
            lines = self
                .shared
                .changed
                .wait_timeout(lines, deadline - now)
                .unwrap_or_else(PoisonError::into_inner)
                .0;
        }
    }

    /// Wait for a session event matching `probe` at or after line `from`.
    pub fn wait_event_from(
        &self,
        from: usize,
        budget: Duration,
        what: &str,
        probe: impl Fn(&Value) -> bool,
    ) -> (usize, Value) {
        let (index, line) = self.wait_line_from(from, budget, what, |line| {
            line["type"] == "session_event" && probe(&line["event"])
        });
        (index, line["event"].clone())
    }

    /// Lines received so far.
    pub fn len(&self) -> usize {
        self.shared.lock().lines.len()
    }

    /// The session events received so far, from line `from`.
    pub fn events_from(&self, from: usize) -> Vec<Value> {
        self.shared
            .lock()
            .lines
            .iter()
            .skip(from)
            .filter(|line| line["type"] == "session_event")
            .map(|line| line["event"].clone())
            .collect()
    }

    /// Wait until the client holds more than `seen` lines (or the
    /// connection closed), at most `timeout`; answers whether it does.
    pub fn wait_beyond(&self, seen: usize, timeout: Duration) -> bool {
        let lines = self.shared.lock();
        let (lines, _) = self
            .shared
            .changed
            .wait_timeout_while(lines, timeout, |lines| {
                lines.lines.len() <= seen && !lines.closed
            })
            .unwrap_or_else(PoisonError::into_inner);
        lines.lines.len() > seen
    }
}
