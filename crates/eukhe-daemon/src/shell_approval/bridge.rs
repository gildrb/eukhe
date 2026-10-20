//! The bridge between the routing of approval questions and its Bend
//! model (`bend/approvals.bend`, laws `laws/approvals.bend`, G5, proved in
//! `PROOF.bend`): both run the same chains of sessions and must print the
//! same transcript, byte for byte (`bend/bridge_approvals.bend` documents
//! the format). A chain is real [`ShellApprovals`], one per session, from
//! the subagent that asks up to its root; each hands a question up through
//! its parent's real `relay_shell_approval` handler (in place of the
//! supervisor link, which only carries the command). The clients of each
//! session are away (none attached), leave without an answer, deny, or
//! approve (with the phone gateway attached beside them in every other
//! session), or the session's only client is the phone gateway, or its
//! interactive clients leave while the gateway stays. The step writes,
//! runs a program, writes a protected path, or reads a secret. Every
//! chain of up to 3 sessions runs with each step, then generated longer
//! ones.

use std::fmt::Write as _;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::shell::{
    ShellAnswer, ShellApprovalRequest, ShellEffect, ShellEffects, ShellVerdict,
};
use futures::FutureExt as _;
use serde_json::{json, Value};

use super::{Relay, ShellApprovals};
use crate::worker::{EventPump, SessionCore};

/// The name of the session that asks (session 0).
const ASKER: &str = "scout";

/// The steps a question asks about, as effect codes
/// (bend/tools.bend `Eff.code`): a write, a run of a program, a write of a
/// protected path, a read of a secret.
const STEPS: [&[u8]; 4] = [&[1], &[2], &[1, 5], &[0, 6]];

/// What the clients of one session do with a question
/// (bend/approvals.bend `Desk`).
#[derive(Debug, Clone, Copy)]
enum Desk {
    /// No client attached.
    Away,
    /// Clients get it and all detach without an answer.
    Left,
    /// Clients get it and the first answer is this verdict.
    Says(ShellVerdict),
    /// The phone gateway is the only client.
    Phone,
    /// Interactive clients get it and all detach without an answer; the
    /// phone gateway stays.
    PhoneLeft,
}

impl Desk {
    /// The desk of a code of `bend/bridge_approvals.bend`.
    fn of(code: u64) -> Self {
        match code {
            0 => Self::Away,
            1 => Self::Left,
            2 => Self::Says(ShellVerdict::Deny),
            3 => Self::Says(ShellVerdict::Approve),
            4 => Self::Phone,
            _ => Self::PhoneLeft,
        }
    }

    /// The desk's code in the events.
    fn code(self) -> u8 {
        match self {
            Self::Away => 0,
            Self::Left => 1,
            Self::Says(ShellVerdict::Deny) => 2,
            Self::Says(ShellVerdict::Approve) => 3,
            Self::Phone => 4,
            Self::PhoneLeft => 5,
        }
    }
}

/// The transcript of one question, and the session whose clients
/// answered it.
#[derive(Default)]
struct Log {
    lines: String,
    answered: Option<usize>,
}

/// One session's clients: wait for the question's frame, note it (and
/// whether it names the subagent that asks), then do what `desk` says.
async fn clients(
    at: usize,
    desk: Desk,
    approvals: ShellApprovals,
    core: Arc<Mutex<SessionCore>>,
    mut frames: tokio::sync::broadcast::Receiver<Arc<crate::worker::OutboundFrame>>,
    log: Arc<Mutex<Log>>,
) {
    let Ok(frame) = frames.recv().await else {
        return;
    };
    let payload: Value = serde_json::from_slice(&frame.payload).unwrap();
    let named = match payload.get("agent").and_then(Value::as_str) {
        None => "0",
        Some(ASKER) => "1",
        Some(_) => "?",
    };
    {
        let mut log = log.lock().unwrap_or_else(PoisonError::into_inner);
        writeln!(log.lines, "shown {at} named {named}").unwrap();
        if let Desk::Says(_) = desk {
            log.answered = Some(at);
        }
    }
    match desk {
        Desk::Away | Desk::Phone => {}
        // The interactive client detaches; a gateway stays.
        Desk::Left | Desk::PhoneLeft => {
            let mut guard = core.lock().unwrap_or_else(PoisonError::into_inner);
            let core = &mut *guard;
            core.attached_client_ids
                .retain(|id| core.gateway_client_ids.contains(id));
            approvals.release_if_no_interactive_client(core);
        }
        Desk::Says(verdict) => {
            let answered = approvals.answer(&json!({
                "requestId": payload["request"]["requestId"],
                "verdict": verdict,
            }));
            assert!(answered.success, "{answered:?}");
        }
    }
}

/// Ask one question about a step with the effects of `codes` from the
/// first session of `chain` and return what happened, as
/// `bend/bridge_approvals.bend` prints it.
async fn ask(codes: &[u8], chain: &[Desk]) -> String {
    let log = Arc::new(Mutex::new(Log::default()));
    let mut tasks = Vec::new();
    // From the root down: each session's relay is its parent's handler.
    let mut parent: Option<(String, ShellApprovals)> = None;
    for (at, &desk) in chain.iter().enumerate().rev() {
        let mut core = SessionCore::test_core("/tmp".to_string());
        core.session_name = Some(if at == 0 {
            ASKER.to_string()
        } else {
            format!("s{at}")
        });
        let client = match desk {
            Desk::Away | Desk::Phone => None,
            Desk::Left | Desk::Says(_) | Desk::PhoneLeft => Some(format!("client-{at}")),
        };
        let gateway = match desk {
            Desk::Phone | Desk::PhoneLeft => true,
            // Every other session that answers has the gateway beside its
            // client: the client is asked all the same.
            Desk::Says(_) => at % 2 == 1,
            Desk::Away | Desk::Left => false,
        }
        .then(|| format!("gateway-{at}"));
        core.attached_client_ids = client.into_iter().chain(gateway.clone()).collect();
        core.gateway_client_ids = gateway.into_iter().collect();
        let relay: Relay = match parent.take() {
            Some((parent_id, parent)) => {
                core.parent_session_id = Some(parent_id.clone());
                Arc::new(move |command: Value| {
                    let (parent, parent_id) = (parent.clone(), parent_id.clone());
                    async move {
                        let to = command.get("activeSessionId").and_then(Value::as_str);
                        anyhow::ensure!(to == Some(parent_id.as_str()), "relayed to {to:?}");
                        Ok(parent.relay(&command).await)
                    }
                    .boxed()
                })
            }
            None => {
                Arc::new(|command| async move { anyhow::bail!("a root relayed {command}") }.boxed())
            }
        };
        let core = Arc::new(Mutex::new(core));
        let approvals = ShellApprovals::new(
            Arc::clone(&core),
            Arc::new(EventPump::new()),
            format!("live-{at}"),
            relay,
        );
        let frames = approvals.events.subscribe();
        tasks.push(tokio::spawn(clients(
            at,
            desk,
            approvals.clone(),
            core,
            frames,
            Arc::clone(&log),
        )));
        parent = Some((format!("session-{at}"), approvals));
    }
    let (_, asker) = parent.expect("a chain has a session");
    // A question that waits (a session asked a client that never answers)
    // fails the bridge at once instead of hanging it.
    let answer = tokio::time::timeout(
        std::time::Duration::from_secs(10),
        asker.ask(ShellApprovalRequest {
            request_id: "call-1:0".to_string(),
            step: 0,
            command: "touch a".to_string(),
            effects: ShellEffects::of(
                &codes
                    .iter()
                    .map(|&code| ShellEffect::ALL[usize::from(code)])
                    .collect::<Vec<_>>(),
            ),
        }),
    )
    .await;
    for task in tasks {
        task.abort();
    }
    let log = log.lock().unwrap_or_else(PoisonError::into_inner);
    let at = log
        .answered
        .map_or_else(|| "-".to_string(), |at| at.to_string());
    let end = match (answer, log.answered) {
        (Ok(ShellAnswer::Approve), Some(_)) => format!("end approve {at}"),
        // No client answered: the gateway rule let the step run.
        (Ok(ShellAnswer::Approve), None) => "end ruled run".to_string(),
        (Ok(ShellAnswer::Deny), _) => format!("end deny {at}"),
        (Ok(ShellAnswer::Unanswered), _) => "end unanswered".to_string(),
        (Ok(ShellAnswer::GatewayRefused), _) => "end ruled refuse".to_string(),
        (Err(_), _) => panic!(
            "the question of chain {chain:?} with effects {codes:?} waited: {}",
            log.lines
        ),
    };
    format!("{}{end}\n", log.lines)
}

/// One scenario: a question per step and chain.
async fn scenario(name: &str, questions: &[(&[u8], Vec<Desk>)]) -> Scenario {
    let mut events = String::new();
    let mut transcript = String::new();
    for (codes, chain) in questions {
        let effects: Vec<String> = codes.iter().map(ToString::to_string).collect();
        let desks: Vec<String> = chain.iter().map(|desk| desk.code().to_string()).collect();
        writeln!(events, "q {} {}", effects.join(","), desks.join(" ")).unwrap();
        transcript.push_str(&ask(codes, chain).await);
    }
    Scenario {
        name: name.to_string(),
        events,
        transcript,
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn the_approval_route_is_its_model() {
    // Every chain of 1 to 3 sessions, with each step.
    let mut small: Vec<(&[u8], Vec<Desk>)> = Vec::new();
    for length in 1..=3u32 {
        for index in 0..6u64.pow(length) {
            let chain: Vec<Desk> = (0..length)
                .map(|place| Desk::of(index / 6u64.pow(place) % 6))
                .collect();
            small.extend(STEPS.iter().map(|&codes| (codes, chain.clone())));
        }
    }
    // Longer ones, mostly away (a subagent's ancestors rarely have
    // clients): 4 to 7 sessions.
    let mut rng = Rng(0x0a99_2026);
    let long: Vec<(&[u8], Vec<Desk>)> = (0..80)
        .map(|_| {
            let codes = rng.pick(&STEPS).expect("steps");
            let chain = (0..rng.range(4, 7))
                .map(|_| {
                    if rng.chance(60) {
                        Desk::Away
                    } else {
                        Desk::of(rng.range(1, 5))
                    }
                })
                .collect();
            (codes, chain)
        })
        .collect();
    let scenarios = vec![
        scenario("chains of 1 to 3", &small).await,
        scenario("longer chains", &long).await,
    ];
    compare("bend/bridge_approvals.bend", scenarios);
}
