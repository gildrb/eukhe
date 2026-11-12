//! The `/budget` command: show this session's budget, set one, add to it,
//! or audit its ledger. The daemon owns the ledger: the command sends
//! `get_budget`, `set_budget`, `add_budget` or `audit_budget` and shows
//! the reply as one row (the time left and the deadline of a budget with
//! a time limit included). The report it gets also moves the status
//! line's budget segment, like every `budget_update` after it.
use super::{AgentView, DaemonCommand, Duration, Map, SessionUi, Value, UI_REQUEST_TIMEOUT_MS};
use crate::budget_text;
use crate::glyphs::SEP;
use eukhe_types::budget::{BudgetAmounts, BudgetDimension, BudgetReport};
use eukhe_types::daemon::BudgetAudit;
use serde::Deserialize;

/// What a `/budget` line the command does not read is answered with.
const USAGE: &str = "Usage: /budget [set|add cost=<dollars> tokens=<n> time=<duration> calls=<n> requests=<n> | audit]";

impl SessionUi {
    /// `/budget`: the report line, or `no budget set`. `/budget set
    /// cost=2 tokens=200k time=10m calls=50 requests=30` (any subset)
    /// gives a session without a budget one (time: a deadline that far
    /// from now); `/budget add cost=1 time=10m` adds to it (time moves the
    /// deadline); `/budget audit` replays the ledger. A line that does not
    /// parse stays in the editor with its error; a refusal of the daemon
    /// is the error row.
    pub(super) async fn handle_budget_command(
        &mut self,
        args: &str,
        text: &str,
        view: &mut AgentView,
    ) {
        let (verb, words) = args
            .split_once(char::is_whitespace)
            .map_or((args, ""), |(verb, words)| (verb, words.trim()));
        let active_session_id = self.active_session_id.clone();
        let command = match (verb, budget_text::parse_assignments(words)) {
            ("", _) => DaemonCommand::GetBudget {
                id: None,
                active_session_id,
                rest: Map::default(),
            },
            ("audit", _) if words.is_empty() => DaemonCommand::AuditBudget {
                id: None,
                active_session_id,
                rest: Map::default(),
            },
            ("set", Ok(limits)) => DaemonCommand::SetBudget {
                id: None,
                active_session_id,
                limits,
                rest: Map::default(),
            },
            ("add", Ok(limits)) => DaemonCommand::AddBudget {
                id: None,
                active_session_id,
                amounts: BudgetDimension::ALL.into_iter().fold(
                    BudgetAmounts::default(),
                    |amounts, dimension| {
                        amounts.with(dimension, limits.get(dimension).unwrap_or(0))
                    },
                ),
                rest: Map::default(),
            },
            ("set" | "add", Err(error)) => {
                view.editor.set_text(text);
                self.error_row(&error.to_string(), view);
                return;
            }
            _ => {
                view.editor.set_text(text);
                self.error_row(USAGE, view);
                return;
            }
        };
        let data = match self
            .bounded_request(Duration::from_millis(UI_REQUEST_TIMEOUT_MS), command)
            .await
        {
            Ok(data) => data,
            Err(error) => {
                self.error_row(&format!("{error:#}"), view);
                return;
            }
        };
        if verb == "audit" {
            match BudgetAudit::deserialize(data.get("audit").unwrap_or(&Value::Null)) {
                Ok(audit) => self.note(&budget_text::audit_line(&audit), view),
                Err(error) => {
                    self.error_row(&format!("the audit reply does not read: {error}"), view);
                }
            }
            return;
        }
        // `budget` is the report after the command, `null` without a
        // budget.
        let report = data
            .get("budget")
            .filter(|budget| !budget.is_null())
            .map(BudgetReport::deserialize)
            .transpose();
        match report {
            Ok(report) => {
                let line = report.as_ref().map_or_else(
                    || "no budget set".to_string(),
                    |report| budget_text::report_detail(report, budget_text::now_ms(), SEP),
                );
                self.budget = report;
                view.chrome.budget.clone_from(&self.budget);
                self.note(&line, view);
            }
            Err(error) => {
                self.error_row(&format!("the budget reply does not read: {error}"), view);
            }
        }
    }
}
