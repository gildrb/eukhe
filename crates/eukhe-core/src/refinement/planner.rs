//! The refine planner: proposal parsing, edit validation, application, and
//! rollback. Port of the apply half of core/refinement/refinement.ts. The
//! decisions run as the compiled core (`eukhe_bend::rules::refine_plan`):
//! Rust reads the JSON, gives the facts, and mutates the state as told.

use eukhe_bend::rules::refine_plan as rule;
use serde::{Deserialize, Serialize};

use super::{
    AppliedRefinementEdit, HarnessEntry, HarnessRefinementEvent, HarnessScope, HarnessState,
    RefinementAction, RefinementKind,
};

pub const REFINEMENT_SYSTEM_PROMPT: &str = "You are Eukhe's /refine continual harness subsystem.\n\nYour job is to improve the editable continual harness state from the current trajectory.\nThis is similar in spirit to context compaction, but instead of summarizing the\nconversation you emit precise Create, Update, or Delete edits to reusable state.\nThe continual harness is the persistent, editable set of prompt notes, memories,\nskills, and subagent specs that lets Eukhe improve reusable behavior\noutside the token history.\nUse \"continual harness\" for that persistent artifact layer; keep \"RLM\" for the\nruntime, Python REPL kernel, and native call interface that executes those artifacts.\n\nContinual harness components:\n- prompt: supplemental prompt notes only. The base system prompt is immutable and MUST NOT be rewritten.\n- memory: durable facts, decisions, failures, preferences, and outcomes.\n- skill: installed Python REPL skill. Skill create/update edits MUST include a `reference` object with `{\"type\":\"python\"}`, a Python import, and a callable or call pattern; they also MUST include an `arguments` object describing accepted inputs, required fields, defaults, and constraints. Use `{}` for `arguments` only when the Python callable truly needs no external inputs. Include the RLM-native call form `await <skill_import>(...)`.\n- subagent: reusable delegation specs, including purpose, instructions, and when to invoke. Include the RLM-native call form: compose a concise task prompt and spawn with `handle = await rlm.spawn(\"sub-task\", name=\"worker\")`; admission returns immediately with `rlm_child_id`, `name`, `session_dir`, and `model`, never the child's answer. Results arrive only through explicit `agent_message` replies or files; children reply with `await agent_message.send(message, receiver_role=\"parent\")`. Use `await rlm.list_subagents()` to recover direct child handles and `await agent_message.send(..., receiver_role=\"child\", receiver_name=handle.name)` for follow-ups. Do not invent wrappers like `run_subagent(...)`.\n- factory: declarative state-machine workflow specs of subagent states. The spec lives in `arguments.machine` (the original DAG sugar in `arguments.dag` compiles to machine form; pass exactly one form). The kernel validator (`rlm.factory`) enforces the full machine semantics at write time: run a stored factory with `await rlm.factory.run('<id>')`, watch with `await rlm.factory.status(run_id)`, stop with `await rlm.factory.stop(run_id)`, and resume an escalate-paused run with `await rlm.factory.resume(run_id)`.\n\nScope and persistence policy:\n- The default editable continual harness store is local to the current Eukhe session. Use it for session-specific progress, active task state, current-run coordination notes, temporary blockers, and project facts that should not affect other sessions.\n- A caller may explicitly request global refinement. Global edits must be stable cross-session lessons, durable user preferences, reusable skills/subagents, or tool/environment facts that should affect future sessions.\n- Entry ids in the harness overview may carry a display-only `local:` or `global:` prefix. Always use the bare id (no prefix) in edits.\n- All edits in one refinement apply only to the requested scope's store. During a local refinement, global entries are read-only context: never propose update or delete edits for them; create a local entry instead when a session-specific override is genuinely needed.\n- Project/workspace-specific lessons may be persisted globally only when the title, path, or content explicitly names the project/workspace and the lesson is likely to be reused in future sessions for that project. Prefer local edits when the lesson only belongs in the current conversation.\n- Use memory for declarative facts and preferences, skill for repeatable procedures exposed as Python calls, prompt for narrow behavioral policy addendums, and subagent for reusable delegation roles.\n- Create or update the smallest relevant component: repeated delegation roles should become subagent specs, repeated procedures should become skills, durable facts/preferences should become memories, and narrow behavioral policies should become prompt addendums.\n- When an edit is persisted, include metadata such as `{\"scope\":\"local\"}` or `{\"scope\":\"global\"}` when that helps future review understand the intended blast radius.\n\nUse the trajectory, current continual harness state, and prior refinement history. Prefer\nsmall evidence-backed edits. If prior refinements caused issues, rollback or\nreplace the faulty editable entries. Never edit source files directly. Output\nJSON only with this exact shape:\n\n{\n  \"summary\": \"one sentence\",\n  \"rationale\": \"why these edits are justified by trajectory evidence\",\n  \"expectedOutcome\": \"what should improve and how to validate it\",\n  \"edits\": [\n    {\n      \"action\": \"create|update|delete\",\n      \"kind\": \"prompt|memory|skill|subagent|factory\",\n      \"id\": \"stable id for update/delete, optional for create\",\n      \"title\": \"required for create/update except delete\",\n      \"content\": \"required for create/update except delete\",\n      \"path\": \"optional grouping path\",\n      \"reference\": {\"type\": \"python\", \"import\": \"package.module\", \"callable\": \"function_name\", \"call_pattern\": \"await function_name(...)\"},\n      \"arguments\": {\"name\": {\"type\": \"string\", \"required\": true, \"description\": \"accepted input\"}},\n      \"metadata\": {},\n      \"reason\": \"why this edit is useful\"\n    }\n  ]\n}";

pub const AUTO_REFINE_REVIEW_SYSTEM_PROMPT: &str = "You are Eukhe's automatic /refine review gate.\n\nDecide whether this checkpoint should run /refine. Auto /refine writes local continual harness state by default, so approve when the trajectory contains evidence useful to this session's future turns.\nReject one-off noise, unsupported hypotheses, and transient tool outputs. Ask for global refinement only for durable cross-session lessons or explicitly project-qualified lessons likely to be reused in future sessions.\n\nReturn JSON only:\n{\n  \"shouldRefine\": true|false,\n  \"rationale\": \"short reason\",\n  \"instructions\": \"optional concise instructions for /refine if shouldRefine is true\"\n}";

/// Output caps (reasoning off shares the model's output budget with JSON).
pub const REFINEMENT_MAX_OUTPUT_TOKENS: u64 = 32_000;
pub const AUTO_REFINE_REVIEW_MAX_OUTPUT_TOKENS: u64 = 4_096;

pub const TRUNCATED_JSON_ERROR: &str = "the model stopped before completing its JSON object. This usually means the output budget was exhausted; retry with a smaller request.";

/// One proposed edit.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RefinementEdit {
    pub action: Option<RefinementAction>,
    pub kind: Option<RefinementKind>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub title: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub content: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reference: Option<serde_json::Map<String, serde_json::Value>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub arguments: Option<serde_json::Map<String, serde_json::Value>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub metadata: Option<serde_json::Map<String, serde_json::Value>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

/// The refiner's proposal.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct RefinementProposal {
    pub summary: String,
    pub rationale: String,
    pub expected_outcome: String,
    pub edits: Vec<RefinementEdit>,
}

/// Whether a JSON candidate ends mid-value (unterminated string, unclosed
/// object/array): a truncated reply, as opposed to a malformed-but-balanced
/// one. The compiled core scans it (`bend/refine_plan.bend`, R7).
#[must_use]
pub fn is_incomplete_json(candidate: &str) -> bool {
    rule::incomplete(candidate)
}

fn parse_json_candidate(candidate: &str) -> Result<serde_json::Value, String> {
    match serde_json::from_str::<serde_json::Value>(candidate) {
        Ok(value) => Ok(value),
        Err(error) => {
            if is_incomplete_json(candidate) {
                Err(TRUNCATED_JSON_ERROR.to_string())
            } else {
                Err(format!("the model did not return valid JSON: {error}"))
            }
        }
    }
}

/// Extract the proposal JSON from a reply: direct, fenced, or brace-sliced
/// out of prose (with truncation diagnosed against the original text).
///
/// # Errors
///
/// Returns a human-readable error string when the reply contains no JSON
/// object, the candidate JSON is invalid, or the reply looks truncated.
pub fn extract_json_object(text: &str) -> Result<serde_json::Value, String> {
    let trimmed = text.trim();
    if trimmed.starts_with('{') && trimmed.ends_with('}') {
        return parse_json_candidate(trimmed);
    }
    // Fenced block: ``` or ```json ... ```.
    if let Some(start) = trimmed.find("```") {
        let after_fence = &trimmed[start + 3..];
        let after_lang = after_fence.trim_start_matches("json").trim_start();
        if let Some(end) = after_lang.find("```") {
            return parse_json_candidate(after_lang[..end].trim());
        }
    }
    let start = trimmed.find('{');
    let end = trimmed.rfind('}');
    if let (Some(start), Some(end)) = (start, end) {
        if end > start {
            if let Ok(value) = serde_json::from_str::<serde_json::Value>(&trimmed[start..=end]) {
                return Ok(value);
            }
            return parse_json_candidate(&trimmed[start..]);
        }
    }
    if is_incomplete_json(trimmed) {
        return Err(TRUNCATED_JSON_ERROR.to_string());
    }
    Err("Refiner did not return a JSON object".to_string())
}

/// Normalize an untrusted proposal, preserving invalid edit fields for
/// apply-time validation.
#[must_use]
pub fn normalize_refinement_proposal(value: &serde_json::Value) -> RefinementProposal {
    let record = value.as_object();
    let text = |key: &str| {
        record
            .and_then(|record| record.get(key))
            .and_then(serde_json::Value::as_str)
    };
    let texts = rule::norm(text("summary"), text("rationale"), text("expectedOutcome"));
    let edits = record
        .and_then(|record| record.get("edits"))
        .and_then(serde_json::Value::as_array)
        .map(|edits| {
            edits
                .iter()
                .filter(|edit| edit.is_object())
                .filter_map(|edit| serde_json::from_value::<RefinementEdit>(edit.clone()).ok())
                .collect()
        })
        .unwrap_or_default();
    RefinementProposal {
        summary: texts.summary,
        rationale: texts.rationale,
        expected_outcome: texts.outcome,
        edits,
    }
}

/// Parse and normalize a refinement proposal from a model reply.
///
/// # Errors
///
/// Returns a human-readable error string when the reply's JSON cannot be
/// extracted or its top level is not an object.
pub fn parse_proposal(text: &str) -> Result<RefinementProposal, String> {
    let value = extract_json_object(text)?;
    if !value.is_object() {
        return Err("Refiner JSON must be an object".to_string());
    }
    Ok(normalize_refinement_proposal(&value))
}

fn now_iso() -> String {
    crate::session::manager::format_iso_now()
}

/// Options for applying a proposal.
pub struct ApplyOptions {
    pub id: String,
    pub rollback_of: Option<String>,
    pub scope: Option<HarnessScope>,
    /// Target-scope state captured before planning; edits whose entry changed
    /// since the baseline are rejected.
    pub baseline_state: Option<HarnessState>,
    /// The resolved `factory.enabled` opt-in (default off). While it is off,
    /// factory create/update edits refuse with the one disabled message, the
    /// same gate the kernel-side factory writers raise
    /// (`rlm.factory.require_factory_enabled`).
    pub factory_enabled: bool,
    /// Where the session's memory lives: in a chat-memory session, memory
    /// and prompt-note edits refuse with [`super::CHAT_MEMORY_MESSAGE`].
    pub memory: super::HarnessMemory,
}

/// Apply a proposal to the state (mutating entries and recording the event).
/// The compiled core decides each edit (`bend/refine_plan.bend`: its id,
/// validation, the baseline, factory and memory gates, and the entry's
/// presence as the proposal's earlier edits left it) and the change lines;
/// Rust gives it the facts and mutates the state as it says.
pub fn apply_refinement_proposal(
    state: &mut HarnessState,
    proposal: &RefinementProposal,
    options: ApplyOptions,
) -> super::RefinementResult {
    let held = |edit: &RefinementEdit| edit.kind.is_none_or(|kind| options.memory.holds(kind));
    let unstored: Vec<rule::Ed> = proposal
        .edits
        .iter()
        .map(|edit| edit_facts(edit, false, false, held(edit)))
        .collect();
    let ids = rule::ids(&unstored);
    let facts: Vec<rule::Ed> = proposal
        .edits
        .iter()
        .zip(&ids)
        .map(|(edit, id)| {
            let (exists, differs) = match (edit.kind, id) {
                (Some(kind), Some(id)) => {
                    let stored = state.entries.get(&kind).and_then(|entries| entries.get(id));
                    let differs = options.baseline_state.as_ref().is_some_and(|baseline| {
                        let planned = baseline
                            .entries
                            .get(&kind)
                            .and_then(|entries| entries.get(id));
                        serde_json::to_value(stored).ok() != serde_json::to_value(planned).ok()
                    });
                    (stored.is_some(), differs)
                }
                _ => (false, false),
            };
            edit_facts(edit, exists, differs, held(edit))
        })
        .collect();
    let plan = rule::plan(
        rule::Opts {
            factory: options.factory_enabled,
            baseline: options.baseline_state.is_some(),
        },
        &facts,
    );
    let mut applied_edits: Vec<AppliedRefinementEdit> = Vec::with_capacity(plan.rows.len());
    for (edit, row) in proposal.edits.iter().zip(plan.rows) {
        let kind = kind_of(row.comp);
        let mut applied =
            AppliedRefinementEdit::planned(edit, action_of(row.verb), kind, row.id.clone());
        match row.out {
            rule::Out::Invalid(error) => applied.error = Some(error),
            rule::Out::Refused(error) => {
                applied.before = state
                    .entries
                    .get(&kind)
                    .and_then(|entries| entries.get(&row.id))
                    .cloned();
                applied.error = Some(error);
            }
            rule::Out::Removed => {
                applied.before = state.entries.entry(kind).or_default().remove(&row.id);
                applied.applied = true;
            }
            rule::Out::Written => {
                let records = state.entries.entry(kind).or_default();
                let before = records.get(&row.id).cloned();
                let after = written_entry(edit, &row.id, kind, before.as_ref(), options.scope);
                records.insert(row.id, after.clone());
                applied.before = before;
                applied.after = Some(after);
                applied.applied = true;
            }
        }
        applied_edits.push(applied);
    }
    state.refinements.push(HarnessRefinementEvent {
        id: options.id.clone(),
        trigger: proposal.summary.clone(),
        changes: plan.changes,
        evidence: proposal.rationale.clone(),
        outcome: proposal.expected_outcome.clone(),
        created_at: now_iso(),
    });
    super::RefinementResult {
        id: options.id,
        summary: proposal.summary.clone(),
        rationale: proposal.rationale.clone(),
        expected_outcome: proposal.expected_outcome.clone(),
        applied_edits,
        harness_state_path: String::new(),
        rollback_of: options.rollback_of,
        scope: options.scope,
    }
}

/// The entry an applied create or update writes: each field the edit's,
/// else the stored entry's, else its default.
fn written_entry(
    edit: &RefinementEdit,
    id: &str,
    kind: RefinementKind,
    before: Option<&HarnessEntry>,
    scope: Option<HarnessScope>,
) -> HarnessEntry {
    HarnessEntry {
        id: id.to_string(),
        kind,
        title: edit
            .title
            .clone()
            .or_else(|| before.map(|entry| entry.title.clone()))
            .unwrap_or_else(|| id.to_string()),
        content: edit
            .content
            .clone()
            .or_else(|| before.map(|entry| entry.content.clone()))
            .unwrap_or_default(),
        path: edit
            .path
            .clone()
            .or_else(|| before.map(|entry| entry.path.clone()))
            .unwrap_or_else(|| "general".to_string()),
        scope: before
            .and_then(|entry| entry.scope)
            .or(scope)
            .or(Some(HarnessScope::Local)),
        reference: edit
            .reference
            .clone()
            .or_else(|| before.map(|entry| entry.reference.clone()))
            .unwrap_or_default(),
        arguments: edit
            .arguments
            .clone()
            .or_else(|| before.map(|entry| entry.arguments.clone()))
            .unwrap_or_default(),
        metadata: edit
            .metadata
            .clone()
            .or_else(|| before.map(|entry| entry.metadata.clone()))
            .unwrap_or_default(),
        source: "refine".to_string(),
        created_at: before.map_or_else(now_iso, |entry| entry.created_at.clone()),
        updated_at: now_iso(),
        version: before.map_or(1, |entry| entry.version + 1),
    }
}

/// The facts of an edit the core decides on: the JSON fields it reads
/// (the reference's strings, the arguments' spec keys) and its entry's.
fn edit_facts(edit: &RefinementEdit, exists: bool, differs: bool, held: bool) -> rule::Ed {
    let text = |map: &serde_json::Map<String, serde_json::Value>, key: &str| {
        map.get(key)
            .and_then(serde_json::Value::as_str)
            .map(str::to_string)
    };
    let spec_key = |map: &serde_json::Map<String, serde_json::Value>, key: &str| match map.get(key)
    {
        None => rule::Val::Missing,
        Some(serde_json::Value::Null) => rule::Val::Null,
        Some(serde_json::Value::Object(_)) => rule::Val::Object,
        Some(_) => rule::Val::Other,
    };
    rule::Ed {
        verb: edit.action.map(verb_of),
        comp: edit.kind.map(comp_of),
        id: edit.id.clone(),
        title: edit.title.clone(),
        content: edit.content.is_some(),
        pyref: edit.reference.as_ref().map(|reference| rule::Pyref {
            ty: text(reference, "type"),
            import: text(reference, "import"),
            python_import: text(reference, "python_import"),
            callable: text(reference, "callable"),
            call_pattern: text(reference, "call_pattern"),
        }),
        args: edit.arguments.as_ref().map(|arguments| rule::Args {
            dag: spec_key(arguments, "dag"),
            machine: spec_key(arguments, "machine"),
        }),
        exists,
        differs,
        held,
    }
}

/// The proposal that reverts a previously applied result.
#[must_use]
pub fn rollback_proposal(target: &super::RefinementResult) -> RefinementProposal {
    let rows: Vec<rule::Was> = target
        .applied_edits
        .iter()
        .map(|edit| rule::Was {
            applied: edit.applied,
            before: edit.before.is_some(),
            after: edit.after.is_some(),
        })
        .collect();
    let back = rule::back(&target.id, &rows);
    let edits = back
        .picks
        .iter()
        .map(|pick| {
            // The core's index is below the row count (checked on read).
            let row = &target.applied_edits[pick.at];
            // A restore has a before; a delete carries no fields.
            let before = row
                .before
                .as_ref()
                .filter(|_| pick.verb != rule::Verb::Delete);
            RefinementEdit {
                action: Some(action_of(pick.verb)),
                kind: Some(row.kind),
                id: Some(row.id.clone()),
                title: before.map(|entry| entry.title.clone()),
                content: before.map(|entry| entry.content.clone()),
                path: before.map(|entry| entry.path.clone()),
                reference: before.map(|entry| entry.reference.clone()),
                arguments: before.map(|entry| entry.arguments.clone()),
                metadata: before.map(|entry| entry.metadata.clone()),
                reason: Some(back.reason.clone()),
            }
        })
        .collect();
    RefinementProposal {
        summary: back.summary,
        rationale: back.rationale,
        expected_outcome: back.outcome,
        edits,
    }
}

fn verb_of(action: RefinementAction) -> rule::Verb {
    match action {
        RefinementAction::Create => rule::Verb::Create,
        RefinementAction::Update => rule::Verb::Update,
        RefinementAction::Delete => rule::Verb::Delete,
    }
}

fn action_of(verb: rule::Verb) -> RefinementAction {
    match verb {
        rule::Verb::Create => RefinementAction::Create,
        rule::Verb::Update => RefinementAction::Update,
        rule::Verb::Delete => RefinementAction::Delete,
    }
}

fn comp_of(kind: RefinementKind) -> rule::Comp {
    match kind {
        RefinementKind::Prompt => rule::Comp::Prompt,
        RefinementKind::Memory => rule::Comp::Memory,
        RefinementKind::Skill => rule::Comp::Skill,
        RefinementKind::Subagent => rule::Comp::Subagent,
        RefinementKind::Factory => rule::Comp::Factory,
    }
}

fn kind_of(comp: rule::Comp) -> RefinementKind {
    match comp {
        rule::Comp::Prompt => RefinementKind::Prompt,
        rule::Comp::Memory => RefinementKind::Memory,
        rule::Comp::Skill => RefinementKind::Skill,
        rule::Comp::Subagent => RefinementKind::Subagent,
        rule::Comp::Factory => RefinementKind::Factory,
    }
}

/// A length in UTF-8 bytes (one token per byte), for the core.
fn byte_len(text: &str) -> u64 {
    u64::try_from(text.len()).unwrap_or(u64::MAX)
}

/// Fit the refinement request into the model context: trim conversation from
/// the front (binary search) and clamp output tokens. The compiled core walks
/// the search (`bend/refine_plan.bend`, R8); Rust builds and measures each
/// prompt it asks for.
///
/// # Errors
///
/// Returns an error when even the trimmed prompt leaves no room for output
/// tokens in the model's context window.
pub fn refinement_request(
    model: &eukhe_types::ai::Model,
    system_prompt: &str,
    conversation_text: &str,
    build_prompt: &dyn Fn(&str) -> String,
    output_reserve: u64,
) -> anyhow::Result<(u64, String)> {
    let window = rule::Win {
        window: model.context_window,
        max: model.max_tokens,
        reserve: output_reserve,
        system: byte_len(system_prompt),
    };
    let conversation = byte_len(conversation_text);
    let prompt_for_length = |length: u64| -> String {
        let length = usize::try_from(length).unwrap_or(usize::MAX);
        let start = conversation_text.len().saturating_sub(length);
        // Avoid splitting a UTF-8 sequence (the TS surrogate skip).
        let mut start = start.min(conversation_text.len());
        while start < conversation_text.len() && !conversation_text.is_char_boundary(start) {
            start += 1;
        }
        build_prompt(&format!(
            "[Earlier conversation omitted to fit the model context.]\n{}",
            &conversation_text[start..]
        ))
    };
    let mut user_prompt = build_prompt(conversation_text);
    let mut search = rule::Search::Full;
    loop {
        match rule::fit(window, conversation, search, byte_len(&user_prompt)) {
            rule::Step::Try { len, next } => {
                user_prompt = prompt_for_length(len);
                search = next;
            }
            rule::Step::Fits(max_tokens) => return Ok((max_tokens, user_prompt)),
            rule::Step::NoRoom(text) => anyhow::bail!("{text}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::empty_harness_state;
    use super::*;

    fn create_memory_edit(id: &str, title: &str, content: &str) -> RefinementEdit {
        RefinementEdit {
            action: Some(RefinementAction::Create),
            kind: Some(RefinementKind::Memory),
            id: Some(id.to_string()),
            title: Some(title.to_string()),
            content: Some(content.to_string()),
            ..Default::default()
        }
    }

    #[test]
    fn json_extraction_diagnoses_truncation() {
        // Direct object.
        let parsed = parse_proposal(r#"{"summary":"ok","edits":[]}"#).unwrap();
        assert_eq!(parsed.summary, "ok");
        // Fenced block.
        let fenced = parse_proposal("```json\n{\"summary\":\"fenced\"}\n```").unwrap();
        assert_eq!(fenced.summary, "fenced");
        // Brace-sliced out of prose.
        let prose = parse_proposal("Here you go:\n{\"summary\":\"sliced\"}\nAll set.").unwrap();
        assert_eq!(prose.summary, "sliced");
        // Truncated JSON reports the output-budget cause.
        let error = parse_proposal(r#"{"summary":"cut","edits":[{"action":"cre"#).unwrap_err();
        assert_eq!(error, TRUNCATED_JSON_ERROR);
        // Non-JSON text reports missing JSON.
        assert_eq!(
            parse_proposal("no json here").unwrap_err(),
            "Refiner did not return a JSON object"
        );
    }

    fn stored_entry(kind: RefinementKind, id: &str) -> HarnessEntry {
        HarnessEntry {
            id: id.to_string(),
            kind,
            title: "Stored".to_string(),
            content: "Stored.".to_string(),
            path: "general".to_string(),
            scope: Some(HarnessScope::Local),
            reference: serde_json::Map::default(),
            arguments: serde_json::Map::default(),
            metadata: serde_json::Map::default(),
            source: "refine".to_string(),
            created_at: String::new(),
            updated_at: String::new(),
            version: 1,
        }
    }

    /// The row error of one edit applied with the factory opt-in on, its
    /// entry stored or not: Rust's reading of the edit's JSON fields (the
    /// reference strings, the spec keys, null as absent), end to end
    /// through the core.
    fn error_of(edit: &RefinementEdit, stored: bool) -> Option<String> {
        let mut state = empty_harness_state();
        if stored {
            let (kind, id) = (edit.kind.unwrap(), edit.id.clone().unwrap());
            state
                .entries
                .get_mut(&kind)
                .unwrap()
                .insert(id.clone(), stored_entry(kind, &id));
        }
        let result = apply_refinement_proposal(
            &mut state,
            &RefinementProposal {
                edits: vec![edit.clone()],
                ..Default::default()
            },
            ApplyOptions {
                id: "r1".to_string(),
                rollback_of: None,
                scope: None,
                baseline_state: None,
                factory_enabled: true,
                memory: crate::refinement::HarnessMemory::Harness,
            },
        );
        result.applied_edits[0].error.clone()
    }

    #[test]
    fn validation_rules() {
        // Unsupported action.
        let mut edit = create_memory_edit("m", "t", "c");
        edit.action = None;
        assert_eq!(
            error_of(&edit, false).as_deref(),
            Some("unsupported action")
        );
        // base_system_prompt is not editable.
        let prompt_edit = RefinementEdit {
            action: Some(RefinementAction::Update),
            kind: Some(RefinementKind::Prompt),
            id: Some("base_system_prompt".to_string()),
            title: Some("t".into()),
            content: Some("c".into()),
            ..Default::default()
        };
        assert_eq!(
            error_of(&prompt_edit, true).as_deref(),
            Some("base system prompt is not editable")
        );
        // Skill edits require python reference + arguments + callable.
        let mut skill_edit = RefinementEdit {
            action: Some(RefinementAction::Create),
            kind: Some(RefinementKind::Skill),
            title: Some("Skill".into()),
            content: Some("Does things".into()),
            ..Default::default()
        };
        assert_eq!(
            error_of(&skill_edit, false).as_deref(),
            Some("create skill requires arguments")
        );
        skill_edit.arguments = Some(serde_json::Map::default());
        assert_eq!(
            error_of(&skill_edit, false).as_deref(),
            Some("create skill requires python reference")
        );
        skill_edit.reference = Some(
            serde_json::from_value(
                serde_json::json!({ "type": "python", "import": "pkg.mod", "callable": "run" }),
            )
            .unwrap(),
        );
        assert_eq!(error_of(&skill_edit, false), None);
        // A python_import and a call_pattern stand in for import and callable.
        skill_edit.reference = Some(
            serde_json::from_value(serde_json::json!({
                "type": "python", "import": "", "python_import": "pkg", "call_pattern": "await run()"
            }))
            .unwrap(),
        );
        assert_eq!(error_of(&skill_edit, false), None);
        // Wrong reference type; a non-string import is no import.
        skill_edit.reference = Some(
            serde_json::from_value(
                serde_json::json!({ "type": "shell", "import": "pkg.mod", "callable": "run" }),
            )
            .unwrap(),
        );
        assert_eq!(
            error_of(&skill_edit, false).as_deref(),
            Some("create skill reference.type must be python")
        );
        skill_edit.reference = Some(
            serde_json::from_value(
                serde_json::json!({ "type": "python", "import": 7, "callable": "run" }),
            )
            .unwrap(),
        );
        assert_eq!(
            error_of(&skill_edit, false).as_deref(),
            Some("create skill requires python import")
        );
    }

    #[test]
    fn factory_edits_accept_exactly_one_spec_form() {
        // Structural check only (TS shape): the kernel validator enforces
        // the full machine semantics at write time.
        let machine = serde_json::json!({
            "states": [{ "id": "collect", "entry": true, "subagent": "worker" }],
            "transitions": []
        });
        let dag = serde_json::json!({ "nodes": [{ "id": "collect", "subagent": "worker" }] });
        let mut edit = RefinementEdit {
            action: Some(RefinementAction::Create),
            kind: Some(RefinementKind::Factory),
            id: Some("sweep".to_string()),
            title: Some("Factory".into()),
            content: Some("Sweep review across changed files.".into()),
            ..Default::default()
        };
        // A dag object passes.
        edit.arguments = Some(serde_json::from_value(serde_json::json!({ "dag": dag })).unwrap());
        assert_eq!(error_of(&edit, false), None);
        // A machine object passes.
        edit.arguments =
            Some(serde_json::from_value(serde_json::json!({ "machine": machine })).unwrap());
        assert_eq!(error_of(&edit, false), None);
        // Both forms at once are rejected with the kernel wording.
        edit.arguments = Some(
            serde_json::from_value(serde_json::json!({ "dag": dag, "machine": machine })).unwrap(),
        );
        assert_eq!(
            error_of(&edit, false).as_deref(),
            Some("pass either dag or machine form, not both")
        );
        // Neither form (or a non-object spec) is rejected.
        edit.arguments = Some(serde_json::Map::default());
        assert_eq!(
            error_of(&edit, false).as_deref(),
            Some("factory entry requires a dag or machine object in arguments")
        );
        edit.arguments = Some(
            serde_json::from_value(serde_json::json!({ "machine": "not an object" })).unwrap(),
        );
        assert_eq!(
            error_of(&edit, false).as_deref(),
            Some("factory entry requires a dag or machine object in arguments")
        );
        edit.arguments = None;
        assert_eq!(
            error_of(&edit, false).as_deref(),
            Some("factory entry requires a dag or machine object in arguments")
        );
        // Delete edits carry no spec requirement.
        edit.action = Some(RefinementAction::Delete);
        assert_eq!(error_of(&edit, true), None);
        // An update that omits `arguments` keeps the stored spec (apply
        // preserves `before.arguments`), exactly like update_factory.
        edit.action = Some(RefinementAction::Update);
        edit.arguments = None;
        assert_eq!(error_of(&edit, true), None);
        // An update that does supply arguments gets the same shape checks.
        edit.arguments =
            Some(serde_json::from_value(serde_json::json!({ "machine": machine })).unwrap());
        assert_eq!(error_of(&edit, true), None);
        // JSON null is absent, exactly like the kernel's Python writers: a
        // valid dag with "machine": null is a dag-form edit, not both forms.
        edit.arguments = Some(
            serde_json::from_value(serde_json::json!({ "dag": dag, "machine": null })).unwrap(),
        );
        assert_eq!(error_of(&edit, true), None);
        edit.arguments = Some(
            serde_json::from_value(serde_json::json!({ "dag": dag, "machine": machine })).unwrap(),
        );
        assert_eq!(
            error_of(&edit, true).as_deref(),
            Some("pass either dag or machine form, not both")
        );
    }

    #[test]
    fn apply_create_update_delete() {
        let mut state = empty_harness_state();
        let proposal = RefinementProposal {
            summary: "add a memory".to_string(),
            rationale: "used twice".to_string(),
            expected_outcome: "faster".to_string(),
            edits: vec![create_memory_edit("m1", "Fact", "builds are green")],
        };
        let result = apply_refinement_proposal(
            &mut state,
            &proposal,
            ApplyOptions {
                id: "r1".to_string(),
                rollback_of: None,
                scope: Some(HarnessScope::Local),
                baseline_state: None,
                factory_enabled: false,
                memory: crate::refinement::HarnessMemory::Harness,
            },
        );
        assert_eq!(result.applied_edits.len(), 1);
        assert!(result.applied_edits[0].applied);
        let entry = &state.entries[&RefinementKind::Memory]["m1"];
        assert_eq!(entry.content, "builds are green");
        assert_eq!(entry.version, 1);
        assert_eq!(entry.scope, Some(HarnessScope::Local));
        // Duplicate create is rejected.
        let duplicate = apply_refinement_proposal(
            &mut state,
            &RefinementProposal {
                summary: "again".to_string(),
                rationale: String::new(),
                expected_outcome: String::new(),
                edits: vec![create_memory_edit("m1", "Fact", "again")],
            },
            ApplyOptions {
                id: "r2".to_string(),
                rollback_of: None,
                scope: None,
                baseline_state: None,
                factory_enabled: false,
                memory: crate::refinement::HarnessMemory::Harness,
            },
        );
        assert!(!duplicate.applied_edits[0].applied);
        assert_eq!(
            duplicate.applied_edits[0].error.as_deref(),
            Some("entry already exists")
        );
        // Update bumps the version.
        let mut update_edit = create_memory_edit("m1", "Fact", "updated fact");
        update_edit.action = Some(RefinementAction::Update);
        apply_refinement_proposal(
            &mut state,
            &RefinementProposal {
                summary: "update".to_string(),
                rationale: String::new(),
                expected_outcome: String::new(),
                edits: vec![update_edit],
            },
            ApplyOptions {
                id: "r3".to_string(),
                rollback_of: None,
                scope: None,
                baseline_state: None,
                factory_enabled: false,
                memory: crate::refinement::HarnessMemory::Harness,
            },
        );
        assert_eq!(state.entries[&RefinementKind::Memory]["m1"].version, 2);
        // Rollback restores the original content and keeps history.
        let rollback = rollback_proposal(&result);
        let rolled = apply_refinement_proposal(
            &mut state,
            &rollback,
            ApplyOptions {
                id: "r4".to_string(),
                rollback_of: Some("r1".to_string()),
                scope: None,
                baseline_state: None,
                factory_enabled: false,
                memory: crate::refinement::HarnessMemory::Harness,
            },
        );
        assert!(rolled.applied_edits[0].applied);
        // r1 created m1 with no before snapshot, so the rollback deletes it.
        assert!(!state.entries[&RefinementKind::Memory].contains_key("m1"));
    }

    #[test]
    fn factory_edits_refuse_while_the_opt_in_is_disabled() {
        // The opt-in gate on the apply path: while `factory.enabled` is
        // off, a refinement cannot author or re-author factory entries —
        // the same refusal, byte for byte, the kernel-side factory
        // writers raise (`rlm.factory.require_factory_enabled`).
        let machine = serde_json::json!({
            "states": [{ "id": "collect", "entry": true, "subagent": "worker" }],
            "transitions": []
        });
        let factory_edit = |action: RefinementAction, id: &str| RefinementEdit {
            action: Some(action),
            kind: Some(RefinementKind::Factory),
            id: Some(id.to_string()),
            title: Some("Factory".into()),
            content: Some("Sweep review across changed files.".into()),
            arguments: Some(
                serde_json::from_value(serde_json::json!({ "machine": machine })).unwrap(),
            ),
            ..Default::default()
        };
        let mut state = empty_harness_state();
        let proposal = |edits: Vec<RefinementEdit>| RefinementProposal {
            summary: "sweep".to_string(),
            rationale: String::new(),
            expected_outcome: String::new(),
            edits,
        };
        let disabled = apply_refinement_proposal(
            &mut state,
            &proposal(vec![factory_edit(RefinementAction::Create, "sweep")]),
            ApplyOptions {
                id: "r1".to_string(),
                rollback_of: None,
                scope: Some(HarnessScope::Local),
                baseline_state: None,
                factory_enabled: false,
                memory: crate::refinement::HarnessMemory::Harness,
            },
        );
        assert!(!disabled.applied_edits[0].applied);
        assert_eq!(
            disabled.applied_edits[0].error.as_deref(),
            Some(super::super::FACTORY_DISABLED_MESSAGE)
        );
        assert!(state.entries[&RefinementKind::Factory].is_empty());
        // An update of a stored entry refuses too: cleanup is not
        // authoring, but re-authoring while disabled is.
        state
            .entries
            .get_mut(&RefinementKind::Factory)
            .unwrap()
            .insert(
                "sweep".to_string(),
                HarnessEntry {
                    id: "sweep".to_string(),
                    kind: RefinementKind::Factory,
                    title: "Factory".to_string(),
                    content: "Sweep.".to_string(),
                    path: "general".to_string(),
                    scope: Some(HarnessScope::Local),
                    reference: serde_json::Map::default(),
                    arguments: serde_json::Map::default(),
                    metadata: serde_json::Map::default(),
                    source: "refine".to_string(),
                    created_at: String::new(),
                    updated_at: String::new(),
                    version: 1,
                },
            );
        let refused_update = apply_refinement_proposal(
            &mut state,
            &proposal(vec![factory_edit(RefinementAction::Update, "sweep")]),
            ApplyOptions {
                id: "r2".to_string(),
                rollback_of: None,
                scope: None,
                baseline_state: None,
                factory_enabled: false,
                memory: crate::refinement::HarnessMemory::Harness,
            },
        );
        assert!(!refused_update.applied_edits[0].applied);
        assert_eq!(
            refused_update.applied_edits[0].error.as_deref(),
            Some(super::super::FACTORY_DISABLED_MESSAGE)
        );
        // A delete is not authoring: cleanup stays available while
        // disabled (the gate's documented split).
        let cleanup = apply_refinement_proposal(
            &mut state,
            &proposal(vec![{
                let mut edit = factory_edit(RefinementAction::Delete, "sweep");
                edit.arguments = None;
                edit
            }]),
            ApplyOptions {
                id: "r3".to_string(),
                rollback_of: None,
                scope: None,
                baseline_state: None,
                factory_enabled: false,
                memory: crate::refinement::HarnessMemory::Harness,
            },
        );
        assert!(cleanup.applied_edits[0].applied);
        assert!(state.entries[&RefinementKind::Factory].is_empty());
    }

    #[test]
    fn factory_edits_apply_when_the_opt_in_is_enabled() {
        let machine = serde_json::json!({
            "states": [{ "id": "collect", "entry": true, "subagent": "worker" }],
            "transitions": []
        });
        let mut state = empty_harness_state();
        let result = apply_refinement_proposal(
            &mut state,
            &RefinementProposal {
                summary: "sweep".to_string(),
                rationale: String::new(),
                expected_outcome: String::new(),
                edits: vec![RefinementEdit {
                    action: Some(RefinementAction::Create),
                    kind: Some(RefinementKind::Factory),
                    id: Some("sweep".to_string()),
                    title: Some("Factory".into()),
                    content: Some("Sweep review across changed files.".into()),
                    arguments: Some(
                        serde_json::from_value(serde_json::json!({ "machine": machine })).unwrap(),
                    ),
                    ..Default::default()
                }],
            },
            ApplyOptions {
                id: "r1".to_string(),
                rollback_of: None,
                scope: Some(HarnessScope::Local),
                baseline_state: None,
                factory_enabled: true,
                memory: crate::refinement::HarnessMemory::Harness,
            },
        );
        assert!(result.applied_edits[0].applied);
        assert!(result.applied_edits[0].error.is_none());
        assert!(state.entries[&RefinementKind::Factory].contains_key("sweep"));
    }

    #[test]
    fn chat_memory_refinements_author_tools_only() {
        let mut state = empty_harness_state();
        let result = apply_refinement_proposal(
            &mut state,
            &RefinementProposal {
                summary: "remember and reuse".to_string(),
                rationale: String::new(),
                expected_outcome: String::new(),
                edits: vec![
                    create_memory_edit("m1", "Fact", "the favorite prime is 104729"),
                    RefinementEdit {
                        action: Some(RefinementAction::Create),
                        kind: Some(RefinementKind::Prompt),
                        id: Some("p1".to_string()),
                        title: Some("Policy".into()),
                        content: Some("Answer tersely.".into()),
                        ..Default::default()
                    },
                    RefinementEdit {
                        action: Some(RefinementAction::Create),
                        kind: Some(RefinementKind::Subagent),
                        id: Some("reviewer".to_string()),
                        title: Some("Reviewer".into()),
                        content: Some("Review the diff for bugs.".into()),
                        ..Default::default()
                    },
                ],
            },
            ApplyOptions {
                id: "r1".to_string(),
                rollback_of: None,
                scope: Some(HarnessScope::Local),
                baseline_state: None,
                factory_enabled: false,
                memory: crate::refinement::HarnessMemory::Chat,
            },
        );
        let outcomes: Vec<(RefinementKind, bool, Option<&str>)> = result
            .applied_edits
            .iter()
            .map(|edit| (edit.kind, edit.applied, edit.error.as_deref()))
            .collect();
        assert_eq!(
            outcomes,
            vec![
                (
                    RefinementKind::Memory,
                    false,
                    Some(crate::refinement::CHAT_MEMORY_MESSAGE)
                ),
                (
                    RefinementKind::Prompt,
                    false,
                    Some(crate::refinement::CHAT_MEMORY_MESSAGE)
                ),
                (RefinementKind::Subagent, true, None),
            ]
        );
        assert!(state.entries[&RefinementKind::Memory].is_empty());
        assert!(state.entries[&RefinementKind::Prompt].is_empty());
        assert!(state.entries[&RefinementKind::Subagent].contains_key("reviewer"));
    }
}
