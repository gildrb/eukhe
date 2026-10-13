//! The refinement rows and auto-refine gates: the `refinement_outcome` /
//! `refinement_notice` message builders (core/messages.ts), who triggered a
//! run, and the resolved `autoRefine` settings block.

use eukhe_types::ai::UserContent;
use eukhe_types::custom_type::CustomType;
use eukhe_types::session::CustomMessage;
use serde_json::json;

use crate::autonomous::now_millis;
use crate::refinement::executor::AutoRefineReview;
use crate::refinement::{format_refinement_notice_body, HarnessScope, RefinementResult};

/// The compact trigger's review-request reason (TS `AutoRefineReason`
/// `"compact"`): the label the review prompt's trigger line and the
/// auto-refine instructions carry.
pub const AUTO_REFINE_COMPACT_REASON: &str = "compact";

/// The resolved auto-refine gates (TS `settingsManager.getAutoRefineSettings`):
/// the settings file's `autoRefine` block with the product defaults and
/// clamps applied.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AutoRefineGates {
    pub enabled: bool,
    pub turn_interval: u64,
    pub compact: bool,
    pub cooldown_ms: u64,
}

impl Default for AutoRefineGates {
    fn default() -> Self {
        Self {
            enabled: true,
            turn_interval: 25,
            compact: true,
            cooldown_ms: 20 * 60 * 1000,
        }
    }
}

impl AutoRefineGates {
    /// Resolve the gates from the raw settings block (TS
    /// `getAutoRefineSettings`: `enabled`/`compact` default on, the turn
    /// interval clamps to at least 1 and defaults to 25, the cooldown
    /// clamps to at least 0 and defaults to 20 minutes).
    #[must_use]
    pub fn from_settings(raw: Option<&crate::settings::AutoRefineSettings>) -> Self {
        let Some(raw) = raw else {
            return Self::default();
        };
        let defaults = Self::default();
        Self {
            enabled: raw.enabled.unwrap_or(defaults.enabled),
            turn_interval: raw.turn_interval.unwrap_or(defaults.turn_interval).max(1),
            compact: raw.compact.unwrap_or(defaults.compact),
            cooldown_ms: raw.cooldown_ms.unwrap_or(defaults.cooldown_ms),
        }
    }
}

/// The instructions an approved auto-refine review carries into the
/// refinement run (TS `autoRefineInstructions`).
#[must_use]
pub fn auto_refine_instructions(reason: &str, review: &AutoRefineReview) -> String {
    let detail = review
        .instructions
        .as_deref()
        .map(|instructions| {
            format!(
                "

Reviewer instructions: {instructions}"
            )
        })
        .unwrap_or_default();
    format!(
        "Automatic refine review triggered by {reason}. Only create/update/delete local harness entries if there is clear evidence that should help this session continue. Prefer an empty edits array over speculative or one-off memories. Do not promote anything global unless explicitly requested. Reviewer rationale: {}{detail}",
        review.rationale
    )
}

/// Who triggered a refinement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefinementSource {
    Auto,
    User,
    SelfRefine,
}

impl RefinementSource {
    fn as_str(self) -> &'static str {
        match self {
            RefinementSource::Auto => "auto",
            RefinementSource::User => "user",
            RefinementSource::SelfRefine => "self",
        }
    }
}

/// TUI-rendered outcome message (`refinement_outcome`).
#[must_use]
pub fn create_refinement_outcome_message(result: &RefinementResult) -> CustomMessage {
    let mut details = json!({
        "refinementId": result.id,
        "summary": result.summary,
        "scope": result.scope.unwrap_or(HarnessScope::Local),
        "edits": result.applied_edits,
    });
    if let (Some(rollback), Some(map)) = (result.rollback_of.clone(), details.as_object_mut()) {
        map.insert("rollbackOf".to_string(), json!(rollback));
    }
    CustomMessage {
        custom_type: CustomType::RefinementOutcome,
        content: UserContent::Text(format!("Refinement complete: {}", result.summary)),
        display: true,
        details: Some(details),
        timestamp: now_millis(),
        rest: serde_json::Map::default(),
    }
}

/// Model-facing notice (`refinement_notice`, display=false).
#[must_use]
pub fn create_refinement_notice_message(
    result: &RefinementResult,
    source: RefinementSource,
) -> CustomMessage {
    let mut details = json!({
        "refinementId": result.id,
        "summary": result.summary,
        "scope": result.scope.unwrap_or(HarnessScope::Local),
        "edits": result.applied_edits,
        "source": source.as_str(),
    });
    if let (Some(rollback), Some(map)) = (result.rollback_of.clone(), details.as_object_mut()) {
        map.insert("rollbackOf".to_string(), json!(rollback));
    }
    CustomMessage {
        custom_type: CustomType::RefinementNotice,
        content: UserContent::Text(format!(
            "[{}-refinement]\n\n{}",
            source.as_str(),
            format_refinement_notice_body(result)
        )),
        display: false,
        details: Some(details),
        timestamp: now_millis(),
        rest: serde_json::Map::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refinement_messages_match_wire_shape() {
        let result = RefinementResult {
            id: "refine_1".to_string(),
            summary: "add memory".to_string(),
            rationale: "seen twice".to_string(),
            expected_outcome: "recall".to_string(),
            applied_edits: vec![],
            harness_state_path: String::new(),
            rollback_of: None,
            scope: Some(HarnessScope::Local),
        };
        let outcome = create_refinement_outcome_message(&result);
        assert_eq!(outcome.custom_type, CustomType::RefinementOutcome);
        assert_eq!(
            outcome.content,
            UserContent::Text("Refinement complete: add memory".to_string())
        );
        assert!(outcome.display);
        let notice = create_refinement_notice_message(&result, RefinementSource::User);
        assert_eq!(notice.custom_type, CustomType::RefinementNotice);
        assert!(!notice.display);
        assert_eq!(
            notice.content,
            UserContent::Text("[user-refinement]\n\nadd memory".to_string())
        );
    }

    #[test]
    fn auto_refine_gates_resolve_the_ts_defaults_and_clamps() {
        // Absent block: the product defaults.
        assert_eq!(
            AutoRefineGates::from_settings(None),
            AutoRefineGates {
                enabled: true,
                turn_interval: 25,
                compact: true,
                cooldown_ms: 20 * 60 * 1000,
            }
        );
        // Partial block: the declared values win; the interval clamps to
        // at least 1 (TS `Math.max(1, ...)`).
        let raw = crate::settings::AutoRefineSettings {
            enabled: Some(false),
            turn_interval: Some(0),
            compact: Some(false),
            cooldown_ms: Some(5),
        };
        assert_eq!(
            AutoRefineGates::from_settings(Some(&raw)),
            AutoRefineGates {
                enabled: false,
                turn_interval: 1,
                compact: false,
                cooldown_ms: 5,
            }
        );
    }

    #[test]
    fn auto_refine_instructions_compose_the_ts_text() {
        let review = AutoRefineReview {
            should_refine: true,
            rationale: "reusable tactic".to_string(),
            instructions: Some("record it".to_string()),
        };
        assert_eq!(
            auto_refine_instructions("compact", &review),
            "Automatic refine review triggered by compact. Only create/update/delete local harness entries if there is clear evidence that should help this session continue. Prefer an empty edits array over speculative or one-off memories. Do not promote anything global unless explicitly requested. Reviewer rationale: reusable tactic

Reviewer instructions: record it"
        );
        let bare = AutoRefineReview {
            should_refine: true,
            rationale: "reusable tactic".to_string(),
            instructions: None,
        };
        assert_eq!(
            auto_refine_instructions("compact", &bare),
            "Automatic refine review triggered by compact. Only create/update/delete local harness entries if there is clear evidence that should help this session continue. Prefer an empty edits array over speculative or one-off memories. Do not promote anything global unless explicitly requested. Reviewer rationale: reusable tactic"
        );
    }
}
