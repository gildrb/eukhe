//! The reading of a headless run's final answer: whether it states work
//! of its task left. The acceptance judge decides it (one model request
//! with no tools and no transcript, `JudgeQuestion::Report`), on the
//! answer alone; the headless task rule
//! (`eukhe_bend::rules::headless::task`) reads the result.

use std::sync::Arc;

use eukhe_bend::rules::verify::Answer;
use eukhe_chord::context::Context;
use eukhe_durable::types::ConversationId;

use super::evidence::MAX_JUDGE_EVIDENCE_CHARS;
use super::evidence::{read_answer, Judge, JudgeQuestion, JudgeReply, JudgeRequest, ModelJudge};
use crate::durable::EukheSession;

/// What the judge read in a final answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnswerReading {
    /// The answer states no work of the task left.
    Done,
    /// The answer states work left: the items the judge listed, in the
    /// answer's words (empty when it listed none).
    Left(Vec<String>),
    /// The judge gave no verdict, and why.
    Unjudged(String),
}

/// The product judge of `session`: one request to its conversation's
/// model.
#[must_use]
pub fn session_judge(session: &EukheSession) -> Arc<dyn Judge> {
    let deps = session.deps();
    Arc::new(ModelJudge {
        harness: deps.harness.clone(),
        models: deps.models.clone(),
    })
}

/// Ask `judge` whether `answer`, the final answer of `conversation_id`,
/// states work of its task left: one request.
pub async fn read_final_answer(
    judge: &dyn Judge,
    conversation_id: ConversationId,
    answer: &str,
    cx: &Context,
) -> AnswerReading {
    let reply = judge
        .judge(
            JudgeRequest {
                conversation_id,
                question: JudgeQuestion::Report,
                evidence: answer.chars().take(MAX_JUDGE_EVIDENCE_CHARS).collect(),
                model: None,
            },
            cx,
        )
        .await;
    reading(&reply)
}

/// The reading a judge's reply gives: PASS is done, FAIL is work left
/// with the lines after the verdict as its items; anything else is no
/// verdict.
fn reading(reply: &JudgeReply) -> AnswerReading {
    match read_answer(reply) {
        Answer::Yes => AnswerReading::Done,
        Answer::No => AnswerReading::Left(left_items(reply)),
        Answer::Unreadable => AnswerReading::Unjudged(format!(
            "the judge's reply starts with neither PASS nor FAIL: {}",
            first_line(reply)
        )),
        Answer::Unavailable => AnswerReading::Unjudged(match reply {
            JudgeReply::Unavailable(reason) => reason.clone(),
            JudgeReply::Text(_) | JudgeReply::Stopped => "the judge did not answer".to_owned(),
        }),
        Answer::Stopped => AnswerReading::Unjudged("the judge's request was stopped".to_owned()),
    }
}

/// The items a FAIL reply lists: its lines after the first, without list
/// marks, blank lines dropped.
fn left_items(reply: &JudgeReply) -> Vec<String> {
    match reply {
        JudgeReply::Text(text) => text
            .lines()
            .skip(1)
            .map(|line| line.trim().trim_start_matches(['-', '*', '•']).trim())
            .filter(|line| !line.is_empty())
            .map(str::to_owned)
            .collect(),
        JudgeReply::Unavailable(_) | JudgeReply::Stopped => Vec::new(),
    }
}

/// The first line of a text reply.
fn first_line(reply: &JudgeReply) -> String {
    match reply {
        JudgeReply::Text(text) => text.lines().next().unwrap_or_default().trim().to_owned(),
        JudgeReply::Unavailable(_) | JudgeReply::Stopped => String::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// PASS is done; FAIL lists the items after its first line; a reply
    /// that is neither, a failed request and a stopped one give no verdict.
    #[test]
    fn a_reply_reads_as_done_left_or_unjudged() {
        let text = |reply: &str| JudgeReply::Text(reply.to_owned());
        assert_eq!(
            [
                reading(&text("PASS: the answer reports every item done")),
                reading(&text(
                    "FAIL\n- W5: cargo is not on PATH\n\n* W6: DNS failed"
                )),
                reading(&text("FAIL")),
                reading(&text("maybe\nW5")),
                reading(&JudgeReply::Unavailable("429 usage limit".to_owned())),
                reading(&JudgeReply::Stopped),
            ],
            [
                AnswerReading::Done,
                AnswerReading::Left(vec![
                    "W5: cargo is not on PATH".to_owned(),
                    "W6: DNS failed".to_owned()
                ]),
                AnswerReading::Left(Vec::new()),
                AnswerReading::Unjudged(
                    "the judge's reply starts with neither PASS nor FAIL: maybe".to_owned()
                ),
                AnswerReading::Unjudged("429 usage limit".to_owned()),
                AnswerReading::Unjudged("the judge's request was stopped".to_owned()),
            ]
        );
    }
}
