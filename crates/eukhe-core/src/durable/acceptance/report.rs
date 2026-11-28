//! The readings of a run's final answer. The acceptance judge decides each
//! one (one model request with no tools and no transcript), on the answer
//! alone: whether it states work of its task left, whatever the reason
//! (`JudgeQuestion::Report`, which the headless task rule
//! `eukhe_bend::rules::headless::task` reads), and whether it leaves task
//! work the worker itself can still do now, without the user
//! (`JudgeQuestion::WorkLeft`, which the work-left Director
//! `eukhe_bend::rules::work_left` and an autonomous run's passing claim
//! read).

use std::sync::Arc;

use eukhe_bend::rules::verify::Answer;
use eukhe_chord::context::Context;
use eukhe_durable::types::ConversationId;
use futures::future::BoxFuture;
use futures::FutureExt;

use super::evidence::MAX_JUDGE_EVIDENCE_CHARS;
use super::evidence::{read_answer, Judge, JudgeQuestion, JudgeReply, JudgeRequest, ModelJudge};
use crate::durable::{EukheSession, HarnessCell};

/// What the judge read in a final answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnswerReading {
    /// The answer states no work of the task left (for
    /// `JudgeQuestion::WorkLeft`: none the worker can still do now).
    Done,
    /// The answer states work left (for `JudgeQuestion::WorkLeft`: work the
    /// worker can still do now): the items the judge listed, in its own
    /// words (empty when it listed none).
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

/// The judge of a final answer inside a session (the work-left Director,
/// `crate::durable::directors`): one request to the conversation's model.
/// A faux model (the verification seams; the product never runs one)
/// serves its script's replies in order from one queue for every request
/// of the session, so a judge request would take a turn's answer: it takes
/// none, and the reading is no verdict.
pub(crate) fn answer_judge(
    harness: HarnessCell,
    models: eukhe_ai::models::Models,
) -> Arc<dyn Judge> {
    Arc::new(AnswerJudge(ModelJudge { harness, models }))
}

/// [`ModelJudge`], but for a conversation on a faux model.
struct AnswerJudge(ModelJudge);

impl Judge for AnswerJudge {
    fn judge(&self, request: JudgeRequest, cx: &Context) -> BoxFuture<'_, JudgeReply> {
        let cx = cx.clone();
        async move {
            let faux = match self.0.session_model(request.conversation_id, &cx).await {
                Ok(selector) => selector
                    .as_deref()
                    .and_then(|selector| selector.split_once('/'))
                    .and_then(|(provider, id)| self.0.models.get_model(provider, id))
                    .is_some_and(|model| model.api.as_str().split(':').next() == Some(FAUX_API)),
                Err(error) => return JudgeReply::Unavailable(error.to_string()),
            };
            if faux {
                return JudgeReply::Unavailable(
                    "a faux model answers its script in order: it takes no judge request"
                        .to_owned(),
                );
            }
            self.0.judge(request, &cx).await
        }
        .boxed()
    }
}

/// The api of the faux provider (`eukhe_ai::providers::faux`): `faux` for
/// the scripted provider, `faux:<time>:<id>` for one registered without an
/// api of its own.
const FAUX_API: &str = "faux";

/// Ask `judge` whether `answer`, the final answer of `conversation_id`,
/// states work of its task left, whatever the reason: one request.
pub async fn read_final_answer(
    judge: &dyn Judge,
    conversation_id: ConversationId,
    answer: &str,
    cx: &Context,
) -> AnswerReading {
    read_answer_for(judge, JudgeQuestion::Report, conversation_id, answer, cx).await
}

/// Ask `judge` whether `answer`, the final answer of `conversation_id`,
/// leaves task work the worker itself can still do now, without the user:
/// one request. A step that needs the user, one the worker declined for a
/// stated reason, an assumption or a next step for the user is no such
/// work.
pub(crate) async fn read_work_left(
    judge: &dyn Judge,
    conversation_id: ConversationId,
    answer: &str,
    cx: &Context,
) -> AnswerReading {
    read_answer_for(judge, JudgeQuestion::WorkLeft, conversation_id, answer, cx).await
}

/// One judge request on `answer` for `question`, and its reading.
async fn read_answer_for(
    judge: &dyn Judge,
    question: JudgeQuestion,
    conversation_id: ConversationId,
    answer: &str,
    cx: &Context,
) -> AnswerReading {
    let reply = judge
        .judge(
            JudgeRequest {
                conversation_id,
                question,
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
