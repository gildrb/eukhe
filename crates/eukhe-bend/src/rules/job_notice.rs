//! Whether the end of one settled job wakes its session
//! (`bend/job_notice.bend`, entry `bend/ffi_job_notice.bend`;
//! `laws/job_notice.bend`, spec `spec/durable/job_notice.bend`): a job that
//! settles after its call stopped blocking the turn wakes the session
//! unless the agent itself stopped it (`handle.kill()`) or its own call
//! took the result (a `jobs.cancel` that saw the job settle in time).

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// Who stopped a job; a job that ended by itself has none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stopper {
    /// The agent's own code (`handle.kill()`).
    Agent,
    /// The user, from the bash view.
    User,
    /// An interrupt (a cancelled one-shot `await bash(...)`).
    Interrupt,
}

/// What becomes of a settled job's end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Notice {
    /// No news to the agent: no input, no row, no wake.
    Drop,
    /// Delivered as session input: steered into a busy turn, queued, an
    /// idle session resumed.
    Wake,
}

/// The notice of a job's end: `stopped_by` who stopped it (none when it
/// ended by itself), `taken` whether the agent's own call already holds its
/// result.
#[must_use]
pub fn notice(stopped_by: Option<Stopper>, taken: bool) -> Notice {
    expect_core(Entry::JobNotice, notice_call(stopped_by, taken))
}

fn notice_call(stopped_by: Option<Stopper>, taken: bool) -> Result<Notice, Error> {
    let tag = match stopped_by {
        None => 0,
        Some(Stopper::Agent) => 1,
        Some(Stopper::User) => 2,
        Some(Stopper::Interrupt) => 3,
    };
    let mut request = Writer::new();
    request.tag(tag).bool(taken);
    let reply = call(Entry::JobNotice, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let notice = match reader.tag_of(2, "a job notice")? {
        0 => Notice::Drop,
        // `tag_of` answers a tag below 2: this is 1.
        _ => Notice::Wake,
    };
    reader.end()?;
    Ok(notice)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The table comes from the compiled core: only an end the agent did
    /// not stop and whose result no call took wakes the session.
    #[test]
    fn the_core_wakes_only_on_news() {
        let stoppers = [
            None,
            Some(Stopper::Agent),
            Some(Stopper::User),
            Some(Stopper::Interrupt),
        ];
        let table: Vec<(Option<Stopper>, bool, Notice)> = [false, true]
            .into_iter()
            .flat_map(|taken| stoppers.map(|by| (by, taken, notice(by, taken))))
            .collect();
        assert_eq!(
            table,
            vec![
                (None, false, Notice::Wake),
                (Some(Stopper::Agent), false, Notice::Drop),
                (Some(Stopper::User), false, Notice::Wake),
                (Some(Stopper::Interrupt), false, Notice::Wake),
                (None, true, Notice::Drop),
                (Some(Stopper::Agent), true, Notice::Drop),
                (Some(Stopper::User), true, Notice::Drop),
                (Some(Stopper::Interrupt), true, Notice::Drop),
            ]
        );
    }
}
