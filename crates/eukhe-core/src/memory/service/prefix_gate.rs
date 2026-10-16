//! One writer per cache prefix (spec §3.3): compactions start up to
//! [`crate::memory::JOBS`] at a time on one prefix, and two calls that both
//! write the same new cache entry both pay for it. So the first call on a
//! prefix the compactor has not written yet goes alone, and the others on
//! it wait until its response starts (the owner reports the start as a
//! finished write); after that the prefix is warm and calls on it go at
//! once.

use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, VecDeque};
use std::hash::{Hash, Hasher};

use crate::memory::compactor::NodeRequest;
use crate::memory::view::{pieces, Part};

/// How many recently written prefixes count as warm.
const WARM: usize = 64;

/// The cache prefix of a compaction: the prompt in force (by generation)
/// and the marked piece of its view, if the view has one.
pub(super) fn prefix_key(prompt_generation: u64, request: &NodeRequest) -> u64 {
    let pieces = pieces(&request.context);
    let marked = if pieces.len() > 1 {
        pieces[0].as_str()
    } else {
        ""
    };
    let mut hasher = DefaultHasher::new();
    prompt_generation.hash(&mut hasher);
    marked.hash(&mut hasher);
    hasher.finish()
}

/// The compactions writing a prefix, and those waiting on them.
#[derive(Debug, Default)]
pub(super) struct PrefixGate {
    warm: VecDeque<u64>,
    /// The writer of each prefix being written, with its waiters.
    writing: HashMap<u64, Writing>,
    /// The prefix each writer writes.
    writers: HashMap<Part, u64>,
}

#[derive(Debug)]
struct Writing {
    waiting: Vec<(Part, NodeRequest)>,
}

impl PrefixGate {
    /// A compaction on prefix `key` asks to start: `Some` when it may go
    /// now (the prefix is warm, or it becomes the prefix's writer), `None`
    /// when it waits for the writer.
    pub(super) fn admit(
        &mut self,
        key: u64,
        part: Part,
        request: NodeRequest,
    ) -> Option<NodeRequest> {
        if self.warm.contains(&key) {
            return Some(request);
        }
        if let Some(writing) = self.writing.get_mut(&key) {
            writing.waiting.push((part, request));
            return None;
        }
        self.writing.insert(
            key,
            Writing {
                waiting: Vec::new(),
            },
        );
        self.writers.insert(part, key);
        Some(request)
    }

    /// Compaction `part` wrote its prefix (its response started; `wrote`)
    /// or ended without writing it. Returns the compactions that may go
    /// now: every waiter once the prefix is warm, else the first waiter,
    /// which writes it instead. A writer already reported is no writer.
    pub(super) fn finished(&mut self, part: Part, wrote: bool) -> Vec<(Part, NodeRequest)> {
        let Some(key) = self.writers.remove(&part) else {
            return Vec::new();
        };
        let Some(mut writing) = self.writing.remove(&key) else {
            return Vec::new();
        };
        if wrote {
            if self.warm.len() >= WARM {
                self.warm.pop_front();
            }
            self.warm.push_back(key);
            return writing.waiting;
        }
        if writing.waiting.is_empty() {
            return Vec::new();
        }
        let next = writing.waiting.remove(0);
        self.writers.insert(next.0, key);
        self.writing.insert(key, writing);
        vec![next]
    }

    /// The compactions of the nodes `gone` names stopped (a waiting turn
    /// holds them back): their waits end, and a prefix one of them was
    /// writing goes to its first remaining waiter. Returns the compactions
    /// that may go now.
    pub(super) fn cancel(&mut self, gone: impl Fn(Part) -> bool) -> Vec<(Part, NodeRequest)> {
        for writing in self.writing.values_mut() {
            writing.waiting.retain(|(part, _)| !gone(*part));
        }
        let writers: Vec<Part> = self
            .writers
            .keys()
            .copied()
            .filter(|part| gone(*part))
            .collect();
        writers
            .into_iter()
            .flat_map(|part| self.finished(part, false))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(task: &str) -> NodeRequest {
        NodeRequest {
            context: "<chat>\n0+1|a\n1+1|b\n2+1|c\n3+1|d\n</chat>".to_string(),
            task: task.to_string(),
            input: String::new(),
        }
    }

    fn part(i: u64) -> Part {
        Part { l: 0, i }
    }

    /// The first call on a new prefix writes it alone; the rest go once
    /// it is done, and later calls on the warm prefix go at once. A failed
    /// writer hands the prefix to the first waiter.
    #[test]
    fn one_call_writes_a_new_prefix_and_the_others_wait_for_it() {
        let mut gate = PrefixGate::default();
        let key = prefix_key(1, &request("t0"));
        let admitted = [
            gate.admit(key, part(0), request("t0")),
            gate.admit(key, part(1), request("t1")),
            gate.admit(key, part(2), request("t2")),
        ];
        let after_failure = gate.finished(part(0), false);
        let after_write = gate.finished(part(1), true);
        let warm = gate.admit(key, part(3), request("t3"));
        assert_eq!(
            (admitted, after_failure, after_write, warm),
            (
                [Some(request("t0")), None, None],
                vec![(part(1), request("t1"))],
                vec![(part(2), request("t2"))],
                Some(request("t3"))
            )
        );
    }

    /// The key is the prompt in force and the view's marked piece: a task
    /// or an unmarked tail does not change it.
    #[test]
    fn the_key_follows_the_prompt_and_the_marked_piece() {
        let base = request("a");
        let other_tail = NodeRequest {
            context: "<chat>\n0+1|a\n1+1|b\n2+1|c\n3+1|d\n4+1|e\n</chat>".to_string(),
            task: "b".to_string(),
            input: String::new(),
        };
        let other_block = NodeRequest {
            context: "<chat>\n0+2|ab\n2+1|c\n3+1|d\n4+1|e\n</chat>".to_string(),
            task: "a".to_string(),
            input: String::new(),
        };
        let key = prefix_key(1, &base);
        assert_eq!(
            [
                prefix_key(1, &other_tail) == key,
                prefix_key(2, &base) == key,
                prefix_key(1, &other_block) == key,
            ],
            [true, false, false]
        );
    }
}
