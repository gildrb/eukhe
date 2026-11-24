//! The reply-ask byte anchors: the exact byte strings the Rust side
//! (crates/eukhe-durable/src/harness/generation/decide.rs) sends and the
//! one-line answers the compiled core returns, pinned over
//! [`eukhe_bend::call`]. The same pins lived as bend laws and moved here:
//! the identical byte literals mis-compile inside the bend entry's
//! closure (its string pool hands one literal to another; as a top-level
//! law the same bytes evaluate correctly), while the wire grammar itself
//! stays pinned in bend by the codec round-trip laws of the entry.

use eukhe_bend::{call, Entry};

#[test]
fn the_reply_ask_bytes_answer_as_pinned() {
    for (request, answer) in [
        // a plain reply answers, calls run the tools, a deferred one
        // polls, a deferred one at its job's deadline is late
        ("0,2,5,1,1,1,1,0,0,0,F0,F", "0,"),
        ("0,2,5,1,1,1,1,0,0,0,F1,F", "1,"),
        ("0,2,5,1,1,1,1,0,0,0,F2,F", "2,"),
        ("0,2,5,1,1,1,1,0,0,5,F2,F", "7,"),
        // a transient error retries, a noted one notes, an overflow with
        // a cut compacts, without one fails
        ("0,2,5,1,1,1,1,0,0,0,F3,TFF", "3,"),
        ("0,2,5,1,1,1,1,0,0,0,F3,FTF", "4,"),
        ("0,2,5,1,1,1,1,0,0,0,F4,TF", "5,"),
        ("0,2,5,1,1,1,1,0,0,0,F4,FF", "6,"),
        // the stream flag: a cut with stream budget left retries on it, a
        // cut past the budget goes on as without the flag
        ("0,2,5,1,1,5,2,1,0,0,F3,TFT", "3,"),
        ("0,2,5,1,1,1,4,1,1,0,F3,FTT", "6,"),
        // a message that ends the turn: tools or answers, a noted error
        // notes, thresholds, overflow and threshold compactions, rounds
        ("1,TF", "0,"),
        ("1,FT", "1,"),
        ("1,FF", "3,FT"),
        ("2,F2,", "0,"),
        ("2,F1,", "1,T"),
        ("2,T2,", "1,F"),
        ("3,T0,", "T"),
        ("3,T1,", "F"),
        ("3,F1,", "T"),
        ("3,F2,", "F"),
        ("4,2,5,1,1,1,0,FF", "3,1,"),
        ("4,2,5,1,1,1,1,FF", "2,"),
        ("4,2,5,1,1,1,0,TF", "0,"),
        ("4,2,5,1,1,1,0,FT", "1,"),
        ("5,2,2,2,5,0,0,0,0,0,FF0,0,", "1,1,"),
        ("5,2,2,2,5,1,2,2,", "2,"),
        ("5,2,2,2,5,2,0,0,0,", "0,"),
        ("5,2,2,2,5,0,0,0,0,0,FF1,2,", "2,"),
        ("6,T0,1,", "T"),
        ("6,T1,1,", "F"),
        // the note, retry and stream caps read apart
        ("0,2,5,3,1,1,2,1,0,0,F3,TFF", "3,"),
        ("0,2,5,3,1,1,1,0,0,0,F3,FTF", "4,"),
        ("0,2,5,3,1,1,4,0,0,0,F3,TFF", "6,"),
        ("0,2,5,3,1,1,4,1,0,0,F3,TFF", "3,"),
        ("0,2,5,1,3,1,2,1,0,0,F3,FTF", "4,"),
        ("0,2,5,3,1,1,2,1,1,0,F3,TFT", "3,"),
        ("0,2,5,3,1,1,5,1,1,0,F3,TFT", "6,"),
        // the error bytes: unknown request, reply, threshold, compaction,
        // stuck reply, recovery tag, no input, input left over
        ("7,", "E run: malformed request"),
        ("0,2,5,1,1,1,1,0,0,0,F5,", "E run: malformed request"),
        ("2,F3,", "E run: malformed request"),
        ("3,T3,", "E run: malformed request"),
        ("5,2,2,2,5,4,", "E run: malformed request"),
        ("5,2,2,2,5,1,5,0,", "E run: malformed request"),
        ("", "E run: malformed request"),
        ("6,T0,1,x", "E run: input left over after the request"),
    ] {
        assert_eq!(
            call(Entry::Run, request).expect("the entry answers"),
            answer,
            "request {request}"
        );
    }
}
