# eukhe: the pinned bytes of the reply-ask anchors (the tags example), in
# a file of their own: long similar literals in laws/run/entry.bend's
# closure mis-compile in the bend entry (the string pool hands one
# literal to another), so the bytes live in a small file whose closure is
# just the wire and the entry.
#
# Each law answers one reply-ask byte string the Rust side
# (crates/eukhe-durable/src/harness/generation/decide.rs) sends, through
# the compiled core (bend/ffi_run.bend): a plain reply answers (0,), a
# reply with calls runs its tools (1,), a deferred one polls (2,), a
# transient error retries (3,), a noted one notes (4,), an overflow with
# a cut compacts (5,), without one fails (6,), a deferred one at its
# job's deadline is late (7,). The stream flag retries a cut on the
# stream budget and a cut past it goes on without the flag.

import Base
import ../../bend/ffi_run.bend as FRn

def tags.req_plain0() -> String:
  "0,2,5,1,1,1,1,0,0,0,F0,F"

def tags.req_plain1() -> String:
  "0,2,5,1,1,1,1,0,0,0,F1,F"

def tags.req_plain2() -> String:
  "0,2,5,1,1,1,1,0,0,0,F2,F"

def tags.req_retry() -> String:
  "0,2,5,1,1,1,1,0,0,0,F3,TF,F"

def tags.req_noted() -> String:
  "0,2,5,1,1,1,1,0,0,0,F3,FT,F"

def tags.req_overflow() -> String:
  "0,2,5,1,1,1,1,0,0,0,F4,T,F"

def tags.req_no_overflow() -> String:
  "0,2,5,1,1,1,1,0,0,0,F4,F,F"

def tags.req_late() -> String:
  "0,2,5,1,1,1,1,0,0,5,F2,F"

def tags.req_stream_retry() -> String:
  "0,2,5,1,1,5,2,1,0,0,F3,TF,T"

def tags.req_stream_spent() -> String:
  "0,2,5,1,1,1,4,1,1,0,F3,FT,T"

# LAW run_ffi_tags_example: the plain, calls, deferred and late answers
law run_ffi_tags_example:
  {FRn.ffi(tags.req_plain0) == "0," : String} &
  {FRn.ffi(tags.req_plain1) == "1," : String} &
  {FRn.ffi(tags.req_plain2) == "2," : String} &
  {FRn.ffi(tags.req_late) == "7," : String}

# LAW run_ffi_tags_retry_answer: a transient error retries
law run_ffi_tags_retry_answer:
  {FRn.ffi(tags.req_retry) == "3," : String}

# LAW run_ffi_tags_noted_answer: a noted error notes
law run_ffi_tags_noted_answer:
  {FRn.ffi(tags.req_noted) == "4," : String}

# LAW run_ffi_tags_overflow_answers: an overflow with a cut compacts,
# without one fails
law run_ffi_tags_overflow_answers:
  {FRn.ffi(tags.req_overflow) == "5," : String} &
  {FRn.ffi(tags.req_no_overflow) == "6," : String}

# LAW run_ffi_tags_stream_answers: a cut with stream budget retries on it
# (3,), a cut past it fails like without the flag (6,)
law run_ffi_tags_stream_answers:
  {FRn.ffi(tags.req_stream_retry) == "3," : String} &
  {FRn.ffi(tags.req_stream_spent) == "6," : String}

# LAW run_ffi_tags_other_answers: the other tags the entry answers: a
# message that ends the turn runs its tools or answers, a noted error
# notes (3,FT), a threshold waits or sends, an overflow's and a
# threshold's compaction and a round end as asked, a failed poll repolls
# or not
law run_ffi_tags_other_answers:
  {[FRn.ffi("1,TF"), FRn.ffi("1,FT"), FRn.ffi("1,FF"), FRn.ffi("2,F2,"), FRn.ffi("2,F1,"), FRn.ffi("2,T2,"), FRn.ffi("3,T0,"), FRn.ffi("3,T1,"), FRn.ffi("3,F1,"), FRn.ffi("3,F2,")] == ["0,", "1,", "3,FT", "0,", "1,T", "1,F", "T", "F", "T", "F"] : List<&2, String>} &
  {[FRn.ffi("4,2,5,1,1,1,0,FF"), FRn.ffi("4,2,5,1,1,1,1,FF"), FRn.ffi("4,2,5,1,1,1,0,TF"), FRn.ffi("4,2,5,1,1,1,0,FT"), FRn.ffi("5,2,2,2,5,0,0,0,0,0,FF0,0,"), FRn.ffi("5,2,2,2,5,1,2,2,"), FRn.ffi("5,2,2,2,5,2,0,0,0,"), FRn.ffi("5,2,2,2,5,0,0,0,0,0,FF1,2,"), FRn.ffi("6,T0,1,"), FRn.ffi("6,T1,1,")] == ["3,1,", "2,", "0,", "1,", "1,1,", "2,", "0,", "2,", "T", "F"] : List<&2, String>}
