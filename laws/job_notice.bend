# eukhe: the laws of area job_notice

import Base
import ../bend/job_notice.bend as JN
import ../bend/ffi_job_notice.bend as FJn
import ../bend/wire.bend as Wr
import ../spec/durable/job_notice.bend as S
import ./base.bend as LawsBase

# (D6) A job the agent stopped never wakes the session
# ----------------------------------------------------
# spec/README.md D6. bend/job_notice.bend: the end of a job that settles
# after its call stopped blocking the turn (a background kernel `bash()`
# command, a detached cell, a `bash` tool script) wakes the session (input
# steered into a busy turn, queued, an idle session resumed) unless the
# agent itself stopped it (`handle.kill()`) or its own call holds the
# result (a `jobs.cancel` that saw the job settle in time). It runs as the
# compiled core by bend/ffi_job_notice.bend (eukhe-bend
# rules/job_notice.rs), asked by eukhe-daemon JobNotices::deliver for
# every settled job and by eukhe-core jobs.cancel for its settled or
# detached branch. spec/durable/job_notice.bend restates the rule (S1-S3).
# Every input is free: every stopper, taken or not, every input string.
#
# R1: the agent's own stop never wakes, whatever else holds (S1, S2).
# R2: a result the agent's call took never wakes, whoever stopped the job
#     (S1, S2).
# R3: every other end wakes: a natural end, a user's or an interrupt's
#     stop, not taken; nothing else is dropped (S3).
# R4: the entry answers each request Rust writes with the spec's notice,
#     reads exactly the request and nothing after it, and answers any other
#     input with the exact error form `E job_notice: malformed request`.
#
# Not pinned here: that Rust maps JobSettled to the request (a `bash()`
# command's stopped_by, no stopper for a cell or a script, taken false in
# the notices; taken true for a cancel that settled): the Rust tests
# (job_notices.rs, rlm/tests.rs, agent_stopped_job_e2e) cover it.

# Spec helpers
# ------------

# the tag of a stopper on the wire: 0 nobody, 1 the agent, 2 the user, 3
# an interrupt
def sp_tag(by: JN.Stopper) -> Nat:
  match by:
    case JN.NoStop{}:
      0n
    case JN.AgentStop{}:
      1n
    case JN.UserStop{}:
      2n
    case JN.InterruptStop{}:
      3n

# R4: the spelling of a request: the stopper's tag, then T|F taken
def sp_w_req(by: JN.Stopper, taken: Bool, rest: String) -> String:
  Wr.put_nat(sp_tag(by), Wr.put_bool(taken, rest))

# R4: the spelling of a reply: 0 dropped, 1 a wake
def sp_w_reply(n: JN.Notice) -> String:
  match n:
    case JN.Drops{}:
      Wr.put_nat(0n, "")
    case JN.Wakes{}:
      Wr.put_nat(1n, "")

# Laws: the decision (R1-R3)
# --------------------------

# LAW job_notice_agent_never_wakes (R1): the entry drops the end of every
# job the agent itself stopped, its result taken or not
# EXCLUDES: "[bash-done ... stopped-by:agent] Resume your work" waking an
#   idle session after its final answer or steering its turn (the repeated
#   final report), a rule keyed on the exit code or the job's kind
law job_notice_agent_never_wakes:
  for taken: Bool
  {FJn.ffi(sp_w_req(JN.AgentStop{}, taken, "")) == sp_w_reply(JN.Drops{}) : String}

# LAW job_notice_taken_never_wakes (R2): the entry drops the end of every
# job whose result the agent's own call took, whoever stopped it
# EXCLUDES: a cancel that settled in time and still sends a job-settled
#   notice, a taken result reported twice
law job_notice_taken_never_wakes:
  for by: JN.Stopper
  {FJn.ffi(sp_w_req(by, True{}, "")) == sp_w_reply(JN.Drops{}) : String}

# LAW job_notice_untaken_wakes (R3): the entry wakes the session for the
# end of every job the agent did not stop and whose result it does not
# hold: a natural end, a user's stop, an interrupt
# EXCLUDES: a fix that drops every stopped job (the user's stop from the
#   bash view, an interrupt) or every bash() end, a lost notice of a job
#   still running when its cancel's budget ran out
law job_notice_untaken_wakes:
  for by: JN.Stopper
  for other: {S.by_agent(by) == False{} : Bool}
  {FJn.ffi(sp_w_req(by, False{}, "")) == sp_w_reply(JN.Wakes{}) : String}

# LAW job_notice_refines_spec (R1-R3): the model's notice is the spec's for
# every stopper, taken or not: dropped exactly when the agent already knows
# the end
# EXCLUDES: a model that drifts from the spec on any of the eight inputs
law job_notice_refines_spec:
  for by: JN.Stopper
  for taken: Bool
  {JN.notice(by, taken) == S.notice(by, taken) : JN.Notice}

# Laws: the entry (R4)
# --------------------

# LAW job_notice_entry_is_spec (R4): the entry answers every request Rust
# spells with the spec's notice, spelled
# EXCLUDES: a tag misread (the agent read as the user), taken ignored or
#   inverted, a default, another reply spelling
law job_notice_entry_is_spec:
  for by: JN.Stopper
  for taken: Bool
  {FJn.ffi(sp_w_req(by, taken, "")) == sp_w_reply(S.notice(by, taken)) : String}

# LAW job_notice_entry_reads (R4): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law job_notice_entry_reads:
  for by: JN.Stopper
  for taken: Bool
  for +rest: String
  {FJn.get_req(sp_w_req(by, taken, rest)) == Wr.Got{FJn.Req{by, taken}, rest} : Wr.Dec<FJn.Req>}

# LAW job_notice_entry_exact (R4): every input the entry does not answer
# with the error form is a spelled request
# EXCLUDES: an answer for input that is no request (a tag past 3, a
#   missing or malformed Bool, a malformed tag, input left over)
law job_notice_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FJn.ffi(s)) == False{} : Bool}
  exs by: JN.Stopper
  exs taken: Bool
  {s == sp_w_req(by, taken, "") : String}

# LAW job_notice_entry_refuses (R4): every error the entry answers is
# exactly `E job_notice: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law job_notice_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FJn.ffi(s)) == True{} : Bool}
  {FJn.ffi(s) == Wr.err("job_notice: malformed request") : String}

# LAW job_notice_entry_example (R1-R4): anchor: the wire strings Rust sends
# and the replies it reads; a tag past 3, a missing Bool, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law job_notice_entry_example:
  {[FJn.ffi("0,F"), FJn.ffi("1,F"), FJn.ffi("2,F"), FJn.ffi("3,F"), FJn.ffi("0,T"), FJn.ffi("1,T"), FJn.ffi("2,T"), FJn.ffi("3,T")] == ["1,", "0,", "1,", "1,", "0,", "0,", "0,", "0,"] : List<&2, String>} &
  {[FJn.ffi("4,F"), FJn.ffi("1,"), FJn.ffi("1,FT"), FJn.ffi("01,F")] == [Wr.err("job_notice: malformed request"), Wr.err("job_notice: malformed request"), Wr.err("job_notice: malformed request"), Wr.err("job_notice: malformed request")] : List<&2, String>}
