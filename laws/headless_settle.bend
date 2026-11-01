# eukhe: the laws of area headless_settle

import Base
import ../bend/headless_settle.bend as Hs
import ../bend/ffi_headless_settle.bend as FHs
import ../bend/wire.bend as Wr
import ../spec/durable/headless.bend as Sp
import ../spec/durable/headless_wire.bend as SpW

# (D4) Every wait of a headless run has an exit
# ---------------------------------------------
# bend/headless_settle.bend, run as the compiled core by
# bend/ffi_headless_settle.bend (eukhe-bend rules/headless.rs `settle`;
# asked by eukhe-cli after each settle notice of `eukhe -p`, `--mode
# json` and `--mode rpc`). spec/durable/headless.bend restates the rule
# (Q1-Q2), spec/durable/headless_wire.bend the wire (W1, W2, W5). Every
# input is free: any facts, any string.
#
# R1: the decision for every facts is the spec's (Q1-Q2).
# R2: the run stops (finished) exactly when it is quiet: never while the
#     main conversation is busy, while any job, kernel job, subagent,
#     workflow run or settle notice is pending, or while the pending-work
#     read failed.
# R3: the run gives up only once the wait limit elapsed, and once it
#     elapsed it never waits again: every wait has an exit.
# R4: the entry answers each request Rust writes (W1, every count within
#     the wire) with the spelling (W2) of the spec's decision, and any
#     input that is not exactly one request with exactly
#     `E headless_settle: malformed request`.

# the decision is to stop
def finished(x: Hs.Settle) -> Bool:
  match x:
    case Hs.Finished{}:
      True{}
    case Hs.Waiting{}:
      False{}
    case Hs.GiveUp{}:
      False{}

# the decision is to wait
def waiting(x: Hs.Settle) -> Bool:
  match x:
    case Hs.Finished{}:
      False{}
    case Hs.Waiting{}:
      True{}
    case Hs.GiveUp{}:
      False{}

# the decision is to give up
def gives_up(x: Hs.Settle) -> Bool:
  match x:
    case Hs.Finished{}:
      False{}
    case Hs.Waiting{}:
      False{}
    case Hs.GiveUp{}:
      True{}

# Laws: the decision (R1-R3)
# --------------------------

# LAW headless_settle_refines_spec (R1): the decision for every facts is
# the spec's
# EXCLUDES: a count or flag left out of the check, a busy or unknown flag
#   read the wrong way round, a give-up below the limit, a wait at the
#   limit, a stop with work pending
law headless_settle_refines_spec:
  for +f: Hs.Facts
  {Hs.settle(f) == Sp.settle_spec(f) : Hs.Settle}

# LAW headless_settle_done_iff_quiet (R2): the run stops exactly when it
# is quiet
# EXCLUDES: a quiet run kept waiting (a headless run that never exits),
#   a run that stops with something pending
law headless_settle_done_iff_quiet:
  for +f: Hs.Facts
  {finished(Hs.settle(f)) == Sp.quiet(f) : Bool}

# LAW headless_settle_busy_never_done (R2): a busy main conversation (a
# run, queued input) never stops the run
# EXCLUDES: a `-p` run that exits while its own follow-up turn runs
law headless_settle_busy_never_done:
  for j: Nat
  for k: Nat
  for c: Nat
  for w: Nat
  for x: Nat
  for u: Bool
  for l: Bool
  {finished(Hs.settle(Hs.Facts{True{}, j, k, c, w, x, u, l})) == False{} : Bool}

# LAW headless_settle_jobs_never_done (R2): a running session job never
# stops the run
# EXCLUDES: a run that exits while a background Cell or Shell job runs
law headless_settle_jobs_never_done:
  for b: Bool
  for j: Nat
  for k: Nat
  for c: Nat
  for w: Nat
  for x: Nat
  for u: Bool
  for l: Bool
  {finished(Hs.settle(Hs.Facts{b, 1n+j, k, c, w, x, u, l})) == False{} : Bool}

# LAW headless_settle_kernel_jobs_never_done (R2): a running kernel
# background command never stops the run
# EXCLUDES: a run that exits while a kernel bash() command runs
law headless_settle_kernel_jobs_never_done:
  for b: Bool
  for j: Nat
  for k: Nat
  for c: Nat
  for w: Nat
  for x: Nat
  for u: Bool
  for l: Bool
  {finished(Hs.settle(Hs.Facts{b, j, 1n+k, c, w, x, u, l})) == False{} : Bool}

# LAW headless_settle_children_never_done (R2): an unsettled subagent
# never stops the run
# EXCLUDES: a run that exits before its subagents report
law headless_settle_children_never_done:
  for b: Bool
  for j: Nat
  for k: Nat
  for c: Nat
  for w: Nat
  for x: Nat
  for u: Bool
  for l: Bool
  {finished(Hs.settle(Hs.Facts{b, j, k, 1n+c, w, x, u, l})) == False{} : Bool}

# LAW headless_settle_workflow_runs_never_done (R2): an unsettled
# workflow run never stops the run
# EXCLUDES: a run that exits while a workflow run it started is live
law headless_settle_workflow_runs_never_done:
  for b: Bool
  for j: Nat
  for k: Nat
  for c: Nat
  for w: Nat
  for x: Nat
  for u: Bool
  for l: Bool
  {finished(Hs.settle(Hs.Facts{b, j, k, c, 1n+w, x, u, l})) == False{} : Bool}

# LAW headless_settle_wakes_never_done (R2): a settle notice being
# admitted never stops the run
# EXCLUDES: a run that exits between a job's settlement and the turn its
#   notice starts (the wake lost)
law headless_settle_wakes_never_done:
  for b: Bool
  for j: Nat
  for k: Nat
  for c: Nat
  for w: Nat
  for x: Nat
  for u: Bool
  for l: Bool
  {finished(Hs.settle(Hs.Facts{b, j, k, c, w, 1n+x, u, l})) == False{} : Bool}

# LAW headless_settle_unknown_never_done (R2): a failed pending-work read
# never stops the run
# EXCLUDES: an unreadable state read as quiet
law headless_settle_unknown_never_done:
  for b: Bool
  for j: Nat
  for k: Nat
  for c: Nat
  for w: Nat
  for x: Nat
  for l: Bool
  {finished(Hs.settle(Hs.Facts{b, j, k, c, w, x, True{}, l})) == False{} : Bool}

# LAW headless_settle_give_up_needs_limit (R3): below the wait limit the
# run never gives up
# EXCLUDES: a give-up before the stated limit (pending work abandoned
#   early)
law headless_settle_give_up_needs_limit:
  for b: Bool
  for j: Nat
  for k: Nat
  for c: Nat
  for w: Nat
  for x: Nat
  for u: Bool
  {gives_up(Hs.settle(Hs.Facts{b, j, k, c, w, x, u, False{}})) == False{} : Bool}

# LAW headless_settle_limit_exits (R3): once the wait limit elapsed the
# run never waits: every wait has an exit
# EXCLUDES: a headless run that waits forever on a job that never settles
law headless_settle_limit_exits:
  for b: Bool
  for j: Nat
  for k: Nat
  for c: Nat
  for w: Nat
  for x: Nat
  for u: Bool
  {waiting(Hs.settle(Hs.Facts{b, j, k, c, w, x, u, True{}})) == False{} : Bool}

# LAW headless_settle_example (R1-R3): anchor: quiet stops (below and at
# the limit); a job waits; two subagents at the limit give up; a wake, an
# unknown read and a busy conversation wait
# EXCLUDES: a spec that drifts from the decisions Rust acts on
law headless_settle_example:
  {[Hs.settle(Hs.Facts{False{}, 0n, 0n, 0n, 0n, 0n, False{}, False{}}), Hs.settle(Hs.Facts{False{}, 0n, 0n, 0n, 0n, 0n, False{}, True{}}), Hs.settle(Hs.Facts{False{}, 1n, 0n, 0n, 0n, 0n, False{}, False{}}), Hs.settle(Hs.Facts{False{}, 0n, 0n, 2n, 0n, 0n, False{}, True{}}), Hs.settle(Hs.Facts{False{}, 0n, 0n, 0n, 0n, 1n, False{}, False{}}), Hs.settle(Hs.Facts{False{}, 0n, 0n, 0n, 0n, 0n, True{}, False{}}), Hs.settle(Hs.Facts{True{}, 0n, 0n, 0n, 0n, 0n, False{}, False{}})] == [Hs.Finished{}, Hs.Finished{}, Hs.Waiting{}, Hs.GiveUp{}, Hs.Waiting{}, Hs.Waiting{}, Hs.Waiting{}] : List<&2, Hs.Settle>}

# Laws: the entry (R4)
# --------------------

# LAW headless_settle_entry_answers (R4): the entry answers every request
# Rust spells, every count within the wire, with the spelling of the
# spec's decision
# EXCLUDES: a field misread or swapped (two counts, busy and unknown), a
#   decision tag of another answer, a default
law headless_settle_entry_answers:
  for +f: Hs.Facts
  for fit: {SpW.fit_settle(f) == True{} : Bool}
  {FHs.ffi(SpW.w_settle_req(f, "")) == SpW.w_settle_reply(f) : String}

# LAW headless_settle_entry_reads (R4): the laws' reader reads every
# spelled request that fits the wire back whole, so
# headless_settle_entry_malformed_exact refuses only what Rust never
# writes
# EXCLUDES: a reader (and so an entry) that refuses a request Rust writes
law headless_settle_entry_reads:
  for +f: Hs.Facts
  for fit: {SpW.fit_settle(f) == True{} : Bool}
  {SpW.read_settle(SpW.w_settle_req(f, "")) == Some{f} : Maybe<&2, Hs.Facts>}

# LAW headless_settle_entry_malformed_exact (R4): every input that is not
# exactly one request (a malformed field, a short request, input left
# over) gets exactly the error form 'E ', then
# "headless_settle: malformed request"
# EXCLUDES: a decision answered for input that is no request, another
#   error text, a default
law headless_settle_entry_malformed_exact:
  for +s: String
  for no: {SpW.read_settle(s) == None{} : Maybe<&2, Hs.Facts>}
  {FHs.ffi(s) == Wr.err("headless_settle: malformed request") : String}

# LAW headless_settle_entry_example (R4): anchor: the strings Rust sends
# and the replies it reads: quiet, busy, kernel jobs at the limit, a
# subagent; a short request, input left over, a leading zero
# EXCLUDES: another spelling of a request or a reply
law headless_settle_entry_example:
  {[FHs.ffi("F0,0,0,0,0,FF"), FHs.ffi("T0,0,0,0,0,FF"), FHs.ffi("F0,3,0,0,0,FT"), FHs.ffi("F0,0,1,0,0,FF"), FHs.ffi("F0,0,0,0,0,F"), FHs.ffi("F0,0,0,0,0,FFx"), FHs.ffi("F01,0,0,0,0,FF")] == ["0,", "1,", "2,", "1,", Wr.err("headless_settle: malformed request"), Wr.err("headless_settle: malformed request"), Wr.err("headless_settle: malformed request")] : List<&2, String>}
