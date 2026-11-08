# eukhe: the laws of area workflow, section entry: the whole entry bend/ffi_workflow.bend, every input
# (R1, R2, R3)

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../bend/workflow.bend as W
import ../base.bend as LawsBase
import ./model.bend as Workflow

# The whole entry, every input (R1, R2, R3)
# -----------------------------------------
# The request and the reply as the grammar above, read and spelled with
# the wire primitives alone (never the entry's own codec), and the answer
# from the spec of the admission and the limits (wf_again, wf_first,
# wf_min, the pool's units; the laws wf_admitted_never_respawns,
# wf_reuses_first_answer, wf_spawns_within_budget, wf_refused_when_spent,
# wf_limits_uncapped and wf_limits_capped pin W.admit and W.effective to
# them for every input). A request that cannot be read answers "workflow:
# malformed request"; a request with input after it answers "workflow:
# input left over".

def wfs_read.status(t: Nat, s: String) -> Wr.Dec<W.Sts>:
  match t:
    case 0n:
      Wr.Got{W.Queued{}, s}
    case 1n:
      Wr.Got{W.Running{}, s}
    case 2n:
      Wr.Got{W.Finished{}, s}
    case 3n:
      Wr.Got{W.Erred{}, s}
    case 4n:
      Wr.Got{W.Cancelled{}, s}
    case 5n:
      Wr.Got{W.Cached{}, s}
    case 6n+p:
      Wr.Bad{}

# a status: its tag (0 queued | 1 running | 2 done | 3 failed | 4 cancelled
# | 5 cached)
def wfs_read_sts(r: Wr.Dec<Nat>) -> Wr.Dec<W.Sts>:
  match r:
    case Wr.Got{t, s}:
      wfs_read.status(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read_row.sts(k: Nat, r: Wr.Dec<W.Sts>) -> Wr.Dec<W.Row>:
  match r:
    case Wr.Got{st, s}:
      Wr.Got{W.Row{k, st}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read_row.of(r: Wr.Dec<Nat>) -> Wr.Dec<W.Row>:
  match r:
    case Wr.Got{k, s}:
      wfs_read_row.sts(k, wfs_read_sts(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a row: its key, then its status
def wfs_read_row(s: String) -> Wr.Dec<W.Row>:
  wfs_read_row.of(Wr.get_nat(s))

def wfs_read.left(prior: Maybe<&2, W.Sts>, k: Nat, rows: List<&2, W.Row>, t: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FW.Req>:
  match r:
    case Wr.Got{l, s}:
      Wr.Got{FW.AdmitReq{prior, k, rows, W.Pool{t, l}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read.taken(prior: Maybe<&2, W.Sts>, k: Nat, rows: List<&2, W.Row>, r: Wr.Dec<Nat>) -> Wr.Dec<FW.Req>:
  match r:
    case Wr.Got{t, s}:
      wfs_read.left(prior, k, rows, t, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read.rows(prior: Maybe<&2, W.Sts>, k: Nat, r: Wr.Dec<List<&2, W.Row>>) -> Wr.Dec<FW.Req>:
  match r:
    case Wr.Got{rows, s}:
      wfs_read.taken(prior, k, rows, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read.key(prior: Maybe<&2, W.Sts>, r: Wr.Dec<Nat>) -> Wr.Dec<FW.Req>:
  match r:
    case Wr.Got{k, s}:
      wfs_read.rows(prior, k, LawsBase.wire_read_list(~W.Row, ~wfs_read_row, s))
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read.prior_some(r: Wr.Dec<W.Sts>) -> Wr.Dec<FW.Req>:
  match r:
    case Wr.Got{st, s}:
      wfs_read.key(Some{st}, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read.prior(r: Wr.Dec<Nat>) -> Wr.Dec<FW.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          wfs_read.key(None{}, Wr.get_nat(s))
        case 1n:
          wfs_read.prior_some(wfs_read_sts(Wr.get_nat(s)))
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read.cap(c: Nat, m: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FW.Req>:
  match r:
    case Wr.Got{cap, s}:
      Wr.Got{FW.LimitsReq{c, m, cap}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read.max(c: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FW.Req>:
  match r:
    case Wr.Got{m, s}:
      wfs_read.cap(c, m, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read.conc(r: Wr.Dec<Nat>) -> Wr.Dec<FW.Req>:
  match r:
    case Wr.Got{c, s}:
      wfs_read.max(c, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def wfs_read.tag(r: Wr.Dec<Nat>) -> Wr.Dec<FW.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          wfs_read.prior(Wr.get_nat(s))
        case 1n:
          wfs_read.conc(Wr.get_nat(s))
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the head of s, and the input after it
def wfs_read(s: String) -> Wr.Dec<FW.Req>:
  wfs_read.tag(Wr.get_nat(s))

# a new call with no earlier answer: it spawns while the budget has an
# agent left (one moves from left to taken), else it is refused
def wfs_budget(p: W.Pool) -> W.Admit & W.Pool:
  match p:
    case W.Pool{t, l}:
      match l:
        case 0n:
          (W.Refused{}, W.Pool{t, 0n})
        case 1n+m:
          (W.Spawn{}, W.Pool{1n+t, m})

def wfs_fresh(hit: Maybe<&2, Nat>, p: W.Pool) -> W.Admit & W.Pool:
  match hit:
    case Some{i}:
      (W.Reuse{i}, p)
    case None{}:
      wfs_budget(p)

# the admission of one call: a repeated ordinal replays or reattaches; a
# new one reuses the first finished answer of its key, else the budget
# decides; only a spawn takes budget
def wfs_admit(prior: Maybe<&2, W.Sts>, +k: Nat, rows: List<&2, W.Row>, p: W.Pool) -> W.Admit & W.Pool:
  match prior:
    case Some{s}:
      (Workflow.wf_again(s), p)
    case None{}:
      wfs_fresh(Workflow.wf_first(rows, k), p)

def wfs_spell_admit(a: W.Admit, rest: String) -> String:
  match a:
    case W.Ended{}:
      Wr.put_nat(0n, rest)
    case W.Reattach{}:
      Wr.put_nat(1n, rest)
    case W.Reuse{i}:
      Wr.put_nat(2n, Wr.put_nat(i, rest))
    case W.Spawn{}:
      Wr.put_nat(3n, rest)
    case W.Refused{}:
      Wr.put_nat(4n, rest)

# the reply to an admission: the decision, then the pool (taken, left)
def wfs_spell_decision(d: W.Admit & W.Pool) -> String:
  (a, p) = d
  match p:
    case W.Pool{t, l}:
      wfs_spell_admit(a, Wr.put_nat(t, Wr.put_nat(l, "")))

# a run's concurrency: its size's with no cap (0), else at most the cap
def wfs_conc(c: Nat, cap: Nat) -> Nat:
  match cap:
    case 0n:
      c
    case 1n+x:
      Workflow.wf_min(c, 1n+x)

def wfs_reply(q: FW.Req) -> String:
  match q:
    case FW.AdmitReq{prior, k, rows, p}:
      wfs_spell_decision(wfs_admit(prior, k, rows, p))
    case FW.LimitsReq{c, m, cap}:
      Wr.put_nat(wfs_conc(c, cap), Wr.put_nat(m, ""))

def wfs_entry.of(d: Wr.Dec<FW.Req>) -> String:
  match d:
    case Wr.Got{q, r}:
      match r:
        case SNil{}:
          wfs_reply(q)
        case SCon{c, t}:
          Wr.err("workflow: input left over")
    case Wr.Bad{}:
      Wr.err("workflow: malformed request")

# the entry's answer to s
def wfs_entry(s: String) -> String:
  wfs_entry.of(wfs_read(s))

# LAW wfw_ffi_exact (R1, R2, R3): for every input, the entry answers exactly: on a request (as
# the wire primitives read it) with nothing after it, the admission of the
# call (a repeated ordinal replays or reattaches and takes no budget; a new
# one reuses the first finished answer of its key, else spawns while the
# budget has an agent left, else is refused) and the pool after it, or the
# run's limits (the concurrency at most the cap, 0 no cap; the max agents);
# on a request with input after it, the error form "workflow: input left
# over"; on any other input, the error form "workflow: malformed request"
# EXCLUDES: a misread or reordered field, row or status, a tag read as
#   another, an answer on garbage or on a request with input after it,
#   another error text, a codec of the entry wrong both ways (the spec
#   never calls it)
law wfw_ffi_exact:
  for +s: String
  {FW.ffi(s) == wfs_entry(s) : String}

# LAW wfw_ffi_exact_example (R1, R2, R3): anchor: the spec on the strings Rust writes: a spawn,
# a reuse of the first finished row of the key, a replay, a refusal, the
# limits under a cap; an unknown kind and input left over
# EXCLUDES: a field order other than Rust's, a vacuous wfw_ffi_exact
law wfw_ffi_exact_example:
  {[wfs_entry("0,0,7,1,3,3,1,2,"), wfs_entry("0,0,4,2,4,1,4,5,0,0,"), wfs_entry("0,1,2,7,0,1,0,"), wfs_entry("0,0,7,0,5,0,"), wfs_entry("1,4,9,2,"), wfs_entry("2,"), wfs_entry("1,4,9,0,x")] == ["3,2,1,", "2,1,0,0,", "0,1,0,", "4,5,0,", "2,9,", Wr.err("workflow: malformed request"), Wr.err("workflow: input left over")] : List<&2, String>}
