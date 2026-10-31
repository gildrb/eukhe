# eukhe: the laws of area family

import Base
import ../bend/family.bend as F
import ../bend/ffi_family.bend as FF
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/rlm/family.bend as FamSpec

# (D1) Subagent admission
# -----------------------
# bend/family.bend, run as the compiled core by bend/ffi_family.bend
# (eukhe-bend rules/family.rs; asked by eukhe-core
# durable/children/requests.rs for rlm.spawn, rlm.spawn_batch, the
# workflow tool's agent() and the factory's states). The spec is
# spec/rlm/family.bend (S1-S5).
# Every input is free: any depth, bound, running count, cap and whys.
#
# R1: the decision on a batch is the spec's (S1-S5): the code refines it.
# R2: the texts of the refusals: the depth and cap texts Rust wrote before
#     the move (requests.rs `admit_spawns`, `concurrency_limit_full`)
#     byte for byte; the reason text names the task's index, the rule and
#     the four values.
# R3: the entry answers each request Rust writes (the depth, the bound,
#     the running count, the cap, then the whys as List<String>; every
#     number and length within the wire) with the decision (0 then the
#     child's depth | 1 then the refusal's text), reads exactly the request
#     and nothing after it, and answers any other input with the exact
#     error form `E family: malformed request`.

# Spec helpers
# ------------

# a verdict admits
def fam_admitted(v: F.Verdict) -> Bool:
  match v:
    case F.Admit{k}:
      True{}
    case F.Refuse{f}:
      False{}

# R2: the reason rule, as Rust's callers read it
def fam_rule() -> String:
  "why must be \"parallel\" (independent tasks run at once), \"isolate\" (the work would bloat this context; only a compact result comes back), \"tools\" (the task needs a tool set or instructions that conflict with this agent's) or \"user\" (the user asked for a subagent); otherwise do the work in this loop"

# R2: the text of a refusal at depth d under the bound m
def fam_text(+d: Nat, +m: Nat, f: F.Refusal) -> String:
  match f:
    case F.DepthLimit{}:
      String.append("RLM recursion depth limit reached (RLM_DEPTH=", String.append(Nat.show(d), String.append(", RLM_MAX_DEPTH=", String.append(Nat.show(m), ")"))))
    case F.FamilyFull{c}:
      String.append("subagent concurrency limit ", String.append(Nat.show(c), " is already full"))
    case F.NoReason{i}:
      String.append("rlm.spawn task ", String.append(Nat.show(i), String.append(" has no allowed why: ", fam_rule())))

# R3: the spelling of a request and of its reply

def fam_w_strs(ws: List<&2, String>, rest: String) -> String:
  match ws:
    case Nil{}:
      rest
    case w <> t:
      Wr.put_str(w, fam_w_strs(t, rest))

def fam_w_req(q: FF.Req, rest: String) -> String:
  match q:
    case FF.Req{d, m, r, c, +ws}:
      Wr.put_nat(d, Wr.put_nat(m, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(List.length(&2, String, ws), fam_w_strs(ws, rest))))))

def fam_w_verdict(+d: Nat, +m: Nat, v: F.Verdict) -> String:
  match v:
    case F.Admit{k}:
      Wr.put_nat(0n, Wr.put_nat(k, ""))
    case F.Refuse{f}:
      Wr.put_nat(1n, Wr.put_str(fam_text(d, m, f), ""))

def fam_w_reply(q: FF.Req) -> String:
  match q:
    case FF.Req{+d, +m, +r, +c, +ws}:
      fam_w_verdict(d, m, FamSpec.verdict(d, m, r, c, ws))

def fam_fit_strs(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case w <> t:
      Bool.and(LawsBase.wire_fits(String.length(w)), fam_fit_strs(t))

# every number and length of the request fits the wire
def fam_fit_req(q: FF.Req) -> Bool:
  match q:
    case FF.Req{d, m, r, c, +ws}:
      Bool.and(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(List.length(&2, String, ws)), fam_fit_strs(ws))))))

# Laws: the decision (R1)
# -----------------------

# LAW family_refusal_precedence (R1, S5): the decision on every batch is
# the spec's: a missing reason first, then the depth, then the cap
# EXCLUDES: the cap checked before the depth or the reasons, the depth
#   checked before the reasons, another index for a missing reason,
#   another cap named, another child depth
law family_refusal_precedence:
  for +d: Nat
  for +m: Nat
  for +r: Nat
  for +c: Nat
  for +ws: List<&2, String>
  {F.decide(d, m, r, c, ws) == FamSpec.verdict(d, m, r, c, ws) : F.Verdict}

# LAW family_admit_iff (R1, S1-S4): a batch is admitted exactly when every
# why is a reason, the caller is below the bound and the batch fits the cap
# EXCLUDES: an admission past a bound, a refusal of a batch that fits, a
#   reason accepted by prefix or case
law family_admit_iff:
  for +d: Nat
  for +m: Nat
  for +r: Nat
  for +c: Nat
  for +ws: List<&2, String>
  {fam_admitted(F.decide(d, m, r, c, ws)) == FamSpec.admits(d, m, r, c, ws) : Bool}

# LAW family_admit_depth_bound (R1, S2): an admitted child is one level
# deeper than its caller, and within the bound
# EXCLUDES: a child at the caller's depth or deeper by two, a child past
#   the bound (an off-by-one `depth > max`)
law family_admit_depth_bound:
  for +d: Nat
  for +m: Nat
  for +r: Nat
  for +c: Nat
  for +ws: List<&2, String>
  for +k: Nat
  for e: {F.decide(d, m, r, c, ws) == F.Admit{k} : F.Verdict}
  {k == 1n+d : Nat} & {Nat.is_le(k, m) == True{} : Bool}

# LAW family_refuse_at_depth (R1, S2): a caller at or past the bound is
# refused for the depth when its whys are reasons
# EXCLUDES: a spawn at the bound admitted, the cap refusal named instead
law family_refuse_at_depth:
  for +d: Nat
  for +m: Nat
  for +r: Nat
  for +c: Nat
  for +ws: List<&2, String>
  for ok: {FamSpec.first_bad(ws, 0n) == None{} : Maybe<&2, Nat>}
  for at: {Nat.is_le(m, d) == True{} : Bool}
  {F.decide(d, m, r, c, ws) == F.Refuse{F.DepthLimit{}} : F.Verdict}

# LAW family_cap_bound (R1, S3): an admitted batch fits the cap with the
# family's running subagents
# EXCLUDES: a batch admitted when only its first spawn fits, the running
#   count left out, a cap of 0 read as full
law family_cap_bound:
  for +d: Nat
  for +m: Nat
  for +r: Nat
  for +c: Nat
  for +ws: List<&2, String>
  for +k: Nat
  for e: {F.decide(d, m, r, c, ws) == F.Admit{k} : F.Verdict}
  {FamSpec.cap_ok(r, c, List.length(&2, String, ws)) == True{} : Bool}

# LAW family_batch_all_or_none (R1, S4): a batch xs ++ ys is admitted
# exactly when xs is and then ys is, with the xs running: one batch is
# one decision on all of it
# EXCLUDES: a batch admitted in part (the spawns that fit), a batch whose
#   size is not counted whole, a reason checked only on the first spawn
law family_batch_all_or_none:
  for +d: Nat
  for +m: Nat
  for +r: Nat
  for +c: Nat
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  {fam_admitted(F.decide(d, m, r, c, List.append(&2, String, xs, ys))) == Bool.and(fam_admitted(F.decide(d, m, r, c, xs)), fam_admitted(F.decide(d, m, Nat.add(r, List.length(&2, String, xs)), c, ys))) : Bool}

# LAW family_why_required (R1, S1, S5): a batch with a why that is no
# reason is refused for it, naming the first such task, whatever the
# depth and the cap
# EXCLUDES: a missing why defaulted, a reason matched by prefix, the
#   depth or cap refusal hiding a missing reason, a later index named
law family_why_required:
  for +d: Nat
  for +m: Nat
  for +r: Nat
  for +c: Nat
  for +ws: List<&2, String>
  for +i: Nat
  for e: {FamSpec.first_bad(ws, 0n) == Some{i} : Maybe<&2, Nat>}
  {F.decide(d, m, r, c, ws) == F.Refuse{F.NoReason{i}} : F.Verdict}

# LAW family_text_spec (R2): every refusal text is the spec's
# EXCLUDES: a changed depth or cap text, the depth and bound swapped
law family_text_spec:
  for +d: Nat
  for +m: Nat
  for +f: F.Refusal
  {F.text(d, m, f) == fam_text(d, m, f) : String}

# LAW family_example (R1, R2): anchor: Rust's tests: a spawn at depth 2
# under the bound 2; a batch of 3 with 1 running under the cap 3; a
# batch of 2 that fits; an empty why; a why of another case
# EXCLUDES: a spec that drifts from the Rust it replaced
law family_example:
  {[F.decide(2n, 2n, 0n, 0n, ["parallel"]), F.decide(0n, 2n, 1n, 3n, ["parallel", "parallel", "tools"]), F.decide(0n, 2n, 1n, 3n, ["isolate", "user"]), F.decide(2n, 2n, 0n, 0n, ["parallel", ""]), F.decide(0n, 2n, 0n, 0n, ["Parallel"])] == [F.Refuse{F.DepthLimit{}}, F.Refuse{F.FamilyFull{3n}}, F.Admit{1n}, F.Refuse{F.NoReason{1n}}, F.Refuse{F.NoReason{0n}}] : List<&2, F.Verdict>}

# LAW family_text_example (R2): anchor: the texts Rust's tests read
# EXCLUDES: a text that drifts from the Rust it replaced
law family_text_example:
  {[F.text(2n, 2n, F.DepthLimit{}), F.text(0n, 2n, F.FamilyFull{3n})] == ["RLM recursion depth limit reached (RLM_DEPTH=2, RLM_MAX_DEPTH=2)", "subagent concurrency limit 3 is already full"] : List<&2, String>}

# Laws: the entry (R3)
# --------------------

# LAW family_entry_answers (R3): the entry answers every request Rust
# spells, every number and length within the wire, with the spec's
# decision spelled
# EXCLUDES: fields read in another order, the running count and the cap
#   swapped, a why lost, a default
law family_entry_answers:
  for +q: FF.Req
  for fit: {fam_fit_req(q) == True{} : Bool}
  {FF.ffi(fam_w_req(q, "")) == fam_w_reply(q) : String}

# LAW family_entry_left_over (R3): a spelled request followed by more
# input answers the error form
# EXCLUDES: the input after the request ignored or read into a field
law family_entry_left_over:
  for +q: FF.Req
  for +ch: Char
  for +t: String
  for fit: {fam_fit_req(q) == True{} : Bool}
  {FF.ffi(fam_w_req(q, SCon{ch, t})) == Wr.err("family: malformed request") : String}

# LAW family_entry_reads (R3): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (a short field, a list
#   shorter than its count, input left over)
law family_entry_reads:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FF.ffi(s)) == False{} : Bool}
  exs q: FF.Req
  {s == fam_w_req(q, "") : String} & {fam_fit_req(q) == True{} : Bool}

# LAW family_entry_malformed_exact (R3): every error the entry answers is
# exactly `E family: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law family_entry_malformed_exact:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FF.ffi(s)) == True{} : Bool}
  {FF.ffi(s) == Wr.err("family: malformed request") : String}

# LAW family_entry_example (R3): anchor: the wire strings Rust sends and
# the replies it reads
# EXCLUDES: another spelling of a request or of a reply
law family_entry_example:
  {[FF.ffi("2,2,0,0,1,8,parallel"), FF.ffi("0,2,1,3,2,7,isolate4,user"), FF.ffi("0,2,0,0,0,x"), FF.ffi("0,2,0,")] == ["1,64,RLM recursion depth limit reached (RLM_DEPTH=2, RLM_MAX_DEPTH=2)", "0,1,", Wr.err("family: malformed request"), Wr.err("family: malformed request")] : List<&2, String>}
