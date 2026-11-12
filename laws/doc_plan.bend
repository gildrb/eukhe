# eukhe: the laws of area doc_plan
#
# LAWS (R1, R2): what a session commit writes and publishes for one staged
# document (bend/doc_plan.bend, the port of eukhe-durable session/plans.rs
# `plan_loaded` and `publishes`). Each law is an open claim about
# Dp.content or Dp.publishes; PROOF.bend proves them (as DocPlan.<law>)
# with the lemmas of proof/doc_plan/.
#
# Requirements (crates/eukhe-durable/src/session/plans.rs doc comments):
# R1: a loaded incarnation whose stored version is older than its
#     definition's writes a new base, with or without staged operations;
#     else it writes a delta when operations are staged, and nothing when
#     none are.
# R2: adoption publishes a plan that retires its document, a plan with no
#     change or a created document's change, and a loaded incarnation's
#     plan only when it writes content (a migration-only base included).
# R3: the entry (section below) answers each question with R1-R2, spelled
#     as crates/eukhe-bend/WIRE.md, and any other input with its two error
#     forms.
# Every version, flag and change is free. R1 is stated by the arithmetic
# of the two versions (the definition's above the stored one by 1 + d, or
# the stored one at or above the definition's by d: every pair is one of
# the two), not by the code's comparison.

import Base
import ../bend/doc_plan.bend as Dp
import ../bend/ffi_doc_plan.bend as FDp
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# Terms
# -----

# R2: the plan writes content: Rust passes `content.is_some()` (plans.rs
# `publishes`), and only Kept stores nothing (plans.rs `plan_loaded`)
def writes(c: Dp.Content) -> Bool:
  match c:
    case Dp.Kept{}:
      False{}
    case Dp.NewBase{}:
      True{}
    case Dp.NewDelta{}:
      True{}

# Laws
# ----

# LAW doc_plan_base_when_older (R1): a loaded incarnation whose definition's version is above the stored one by any amount (version = stored + 1 + d) writes a new base, with or without staged operations
# EXCLUDES: a migration without operations that writes nothing or a delta;
#   a delta written over an older stored shape; a base only for a version
#   one above
law doc_plan_base_when_older:
  for +stored: Nat
  for +d: Nat
  for ops: Bool
  {Dp.content(stored, Nat.add(stored, 1n+d), ops) == Dp.NewBase{} : Dp.Content}

# LAW doc_plan_delta_when_not_older (R1): a loaded incarnation stored at its definition's version or any later one (stored = version + d) with staged operations writes a delta
# EXCLUDES: a base rewritten at the same version (`<=` for `<`) or over a
#   newer stored version; staged operations dropped
law doc_plan_delta_when_not_older:
  for +version: Nat
  for +d: Nat
  {Dp.content(Nat.add(version, d), version, True{}) == Dp.NewDelta{} : Dp.Content}

# LAW doc_plan_kept_when_not_older (R1): a loaded incarnation stored at its definition's version or any later one (stored = version + d) with no staged operations writes nothing
# EXCLUDES: an empty delta; a base rewritten at the same version or over a
#   newer stored version
law doc_plan_kept_when_not_older:
  for +version: Nat
  for +d: Nat
  {Dp.content(Nat.add(version, d), version, False{}) == Dp.Kept{} : Dp.Content}

# LAW doc_plan_unpublished_only_quiet_loaded (R2): a plan adoption leaves unpublished is a loaded incarnation's plan that neither retires its document nor writes content
# EXCLUDES: a creation, copy or retirement left unpublished; a loaded
#   incarnation's written content left unpublished
law doc_plan_unpublished_only_quiet_loaded:
  for +retire: Bool
  for +c: Dp.Change
  for +w: Bool
  for no: {Dp.publishes(retire, c, w) == False{} : Bool}
  {retire == False{} : Bool} & {c == Dp.OfLoaded{} : Dp.Change} & {w == False{} : Bool}

# LAW doc_plan_loaded_publishes_its_write (R1, R2): a loaded incarnation's plan that does not retire its document, without staged operations, is not published when stored at its definition's version or a later one (it writes nothing), and is published when its definition is newer (the migration-only base)
# EXCLUDES: a spurious notification for a plan that writes nothing; a
#   migration-only base left unpublished (observers keep the older shape)
law doc_plan_loaded_publishes_its_write:
  for +version: Nat
  for +d: Nat
  for +stored: Nat
  for +e: Nat
  {Dp.publishes(False{}, Dp.OfLoaded{}, writes(Dp.content(Nat.add(version, d), version, False{}))) == False{} : Bool} & {Dp.publishes(False{}, Dp.OfLoaded{}, writes(Dp.content(stored, Nat.add(stored, 1n+e), False{}))) == True{} : Bool}

# LAW doc_plan_example: anchor: a migration without operations writes a base, a same-version change a delta, a quiet incarnation nothing and is not published; a creation is published
# EXCLUDES: a model that is wrong on the session's cases
law doc_plan_example:
  {Dp.content(1n, 2n, False{}) == Dp.NewBase{} : Dp.Content} &
  {Dp.content(2n, 2n, True{}) == Dp.NewDelta{} : Dp.Content} &
  {Dp.content(2n, 2n, False{}) == Dp.Kept{} : Dp.Content} &
  {Dp.content(3n, 2n, True{}) == Dp.NewDelta{} : Dp.Content} &
  {Dp.publishes(False{}, Dp.OfLoaded{}, False{}) == False{} : Bool} &
  {Dp.publishes(False{}, Dp.Fresh{}, False{}) == True{} : Bool}

# LAWS (R3): the entry of the compiled Bend core (bend/ffi_doc_plan.bend,
# called by crates/eukhe-durable session plans through
# `eukhe_bend::rules::doc_plan`). Each law is an open claim about FDp.ffi,
# stated with spec spellers built only from the wire primitives of
# bend/wire.bend (their round trips: laws/wire.bend).
#
# R3: a request is a question: tag 0, the stored version and the
#     definition's version (Nats) and whether operations are staged
#     (Bool), answered with the content (0 nothing, 1 a new base, 2 a
#     delta); or tag 1, whether the plan retires its document (Bool), its
#     change (0 none, 1 a created document's, 2 a loaded incarnation's)
#     and whether it writes content (Bool), answered with whether adoption
#     publishes it (Bool). A malformed request answers the error form
#     "doc_plan: malformed request", input left after the request
#     "doc_plan: input left after the request", never a default.

# Spec spellers
# -------------

def spell_change(c: Dp.Change, rest: String) -> String:
  match c:
    case Dp.NoChange{}:
      Wr.put_nat(0n, rest)
    case Dp.Fresh{}:
      Wr.put_nat(1n, rest)
    case Dp.OfLoaded{}:
      Wr.put_nat(2n, rest)

# a question, then rest
def spell_req(q: FDp.Req, rest: String) -> String:
  match q:
    case FDp.QContent{s, v, o}:
      Wr.put_nat(0n, Wr.put_nat(s, Wr.put_nat(v, Wr.put_bool(o, rest))))
    case FDp.QPublishes{re, c, w}:
      Wr.put_nat(1n, Wr.put_bool(re, spell_change(c, Wr.put_bool(w, rest))))

def spell_content(c: Dp.Content) -> String:
  match c:
    case Dp.Kept{}:
      Wr.put_nat(0n, "")
    case Dp.NewBase{}:
      Wr.put_nat(1n, "")
    case Dp.NewDelta{}:
      Wr.put_nat(2n, "")

# the answer R3 gives a question: the model's choice (Dp.content,
# Dp.publishes, pinned by the R1-R2 laws above), spelled
def answer_spec(q: FDp.Req) -> String:
  match q:
    case FDp.QContent{s, v, o}:
      spell_content(Dp.content(s, v, o))
    case FDp.QPublishes{re, c, w}:
      Wr.put_bool(Dp.publishes(re, c, w), "")

# every number of the question fits the wire
def req_fits(q: FDp.Req) -> Bool:
  match q:
    case FDp.QContent{+s, +v, o}:
      Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(v))
    case FDp.QPublishes{re, c, w}:
      True{}

# a question with more input after it: the question, then a char and the
# rest
type LeftOver is Data:
  LeftOver{req: FDp.Req, head: Char, tail: String}

# the question of a left-over input
def left_req(w: LeftOver) -> FDp.Req:
  match w:
    case LeftOver{q, h, t}:
      q

def spell_left_over(w: LeftOver) -> String:
  match w:
    case LeftOver{q, h, t}:
      spell_req(q, SCon{h, t})

# Laws
# ----

# LAW doc_plan_ffi_answers (R3): a spelled question whose versions fit the wire answers the model's content or publish choice (pinned by the R1-R2 laws), spelled as R3
# EXCLUDES: the two versions swapped, a flag misread, a change of another
#   tag, the two questions swapped, an answer in another spelling
law doc_plan_ffi_answers:
  for +q: FDp.Req
  for fit: {req_fits(q) == True{} : Bool}
  {FDp.ffi(spell_req(q, "")) == answer_spec(q) : String}

# LAW doc_plan_ffi_exact: every input the entry answers with a value (not the error form) is a spelled question whose versions fit the wire
# EXCLUDES: a default answer for a malformed request (an unknown tag, a
#   missing field, a Nat of 15 or more digits) or one with input left over
law doc_plan_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FDp.ffi(s)) == False{} : Bool}
  exs q: FDp.Req
  {s == spell_req(q, "") : String} & {req_fits(q) == True{} : Bool}

# LAW doc_plan_ffi_left_over: a question that fits the wire, followed by more input, answers the left-over error form
# EXCLUDES: the input after the question ignored or read as part of it
law doc_plan_ffi_left_over:
  for +q: FDp.Req
  for +h: Char
  for +t: String
  for fit: {req_fits(q) == True{} : Bool}
  {FDp.ffi(spell_req(q, SCon{h, t})) == Wr.err("doc_plan: input left after the request") : String}

# LAW doc_plan_ffi_left_over_exact: the entry answers the left-over error form only for a spelled question that fits the wire, followed by more input
# EXCLUDES: the left-over text for a malformed request
law doc_plan_ffi_left_over_exact:
  for +s: String
  for e: {FDp.ffi(s) == Wr.err("doc_plan: input left after the request") : String}
  exs w: LeftOver
  {s == spell_left_over(w) : String} & {req_fits(left_req(w)) == True{} : Bool}

# LAW doc_plan_ffi_errors: every error the entry answers is the malformed or the left-over error form; with doc_plan_ffi_exact and doc_plan_ffi_left_over_exact, every input that spells no question answers exactly "doc_plan: malformed request"
# EXCLUDES: another error text
law doc_plan_ffi_errors:
  for +s: String
  for e: {LawsBase.wire_opens_err(FDp.ffi(s)) == True{} : Bool}
  {Bool.or(LawsBase.text_same(FDp.ffi(s), Wr.err("doc_plan: malformed request")), LawsBase.text_same(FDp.ffi(s), Wr.err("doc_plan: input left after the request"))) == True{} : Bool}

# LAW doc_plan_ffi_example: anchor: the exact bytes Rust sends for a migration without operations and for a quiet loaded incarnation, and three refusals
# EXCLUDES: another spelling of a question or of an answer
law doc_plan_ffi_example:
  {FDp.ffi("0,1,2,F") == "1," : String} &
  {FDp.ffi("1,F2,F") == "F" : String} &
  {FDp.ffi("1,F3,F") == Wr.err("doc_plan: malformed request") : String} &
  {FDp.ffi("0,1,2,") == Wr.err("doc_plan: malformed request") : String} &
  {FDp.ffi("1,T0,Tx") == Wr.err("doc_plan: input left after the request") : String}
