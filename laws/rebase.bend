# eukhe: the laws of area rebase

import Base
import ../bend/rebase.bend as R
import ../bend/ffi_rebase.bend as FR
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/harness/rebase.bend as RbSpec

# (H1) The three-way rebase of a stale edit
# -----------------------------------------
# bend/rebase.bend, run as the compiled core by bend/ffi_rebase.bend
# (eukhe-bend rules/rebase.rs; asked by eukhe-docs rebase.rs for the
# hashline patcher's recovery of an edit whose tag names an older
# snapshot: omp² "documents checked out", the 3-way rebase). Every input is
# free: any base, head and edits, sorted or not.
#
# R1: the rebase follows spec/harness/rebase.bend S1-S5: the edits are
#     sorted and apart or Invalid at the first that is not
#     (rebase_invalid_first); a head that is the base takes them unchanged
#     (R2); each edit is found in the head by its window (its lines with 0
#     to 8 lines of context, anchored at the file's ends), landing only
#     where the base and the head each hold exactly one copy, else Moved
#     (no copy in the head) or Ambiguous (two or more at every context)
#     (R3-R5); the edits are decided each alone, the first failure refuses
#     all, landed edits that cross are refused (rebase_each_alone).
# R2: a head that is the base takes valid edits unchanged.
# R3: a stale edit whose lines the head left in place (found once in the
#     base, at the edit, and once in the head) lands there with the same
#     effect: the same lines replaced by the same lines.
# R4: an edit whose lines (with the context it is first looked for by)
#     the head no longer holds refuses the whole rebase: nothing lands in
#     part.
# R5: an alignment with more than one match at every context is refused
#     (Ambiguous), never guessed.
# R6: a rebase that lands answers edits that apply to the head: sorted and
#     apart within it, one per edit, each putting the edit's lines in place
#     of head lines that are exactly the base lines the edit replaced (the
#     3-way merge: the head's change kept outside, the session's inside).
# R7: the entry answers each request Rust writes (the base, the head and
#     the flat edits as List<Nat>: start, end, the count of lines, the
#     lines; every number within the wire) with the rule's answer within
#     the work bound (the edits times the lines of base and head at most
#     1048576, else TooLarge): `0,` then the flat edits, or `1,` then the
#     refusal's tag (0 Invalid, 1 Moved, 2 Ambiguous, 3 Crossed, each with
#     the edit's index; 4 TooLarge); reads exactly the request; answers
#     anything else with `E rebase: malformed request`.

# Spec helpers: the entry's spelling
# ----------------------------------

# the edits, flat: start, end, the count of lines, the lines
def rb_flat(es: List<&2, R.Edit>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      match e:
        case R.Edit{s, t, +ls}:
          s <> (t <> (List.length(&2, Nat, ls) <> List.append(&2, Nat, ls, rb_flat(rest))))

def rb_nats(xs: List<&2, Nat>, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)

# a request: the base, the head, the flat edits
def rb_w_req(b: List<&2, Nat>, h: List<&2, Nat>, es: List<&2, R.Edit>, rest: String) -> String:
  rb_nats(b, rb_nats(h, rb_nats(rb_flat(es), rest)))

def rb_nfit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# every count and number of the request fits the wire
def rb_fit(+b: List<&2, Nat>, +h: List<&2, Nat>, es: List<&2, R.Edit>) -> Bool:
  Bool.and(rb_nfit(b), Bool.and(rb_nfit(h), rb_nfit(rb_flat(es))))

def rb_w_why(w: R.Why) -> String:
  match w:
    case R.Invalid{i}:
      Wr.put_nat(0n, Wr.put_nat(i, ""))
    case R.Moved{i}:
      Wr.put_nat(1n, Wr.put_nat(i, ""))
    case R.Ambiguous{i}:
      Wr.put_nat(2n, Wr.put_nat(i, ""))
    case R.Crossed{i}:
      Wr.put_nat(3n, Wr.put_nat(i, ""))
    case R.TooLarge{}:
      Wr.put_nat(4n, "")

# a reply
def rb_w_reply(o: R.Outcome) -> String:
  match o:
    case R.Rebased{fs}:
      Wr.put_nat(0n, rb_nats(rb_flat(fs), ""))
    case R.Conflict{w}:
      Wr.put_nat(1n, rb_w_why(w))

# the most edits times lines one rebase scans
def rb_work_max() -> Nat:
  1048576n

def rb_bounded.of(ok: Bool, +b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> R.Outcome:
  match ok:
    case True{}:
      R.rebase(b, h, es)
    case False{}:
      R.Conflict{R.TooLarge{}}

# the rule's answer within the work bound
def rb_answer(+b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> R.Outcome:
  rb_bounded.of(Nat.is_le(Nat.mul(List.length(&2, R.Edit, es), Nat.add(List.length(&2, Nat, b), List.length(&2, Nat, h))), rb_work_max()), b, h, es)

# Spec helpers: the rule's refusals
# ---------------------------------

# the edit an Invalid refusal names; none for any other answer
def rb_invalid(o: R.Outcome) -> Maybe<&2, Nat>:
  match o:
    case R.Rebased{fs}:
      None{}
    case R.Conflict{w}:
      match w:
        case R.Invalid{i}:
          Some{i}
        case R.Moved{i}:
          None{}
        case R.Ambiguous{i}:
          None{}
        case R.Crossed{i}:
          None{}
        case R.TooLarge{}:
          None{}

# a refusal's reason, naming the i-th edit
def rb_at(w: R.Why, +i: Nat) -> R.Why:
  match w:
    case R.Invalid{k}:
      R.Invalid{i}
    case R.Moved{k}:
      R.Moved{i}
    case R.Ambiguous{k}:
      R.Ambiguous{i}
    case R.Crossed{k}:
      R.Crossed{i}
    case R.TooLarge{}:
      R.TooLarge{}

# S5 for one edit: o is the rebase of the i-th edit alone, r the answer
# for the edits after it; the edit it lands as joins r, its refusal
# refuses them all, naming the i-th edit
def rb_alone.at(o: R.Outcome, +i: Nat, r: R.Outcome) -> R.Outcome:
  match o:
    case R.Rebased{fs}:
      match fs:
        case Nil{}:
          r
        case Con{f, more}:
          match r:
            case R.Rebased{gs}:
              R.Rebased{f <> gs}
            case R.Conflict{w}:
              R.Conflict{w}
    case R.Conflict{w}:
      R.Conflict{rb_at(w, i)}

# the edits es (the first is the i-th) each rebased alone onto h
def rb_alone.go(+b: List<&2, Nat>, +h: List<&2, Nat>, es: List<&2, R.Edit>, +i: Nat) -> R.Outcome:
  match es:
    case Nil{}:
      R.Rebased{Nil{}}
    case Con{e, rest}:
      rb_alone.at(R.rebase(b, h, [e]), i, rb_alone.go(b, h, rest, 1n+i))

# S5 from each edit alone: the first refusal refuses all; else the edits
# as each lands alone, refused as Crossed at the first that breaks S1
# against the head (RbSpec.crossed: each edit against the one before it)
def rb_alone(+b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> R.Outcome:
  RbSpec.crossed(rb_alone.go(b, h, es, 0n), List.length(&2, Nat, h))

# A request, as the entry's answer shows it was spelled
type Ask is Data:
  Ask{base: List<&2, Nat>, head: List<&2, Nat>, edits: List<&2, R.Edit>}

def rb_w_ask(q: Ask) -> String:
  match q:
    case Ask{b, h, es}:
      rb_w_req(b, h, es, "")

def rb_fit_ask(q: Ask) -> Bool:
  match q:
    case Ask{+b, +h, es}:
      rb_fit(b, h, es)

# Laws: the rule
# --------------

# LAW rebase_invalid_first (R1: S1): a rebase is refused as Invalid exactly
# when its edits are not sorted and apart within the base, and then names
# the first edit that breaks it (RbSpec.bad: each edit within the base and
# after the one before it, compared pairwise), for every base, head and
# edits
# EXCLUDES: the floor of an insertion taken as its end (two insertions at
#   one place passed), an edit past the base or ending before it starts
#   passed, a later or earlier index named, Invalid answered for sorted
#   edits, an unchanged head that skips the check
law rebase_invalid_first:
  for +b: List<&2, Nat>
  for +h: List<&2, Nat>
  for +es: List<&2, R.Edit>
  {rb_invalid(R.rebase(b, h, es)) == RbSpec.bad(es, List.length(&2, Nat, b)) : Maybe<&2, Nat>}

# LAW rebase_each_alone (R1: S4, S5): sorted edits against a head that is
# not the base are decided edit by edit, each as the rebase of that edit
# alone decides it: the first edit whose own rebase is refused refuses them
# all, naming that edit with the same reason; else each lands where it
# lands alone, and the landed edits are refused as Crossed at the first
# that is not sorted and apart from the one before it in the head
# EXCLUDES: an edit landed or refused by the edits around it (an offset
#   carried over, a window cut at a neighbour), a refusal named at another
#   index or with another reason, a later refusal reported before an
#   earlier one, landed edits that cross returned, Crossed at another index
law rebase_each_alone:
  for +b: List<&2, Nat>
  for +h: List<&2, Nat>
  for +es: List<&2, R.Edit>
  for ok: {RbSpec.valid(es, List.length(&2, Nat, b)) == True{} : Bool}
  for stale: {RbSpec.same(b, h) == False{} : Bool}
  {R.rebase(b, h, es) == rb_alone(b, h, es) : R.Outcome}

# LAW rebase_identity_when_head_is_base (R2): a head that is the base takes
# valid edits unchanged
# EXCLUDES: an unchanged file still searched (a repeated line refused), an
#   edit moved or its lines changed when nothing moved
law rebase_identity_when_head_is_base:
  for +b: List<&2, Nat>
  for +es: List<&2, R.Edit>
  for ok: {RbSpec.valid(es, List.length(&2, Nat, b)) == True{} : Bool}
  {R.rebase(b, b, es) == R.Rebased{es} : R.Outcome}

# LAW rebase_disjoint_lands (R3): a stale replacement of the base lines
# [s, t) whose lines occur once in the base (at s) and once in the head (at
# j) lands at j, replacing as many lines with the same lines
# EXCLUDES: a disjoint edit refused, landed at its base position or off by
#   the head's change before it, its length or lines changed, the head's
#   own change dropped (the answer is the one edit)
law rebase_disjoint_lands:
  for +b: List<&2, Nat>
  for +h: List<&2, Nat>
  for +s: Nat
  for +t: Nat
  for +p: List<&2, Nat>
  for +j: Nat
  for apart: {Nat.is_lt(s, t) == True{} : Bool}
  for inside: {Nat.is_le(t, List.length(&2, Nat, b)) == True{} : Bool}
  for stale: {RbSpec.same(b, h) == False{} : Bool}
  for once_b: {RbSpec.copies(b, RbSpec.region(b, R.Edit{s, t, p})) == [s] : List<&2, Nat>}
  for once_h: {RbSpec.copies(h, RbSpec.region(b, R.Edit{s, t, p})) == [j] : List<&2, Nat>}
  {R.rebase(b, h, [R.Edit{s, t, p}]) == R.Rebased{[R.Edit{j, Nat.add(j, Nat.sub(t, s)), p}]} : R.Outcome}

# LAW rebase_conflict_no_write (R4): when the head holds no copy of an
# edit's first window, the rebase of any edits around it is refused whole
# EXCLUDES: the other edits landed without it, an overlapping edit written
#   over the head's change, an edit placed by its old line numbers
law rebase_conflict_no_write:
  for +b: List<&2, Nat>
  for +h: List<&2, Nat>
  for +xs: List<&2, R.Edit>
  for +e: R.Edit
  for +ys: List<&2, R.Edit>
  for stale: {RbSpec.same(b, h) == False{} : Bool}
  for gone: {RbSpec.held(b, h, e) == Nil{} : List<&2, Nat>}
  {RbSpec.is_conflict(R.rebase(b, h, List.append(&2, R.Edit, xs, e <> ys))) == True{} : Bool}

# LAW rebase_ambiguous_refused (R5): a valid edit whose every window the
# contexts allow occurs twice or more in a changed head is refused as
# Ambiguous
# EXCLUDES: the first (or any) of several copies taken, a refusal named
#   Moved, a context bound that gives up early and guesses
law rebase_ambiguous_refused:
  for +b: List<&2, Nat>
  for +h: List<&2, Nat>
  for +e: R.Edit
  for ok: {RbSpec.valid([e], List.length(&2, Nat, b)) == True{} : Bool}
  for stale: {RbSpec.same(b, h) == False{} : Bool}
  for many: {RbSpec.many(b, h, e) == True{} : Bool}
  {R.rebase(b, h, [e]) == R.Conflict{R.Ambiguous{0n}} : R.Outcome}

# LAW rebase_result_applies (R6): the edits a rebase answers replay the
# session's edits on the head: sorted and apart within it, one for each,
# with its lines, over head lines that are the base lines it replaced
# EXCLUDES: an edit landed on lines the head changed, a landing shifted by
#   the context, a length or lines changed in the move, edits that overlap
#   or run past the head, an edit dropped or added
law rebase_result_applies:
  for +b: List<&2, Nat>
  for +h: List<&2, Nat>
  for +es: List<&2, R.Edit>
  for +fs: List<&2, R.Edit>
  for got: {R.rebase(b, h, es) == R.Rebased{fs} : R.Outcome}
  {RbSpec.replays(b, h, es, fs) == True{} : Bool}

# LAW rebase_example (R1): anchor: the byte rebase's tests, one line per
# word (ids): a stale disjoint edit lands; the edit's lines changed in the
# head; two insertions at one gap; a deletion before the edit shifts it;
# repeated lines; two edits around a head insertion; insertions at one
# place; a range past the base; blocks the head swapped; an insertion at
# the file's start
# EXCLUDES: a spec that drifts from the Rust it replaced
law rebase_example:
  {[R.rebase([1n, 2n, 3n], [4n, 2n, 3n], [R.Edit{2n, 3n, [5n]}]), R.rebase([1n, 2n, 3n], [1n, 6n, 3n], [R.Edit{1n, 2n, [7n]}]), R.rebase([1n, 2n], [1n, 3n, 2n], [R.Edit{1n, 1n, [9n]}]), R.rebase([1n, 2n, 3n], [2n, 3n], [R.Edit{2n, 3n, [8n]}]), R.rebase([1n, 1n, 1n, 1n], [1n, 1n, 1n, 1n, 1n], [R.Edit{1n, 2n, [9n]}]), R.rebase([1n, 2n, 3n, 4n, 5n, 6n], [1n, 2n, 3n, 4n, 7n, 5n, 6n], [R.Edit{1n, 2n, [8n]}, R.Edit{5n, 6n, [9n]}]), R.rebase([1n, 2n], [1n, 2n], [R.Edit{1n, 1n, [9n]}, R.Edit{1n, 1n, [9n]}]), R.rebase([1n, 2n], [3n, 1n, 2n], [R.Edit{1n, 3n, [9n]}]), R.rebase([1n, 2n, 3n, 4n], [3n, 4n, 1n, 2n], [R.Edit{0n, 1n, [8n]}, R.Edit{2n, 3n, [9n]}]), R.rebase([1n, 2n], [1n, 2n, 3n], [R.Edit{0n, 0n, [9n]}])] == [R.Rebased{[R.Edit{2n, 3n, [5n]}]}, R.Conflict{R.Moved{0n}}, R.Conflict{R.Moved{0n}}, R.Rebased{[R.Edit{1n, 2n, [8n]}]}, R.Conflict{R.Ambiguous{0n}}, R.Rebased{[R.Edit{1n, 2n, [8n]}, R.Edit{6n, 7n, [9n]}]}, R.Conflict{R.Invalid{1n}}, R.Conflict{R.Invalid{0n}}, R.Conflict{R.Crossed{1n}}, R.Rebased{[R.Edit{0n, 0n, [9n]}]}] : List<&2, R.Outcome>}

# Laws: the entry (R7)
# --------------------

# LAW rebase_entry_answers (R7): the entry answers every request Rust
# spells, every number within the wire, with the rule's answer (pinned by
# the R1-R6 laws) within the work bound, spelled
# EXCLUDES: the base and the head swapped, an edit's start, end or count
#   misread, the bound skipped or counted on other sizes, a refusal spelled
#   with another tag or without its index, a default
law rebase_entry_answers:
  for +b: List<&2, Nat>
  for +h: List<&2, Nat>
  for +es: List<&2, R.Edit>
  for fit: {rb_fit(b, h, es) == True{} : Bool}
  {FR.ffi(rb_w_req(b, h, es, "")) == rb_w_reply(rb_answer(b, h, es)) : String}

# LAW rebase_entry_left_over (R7): a spelled request followed by more input
# answers the error form
# EXCLUDES: the input after the request ignored or read into a field
law rebase_entry_left_over:
  for +b: List<&2, Nat>
  for +h: List<&2, Nat>
  for +es: List<&2, R.Edit>
  for +c: Char
  for +t: String
  for fit: {rb_fit(b, h, es) == True{} : Bool}
  {FR.ffi(rb_w_req(b, h, es, SCon{c, t})) == Wr.err("rebase: malformed request") : String}

# LAW rebase_entry_reads (R7): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an edit cut short, a
#   count past the lines left, a list shorter than its count, input left
#   over)
law rebase_entry_reads:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FR.ffi(s)) == False{} : Bool}
  exs q: Ask
  {s == rb_w_ask(q) : String} & {rb_fit_ask(q) == True{} : Bool}

# LAW rebase_entry_refuses (R7): every error the entry answers is exactly
# `E rebase: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law rebase_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FR.ffi(s)) == True{} : Bool}
  {FR.ffi(s) == Wr.err("rebase: malformed request") : String}

# LAW rebase_entry_example (R7): anchor: the wire strings Rust sends and
# the replies it reads: a landing, a refusal with its index, an edit cut
# short, input left over, the work bound
# EXCLUDES: another spelling of a request or of a reply
law rebase_entry_example:
  {[FR.ffi("3,1,2,3,3,4,2,3,4,2,3,1,5,"), FR.ffi("3,1,2,3,3,1,6,3,4,1,2,1,7,"), FR.ffi("2,1,2,2,1,2,2,1,1,"), FR.ffi("2,1,2,2,1,2,0,x"), FR.ffi("0,0,0,")] == ["0,4,2,3,1,5,", "1,1,0,", Wr.err("rebase: malformed request"), Wr.err("rebase: malformed request"), "0,0,"] : List<&2, String>}
