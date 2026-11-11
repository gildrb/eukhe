# eukhe: lemmas the proofs of area orphan share

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ../base/logic/bool.bend as LLogicBool
import ../base/nat.bend as LNat
import ./orphan_work_exit_due.bend as POrphanWorkExitDue

def ps.ffi_work(k: Or.Work, +r: String) -> {Wr.Got{k, r} == FO.get_work(FO.put_work(k, r)) : Wr.Dec<Or.Work>}:
  match k:
    case Or.Idle{}:
      {==}
    case Or.Ongoing{}:
      {==}

# The entry, by the grammar's spelling
# ------------------------------------

# a spelled window that fits reads back
def oe.window(m: Maybe<&2, Nat>, +r: String, fm: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, r} == FO.get_window(Orphan.orphan_spell_mwindow(m, r)) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %LWire.ps.ffi_nat(0n, r, {==}) : {Wr.Got{None{}, r} == FO.get_window.of(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+n}:
      %LWire.ps.ffi_nat(1n, Wr.put_nat(n, r), {==}) : {Wr.Got{Some{n}, r} == FO.get_window.of(_) : Wr.Dec<Maybe<&2, Nat>>}
      %LWire.ps.ffi_nat(n, r, fm) : {Wr.Got{Some{n}, r} == FO.get_window.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

# a spelled work reads back
def oe.work(k: Or.Work, +r: String) -> {Wr.Got{k, r} == FO.get_work(Orphan.orphan_spell_work(k, r)) : Wr.Dec<Or.Work>}:
  match k:
    case Or.Idle{}:
      {==}
    case Or.Ongoing{}:
      {==}

# a spelled request that fits reads back
def oe.req(q: FO.Req, +rest: String, fits: {Orphan.orphan_req_fits(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FO.get_req(Orphan.orphan_spell_req(q, rest)) : Wr.Dec<FO.Req>}:
  match q:
    case FO.Req{+m, +a, +k}:
      +fs = fits
      %oe.window(m, Wr.put_nat(a, Orphan.orphan_spell_work(k, rest)), LLogicBool.pq.and_l(LawsBase.wire_mfits(m), LawsBase.wire_fits(a), fs)) : {Wr.Got{FO.Req{m, a, k}, rest} == FO.get_req.window(_) : Wr.Dec<FO.Req>}
      %LWire.ps.ffi_nat(a, Orphan.orphan_spell_work(k, rest), LLogicBool.pq.and_r(LawsBase.wire_mfits(m), LawsBase.wire_fits(a), fs)) : {Wr.Got{FO.Req{m, a, k}, rest} == FO.get_req.absent(m, _) : Wr.Dec<FO.Req>}
      %oe.work(k, rest) : {Wr.Got{FO.Req{m, a, k}, rest} == FO.get_req.work(m, a, _) : Wr.Dec<FO.Req>}
      {==}

# a spelled request that fits, then rest, runs to the entry's last stage
def oe.run(+q: FO.Req, +rest: String, fits: {Orphan.orphan_req_fits(q) == True{} : Bool}) -> {FO.ffi(Orphan.orphan_spell_req(q, rest)) == FO.ffi.fin(Wr.end(rest), q) : String}:
  %oe.req(q, rest, fits) : {FO.ffi.go(_) == FO.ffi.fin(Wr.end(rest), q) : String}
  {==}

def oe.answer.at(m: Maybe<&2, Nat>, +a: Nat, k: Or.Work) -> {FO.put_reply(FO.decide(FO.Req{m, a, k}), "") == Orphan.orphan_spell_answer(FO.Req{m, a, k}) : String}:
  match m:
    case None{}:
      match k:
        case Or.Idle{}:
          {==}
        case Or.Ongoing{}:
          {==}
    case Some{+w}:
      match k:
        case Or.Idle{}:
          {==}
        case Or.Ongoing{}:
          Equal.cong(Bool, String, x => Wr.put_bool(x, Wr.put_nat(1n, "")), Or.exit_due.at(Some{w}, a, Or.Ongoing{}), Nat.is_le(Nat.add(w, w), a), Orphan.orphan_work_exit_due(w, a))

# the entry's reply on the model's decision is the spelled spec decision
def oe.answer(q: FO.Req) -> {FO.put_reply(FO.decide(q), "") == Orphan.orphan_spell_answer(q) : String}:
  match q:
    case FO.Req{m, +a, k}:
      oe.answer.at(m, a, k)

# The event machine by its history
# --------------------------------

# a history and one more event
def oh.snoc(xs: List<&2, Or.Ev>, e: Or.Ev) -> List<&2, Or.Ev>:
  List.append(&2, Or.Ev, xs, [e])

# The machine's state, field by field: one left fold per field over the
# history, each step the machine's step on that field (oh.agree equates
# them with the declared state of laws/orphan.bend)

# a run: a run start opens it, a run end closes it, any other event keeps it
def oh.run_ev(open: Bool, e: Or.Ev) -> Bool:
  match e:
    case Or.RunStart{}:
      True{}
    case Or.RunEnd{}:
      False{}
    case Or.Queue{}:
      open
    case Or.Drain{}:
      open
    case Or.CompactStart{}:
      open
    case Or.CompactEnd{}:
      open
    case Or.Gone{g}:
      open
    case Or.Back{}:
      open

def oh.run_fold(evs: List<&2, Or.Ev>, open: Bool) -> Bool:
  match evs:
    case Nil{}:
      open
    case e <> rest:
      oh.run_fold(rest, oh.run_ev(open, e))

# whether a run is open after the history evs, from `open` (a left fold)
def oh.run_open(open: Bool, evs: List<&2, Or.Ev>) -> Bool:
  oh.run_fold(evs, open)

# a compaction: a compaction start opens it, a compaction end closes it,
# any other event keeps it
def oh.compact_ev(open: Bool, e: Or.Ev) -> Bool:
  match e:
    case Or.RunStart{}:
      open
    case Or.RunEnd{}:
      open
    case Or.Queue{}:
      open
    case Or.Drain{}:
      open
    case Or.CompactStart{}:
      True{}
    case Or.CompactEnd{}:
      False{}
    case Or.Gone{g}:
      open
    case Or.Back{}:
      open

def oh.compact_fold(evs: List<&2, Or.Ev>, open: Bool) -> Bool:
  match evs:
    case Nil{}:
      open
    case e <> rest:
      oh.compact_fold(rest, oh.compact_ev(open, e))

# whether a compaction is open after the history evs, from `open`
def oh.compact_open(open: Bool, evs: List<&2, Or.Ev>) -> Bool:
  oh.compact_fold(evs, open)

# the queued inputs: a queue adds one, a drain takes one (none stay none),
# any other event keeps them
def oh.queued_ev(q: Nat, e: Or.Ev) -> Nat:
  match e:
    case Or.RunStart{}:
      q
    case Or.RunEnd{}:
      q
    case Or.Queue{}:
      1n+q
    case Or.Drain{}:
      Nat.sub(q, 1n)
    case Or.CompactStart{}:
      q
    case Or.CompactEnd{}:
      q
    case Or.Gone{g}:
      q
    case Or.Back{}:
      q

def oh.queued_fold(evs: List<&2, Or.Ev>, q: Nat) -> Nat:
  match evs:
    case Nil{}:
      q
    case e <> rest:
      oh.queued_fold(rest, oh.queued_ev(q, e))

# the inputs queued after the history evs, from q
def oh.queued(q: Nat, evs: List<&2, Or.Ev>) -> Nat:
  oh.queued_fold(evs, q)

# the ms absent: the supervisor's g more ms add g, its answer resets them
# to 0, any other event keeps them
def oh.absent_ev(a: Nat, e: Or.Ev) -> Nat:
  match e:
    case Or.RunStart{}:
      a
    case Or.RunEnd{}:
      a
    case Or.Queue{}:
      a
    case Or.Drain{}:
      a
    case Or.CompactStart{}:
      a
    case Or.CompactEnd{}:
      a
    case Or.Gone{g}:
      Nat.add(g, a)
    case Or.Back{}:
      0n

def oh.absent_fold(evs: List<&2, Or.Ev>, a: Nat) -> Nat:
  match evs:
    case Nil{}:
      a
    case e <> rest:
      oh.absent_fold(rest, oh.absent_ev(a, e))

# the ms absent after the history evs, from a
def oh.absent(a: Nat, evs: List<&2, Or.Ev>) -> Nat:
  oh.absent_fold(evs, a)

# whether the worker holds work after the history: a run open, a
# compaction open, or an input queued
def oh.folds_busy(+evs: List<&2, Or.Ev>) -> Bool:
  Bool.or(oh.run_open(False{}, evs), Bool.or(oh.compact_open(False{}, evs), Nat.is_lt(0n, oh.queued(0n, evs))))

# whether the exit check after the history's last event is due, by the Nat
# arithmetic above on every non-empty history (no event, no exit check yet:
# the empty history is False)
def oh.due_at(+window: Nat, evs: List<&2, Or.Ev>) -> Bool:
  match evs:
    case Nil{}:
      False{}
    case +e <> +rest:
      Orphan.orphan_due_by(window, oh.folds_busy(e <> rest), oh.absent(0n, e <> rest))

# the state the machine's per-field folds give a history, from a fresh
# worker
def oh.state(+evs: List<&2, Or.Ev>) -> Or.W:
  Or.W{oh.run_open(False{}, evs), oh.queued(0n, evs), oh.compact_open(False{}, evs), oh.absent(0n, evs)}

# due: the exit with the work held; not due: the worker lives on in w
def oh.after_by(due: Bool, +busy: Bool, w: Or.W) -> Or.St:
  match due:
    case True{}:
      Or.Exited{Or.Out{Orphan.orphan_exit_spec(Orphan.orphan_work_of(busy)), Orphan.orphan_work_of(busy), busy, False{}}}
    case False{}:
      Or.Live{w}

# the worker after the history evs, when it was live before its last event
def oh.after(+window: Nat, +evs: List<&2, Or.Ev>) -> Or.St:
  oh.after_by(oh.due_at(window, evs), oh.folds_busy(evs), oh.state(evs))

# the machine over a history and one more event: one more step
def oh.go_snoc(+window: Nat, xs: List<&2, Or.Ev>, +e: Or.Ev, s: Or.St) -> {Or.go(window, oh.snoc(xs, e), s) == Or.step(window, Or.go(window, xs, s), e) : Or.St}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      oh.go_snoc(window, t, e, Or.step(window, s, h))

# each fold over a history and one more event: its step on the fold
def oh.run_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev, o: Bool) -> {oh.run_fold(oh.snoc(xs, e), o) == oh.run_ev(oh.run_fold(xs, o), e) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      oh.run_snoc(t, e, oh.run_ev(o, h))

def oh.compact_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev, o: Bool) -> {oh.compact_fold(oh.snoc(xs, e), o) == oh.compact_ev(oh.compact_fold(xs, o), e) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      oh.compact_snoc(t, e, oh.compact_ev(o, h))

def oh.queued_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev, q: Nat) -> {oh.queued_fold(oh.snoc(xs, e), q) == oh.queued_ev(oh.queued_fold(xs, q), e) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      oh.queued_snoc(t, e, oh.queued_ev(q, h))

def oh.absent_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev, a: Nat) -> {oh.absent_fold(oh.snoc(xs, e), a) == oh.absent_ev(oh.absent_fold(xs, a), e) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      oh.absent_snoc(t, e, oh.absent_ev(a, h))

def oh.w_eq(-r1: Bool, -r2: Bool, -q1: Nat, -q2: Nat, -c1: Bool, -c2: Bool, -a1: Nat, -a2: Nat, er: {r1 == r2 : Bool}, eq: {q1 == q2 : Nat}, ec: {c1 == c2 : Bool}, ea: {a1 == a2 : Nat}) -> {Or.W{r1, q1, c1, a1} == Or.W{r2, q2, c2, a2} : Or.W}:
  %er : {Or.W{r1, q1, c1, a1} == Or.W{_, q2, c2, a2} : Or.W}
  %eq : {Or.W{r1, q1, c1, a1} == Or.W{r1, _, c2, a2} : Or.W}
  %ec : {Or.W{r1, q1, c1, a1} == Or.W{r1, q1, _, a2} : Or.W}
  %ea : {Or.W{r1, q1, c1, a1} == Or.W{r1, q1, c1, _} : Or.W}
  {==}

def oh.sub_zero(p: Nat) -> {Nat.sub(p, 0n) == p : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+pp:
      {==}

# a drain of the spec is the machine's
def oh.drain(q: Nat) -> {Nat.sub(q, 1n) == Or.dec(q) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      oh.sub_zero(p)

# the spec's steps on each field are the machine's step on the state
def oh.apply_ev(e: Or.Ev, +r: Bool, +q: Nat, +c: Bool, +a: Nat) -> {Or.W{oh.run_ev(r, e), oh.queued_ev(q, e), oh.compact_ev(c, e), oh.absent_ev(a, e)} == Or.apply(Or.W{r, q, c, a}, e) : Or.W}:
  match e:
    case Or.RunStart{}:
      {==}
    case Or.RunEnd{}:
      {==}
    case Or.Queue{}:
      {==}
    case Or.Drain{}:
      Equal.cong(Nat, Or.W, x => Or.W{r, x, c, a}, Nat.sub(q, 1n), Or.dec(q), oh.drain(q))
    case Or.CompactStart{}:
      {==}
    case Or.CompactEnd{}:
      {==}
    case Or.Gone{g}:
      {==}
    case Or.Back{}:
      {==}

# the state of a history and one more event: the machine's step on the
# history's state
def oh.state_snoc(+xs: List<&2, Or.Ev>, +e: Or.Ev) -> {oh.state(oh.snoc(xs, e)) == Or.apply(oh.state(xs), e) : Or.W}:
  Equal.trans(Or.W, oh.state(oh.snoc(xs, e)),
    Or.W{oh.run_ev(oh.run_fold(xs, False{}), e), oh.queued_ev(oh.queued_fold(xs, 0n), e), oh.compact_ev(oh.compact_fold(xs, False{}), e), oh.absent_ev(oh.absent_fold(xs, 0n), e)},
    Or.apply(oh.state(xs), e),
    oh.w_eq(oh.run_fold(oh.snoc(xs, e), False{}), oh.run_ev(oh.run_fold(xs, False{}), e),
      oh.queued_fold(oh.snoc(xs, e), 0n), oh.queued_ev(oh.queued_fold(xs, 0n), e),
      oh.compact_fold(oh.snoc(xs, e), False{}), oh.compact_ev(oh.compact_fold(xs, False{}), e),
      oh.absent_fold(oh.snoc(xs, e), 0n), oh.absent_ev(oh.absent_fold(xs, 0n), e),
      oh.run_snoc(xs, e, False{}), oh.queued_snoc(xs, e, 0n), oh.compact_snoc(xs, e, False{}), oh.absent_snoc(xs, e, 0n)),
    oh.apply_ev(e, oh.run_fold(xs, False{}), oh.queued_fold(xs, 0n), oh.compact_fold(xs, False{}), oh.absent_fold(xs, 0n)))

# the work the machine sees in a state, as the spec's busy flag
def oh.busy(r: Bool, c: Bool, q: Nat) -> Bool:
  Bool.or(r, Bool.or(c, Nat.is_lt(0n, q)))

# the machine's exit test is the spec's
def oh.due(+window: Nat, r: Bool, c: Bool, +q: Nat, +a: Nat) -> {Or.exit_due(window, a, Or.W.work(Or.W{r, q, c, a})) == Orphan.orphan_due_by(window, oh.busy(r, c, q), a) : Bool}:
  match r:
    case True{}:
      Orphan.orphan_work_exit_due(window, a)
    case False{}:
      match c:
        case True{}:
          Orphan.orphan_work_exit_due(window, a)
        case False{}:
          match q:
            case 0n:
              {==}
            case 1n+p:
              Orphan.orphan_work_exit_due(window, a)

# the machine's exit or stay is the spec's
def oh.put(d: Bool, r: Bool, c: Bool, +q: Nat, +a: Nat) -> {Or.check.put(d, Or.W{r, q, c, a}) == oh.after_by(d, oh.busy(r, c, q), Or.W{r, q, c, a}) : Or.St}:
  match d:
    case False{}:
      {==}
    case True{}:
      match r:
        case True{}:
          {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              match q:
                case 0n:
                  {==}
                case 1n+p:
                  {==}

def oh.check(+window: Nat, +r: Bool, +c: Bool, +q: Nat, +a: Nat) -> {Or.check(window, Or.W{r, q, c, a}) == oh.after_by(Orphan.orphan_due_by(window, oh.busy(r, c, q), a), oh.busy(r, c, q), Or.W{r, q, c, a}) : Or.St}:
  %Equal.sym(Bool, Or.exit_due(window, a, Or.W.work(Or.W{r, q, c, a})), Orphan.orphan_due_by(window, oh.busy(r, c, q), a), oh.due(window, r, c, q, a)) : {Or.check.put(_, Or.W{r, q, c, a}) == oh.after_by(Orphan.orphan_due_by(window, oh.busy(r, c, q), a), oh.busy(r, c, q), Or.W{r, q, c, a}) : Or.St}
  oh.put(Orphan.orphan_due_by(window, oh.busy(r, c, q), a), r, c, q, a)

# a history and one more event is never empty: its exit check is the test
def oh.due_snoc(+window: Nat, xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_due_by(window, oh.folds_busy(oh.snoc(xs, e)), oh.absent(0n, oh.snoc(xs, e))) == oh.due_at(window, oh.snoc(xs, e)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# the machine's step after a history's state is the spec's after
def oh.next(+window: Nat, +xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Or.check(window, Or.apply(oh.state(xs), e)) == oh.after(window, oh.snoc(xs, e)) : Or.St}:
  %oh.state_snoc(xs, e) : {Or.check(window, _) == oh.after(window, oh.snoc(xs, e)) : Or.St}
  %oh.due_snoc(window, xs, e) : {Or.check(window, oh.state(oh.snoc(xs, e))) == oh.after_by(_, oh.folds_busy(oh.snoc(xs, e)), oh.state(oh.snoc(xs, e))) : Or.St}
  oh.check(window, oh.run_fold(oh.snoc(xs, e), False{}), oh.compact_fold(oh.snoc(xs, e), False{}), oh.queued_fold(oh.snoc(xs, e), 0n), oh.absent_fold(oh.snoc(xs, e), 0n))

# a live state is the history's state, and its last exit check was not due
def oh.Inv(+window: Nat, +evs: List<&2, Or.Ev>, s: Or.St) -> Type:
  match s:
    case Or.Live{w}:
      {w == oh.state(evs) : Or.W} & {oh.due_at(window, evs) == False{} : Bool}
    case Or.Exited{d}:
      Unit

def oh.after_inv(d: Bool, +window: Nat, +ys: List<&2, Or.Ev>, h: {oh.due_at(window, ys) == d : Bool}) -> oh.Inv(window, ys, oh.after_by(d, oh.folds_busy(ys), oh.state(ys))):
  match d:
    case True{}:
      Unit{}
    case False{}:
      ({==}, h)

def oh.step_inv(+window: Nat, +xs: List<&2, Or.Ev>, +e: Or.Ev, s: Or.St, ok: oh.Inv(window, xs, s)) -> oh.Inv(window, oh.snoc(xs, e), Or.step(window, s, e)):
  match s:
    case Or.Live{w}:
      (ew, nd) = ok
      %Equal.sym(Or.W, w, oh.state(xs), ew) : oh.Inv(window, oh.snoc(xs, e), Or.check(window, Or.apply(_, e)))
      %Equal.sym(Or.St, Or.check(window, Or.apply(oh.state(xs), e)), oh.after(window, oh.snoc(xs, e)), oh.next(window, xs, e)) : oh.Inv(window, oh.snoc(xs, e), _)
      oh.after_inv(oh.due_at(window, oh.snoc(xs, e)), window, oh.snoc(xs, e), {==})
    case Or.Exited{d}:
      Unit{}

def oh.app_nil(xs: List<&2, Or.Ev>) -> {xs == List.append(&2, Or.Ev, xs, Nil{}) : List<&2, Or.Ev>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, Or.Ev>, List<&2, Or.Ev>, l => h <> l, t, List.append(&2, Or.Ev, t, Nil{}), oh.app_nil(t))

def oh.app_snoc(pre: List<&2, Or.Ev>, +h: Or.Ev, +t: List<&2, Or.Ev>) -> {List.append(&2, Or.Ev, oh.snoc(pre, h), t) == List.append(&2, Or.Ev, pre, h <> t) : List<&2, Or.Ev>}:
  match pre:
    case Nil{}:
      {==}
    case +p <> q:
      Equal.cong(List<&2, Or.Ev>, List<&2, Or.Ev>, l => p <> l, List.append(&2, Or.Ev, oh.snoc(q, h), t), List.append(&2, Or.Ev, q, h <> t), oh.app_snoc(q, h, t))

def oh.go_inv(+window: Nat, rest: List<&2, Or.Ev>, +pre: List<&2, Or.Ev>, +s: Or.St, ok: oh.Inv(window, pre, s)) -> oh.Inv(window, List.append(&2, Or.Ev, pre, rest), Or.go(window, rest, s)):
  match rest:
    case Nil{}:
      %oh.app_nil(pre) : oh.Inv(window, _, s)
      ok
    case +h <> +t:
      %oh.app_snoc(pre, h, t) : oh.Inv(window, _, Or.go(window, t, Or.step(window, s, h)))
      oh.go_inv(window, t, oh.snoc(pre, h), Or.step(window, s, h), oh.step_inv(window, pre, h, s, ok))

# a live run: its state is its history's, its last exit check not due
def oh.live(+window: Nat, +evs: List<&2, Or.Ev>, -w: Or.W, h: {Or.run(window, evs) == Or.Live{w} : Or.St}) -> oh.Inv(window, evs, Or.Live{w}):
  %h : oh.Inv(window, evs, _)
  oh.go_inv(window, evs, Nil{}, Or.Live{Or.W.empty()}, ({==}, {==}))

def oh.inv_state(+window: Nat, +evs: List<&2, Or.Ev>, -w: Or.W, p: oh.Inv(window, evs, Or.Live{w})) -> {w == oh.state(evs) : Or.W}:
  (ew, nd) = p
  ew

def oh.inv_due(+window: Nat, +evs: List<&2, Or.Ev>, -w: Or.W, p: oh.Inv(window, evs, Or.Live{w})) -> {oh.due_at(window, evs) == False{} : Bool}:
  (ew, nd) = p
  nd

# The event machine, whole
# ------------------------

def ps.ow_work(w: Or.W) -> {Or.W.work(w) == Orphan.ow_work(w) : Or.Work}:
  match w:
    case Or.W{r, q, c, a}:
      match r:
        case True{}:
          {==}
        case False{}:
          match q:
            case 0n:
              match c:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case 1n+p:
              match c:
                case True{}:
                  {==}
                case False{}:
                  {==}

def ps.ow_out(k: Or.Work) -> {Or.Exited{Or.exit.done(Or.orphan_exit(k), k)} == Or.Exited{Orphan.ow_out(k)} : Or.St}:
  match k:
    case Or.Idle{}:
      {==}
    case Or.Ongoing{}:
      {==}

def ps.ow_put(due: Bool, +w: Or.W) -> {Or.check.put(due, w) == Orphan.ow_check.put(due, w) : Or.St}:
  match due:
    case True{}:
      %Equal.sym(Or.Work, Or.W.work(w), Orphan.ow_work(w), ps.ow_work(w)) : {Or.Exited{Or.exit.done(Or.orphan_exit(_), _)} == Or.Exited{Orphan.ow_out(Orphan.ow_work(w))} : Or.St}
      ps.ow_out(Orphan.ow_work(w))
    case False{}:
      {==}

# the spec's decision is the model's: with work, the window passed twice
# (orphan_work_exit_due)
def ps.ow_due(+window: Nat, +a: Nat, k: Or.Work) -> {Orphan.or_due(Some{window}, a, k) == Or.exit_due(window, a, k) : Bool}:
  match k:
    case Or.Idle{}:
      {==}
    case Or.Ongoing{}:
      Equal.sym(Bool, Or.exit_due(window, a, Or.Ongoing{}), Nat.is_le(Nat.add(window, window), a), Orphan.orphan_work_exit_due(window, a))

def ps.ow_check(+window: Nat, +w: Or.W) -> {Or.check(window, w) == Orphan.ow_check(window, w) : Or.St}:
  match w:
    case Or.W{+r, +q, +c, +a}:
      +x = {Or.W{r, q, c, a} : Or.W}
      %Equal.sym(Or.Work, Or.W.work(x), Orphan.ow_work(x), ps.ow_work(x)) : {Or.check.put(Or.exit_due(window, a, _), x) == Orphan.ow_check.put(Orphan.or_due(Some{window}, a, Orphan.ow_work(x)), x) : Or.St}
      %ps.ow_due(window, a, Orphan.ow_work(x)) : {Or.check.put(_, x) == Orphan.ow_check.put(Orphan.or_due(Some{window}, a, Orphan.ow_work(x)), x) : Or.St}
      ps.ow_put(Orphan.or_due(Some{window}, a, Orphan.ow_work(x)), x)

def ps.ow_drain(q: Nat) -> {Orphan.ow_drain(q) == Or.dec(q) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ps.ow_apply(w: Or.W, e: Or.Ev) -> {Orphan.ow_apply(w, e) == Or.apply(w, e) : Or.W}:
  match w:
    case Or.W{+r, +q, +c, +a}:
      match e:
        case Or.RunStart{}:
          {==}
        case Or.RunEnd{}:
          {==}
        case Or.Queue{}:
          {==}
        case Or.Drain{}:
          %ps.ow_drain(q) : {Or.W{r, Orphan.ow_drain(q), c, a} == Or.W{r, _, c, a} : Or.W}
          {==}
        case Or.CompactStart{}:
          {==}
        case Or.CompactEnd{}:
          {==}
        case Or.Gone{g}:
          {==}
        case Or.Back{}:
          {==}

def ps.ow_step(+window: Nat, s: Or.St, +e: Or.Ev) -> {Or.step(window, s, e) == Orphan.ow_step(window, s, e) : Or.St}:
  match s:
    case Or.Live{+w}:
      %ps.ow_apply(w, e) : {Or.check(window, _) == Orphan.ow_check(window, Orphan.ow_apply(w, e)) : Or.St}
      ps.ow_check(window, Orphan.ow_apply(w, e))
    case Or.Exited{d}:
      {==}

def ps.ow_go(+window: Nat, evs: List<&2, Or.Ev>, +s: Or.St) -> {Or.go(window, evs, s) == Orphan.ow_go(window, evs, s) : Or.St}:
  match evs:
    case Nil{}:
      {==}
    case +e <> rest:
      %Equal.sym(Or.St, Or.step(window, s, e), Orphan.ow_step(window, s, e), ps.ow_step(window, s, e)) : {Or.go(window, rest, _) == Orphan.ow_go(window, rest, Orphan.ow_step(window, s, e)) : Or.St}
      ps.ow_go(window, rest, Orphan.ow_step(window, s, e))

# one more event after a live history: the machine's step on the
# history's state
def oh.next_live(+window: Nat, +evs: List<&2, Or.Ev>, +e: Or.Ev, -w: Or.W, +live: {Or.run(window, evs) == Or.Live{w} : Or.St}) -> {Or.run(window, oh.snoc(evs, e)) == oh.after(window, oh.snoc(evs, e)) : Or.St}:
  %Equal.sym(Or.St, Or.go(window, oh.snoc(evs, e), Or.Live{Or.W.empty()}), Or.step(window, Or.run(window, evs), e), oh.go_snoc(window, evs, e, Or.Live{Or.W.empty()})) : {_ == oh.after(window, oh.snoc(evs, e)) : Or.St}
  %Equal.sym(Or.St, Or.run(window, evs), Or.Live{w}, live) : {Or.step(window, _, e) == oh.after(window, oh.snoc(evs, e)) : Or.St}
  %Equal.sym(Or.W, w, oh.state(evs), oh.inv_state(window, evs, w, oh.live(window, evs, w, live))) : {Or.check(window, Or.apply(_, e)) == oh.after(window, oh.snoc(evs, e)) : Or.St}
  oh.next(window, evs, e)

# The history's declared state is the machine's
# ---------------------------------------------

def oh.and_true_r(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def oh.and_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def oh.or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# an end after every start: nothing stays open
def oh.b_closed(a: Bool, n: Bool) -> {Bool.or(Bool.and(a, Bool.and(n, False{})), False{}) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      match n:
        case False{}:
          {==}
        case True{}:
          {==}

# an event that neither starts nor ends keeps what is open
def oh.b_kept(a: Bool, n: Bool, u: Bool) -> {Bool.or(Bool.and(a, Bool.and(n, True{})), u) == Bool.or(Bool.and(a, n), u) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      match n:
        case False{}:
          {==}
        case True{}:
          {==}

# a run end after a history and one more event
def oh.no_run_end_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_no_run_end(oh.snoc(xs, e)) == Bool.and(Orphan.orphan_no_run_end(xs), Bool.not(Orphan.orphan_ends_run(e))) : Bool}:
  match xs:
    case Nil{}:
      oh.and_true_r(Bool.not(Orphan.orphan_ends_run(e)))
    case +h <> +t:
      %Equal.sym(Bool, Orphan.orphan_no_run_end(oh.snoc(t, e)), Bool.and(Orphan.orphan_no_run_end(t), Bool.not(Orphan.orphan_ends_run(e))), oh.no_run_end_snoc(t, e)) : {Bool.and(Bool.not(Orphan.orphan_ends_run(h)), _) == Bool.and(Orphan.orphan_no_run_end(h <> t), Bool.not(Orphan.orphan_ends_run(e))) : Bool}
      oh.and_assoc(Bool.not(Orphan.orphan_ends_run(h)), Orphan.orphan_no_run_end(t), Bool.not(Orphan.orphan_ends_run(e)))

def oh.no_compaction_end_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_no_compaction_end(oh.snoc(xs, e)) == Bool.and(Orphan.orphan_no_compaction_end(xs), Bool.not(Orphan.orphan_ends_compaction(e))) : Bool}:
  match xs:
    case Nil{}:
      oh.and_true_r(Bool.not(Orphan.orphan_ends_compaction(e)))
    case +h <> +t:
      %Equal.sym(Bool, Orphan.orphan_no_compaction_end(oh.snoc(t, e)), Bool.and(Orphan.orphan_no_compaction_end(t), Bool.not(Orphan.orphan_ends_compaction(e))), oh.no_compaction_end_snoc(t, e)) : {Bool.and(Bool.not(Orphan.orphan_ends_compaction(h)), _) == Bool.and(Orphan.orphan_no_compaction_end(h <> t), Bool.not(Orphan.orphan_ends_compaction(e))) : Bool}
      oh.and_assoc(Bool.not(Orphan.orphan_ends_compaction(h)), Orphan.orphan_no_compaction_end(t), Bool.not(Orphan.orphan_ends_compaction(e)))

def oh.no_answer_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_no_answer(oh.snoc(xs, e)) == Bool.and(Orphan.orphan_no_answer(xs), Bool.not(Orphan.orphan_answers(e))) : Bool}:
  match xs:
    case Nil{}:
      oh.and_true_r(Bool.not(Orphan.orphan_answers(e)))
    case +h <> +t:
      %Equal.sym(Bool, Orphan.orphan_no_answer(oh.snoc(t, e)), Bool.and(Orphan.orphan_no_answer(t), Bool.not(Orphan.orphan_answers(e))), oh.no_answer_snoc(t, e)) : {Bool.and(Bool.not(Orphan.orphan_answers(h)), _) == Bool.and(Orphan.orphan_no_answer(h <> t), Bool.not(Orphan.orphan_answers(e))) : Bool}
      oh.and_assoc(Bool.not(Orphan.orphan_answers(h)), Orphan.orphan_no_answer(t), Bool.not(Orphan.orphan_answers(e)))

# a run open after one event from a fresh worker
def oh.run_unended_one(e: Or.Ev) -> {Orphan.orphan_run_unended([e]) == oh.run_ev(False{}, e) : Bool}:
  match e:
    case Or.RunStart{}:
      {==}
    case Or.RunEnd{}:
      {==}
    case Or.Queue{}:
      {==}
    case Or.Drain{}:
      {==}
    case Or.CompactStart{}:
      {==}
    case Or.CompactEnd{}:
      {==}
    case Or.Gone{g}:
      {==}
    case Or.Back{}:
      {==}

def oh.run_unended_step(e: Or.Ev, a: Bool, n: Bool, u: Bool) -> {Bool.or(Bool.and(a, Bool.and(n, Bool.not(Orphan.orphan_ends_run(e)))), oh.run_ev(u, e)) == oh.run_ev(Bool.or(Bool.and(a, n), u), e) : Bool}:
  match e:
    case Or.RunStart{}:
      oh.or_true_r(Bool.and(a, Bool.and(n, True{})))
    case Or.RunEnd{}:
      oh.b_closed(a, n)
    case Or.Queue{}:
      oh.b_kept(a, n, u)
    case Or.Drain{}:
      oh.b_kept(a, n, u)
    case Or.CompactStart{}:
      oh.b_kept(a, n, u)
    case Or.CompactEnd{}:
      oh.b_kept(a, n, u)
    case Or.Gone{g}:
      oh.b_kept(a, n, u)
    case Or.Back{}:
      oh.b_kept(a, n, u)

# a run open after a history and one more event: the machine's run step
def oh.run_unended_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_run_unended(oh.snoc(xs, e)) == oh.run_ev(Orphan.orphan_run_unended(xs), e) : Bool}:
  match xs:
    case Nil{}:
      oh.run_unended_one(e)
    case +h <> +t:
      %Equal.sym(Bool, Orphan.orphan_no_run_end(oh.snoc(t, e)), Bool.and(Orphan.orphan_no_run_end(t), Bool.not(Orphan.orphan_ends_run(e))), oh.no_run_end_snoc(t, e)) : {Bool.or(Bool.and(Orphan.orphan_starts_run(h), _), Orphan.orphan_run_unended(oh.snoc(t, e))) == oh.run_ev(Orphan.orphan_run_unended(h <> t), e) : Bool}
      %Equal.sym(Bool, Orphan.orphan_run_unended(oh.snoc(t, e)), oh.run_ev(Orphan.orphan_run_unended(t), e), oh.run_unended_snoc(t, e)) : {Bool.or(Bool.and(Orphan.orphan_starts_run(h), Bool.and(Orphan.orphan_no_run_end(t), Bool.not(Orphan.orphan_ends_run(e)))), _) == oh.run_ev(Orphan.orphan_run_unended(h <> t), e) : Bool}
      oh.run_unended_step(e, Orphan.orphan_starts_run(h), Orphan.orphan_no_run_end(t), Orphan.orphan_run_unended(t))

def oh.compaction_unended_one(e: Or.Ev) -> {Orphan.orphan_compaction_unended([e]) == oh.compact_ev(False{}, e) : Bool}:
  match e:
    case Or.RunStart{}:
      {==}
    case Or.RunEnd{}:
      {==}
    case Or.Queue{}:
      {==}
    case Or.Drain{}:
      {==}
    case Or.CompactStart{}:
      {==}
    case Or.CompactEnd{}:
      {==}
    case Or.Gone{g}:
      {==}
    case Or.Back{}:
      {==}

def oh.compaction_unended_step(e: Or.Ev, a: Bool, n: Bool, u: Bool) -> {Bool.or(Bool.and(a, Bool.and(n, Bool.not(Orphan.orphan_ends_compaction(e)))), oh.compact_ev(u, e)) == oh.compact_ev(Bool.or(Bool.and(a, n), u), e) : Bool}:
  match e:
    case Or.RunStart{}:
      oh.b_kept(a, n, u)
    case Or.RunEnd{}:
      oh.b_kept(a, n, u)
    case Or.Queue{}:
      oh.b_kept(a, n, u)
    case Or.Drain{}:
      oh.b_kept(a, n, u)
    case Or.CompactStart{}:
      oh.or_true_r(Bool.and(a, Bool.and(n, True{})))
    case Or.CompactEnd{}:
      oh.b_closed(a, n)
    case Or.Gone{g}:
      oh.b_kept(a, n, u)
    case Or.Back{}:
      oh.b_kept(a, n, u)

# a compaction open after a history and one more event: the machine's
# compaction step
def oh.compaction_unended_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_compaction_unended(oh.snoc(xs, e)) == oh.compact_ev(Orphan.orphan_compaction_unended(xs), e) : Bool}:
  match xs:
    case Nil{}:
      oh.compaction_unended_one(e)
    case +h <> +t:
      %Equal.sym(Bool, Orphan.orphan_no_compaction_end(oh.snoc(t, e)), Bool.and(Orphan.orphan_no_compaction_end(t), Bool.not(Orphan.orphan_ends_compaction(e))), oh.no_compaction_end_snoc(t, e)) : {Bool.or(Bool.and(Orphan.orphan_starts_compaction(h), _), Orphan.orphan_compaction_unended(oh.snoc(t, e))) == oh.compact_ev(Orphan.orphan_compaction_unended(h <> t), e) : Bool}
      %Equal.sym(Bool, Orphan.orphan_compaction_unended(oh.snoc(t, e)), oh.compact_ev(Orphan.orphan_compaction_unended(t), e), oh.compaction_unended_snoc(t, e)) : {Bool.or(Bool.and(Orphan.orphan_starts_compaction(h), Bool.and(Orphan.orphan_no_compaction_end(t), Bool.not(Orphan.orphan_ends_compaction(e)))), _) == oh.compact_ev(Orphan.orphan_compaction_unended(h <> t), e) : Bool}
      oh.compaction_unended_step(e, Orphan.orphan_starts_compaction(h), Orphan.orphan_no_compaction_end(t), Orphan.orphan_compaction_unended(t))

# the queues and drains of a history and one more event
def oh.queues_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_queues(oh.snoc(xs, e)) == Nat.add(Orphan.orphan_one_queue(e), Orphan.orphan_queues(xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Nat, Orphan.orphan_queues(oh.snoc(t, e)), Nat.add(Orphan.orphan_one_queue(e), Orphan.orphan_queues(t)), oh.queues_snoc(t, e)) : {Nat.add(Orphan.orphan_one_queue(h), _) == Nat.add(Orphan.orphan_one_queue(e), Orphan.orphan_queues(h <> t)) : Nat}
      LNat.wn_add_swap(Orphan.orphan_one_queue(h), Orphan.orphan_one_queue(e), Orphan.orphan_queues(t))

def oh.drains_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_drains(oh.snoc(xs, e)) == Nat.add(Orphan.orphan_one_drain(e), Orphan.orphan_drains(xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Nat, Orphan.orphan_drains(oh.snoc(t, e)), Nat.add(Orphan.orphan_one_drain(e), Orphan.orphan_drains(t)), oh.drains_snoc(t, e)) : {Nat.add(Orphan.orphan_one_drain(h), _) == Nat.add(Orphan.orphan_one_drain(e), Orphan.orphan_drains(h <> t)) : Nat}
      LNat.wn_add_swap(Orphan.orphan_one_drain(h), Orphan.orphan_one_drain(e), Orphan.orphan_drains(t))

# one more queue: every stretch's excess rises by one, and the empty
# stretch's 0 stays below the rest
def oh.most_queue(d: Nat, q: Nat, +p: Nat) -> {Nat.max(Nat.sub(1n+q, d), 1n+p) == 1n+Nat.max(Nat.sub(q, d), p) : Nat}:
  match d:
    case 0n:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, oh.sub_zero(q)) : {Nat.max(1n+q, 1n+p) == 1n+Nat.max(_, p) : Nat}
      {==}
    case 1n+dp:
      match q:
        case 0n:
          {==}
        case 1n+qp:
          oh.most_queue(dp, qp, p)

def oh.sub_succ(q: Nat, d: Nat) -> {Nat.sub(q, 1n+d) == Nat.sub(Nat.sub(q, d), 1n) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+qp:
      match d:
        case 0n:
          {==}
        case 1n+dp:
          oh.sub_succ(qp, dp)

def oh.max_zero_r(y: Nat) -> {Nat.max(y, 0n) == y : Nat}:
  match y:
    case 0n:
      {==}
    case 1n+yp:
      {==}

def oh.max_pred(x: Nat, +p: Nat) -> {Nat.max(Nat.sub(x, 1n), Nat.sub(p, 1n)) == Nat.sub(Nat.max(x, p), 1n) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++xp:
      match p:
        case 0n:
          oh.max_zero_r(Nat.sub(xp, 0n))
        case 1n++pp:
          %Equal.sym(Nat, Nat.sub(xp, 0n), xp, oh.sub_zero(xp)) : {Nat.max(_, Nat.sub(pp, 0n)) == Nat.sub(Nat.max(xp, pp), 0n) : Nat}
          %Equal.sym(Nat, Nat.sub(pp, 0n), pp, oh.sub_zero(pp)) : {Nat.max(xp, _) == Nat.sub(Nat.max(xp, pp), 0n) : Nat}
          Equal.sym(Nat, Nat.sub(Nat.max(xp, pp), 0n), Nat.max(xp, pp), oh.sub_zero(Nat.max(xp, pp)))

# one more drain: every stretch's excess falls by one (none stays none)
def oh.most_drain(+q: Nat, +d: Nat, +p: Nat) -> {Nat.max(Nat.sub(q, 1n+d), Nat.sub(p, 1n)) == Nat.sub(Nat.max(Nat.sub(q, d), p), 1n) : Nat}:
  %Equal.sym(Nat, Nat.sub(q, 1n+d), Nat.sub(Nat.sub(q, d), 1n), oh.sub_succ(q, d)) : {Nat.max(_, Nat.sub(p, 1n)) == Nat.sub(Nat.max(Nat.sub(q, d), p), 1n) : Nat}
  oh.max_pred(Nat.sub(q, d), p)

def oh.most_one(e: Or.Ev) -> {Orphan.orphan_queued_most([e]) == oh.queued_ev(0n, e) : Nat}:
  match e:
    case Or.RunStart{}:
      {==}
    case Or.RunEnd{}:
      {==}
    case Or.Queue{}:
      {==}
    case Or.Drain{}:
      {==}
    case Or.CompactStart{}:
      {==}
    case Or.CompactEnd{}:
      {==}
    case Or.Gone{g}:
      {==}
    case Or.Back{}:
      {==}

def oh.most_step(e: Or.Ev, +q: Nat, +d: Nat, +p: Nat) -> {Nat.max(Nat.sub(Nat.add(Orphan.orphan_one_queue(e), q), Nat.add(Orphan.orphan_one_drain(e), d)), oh.queued_ev(p, e)) == oh.queued_ev(Nat.max(Nat.sub(q, d), p), e) : Nat}:
  match e:
    case Or.RunStart{}:
      {==}
    case Or.RunEnd{}:
      {==}
    case Or.Queue{}:
      oh.most_queue(d, q, p)
    case Or.Drain{}:
      oh.most_drain(q, d, p)
    case Or.CompactStart{}:
      {==}
    case Or.CompactEnd{}:
      {==}
    case Or.Gone{g}:
      {==}
    case Or.Back{}:
      {==}

# the inputs queued after a history and one more event: the machine's
# queue step
def oh.most_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_queued_most(oh.snoc(xs, e)) == oh.queued_ev(Orphan.orphan_queued_most(xs), e) : Nat}:
  match xs:
    case Nil{}:
      oh.most_one(e)
    case +h <> +t:
      %Equal.sym(Nat, Orphan.orphan_queues(oh.snoc(h <> t, e)), Nat.add(Orphan.orphan_one_queue(e), Orphan.orphan_queues(h <> t)), oh.queues_snoc(h <> t, e)) : {Nat.max(Nat.sub(_, Orphan.orphan_drains(oh.snoc(h <> t, e))), Orphan.orphan_queued_most(oh.snoc(t, e))) == oh.queued_ev(Orphan.orphan_queued_most(h <> t), e) : Nat}
      %Equal.sym(Nat, Orphan.orphan_drains(oh.snoc(h <> t, e)), Nat.add(Orphan.orphan_one_drain(e), Orphan.orphan_drains(h <> t)), oh.drains_snoc(h <> t, e)) : {Nat.max(Nat.sub(Nat.add(Orphan.orphan_one_queue(e), Orphan.orphan_queues(h <> t)), _), Orphan.orphan_queued_most(oh.snoc(t, e))) == oh.queued_ev(Orphan.orphan_queued_most(h <> t), e) : Nat}
      %Equal.sym(Nat, Orphan.orphan_queued_most(oh.snoc(t, e)), oh.queued_ev(Orphan.orphan_queued_most(t), e), oh.most_snoc(t, e)) : {Nat.max(Nat.sub(Nat.add(Orphan.orphan_one_queue(e), Orphan.orphan_queues(h <> t)), Nat.add(Orphan.orphan_one_drain(e), Orphan.orphan_drains(h <> t))), _) == oh.queued_ev(Orphan.orphan_queued_most(h <> t), e) : Nat}
      oh.most_step(e, Orphan.orphan_queues(h <> t), Orphan.orphan_drains(h <> t), Orphan.orphan_queued_most(t))

def oh.unanswered_one(e: Or.Ev) -> {Orphan.orphan_unanswered_ms([e]) == oh.absent_ev(0n, e) : Nat}:
  match e:
    case Or.RunStart{}:
      {==}
    case Or.RunEnd{}:
      {==}
    case Or.Queue{}:
      {==}
    case Or.Drain{}:
      {==}
    case Or.CompactStart{}:
      {==}
    case Or.CompactEnd{}:
      {==}
    case Or.Gone{g}:
      {==}
    case Or.Back{}:
      {==}

# an answer after every absence: none counts
def oh.ms_answered(nb: Bool, m: Nat) -> {Nat.add(Bool.pick(Nat, Bool.and(nb, False{}), m, 0n), 0n) == 0n : Nat}:
  match nb:
    case False{}:
      {==}
    case True{}:
      {==}

# one more absence of g ms adds g
def oh.ms_gone(nb: Bool, +m: Nat, +g: Nat, +a: Nat) -> {Nat.add(Bool.pick(Nat, Bool.and(nb, True{}), m, 0n), Nat.add(g, a)) == Nat.add(g, Nat.add(Bool.pick(Nat, nb, m, 0n), a)) : Nat}:
  match nb:
    case False{}:
      {==}
    case True{}:
      LNat.wn_add_swap(m, g, a)

# any other event keeps the absences counted
def oh.ms_kept(nb: Bool, m: Nat, a: Nat) -> {Nat.add(Bool.pick(Nat, Bool.and(nb, True{}), m, 0n), a) == Nat.add(Bool.pick(Nat, nb, m, 0n), a) : Nat}:
  match nb:
    case False{}:
      {==}
    case True{}:
      {==}

def oh.unanswered_step(e: Or.Ev, nb: Bool, +m: Nat, +a: Nat) -> {Nat.add(Bool.pick(Nat, Bool.and(nb, Bool.not(Orphan.orphan_answers(e))), m, 0n), oh.absent_ev(a, e)) == oh.absent_ev(Nat.add(Bool.pick(Nat, nb, m, 0n), a), e) : Nat}:
  match e:
    case Or.RunStart{}:
      oh.ms_kept(nb, m, a)
    case Or.RunEnd{}:
      oh.ms_kept(nb, m, a)
    case Or.Queue{}:
      oh.ms_kept(nb, m, a)
    case Or.Drain{}:
      oh.ms_kept(nb, m, a)
    case Or.CompactStart{}:
      oh.ms_kept(nb, m, a)
    case Or.CompactEnd{}:
      oh.ms_kept(nb, m, a)
    case Or.Gone{g}:
      oh.ms_gone(nb, m, g, a)
    case Or.Back{}:
      oh.ms_answered(nb, m)

# the ms absent after a history and one more event: the machine's absence
# step
def oh.unanswered_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_unanswered_ms(oh.snoc(xs, e)) == oh.absent_ev(Orphan.orphan_unanswered_ms(xs), e) : Nat}:
  match xs:
    case Nil{}:
      oh.unanswered_one(e)
    case +h <> +t:
      %Equal.sym(Bool, Orphan.orphan_no_answer(oh.snoc(t, e)), Bool.and(Orphan.orphan_no_answer(t), Bool.not(Orphan.orphan_answers(e))), oh.no_answer_snoc(t, e)) : {Nat.add(Bool.pick(Nat, _, Orphan.orphan_gone_ms(h), 0n), Orphan.orphan_unanswered_ms(oh.snoc(t, e))) == oh.absent_ev(Orphan.orphan_unanswered_ms(h <> t), e) : Nat}
      %Equal.sym(Nat, Orphan.orphan_unanswered_ms(oh.snoc(t, e)), oh.absent_ev(Orphan.orphan_unanswered_ms(t), e), oh.unanswered_snoc(t, e)) : {Nat.add(Bool.pick(Nat, Bool.and(Orphan.orphan_no_answer(t), Bool.not(Orphan.orphan_answers(e))), Orphan.orphan_gone_ms(h), 0n), _) == oh.absent_ev(Orphan.orphan_unanswered_ms(h <> t), e) : Nat}
      oh.unanswered_step(e, Orphan.orphan_no_answer(t), Orphan.orphan_gone_ms(h), Orphan.orphan_unanswered_ms(t))

# the declared state of a history and one more event: the machine's step
# on the history's declared state
def oh.declared_snoc(+xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_declared(oh.snoc(xs, e)) == Or.apply(Orphan.orphan_declared(xs), e) : Or.W}:
  Equal.trans(Or.W, Orphan.orphan_declared(oh.snoc(xs, e)),
    Or.W{oh.run_ev(Orphan.orphan_run_unended(xs), e), oh.queued_ev(Orphan.orphan_queued_most(xs), e), oh.compact_ev(Orphan.orphan_compaction_unended(xs), e), oh.absent_ev(Orphan.orphan_unanswered_ms(xs), e)},
    Or.apply(Orphan.orphan_declared(xs), e),
    oh.w_eq(Orphan.orphan_run_unended(oh.snoc(xs, e)), oh.run_ev(Orphan.orphan_run_unended(xs), e),
      Orphan.orphan_queued_most(oh.snoc(xs, e)), oh.queued_ev(Orphan.orphan_queued_most(xs), e),
      Orphan.orphan_compaction_unended(oh.snoc(xs, e)), oh.compact_ev(Orphan.orphan_compaction_unended(xs), e),
      Orphan.orphan_unanswered_ms(oh.snoc(xs, e)), oh.absent_ev(Orphan.orphan_unanswered_ms(xs), e),
      oh.run_unended_snoc(xs, e), oh.most_snoc(xs, e), oh.compaction_unended_snoc(xs, e), oh.unanswered_snoc(xs, e)),
    oh.apply_ev(e, Orphan.orphan_run_unended(xs), Orphan.orphan_queued_most(xs), Orphan.orphan_compaction_unended(xs), Orphan.orphan_unanswered_ms(xs)))

# the machine's per-field folds agree with the declared state
def oh.Agree(+xs: List<&2, Or.Ev>) -> Type:
  {oh.state(xs) == Orphan.orphan_declared(xs) : Or.W}

def oh.agree_step(+xs: List<&2, Or.Ev>, +e: Or.Ev, ok: oh.Agree(xs)) -> oh.Agree(oh.snoc(xs, e)):
  %Equal.sym(Or.W, oh.state(oh.snoc(xs, e)), Or.apply(oh.state(xs), e), oh.state_snoc(xs, e)) : {_ == Orphan.orphan_declared(oh.snoc(xs, e)) : Or.W}
  %Equal.sym(Or.W, oh.state(xs), Orphan.orphan_declared(xs), ok) : {Or.apply(_, e) == Orphan.orphan_declared(oh.snoc(xs, e)) : Or.W}
  Equal.sym(Or.W, Orphan.orphan_declared(oh.snoc(xs, e)), Or.apply(Orphan.orphan_declared(xs), e), oh.declared_snoc(xs, e))

def oh.agree_go(rest: List<&2, Or.Ev>, +pre: List<&2, Or.Ev>, ok: oh.Agree(pre)) -> oh.Agree(List.append(&2, Or.Ev, pre, rest)):
  match rest:
    case Nil{}:
      %oh.app_nil(pre) : oh.Agree(_)
      ok
    case +h <> +t:
      %oh.app_snoc(pre, h, t) : oh.Agree(_)
      oh.agree_go(t, oh.snoc(pre, h), oh.agree_step(pre, h, ok))

# every history: its folds' state is its declared state
def oh.agree(+xs: List<&2, Or.Ev>) -> {oh.state(xs) == Orphan.orphan_declared(xs) : Or.W}:
  oh.agree_go(xs, Nil{}, {==})

def oh.w_busy(w: Or.W) -> Bool:
  match w:
    case Or.W{r, q, c, a}:
      Bool.or(r, Bool.or(c, Nat.is_lt(0n, q)))

def oh.w_absent(w: Or.W) -> Nat:
  match w:
    case Or.W{r, q, c, a}:
      a

# the folds' work is the declared work
def oh.busy_eq(+ys: List<&2, Or.Ev>) -> {oh.folds_busy(ys) == Orphan.orphan_declared_busy(ys) : Bool}:
  Equal.cong(Or.W, Bool, w => oh.w_busy(w), oh.state(ys), Orphan.orphan_declared(ys), oh.agree(ys))

# the folds' absence is the declared absence
def oh.absent_eq(+ys: List<&2, Or.Ev>) -> {oh.absent(0n, ys) == Orphan.orphan_unanswered_ms(ys) : Nat}:
  Equal.cong(Or.W, Nat, w => oh.w_absent(w), oh.state(ys), Orphan.orphan_declared(ys), oh.agree(ys))

# The exit after one more event
# -----------------------------

def oh.exited_after(d: Bool, +b: Bool, s: Or.W) -> {Orphan.orphan_exited(oh.after_by(d, b, s)) == d : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

# the exit with the work held b
def oh.held(+b: Bool) -> Or.Out:
  Or.Out{Orphan.orphan_exit_spec(Orphan.orphan_work_of(b)), Orphan.orphan_work_of(b), b, False{}}

def oh.out_of(s: Or.St) -> Or.Out:
  match s:
    case Or.Live{w}:
      oh.held(False{})
    case Or.Exited{d}:
      d

def oh.ExitedIs(s: Or.St, G: Type) -> Type:
  match s:
    case Or.Live{w}:
      Unit
    case Or.Exited{d}:
      G

def oh.live_exited(-G: Type, -s: Or.W, -d: Or.Out, h: {Or.Live{s} == Or.Exited{d} : Or.St}) -> G:
  %h : oh.ExitedIs(_, G)
  Unit{}

def oh.after_exited(dd: Bool, +b: Bool, -s: Or.W, -d: Or.Out, h: {oh.after_by(dd, b, s) == Or.Exited{d} : Or.St}) -> {d == oh.held(b) : Or.Out}:
  match dd:
    case True{}:
      Equal.sym(Or.Out, oh.held(b), d, Equal.cong(Or.St, Or.Out, x => oh.out_of(x), Or.Exited{oh.held(b)}, Or.Exited{d}, h))
    case False{}:
      oh.live_exited({d == oh.held(b) : Or.Out}, s, d, h)
