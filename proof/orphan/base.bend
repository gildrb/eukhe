# eukhe: lemmas the proofs of area orphan share

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ../../bend/wire.bend as Wr
import ./orphan_work_exit_due.bend as POrphanWorkExitDue

def ps.ffi_work(k: Or.Work, +r: String) -> {Wr.Got{k, r} == FO.get_work(FO.put_work(k, r)) : Wr.Dec<Or.Work>}:
  match k:
    case Or.Idle{}:
      {==}
    case Or.Ongoing{}:
      {==}

# The event machine by its history
# --------------------------------

# a history and one more event
def oh.snoc(xs: List<&2, Or.Ev>, e: Or.Ev) -> List<&2, Or.Ev>:
  List.append(&2, Or.Ev, xs, [e])

# the machine over a history and one more event: one more step
def oh.go_snoc(+window: Nat, xs: List<&2, Or.Ev>, +e: Or.Ev, s: Or.St) -> {Or.go(window, oh.snoc(xs, e), s) == Or.step(window, Or.go(window, xs, s), e) : Or.St}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      oh.go_snoc(window, t, e, Or.step(window, s, h))

# each fold over a history and one more event: its step on the fold
def oh.run_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev, o: Bool) -> {Orphan.orphan_run_fold(oh.snoc(xs, e), o) == Orphan.orphan_run_ev(Orphan.orphan_run_fold(xs, o), e) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      oh.run_snoc(t, e, Orphan.orphan_run_ev(o, h))

def oh.compact_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev, o: Bool) -> {Orphan.orphan_compact_fold(oh.snoc(xs, e), o) == Orphan.orphan_compact_ev(Orphan.orphan_compact_fold(xs, o), e) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      oh.compact_snoc(t, e, Orphan.orphan_compact_ev(o, h))

def oh.queued_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev, q: Nat) -> {Orphan.orphan_queued_fold(oh.snoc(xs, e), q) == Orphan.orphan_queued_ev(Orphan.orphan_queued_fold(xs, q), e) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      oh.queued_snoc(t, e, Orphan.orphan_queued_ev(q, h))

def oh.absent_snoc(xs: List<&2, Or.Ev>, +e: Or.Ev, a: Nat) -> {Orphan.orphan_absent_fold(oh.snoc(xs, e), a) == Orphan.orphan_absent_ev(Orphan.orphan_absent_fold(xs, a), e) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      oh.absent_snoc(t, e, Orphan.orphan_absent_ev(a, h))

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
def oh.apply_ev(e: Or.Ev, +r: Bool, +q: Nat, +c: Bool, +a: Nat) -> {Or.W{Orphan.orphan_run_ev(r, e), Orphan.orphan_queued_ev(q, e), Orphan.orphan_compact_ev(c, e), Orphan.orphan_absent_ev(a, e)} == Or.apply(Or.W{r, q, c, a}, e) : Or.W}:
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
def oh.state_snoc(+xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_state(oh.snoc(xs, e)) == Or.apply(Orphan.orphan_state(xs), e) : Or.W}:
  Equal.trans(Or.W, Orphan.orphan_state(oh.snoc(xs, e)),
    Or.W{Orphan.orphan_run_ev(Orphan.orphan_run_fold(xs, False{}), e), Orphan.orphan_queued_ev(Orphan.orphan_queued_fold(xs, 0n), e), Orphan.orphan_compact_ev(Orphan.orphan_compact_fold(xs, False{}), e), Orphan.orphan_absent_ev(Orphan.orphan_absent_fold(xs, 0n), e)},
    Or.apply(Orphan.orphan_state(xs), e),
    oh.w_eq(Orphan.orphan_run_fold(oh.snoc(xs, e), False{}), Orphan.orphan_run_ev(Orphan.orphan_run_fold(xs, False{}), e),
      Orphan.orphan_queued_fold(oh.snoc(xs, e), 0n), Orphan.orphan_queued_ev(Orphan.orphan_queued_fold(xs, 0n), e),
      Orphan.orphan_compact_fold(oh.snoc(xs, e), False{}), Orphan.orphan_compact_ev(Orphan.orphan_compact_fold(xs, False{}), e),
      Orphan.orphan_absent_fold(oh.snoc(xs, e), 0n), Orphan.orphan_absent_ev(Orphan.orphan_absent_fold(xs, 0n), e),
      oh.run_snoc(xs, e, False{}), oh.queued_snoc(xs, e, 0n), oh.compact_snoc(xs, e, False{}), oh.absent_snoc(xs, e, 0n)),
    oh.apply_ev(e, Orphan.orphan_run_fold(xs, False{}), Orphan.orphan_queued_fold(xs, 0n), Orphan.orphan_compact_fold(xs, False{}), Orphan.orphan_absent_fold(xs, 0n)))

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
def oh.put(d: Bool, r: Bool, c: Bool, +q: Nat, +a: Nat) -> {Or.check.put(d, Or.W{r, q, c, a}) == Orphan.orphan_after_by(d, oh.busy(r, c, q), Or.W{r, q, c, a}) : Or.St}:
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

def oh.check(+window: Nat, +r: Bool, +c: Bool, +q: Nat, +a: Nat) -> {Or.check(window, Or.W{r, q, c, a}) == Orphan.orphan_after_by(Orphan.orphan_due_by(window, oh.busy(r, c, q), a), oh.busy(r, c, q), Or.W{r, q, c, a}) : Or.St}:
  %Equal.sym(Bool, Or.exit_due(window, a, Or.W.work(Or.W{r, q, c, a})), Orphan.orphan_due_by(window, oh.busy(r, c, q), a), oh.due(window, r, c, q, a)) : {Or.check.put(_, Or.W{r, q, c, a}) == Orphan.orphan_after_by(Orphan.orphan_due_by(window, oh.busy(r, c, q), a), oh.busy(r, c, q), Or.W{r, q, c, a}) : Or.St}
  oh.put(Orphan.orphan_due_by(window, oh.busy(r, c, q), a), r, c, q, a)

# a history and one more event is never empty: its exit check is the test
def oh.due_snoc(+window: Nat, xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Orphan.orphan_due_by(window, Orphan.orphan_busy(oh.snoc(xs, e)), Orphan.orphan_absent(0n, oh.snoc(xs, e))) == Orphan.orphan_due(window, oh.snoc(xs, e)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# the machine's step after a history's state is the spec's after
def oh.next(+window: Nat, +xs: List<&2, Or.Ev>, +e: Or.Ev) -> {Or.check(window, Or.apply(Orphan.orphan_state(xs), e)) == Orphan.orphan_after(window, oh.snoc(xs, e)) : Or.St}:
  %oh.state_snoc(xs, e) : {Or.check(window, _) == Orphan.orphan_after(window, oh.snoc(xs, e)) : Or.St}
  %oh.due_snoc(window, xs, e) : {Or.check(window, Orphan.orphan_state(oh.snoc(xs, e))) == Orphan.orphan_after_by(_, Orphan.orphan_busy(oh.snoc(xs, e)), Orphan.orphan_state(oh.snoc(xs, e))) : Or.St}
  oh.check(window, Orphan.orphan_run_fold(oh.snoc(xs, e), False{}), Orphan.orphan_compact_fold(oh.snoc(xs, e), False{}), Orphan.orphan_queued_fold(oh.snoc(xs, e), 0n), Orphan.orphan_absent_fold(oh.snoc(xs, e), 0n))

# a live state is the history's state, and its last exit check was not due
def oh.Inv(+window: Nat, +evs: List<&2, Or.Ev>, s: Or.St) -> Type:
  match s:
    case Or.Live{w}:
      {w == Orphan.orphan_state(evs) : Or.W} & {Orphan.orphan_due(window, evs) == False{} : Bool}
    case Or.Exited{d}:
      Unit

def oh.after_inv(d: Bool, +window: Nat, +ys: List<&2, Or.Ev>, h: {Orphan.orphan_due(window, ys) == d : Bool}) -> oh.Inv(window, ys, Orphan.orphan_after_by(d, Orphan.orphan_busy(ys), Orphan.orphan_state(ys))):
  match d:
    case True{}:
      Unit{}
    case False{}:
      ({==}, h)

def oh.step_inv(+window: Nat, +xs: List<&2, Or.Ev>, +e: Or.Ev, s: Or.St, ok: oh.Inv(window, xs, s)) -> oh.Inv(window, oh.snoc(xs, e), Or.step(window, s, e)):
  match s:
    case Or.Live{w}:
      (ew, nd) = ok
      %Equal.sym(Or.W, w, Orphan.orphan_state(xs), ew) : oh.Inv(window, oh.snoc(xs, e), Or.check(window, Or.apply(_, e)))
      %Equal.sym(Or.St, Or.check(window, Or.apply(Orphan.orphan_state(xs), e)), Orphan.orphan_after(window, oh.snoc(xs, e)), oh.next(window, xs, e)) : oh.Inv(window, oh.snoc(xs, e), _)
      oh.after_inv(Orphan.orphan_due(window, oh.snoc(xs, e)), window, oh.snoc(xs, e), {==})
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

def oh.inv_state(+window: Nat, +evs: List<&2, Or.Ev>, -w: Or.W, p: oh.Inv(window, evs, Or.Live{w})) -> {w == Orphan.orphan_state(evs) : Or.W}:
  (ew, nd) = p
  ew

def oh.inv_due(+window: Nat, +evs: List<&2, Or.Ev>, -w: Or.W, p: oh.Inv(window, evs, Or.Live{w})) -> {Orphan.orphan_due(window, evs) == False{} : Bool}:
  (ew, nd) = p
  nd
