# eukhe: lemmas the proofs of area orphan share

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/orphan.bend as Or
import ../../bend/wire.bend as Wr
import ../../laws/orphan.bend as Orphan
import ./orphan_work_exit_due.bend as PWorkExitDue

def ps.ffi_work(k: Or.Work, +r: String) -> {Wr.Got{k, r} == FO.get_work(FO.put_work(k, r)) : Wr.Dec<Or.Work>}:
  match k:
    case Or.Idle{}:
      {==}
    case Or.Ongoing{}:
      {==}

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
