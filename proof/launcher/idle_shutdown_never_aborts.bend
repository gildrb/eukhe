# eukhe: the proof of LAW idle_shutdown_never_aborts

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ../base/bool/misc.bend as LBoolMisc

# (D1) idle_shutdown_never_aborts
# -------------------------------

# a closed gate holds no run
def ps.WOk(w: La.Wk) -> Type:
  match w:
    case La.Wk{b, c}:
      match c:
        case True{}:
          {b == False{} : Bool}
        case False{}:
          Unit

def ps.Inv(ws: List<&2, La.Wk>) -> Type:
  match ws:
    case Nil{}:
      Unit
    case +w <> t:
      (ps.WOk(w) & ps.Inv(t))

# no run aborted, and while the daemon serves, no closed gate holds a run
def ps.Good(s: La.St) -> Type:
  match s:
    case La.St{ws, a, d}:
      match d:
        case True{}:
          {a == 0n : Nat}
        case False{}:
          ({a == 0n : Nat} & ps.Inv(ws))

def ps.prompt_ok(w: La.Wk, ok: ps.WOk(w)) -> ps.WOk(La.prompt(w)):
  match w:
    case La.Wk{b, c}:
      match c:
        case True{}:
          ok
        case False{}:
          Unit{}

def ps.finish_ok(w: La.Wk) -> ps.WOk(La.finish(w)):
  match w:
    case La.Wk{b, c}:
      match c:
        case True{}:
          {==}
        case False{}:
          Unit{}

def ps.quiesce_ok(w: La.Wk, ok: ps.WOk(w)) -> ps.WOk(La.quiesce(w)):
  match w:
    case La.Wk{b, c}:
      match b:
        case True{}:
          ok
        case False{}:
          {==}

def ps.release_ok(w: La.Wk) -> ps.WOk(La.release(w)):
  match w:
    case La.Wk{b, c}:
      Unit{}

def ps.at_prompt(i: Nat, ws: List<&2, La.Wk>, inv: ps.Inv(ws)) -> ps.Inv(La.at(~La.prompt, i, ws)):
  match i:
    case 0n:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (ps.prompt_ok(w, wo), it)
    case 1n+j:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (wo, ps.at_prompt(j, t, it))

def ps.at_finish(i: Nat, ws: List<&2, La.Wk>, inv: ps.Inv(ws)) -> ps.Inv(La.at(~La.finish, i, ws)):
  match i:
    case 0n:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (ps.finish_ok(w), it)
    case 1n+j:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (wo, ps.at_finish(j, t, it))

def ps.at_quiesce(i: Nat, ws: List<&2, La.Wk>, inv: ps.Inv(ws)) -> ps.Inv(La.at(~La.quiesce, i, ws)):
  match i:
    case 0n:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (ps.quiesce_ok(w, wo), it)
    case 1n+j:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (wo, ps.at_quiesce(j, t, it))

def ps.at_release(i: Nat, ws: List<&2, La.Wk>, inv: ps.Inv(ws)) -> ps.Inv(La.at(~La.release, i, ws)):
  match i:
    case 0n:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (ps.release_ok(w), it)
    case 1n+j:
      match ws:
        case Nil{}:
          Unit{}
        case +w <> t:
          (wo, it) = inv
          (wo, ps.at_release(j, t, it))

# every gate closed: no run
def ps.closed_idle(ws: List<&2, La.Wk>, inv: ps.Inv(ws), ac: {La.all_closed(ws) == True{} : Bool}) -> {La.busy_count(ws) == 0n : Nat}:
  match ws:
    case Nil{}:
      {==}
    case w <> t:
      match w:
        case La.Wk{b, c}:
          match b c:
            case True{} False{}:
              LBoolMisc.supervisor.ps.absurdF({La.busy_count(La.Wk{True{}, False{}} <> t) == 0n : Nat}, ac)
            case False{} False{}:
              LBoolMisc.supervisor.ps.absurdF({La.busy_count(La.Wk{False{}, False{}} <> t) == 0n : Nat}, ac)
            case True{} True{}:
              (wo, it) = inv
              LBoolMisc.supervisor.ps.absurd({La.busy_count(La.Wk{True{}, True{}} <> t) == 0n : Nat}, wo)
            case False{} True{}:
              (wo, it) = inv
              ps.closed_idle(t, it, ac)

def ps.commit_good(ok: Bool, +ws: List<&2, La.Wk>, +a: Nat, e: {La.all_closed(ws) == ok : Bool}, ea: {a == 0n : Nat}, inv: ps.Inv(ws)) -> ps.Good(La.commit.put(ok, ws, a)):
  match ok:
    case True{}:
      %Equal.sym(Nat, La.busy_count(ws), 0n, ps.closed_idle(ws, inv, e)) : {Nat.add(_, a) == 0n : Nat}
      ea
    case False{}:
      (ea, inv)

def ps.step_good(s: La.St, +op: La.Op, g: ps.Good(s)) -> ps.Good(La.step(s, op)):
  match s:
    case La.St{+ws, +a, d}:
      match d:
        case True{}:
          g
        case False{}:
          match op:
            case La.Prompt{i}:
              (ea, inv) = g
              (ea, ps.at_prompt(i, ws, inv))
            case La.Finish{i}:
              (ea, inv) = g
              (ea, ps.at_finish(i, ws, inv))
            case La.Quiesce{i}:
              (ea, inv) = g
              (ea, ps.at_quiesce(i, ws, inv))
            case La.Release{i}:
              (ea, inv) = g
              (ea, ps.at_release(i, ws, inv))
            case La.Commit{}:
              (ea, inv) = g
              ps.commit_good(La.all_closed(ws), ws, a, {==}, ea, inv)

def ps.go_good(ops: List<&2, La.Op>, +s: La.St, g: ps.Good(s)) -> ps.Good(La.go(ops, s)):
  match ops:
    case Nil{}:
      g
    case +op <> rest:
      ps.go_good(rest, La.step(s, op), ps.step_good(s, op, g))

def ps.open_inv(bs: List<&2, Bool>) -> ps.Inv(La.open(bs)):
  match bs:
    case Nil{}:
      Unit{}
    case b <> t:
      (Unit{}, ps.open_inv(t))

def ps.aborted_zero(s: La.St, g: ps.Good(s)) -> {La.St.aborted(s) == 0n : Nat}:
  match s:
    case La.St{ws, a, d}:
      match d:
        case True{}:
          g
        case False{}:
          (ea, inv) = g
          ea

def ps.idle_shutdown_never_aborts(+bs: List<&2, Bool>, +ops: List<&2, La.Op>) -> {La.St.aborted(La.run(bs, ops)) == 0n : Nat}:
  ps.aborted_zero(La.run(bs, ops), ps.go_good(ops, La.St{La.open(bs), 0n, False{}}, ({==}, ps.open_inv(bs))))

def Launcher.idle_shutdown_never_aborts(bs, ops):
  ps.idle_shutdown_never_aborts(bs, ops)
