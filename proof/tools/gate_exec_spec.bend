# eukhe: the proof of LAW gate_exec_spec
# The gate's head test `within` is the spec's (membership, then the codes
# an auto set may hold, by induction on the effects); then induction on
# the script, split on the answers and on the head test (a parameter):
# each arm computes to the spec's, the rest by the induction hypothesis.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

# membership is the spec's
def pge.in(xs: List<&2, Nat>, +c: Nat) -> {Tl.elem(xs, c) == Tools.tg_in(xs, c) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> rest:
      %pge.in(rest, c) : {Bool.or(Nat.is_eq(y, c), Tl.elem(rest, c)) == Bool.or(Nat.is_eq(y, c), _) : Bool}
      {==}

# an auto set may hold exactly the codes 0 to 6
def pge.grant(c: Nat) -> {Tl.grantable(c) == Nat.is_lt(c, 7n) : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+d:
              match d:
                case 0n:
                  {==}
                case 1n+e:
                  match e:
                    case 0n:
                      {==}
                    case 1n+f:
                      match f:
                        case 0n:
                          {==}
                        case 1n+g:
                          match g:
                            case 0n:
                              {==}
                            case 1n+h:
                              match h:
                                case 0n:
                                  {==}
                                case 1n+q:
                                  {==}

# the gate's head test is the spec's
def pge.within(effs: List<&2, Nat>, +auto: List<&2, Nat>) -> {Tl.within(effs, auto) == Tools.tg_unasked(effs, auto) : Bool}:
  match effs:
    case Nil{}:
      {==}
    case +c <> rest:
      %pge.grant(c) : {Bool.and(Bool.and(Tl.grantable(c), Tl.elem(auto, c)), Tl.within(rest, auto)) == Bool.and(Bool.and(_, Tools.tg_in(auto, c)), Tools.tg_unasked(rest, auto)) : Bool}
      %pge.in(auto, c) : {Bool.and(Bool.and(Tl.grantable(c), Tl.elem(auto, c)), Tl.within(rest, auto)) == Bool.and(Bool.and(Tl.grantable(c), _), Tools.tg_unasked(rest, auto)) : Bool}
      %pge.within(rest, auto) : {Bool.and(Bool.and(Tl.grantable(c), Tl.elem(auto, c)), Tl.within(rest, auto)) == Bool.and(Bool.and(Tl.grantable(c), Tl.elem(auto, c)), _) : Bool}
      {==}

def pge.free(s: Tl.Step, +auto: List<&2, Nat>) -> {Tl.within(Tl.Step.effs(s), auto) == Tools.tg_free(s, auto) : Bool}:
  match s:
    case Tl.Step{i, f}:
      pge.within(f, auto)

def pge.ran(+s: Tl.Step, r: Tl.Ran) -> {Tl.ran.add(s, r) == Tools.tg_ran(s, r) : Tl.Ran}:
  match r:
    case Tl.Ran{ss, e}:
      {==}

# step s ran, then the rest ran as the spec's
def pge.runs(+s: Tl.Step, +rest: List<&2, Tl.Step>, +auto: List<&2, Nat>, +ans: List<&2, Bool>, ih: {Tl.exec(rest, auto, ans) == Tools.tg_exec(rest, auto, ans) : Tl.Ran}) -> {Tl.ran.add(s, Tl.exec(rest, auto, ans)) == Tools.tg_ran(s, Tools.tg_exec(rest, auto, ans)) : Tl.Ran}:
  %ih : {Tl.ran.add(s, Tl.exec(rest, auto, ans)) == Tools.tg_ran(s, _) : Tl.Ran}
  pge.ran(s, Tl.exec(rest, auto, ans))

# a step denied as the spec denies it
def pge.denied(s: Tl.Step, r: Tl.Ran) -> {Tl.gate(False{}, s, r) == Tools.tg_denied(s) : Tl.Ran}:
  match s:
    case Tl.Step{i, f}:
      {==}

# the user's answer a to an asked step
def pge.answer(a: Bool, +s: Tl.Step, +rest: List<&2, Tl.Step>, +auto: List<&2, Nat>, +more: List<&2, Bool>, ih: {Tl.exec(rest, auto, more) == Tools.tg_exec(rest, auto, more) : Tl.Ran}) -> {Tl.gate(a, s, Tl.exec(rest, auto, more)) == Tools.tg_answer(a, s, Tools.tg_exec(rest, auto, more)) : Tl.Ran}:
  match a:
    case True{}:
      pge.runs(s, rest, auto, more, ih)
    case False{}:
      pge.denied(s, Tl.exec(rest, auto, more))

# no answer left, with head test b
def pge.nil(b: Bool, +s: Tl.Step, +rest: List<&2, Tl.Step>, +auto: List<&2, Nat>, ih: {Tl.exec(rest, auto, Nil{}) == Tools.tg_exec(rest, auto, Nil{}) : Tl.Ran}) -> {Tl.exec.go(s <> rest, auto, b, Nil{}) == Tools.tg_pick(b, Tools.tg_ran(s, Tools.tg_exec(rest, auto, Nil{})), Tools.tg_denied(s)) : Tl.Ran}:
  match b:
    case True{}:
      pge.runs(s, rest, auto, Nil{}, ih)
    case False{}:
      pge.denied(s, Tl.Ran{Nil{}, Tl.Finished{}})

# answer a, then more, with head test b
def pge.cons(b: Bool, +s: Tl.Step, +rest: List<&2, Tl.Step>, +auto: List<&2, Nat>, +a: Bool, +more: List<&2, Bool>, ih1: {Tl.exec(rest, auto, a <> more) == Tools.tg_exec(rest, auto, a <> more) : Tl.Ran}, ih2: {Tl.exec(rest, auto, more) == Tools.tg_exec(rest, auto, more) : Tl.Ran}) -> {Tl.exec.go(s <> rest, auto, b, a <> more) == Tools.tg_pick(b, Tools.tg_ran(s, Tools.tg_exec(rest, auto, a <> more)), Tools.tg_answer(a, s, Tools.tg_exec(rest, auto, more))) : Tl.Ran}:
  match b:
    case True{}:
      pge.runs(s, rest, auto, a <> more, ih1)
    case False{}:
      pge.answer(a, s, rest, auto, more, ih2)

def pge.exec(ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, ans: List<&2, Bool>) -> {Tl.exec(ss, auto, ans) == Tools.tg_exec(ss, auto, ans) : Tl.Ran}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      match ans:
        case Nil{}:
          %pge.free(s, auto) : {Tl.exec.go(s <> rest, auto, Tl.within(Tl.Step.effs(s), auto), Nil{}) == Tools.tg_pick(_, Tools.tg_ran(s, Tools.tg_exec(rest, auto, Nil{})), Tools.tg_denied(s)) : Tl.Ran}
          pge.nil(Tl.within(Tl.Step.effs(s), auto), s, rest, auto, pge.exec(rest, auto, Nil{}))
        case +a <> +more:
          %pge.free(s, auto) : {Tl.exec.go(s <> rest, auto, Tl.within(Tl.Step.effs(s), auto), a <> more) == Tools.tg_pick(_, Tools.tg_ran(s, Tools.tg_exec(rest, auto, a <> more)), Tools.tg_answer(a, s, Tools.tg_exec(rest, auto, more))) : Tl.Ran}
          pge.cons(Tl.within(Tl.Step.effs(s), auto), s, rest, auto, a, more, pge.exec(rest, auto, a <> more), pge.exec(rest, auto, more))

def Tools.gate_exec_spec(ss, auto, ans):
  pge.exec(ss, auto, ans)
