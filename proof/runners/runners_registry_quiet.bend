# eukhe: the proof of LAW runners_registry_quiet
#
# PROOF: every tool of the registry is `python`, `bash` or quiet (rq.all computes); a tool at an index of such a list, not named either, is quiet.

import Base
import ../../bend/runners.bend as Ru
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/runners.bend as Runners
import ../base/staging.bend as LStg

def rq.MD(m: Maybe<&2, Ru.ToolReg>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# every tool of xs is `python`, `bash` or runs no code of its own
def rq.all(xs: List<&2, Ru.ToolReg>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Bool.or(Runners.named_in(Ru.ToolReg.name(x), ["python", "bash"]), Runners.quiet(x)), rq.all(rest))

def rq.or_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, na: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      LStg.stg.absurd({b == True{} : Bool}, na)
    case False{}:
      h

def rq.each(xs: List<&2, Ru.ToolReg>, i: Nat, +t: Ru.ToolReg, +all: {rq.all(xs) == True{} : Bool}, at: {List.get(&2, Ru.ToolReg, xs, i) == Some{t} : Maybe<&2, Ru.ToolReg>}, other: {Runners.named_in(Ru.ToolReg.name(t), ["python", "bash"]) == False{} : Bool}) -> {Runners.quiet(t) == True{} : Bool}:
  match xs:
    case Nil{}:
      %at : rq.MD(_, {Runners.quiet(t) == True{} : Bool})
      Unit{}
    case +x <> +rest:
      match i:
        case 0n:
          +same = Equal.cong(Maybe<&2, Ru.ToolReg>, Ru.ToolReg, m => Maybe.default(&2, Ru.ToolReg, m, t), Some{x}, Some{t}, at)
          %same : {Runners.quiet(_) == True{} : Bool}
          +nx = Equal.trans(Bool, Runners.named_in(Ru.ToolReg.name(x), ["python", "bash"]), Runners.named_in(Ru.ToolReg.name(t), ["python", "bash"]), False{}, Equal.cong(Ru.ToolReg, Bool, z => Runners.named_in(Ru.ToolReg.name(z), ["python", "bash"]), x, t, same), other)
          rq.or_r(Runners.named_in(Ru.ToolReg.name(x), ["python", "bash"]), Runners.quiet(x), LStg.stg.and_l(Bool.or(Runners.named_in(Ru.ToolReg.name(x), ["python", "bash"]), Runners.quiet(x)), rq.all(rest), all), nx)
        case 1n+p:
          rq.each(rest, p, t, LStg.stg.and_r(Bool.or(Runners.named_in(Ru.ToolReg.name(x), ["python", "bash"]), Runners.quiet(x)), rq.all(rest), all), at, other)

def Runners.runners_registry_quiet(i, t, at, other):
  rq.each(Ru.registry(), i, t, {==}, at, other)
