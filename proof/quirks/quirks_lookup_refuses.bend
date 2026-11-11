# eukhe: the proof of LAW quirks_lookup_refuses
#
# PROOF: a lookup read whole answers its answer, a Nat first (0 or 1,
# Wire.wire_nat_not_err), never 'E'; every other branch of the lookup's
# decoder keeps the rulebook with the one error text.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/quirks.bend as Quirks
import ./base/verdicts.bend as QV

def qlf.R(rs: List<&2, If.Rule>, p: FQ.St & String) -> Type:
  {p == (FQ.Book{rs}, SCon{'E', SCon{' ', "quirks: malformed lookup"}}) : FQ.St & String}

# a Nat spelled first never opens with 'E'
def qlf.nat(-G: Type, n: Nat, rest: String, bad: {LawsBase.wire_opens_err(Wr.put_nat(n, rest)) == True{} : Bool}) -> G:
  QV.qv.absurd(G, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(Wr.put_nat(n, rest)), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(Wr.put_nat(n, rest)), False{}, Wire.wire_nat_not_err(n, rest)), bad))

def qlf.ans(-rs: List<&2, If.Rule>, a: If.Ans, bad: {LawsBase.wire_opens_err(FQ.put_ans(a, "")) == True{} : Bool}) -> qlf.R(rs, (FQ.Book{rs}, FQ.put_ans(a, ""))):
  match a:
    case If.Unknown{}:
      qlf.nat(qlf.R(rs, (FQ.Book{rs}, FQ.put_ans(If.Unknown{}, ""))), 0n, "", bad)
    case If.Known{v}:
      qlf.nat(qlf.R(rs, (FQ.Book{rs}, FQ.put_ans(If.Known{v}, ""))), 1n, Wr.put_nat(v, ""), bad)

def qlf.ask(+rs: List<&2, If.Rule>, m: Maybe<&2, FQ.Ask>, bad: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.step.ask(rs, m))) == True{} : Bool}) -> qlf.R(rs, FQ.step.ask(rs, m)):
  match m:
    case None{}:
      {==}
    case Some{a}:
      match a:
        case FQ.Ask{q, d}:
          qlf.ans(rs, If.lookup(rs, q, d), bad)

def qlf.end(+rs: List<&2, If.Rule>, +xs: List<&2, Nat>, s1: String, bad: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.step.end(Wr.end(s1), rs, xs))) == True{} : Bool}) -> qlf.R(rs, FQ.step.end(Wr.end(s1), rs, xs)):
  match s1:
    case SNil{}:
      qlf.ask(rs, FQ.ask(xs), bad)
    case SCon{c, t}:
      {==}

def qlf.book(+rs: List<&2, If.Rule>, d: Wr.Dec<List<&2, Nat>>, bad: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.step.book(rs, d))) == True{} : Bool}) -> qlf.R(rs, FQ.step.book(rs, d)):
  match d:
    case Wr.Got{xs, s1}:
      qlf.end(rs, xs, s1, bad)
    case Wr.Bad{}:
      {==}

def Quirks.quirks_lookup_refuses(rs, s, bad):
  qlf.book(rs, Wr.get_list(~Nat, ~Wr.get_nat, s), bad)
