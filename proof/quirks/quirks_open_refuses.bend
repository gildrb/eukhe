# eukhe: the proof of LAW quirks_open_refuses
#
# PROOF: a rulebook read whole answers a reply that opens with T or F
# (qof.reply), never 'E'; every other branch of the open's decoder is the
# refused state with the one error text.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/quirks.bend as Quirks
import ./base/verdicts.bend as QV

def qof.R(p: FQ.St & String) -> Type:
  {p == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String}

def qof.reply(b: Bool, -rs: List<&2, If.Rule>, -vs: List<&2, If.Verdict>, bad: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open.reply(b, rs, vs))) == True{} : Bool}) -> qof.R(FQ.open.reply(b, rs, vs)):
  match b:
    case True{}:
      QV.qv.absurd(qof.R(FQ.open.reply(True{}, rs, vs)), bad)
    case False{}:
      QV.qv.absurd(qof.R(FQ.open.reply(False{}, rs, vs)), bad)

def qof.book(+known: List<&2, Nat>, m: Maybe<&2, List<&2, If.Rule>>, bad: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open.book(known, m))) == True{} : Bool}) -> qof.R(FQ.open.book(known, m)):
  match m:
    case None{}:
      {==}
    case Some{+rs}:
      qof.reply(If.fine_all(If.verdicts(known, rs)), rs, If.verdicts(known, rs), bad)

def qof.end(+known: List<&2, Nat>, +xs: List<&2, Nat>, s2: String, bad: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open.end(Wr.end(s2), known, xs))) == True{} : Bool}) -> qof.R(FQ.open.end(Wr.end(s2), known, xs)):
  match s2:
    case SNil{}:
      qof.book(known, FQ.rules(xs), bad)
    case SCon{c, t}:
      {==}

def qof.rules(+known: List<&2, Nat>, d: Wr.Dec<List<&2, Nat>>, bad: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open.rules(known, d))) == True{} : Bool}) -> qof.R(FQ.open.rules(known, d)):
  match d:
    case Wr.Got{xs, s2}:
      qof.end(known, xs, s2, bad)
    case Wr.Bad{}:
      {==}

def qof.known(d: Wr.Dec<List<&2, Nat>>, bad: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.open.known(d))) == True{} : Bool}) -> qof.R(FQ.open.known(d)):
  match d:
    case Wr.Got{known, s1}:
      qof.rules(known, Wr.get_list(~Nat, ~Wr.get_nat, s1), bad)
    case Wr.Bad{}:
      {==}

def Quirks.quirks_open_refuses(s, bad):
  qof.known(Wr.get_list(~Nat, ~Wr.get_nat, s), bad)
