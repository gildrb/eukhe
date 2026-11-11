# eukhe: the proof of LAW quirks_rejected_run
#
# PROOF: an open whose reply does not open with T leaves the refused state
# (qrj.known: a rulebook kept answers T; every other branch is Shut); the
# refused state answers every later input with its error (qrj.feed, by
# induction on the inputs).

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/quirks.bend as Quirks
import ../wire/base/spell.bend as LAWireSpell

# from the refused state that answered o, every later step answers its error
def qrj.feed(ins: List<&2, String>, o: String) -> {Quirks.qs_feed(ins, (FQ.Shut{}, o)) == o <> List.replicate(String, List.length(&2, String, ins), SCon{'E', SCon{' ', "quirks: no rulebook"}}) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case i <> t:
      Equal.cong(List<&2, String>, List<&2, String>, z => o <> z, Quirks.qs_feed(t, (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: no rulebook"}})), SCon{'E', SCon{' ', "quirks: no rulebook"}} <> List.replicate(String, List.length(&2, String, t), SCon{'E', SCon{' ', "quirks: no rulebook"}}), qrj.feed(t, SCon{'E', SCon{' ', "quirks: no rulebook"}}))

# the open left the refused state
def qrj.SH(p: FQ.St & String) -> Type:
  {p == (FQ.Shut{}, Pair.snd(FQ.St, String, p)) : FQ.St & String}

def qrj.reply(b: Bool, -rs: List<&2, If.Rule>, -vs: List<&2, If.Verdict>, no: {Quirks.qs_says_compiles(Pair.snd(FQ.St, String, FQ.open.reply(b, rs, vs))) == False{} : Bool}) -> qrj.SH(FQ.open.reply(b, rs, vs)):
  match b:
    case True{}:
      LAWireSpell.ws_absurd(qrj.SH(FQ.open.reply(True{}, rs, vs)), no)
    case False{}:
      {==}

def qrj.book(+known: List<&2, Nat>, m: Maybe<&2, List<&2, If.Rule>>, no: {Quirks.qs_says_compiles(Pair.snd(FQ.St, String, FQ.open.book(known, m))) == False{} : Bool}) -> qrj.SH(FQ.open.book(known, m)):
  match m:
    case None{}:
      {==}
    case Some{+rs}:
      qrj.reply(If.fine_all(If.verdicts(known, rs)), rs, If.verdicts(known, rs), no)

def qrj.end(+known: List<&2, Nat>, +xs: List<&2, Nat>, s2: String, no: {Quirks.qs_says_compiles(Pair.snd(FQ.St, String, FQ.open.end(Wr.end(s2), known, xs))) == False{} : Bool}) -> qrj.SH(FQ.open.end(Wr.end(s2), known, xs)):
  match s2:
    case SNil{}:
      qrj.book(known, FQ.rules(xs), no)
    case SCon{c, t}:
      {==}

def qrj.rules(+known: List<&2, Nat>, d: Wr.Dec<List<&2, Nat>>, no: {Quirks.qs_says_compiles(Pair.snd(FQ.St, String, FQ.open.rules(known, d))) == False{} : Bool}) -> qrj.SH(FQ.open.rules(known, d)):
  match d:
    case Wr.Got{xs, s2}:
      qrj.end(known, xs, s2, no)
    case Wr.Bad{}:
      {==}

def qrj.known(d: Wr.Dec<List<&2, Nat>>, no: {Quirks.qs_says_compiles(Pair.snd(FQ.St, String, FQ.open.known(d))) == False{} : Bool}) -> qrj.SH(FQ.open.known(d)):
  match d:
    case Wr.Got{known, s1}:
      qrj.rules(known, Wr.get_list(~Nat, ~Wr.get_nat, s1), no)
    case Wr.Bad{}:
      {==}

def Quirks.quirks_rejected_run(s, ins, no):
  Equal.trans(List<&2, String>, Quirks.qs_feed(ins, FQ.open(s)), Quirks.qs_feed(ins, (FQ.Shut{}, Pair.snd(FQ.St, String, FQ.open(s)))), Pair.snd(FQ.St, String, FQ.open(s)) <> List.replicate(String, List.length(&2, String, ins), SCon{'E', SCon{' ', "quirks: no rulebook"}}),
    Equal.cong(FQ.St & String, List<&2, String>, p => Quirks.qs_feed(ins, p), FQ.open(s), (FQ.Shut{}, Pair.snd(FQ.St, String, FQ.open(s))), qrj.known(Wr.get_list(~Nat, ~Wr.get_nat, s), no)),
    qrj.feed(ins, Pair.snd(FQ.St, String, FQ.open(s))))
