# eukhe: the proof of LAW tree_ffi_error_keeps
#
# PROOF: a malformed ask and input left after an ask keep the core; an ask
# read whole answers the core's answer, which opens with its tag, never
# 'E' (ts.ans_ok), so the premise excludes it.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tree.bend as Tree
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell

# a step's answer to an ask read whole is no error
def ek.absurd(-G: Type, -R: Tr.St & Tr.Ans, ep: {Ft.step.ans(R) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, R)}, Ft.put_ans(Pair.snd(Tr.St, Tr.Ans, R), "")) : Ft.St & String}, ok: {LawsBase.wire_opens_err(Ft.put_ans(Pair.snd(Tr.St, Tr.Ans, R), "")) == False{} : Bool}, bad: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.step.ans(R))) == True{} : Bool}) -> G:
  LAWireSpell.ws_absurd(G,
    Equal.trans(Bool, True{}, LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.step.ans(R))), False{},
      Equal.sym(Bool, LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.step.ans(R))), True{}, bad),
      Equal.trans(Bool, LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.step.ans(R))), LawsBase.wire_opens_err(Ft.put_ans(Pair.snd(Tr.St, Tr.Ans, R), "")), False{},
        Equal.cong(Ft.St & String, Bool, z => LawsBase.wire_opens_err(Pair.snd(Ft.St, String, z)), Ft.step.ans(R), (Ft.Live{Pair.fst(Tr.St, Tr.Ans, R)}, Ft.put_ans(Pair.snd(Tr.St, Tr.Ans, R), "")), ep),
        ok)))

def ek.fin(+s: Tr.St, +q: Tr.Ask, r: String, bad: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.step.end(Wr.end(r), s, q))) == True{} : Bool}) -> {Pair.fst(Ft.St, String, Ft.step.end(Wr.end(r), s, q)) == Ft.Live{s} : Ft.St}:
  match r:
    case SNil{}:
      ek.absurd({Pair.fst(Ft.St, String, Ft.step.ans(Tr.core.step(s, q))) == Ft.Live{s} : Ft.St}, Tr.core.step(s, q), LASpell.ts.step_put(Tr.core.step(s, q)), LASpell.ts.ans_ok(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), ""), bad)
    case SCon{x, y}:
      {==}

def ek.main(+s: Tr.St, d: Wr.Dec<Tr.Ask>, bad: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.step.ask(s, d))) == True{} : Bool}) -> {Pair.fst(Ft.St, String, Ft.step.ask(s, d)) == Ft.Live{s} : Ft.St}:
  match d:
    case Wr.Got{+q, +r}:
      ek.fin(s, q, r, bad)
    case Wr.Bad{}:
      {==}

def Tree.tree_ffi_error_keeps(s, input, bad):
  ek.main(s, Ft.get_ask(input), bad)
