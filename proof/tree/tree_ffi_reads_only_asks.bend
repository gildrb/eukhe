# eukhe: the proof of LAW tree_ffi_reads_only_asks
#
# PROOF: whatever the entry's decoder reads is the laws' spelling of what
# it read, then the rest, and fits the wire (te.ask); an answer that is no
# error comes from an ask read whole, nothing left (the other branches
# answer the error form, which the premise excludes), and is the core's
# step, its answer spelled (ts.step_ans).

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tree.bend as Tree
import ../wire/base/spell.bend as LAWireSpell
import ./base/exact.bend as LAExact
import ./base/spell.bend as LASpell

def ro.G(s: Tr.St, input: String, out: Ft.St & String) -> Type:
  &q: Tr.Ask -> {(input, (Tree.tree.ask_fits(q), out)) == (Tree.tree.spell_ask(q, ""), (True{}, (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")))) : String & (Bool & (Ft.St & String))}

# an ask read whole: the input, the fit and the step are the spec's
def ro.eq(+s: Tr.St, +input: String, +q: Tr.Ask, e: {input == Tree.tree.spell_ask(q, "") : String}, f: {Tree.tree.ask_fits(q) == True{} : Bool}) -> {(input, (Tree.tree.ask_fits(q), Ft.step.ans(Tr.core.step(s, q)))) == (Tree.tree.spell_ask(q, ""), (True{}, (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")))) : String & (Bool & (Ft.St & String))}:
  %Equal.sym(String, input, Tree.tree.spell_ask(q, ""), e) : {(_, (Tree.tree.ask_fits(q), Ft.step.ans(Tr.core.step(s, q)))) == (Tree.tree.spell_ask(q, ""), (True{}, (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")))) : String & (Bool & (Ft.St & String))}
  %Equal.sym(Bool, Tree.tree.ask_fits(q), True{}, f) : {(Tree.tree.spell_ask(q, ""), (_, Ft.step.ans(Tr.core.step(s, q)))) == (Tree.tree.spell_ask(q, ""), (True{}, (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")))) : String & (Bool & (Ft.St & String))}
  %Equal.sym(Ft.St & String, Ft.step.ans(Tr.core.step(s, q)), (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")), LASpell.ts.step_ans(Tr.core.step(s, q))) : {(Tree.tree.spell_ask(q, ""), (True{}, _)) == (Tree.tree.spell_ask(q, ""), (True{}, (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")))) : String & (Bool & (Ft.St & String))}
  {==}

# the end check: nothing left answers the core's step, anything left is
# the error form
def ro.fin(+s: Tr.St, +input: String, +q: Tr.Ask, r: String, e: {input == Tree.tree.spell_ask(q, r) : String}, f: {Tree.tree.ask_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.step.end(Wr.end(r), s, q))) == False{} : Bool}) -> ro.G(s, input, Ft.step.end(Wr.end(r), s, q)):
  match r:
    case SNil{}:
      (q, ro.eq(s, input, q, e, f))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(ro.G(s, input, Ft.step.end(False{}, s, q)), ok)

def ro.main(+s: Tr.St, +input: String, d: Wr.Dec<Tr.Ask>, inv: LAExact.te.A(input, d), ok: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.step.ask(s, d))) == False{} : Bool}) -> ro.G(s, input, Ft.step.ask(s, d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      ro.fin(s, input, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, input, (Ft.Live{s}, Wr.err("tree: malformed ask"))), ok)

def Tree.tree_ffi_reads_only_asks(s, input, ok):
  ro.main(s, input, Ft.get_ask(input), LAExact.te.ask(input), ok)
