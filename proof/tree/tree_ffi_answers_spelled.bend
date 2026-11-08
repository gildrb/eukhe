# eukhe: the proof of LAW tree_ffi_answers_spelled
#
# PROOF: the laws' spelling of an ask is the entry's (ts.ask), which reads
# back whole (tf.ask_rt); the step then answers the core's pair, its answer
# spelled (ts.step_ans).

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree
import ./base/spell.bend as LASpell
import ./base/wire.bend as LAWire

def Tree.tree_ffi_answers_spelled(s, q, fits):
  %LASpell.ts.ask(q, "") : {Ft.step(Ft.Live{s}, _) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")) : Ft.St & String}
  %Equal.sym(Wr.Dec<Tr.Ask>, Ft.get_ask(Ft.put_ask(q, "")), Wr.Got{q, ""}, LAWire.tf.ask_rt(q, "", fits)) : {Ft.step.ask(s, _) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")) : Ft.St & String}
  LASpell.ts.step_ans(Tr.core.step(s, q))
