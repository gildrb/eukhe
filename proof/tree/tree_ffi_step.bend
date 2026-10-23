# eukhe: the proof of LAW tree_ffi_step

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree
import ./base.bend as LA

# a step's reply is the pair's parts
def tf.ans(r: Tr.St & Tr.Ans) -> {Ft.step.ans(r) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, r)}, Ft.put_ans(Pair.snd(Tr.St, Tr.Ans, r), "")) : Ft.St & String}:
  (s, a) = r
  {==}

def Tree.tree_ffi_step(s, q, h):
  %Equal.sym(Wr.Dec<Tr.Ask>, Ft.get_ask(Ft.put_ask(q, "")), Wr.Got{q, ""}, LA.tf.ask_rt(q, "", h)) : {Ft.step.ask(s, _) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Ft.put_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")) : Ft.St & String}
  tf.ans(Tr.core.step(s, q))
