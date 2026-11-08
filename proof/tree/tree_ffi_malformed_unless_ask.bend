# eukhe: the proof of LAW tree_ffi_malformed_unless_ask
#
# PROOF: the decoder reads only spelled asks that fit, the rest after them
# untouched (te.ask); when it reads none the step answers the malformed
# error, which the premise excludes.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree
import ../wire/base/spell.bend as LAWireSpell
import ./base/exact.bend as LAExact

def mu.goal(input: String) -> Type:
  &q: Tr.Ask -> &rest: String -> {(input, Tree.tree.ask_fits(q)) == (Tree.tree.spell_ask(q, rest), True{}) : String & Bool}

def mu.eq(+input: String, +q: Tr.Ask, +rest: String, e1: {input == Tree.tree.spell_ask(q, rest) : String}, e2: {Tree.tree.ask_fits(q) == True{} : Bool}) -> {(input, Tree.tree.ask_fits(q)) == (Tree.tree.spell_ask(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, input, Tree.tree.spell_ask(q, rest), e1) : {(_, Tree.tree.ask_fits(q)) == (Tree.tree.spell_ask(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Tree.tree.ask_fits(q), True{}, e2) : {(Tree.tree.spell_ask(q, rest), _) == (Tree.tree.spell_ask(q, rest), True{}) : String & Bool}
  {==}

def mu.main(-s: Tr.St, +input: String, d: Wr.Dec<Tr.Ask>, inv: LAExact.te.A(input, d), other: {String.eq(Pair.snd(Ft.St, String, Ft.step.ask(s, d)), Wr.err("tree: malformed ask")) == False{} : Bool}) -> mu.goal(input):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, mu.eq(input, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(mu.goal(input), other)

def Tree.tree_ffi_malformed_unless_ask(s, input, other):
  mu.main(s, input, Ft.get_ask(input), LAExact.te.ask(input), other)
