# PROOF of LAW command_menu_lists_children: the words of the line are the
# names of q and then p (every word is spaceless), so the cut is (q, p)
# (B.cb_cut_last); the walk over q lands on q with its entry
# (B.cb_walk_root), whose menu is the rows of the children of q that
# start with the lowercase of p, which is cmd_rows (B.cb_items, B.cb_lows).

import Base
import ../LAWS.bend as Laws
import ../bend/command.bend as Cmd
import ./base.bend as B

def pml_at(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, hs: {Laws.cmd_some(m) == True{} : Bool}) -> {Cmd.menu.at(B.cb_st.of(m, q), t, p) == Cmd.Kids{q, Cmd.items(t, 0n, q, Cmd.lows(p))} : Cmd.Menu}:
  match m:
    case None{}:
      B.cb_absurd({Cmd.menu.at(B.cb_st.of(None{}, q), t, p) == Cmd.Kids{q, Cmd.items(t, 0n, q, Cmd.lows(p))} : Cmd.Menu}, hs)
    case Some{e}:
      {==}

def Laws.command_menu_lists_children(t, q, p, ok, on, word):
  match q:
    case Nil{}:
      B.cb_absurd({Cmd.menu(t, Laws.cmd_render(List.append(&2, List<&2, Nat>, Nil{}, [p]))) == Cmd.Kids{Nil{}, Laws.cmd_rows(t, 0n, Nil{}, Laws.cmd_lower(p))} : Cmd.Menu}, on)
    case Con{+x, +rest}:
      +qq = {x <> rest : List<&2, List<&2, Nat>>}
      +o = on
      +k = ok
      +line = Laws.cmd_render(List.append(&2, List<&2, Nat>, qq, [p]))
      %B.cb_items(t, 0n, qq, Laws.cmd_lower(p)) : {Cmd.menu(t, line) == Cmd.Kids{qq, _} : Cmd.Menu}
      %B.cb_lows(p) : {Cmd.menu(t, line) == Cmd.Kids{qq, Cmd.items(t, 0n, qq, _)} : Cmd.Menu}
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(Cmd.words(line)), (qq, p), B.cb_cut_last(t, qq, p, k, o, word)) : {Cmd.menu.cut(_, t) == Cmd.Kids{qq, Cmd.items(t, 0n, qq, Cmd.lows(p))} : Cmd.Menu}
      %Equal.sym(Cmd.St, Cmd.walk(qq, t, Cmd.Top{}), B.cb_st(t, qq), B.cb_walk_root(qq, t, k, o)) : {Cmd.menu.at(_, t, p) == Cmd.Kids{qq, Cmd.items(t, 0n, qq, Cmd.lows(p))} : Cmd.Menu}
      pml_at(Laws.cmd_lookup(t, qq), t, qq, p, B.cb_walks_decl(rest, x, t, Nil{}, o))
