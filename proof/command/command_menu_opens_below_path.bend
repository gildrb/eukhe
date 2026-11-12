# eukhe: the proof of LAW command_menu_opens_below_path
#
# PROOF of LAW command_menu_opens_below_path: the words of the line are the
# names of q and then p (every word is spaceless), so the cut is (q, p)
# (LA.cb_cut_last); the walk over q lands on q with its entry
# (LA.cb_walk_root), and a walk at q shows a menu of children of q.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../base/list.bend as LList
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def mob_at(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, hs: {Command.cmd_some(m) == True{} : Bool}) -> {Command.cmd_lists_kids(Cmd.menu.at(LA.cb_st.of(m, q), t, p), q) == True{} : Bool}:
  match m:
    case None{}:
      LLogicLogic.cb_absurd({Command.cmd_lists_kids(Cmd.menu.at(LA.cb_st.of(None{}, q), t, p), q) == True{} : Bool}, hs)
    case Some{e}:
      LNat.cb_path_refl(q)

def Command.command_menu_opens_below_path(t, q, p, ok, on, word):
  match q:
    case Nil{}:
      LLogicLogic.cb_absurd({Command.cmd_lists_kids(Cmd.menu(t, Command.cmd_render(List.append(&2, List<&2, Nat>, Nil{}, [p]))), Nil{}) == True{} : Bool}, on)
    case Con{+x, +rest}:
      +qq = {x <> rest : List<&2, List<&2, Nat>>}
      +o = on
      +k = ok
      +line = Command.cmd_render(List.append(&2, List<&2, Nat>, qq, [p]))
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(Cmd.words(line)), (qq, p), LA.cb_cut_last(t, qq, p, k, o, word)) : {Command.cmd_lists_kids(Cmd.menu.cut(_, t), qq) == True{} : Bool}
      %Equal.sym(Cmd.St, Cmd.walk(qq, t, Cmd.Top{}), LA.cb_st(t, qq), LA.cb_walk_root(qq, t, k, o)) : {Command.cmd_lists_kids(Cmd.menu.at(_, t, p), qq) == True{} : Bool}
      mob_at(Command.cmd_lookup(t, qq), t, qq, p, LList.cb_walks_decl(rest, x, t, Nil{}, o))
