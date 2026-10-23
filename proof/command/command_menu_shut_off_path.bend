# eukhe: the proof of LAW command_menu_shut_off_path
#
# PROOF of LAW command_menu_shut_off_path: the words of the line are q, w,
# more and p (every word is spaceless), so the cut is (q ++ [w] ++ more,
# p); the walk over q lands on q (the root, or q with its entry), and w,
# naming no child of q, lands on Stray at the root, else on Rest (q takes
# text) or Lost (B.cb_walk_miss); each stays one of those whatever
# follows (B.cb_walk_stray, B.cb_walk_rest, B.cb_walk_lost), and none of
# them opens a menu.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command.bend as Command
import ../base/bool.bend as LBool
import ../base/list.bend as LList
import ./base.bend as LA

def pms_go(q: List<&2, List<&2, Nat>>, -w: List<&2, Nat>, -more: List<&2, List<&2, Nat>>, -p: List<&2, Nat>, -t: List<&2, Cmd.Ent>) -> {Cmd.menu.go(List.append(&2, List<&2, Nat>, q, w <> more), p, t) == Cmd.menu.at(Cmd.walk(List.append(&2, List<&2, Nat>, q, w <> more), t, Cmd.Top{}), t, p) : Cmd.Menu}:
  match q:
    case Nil{}:
      {==}
    case Con{y, ys}:
      {==}

def pms_free(b: Bool, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +more: List<&2, List<&2, Nat>>, -p: List<&2, Nat>) -> {Cmd.menu.at(Cmd.walk(more, t, Cmd.step.miss(b, q, w)), t, p) == Cmd.Shut{} : Cmd.Menu}:
  match b:
    case True{}:
      %Equal.sym(Cmd.St, Cmd.walk(more, t, Cmd.Rest{q, [w]}), Cmd.Rest{q, w <> more}, LA.cb_walk_rest(more, t, q, [w])) : {Cmd.menu.at(_, t, p) == Cmd.Shut{} : Cmd.Menu}
      {==}
    case False{}:
      %Equal.sym(Cmd.St, Cmd.walk(more, t, Cmd.Lost{q, w}), Cmd.Lost{q, w}, LA.cb_walk_lost(more, t, q, w)) : {Cmd.menu.at(_, t, p) == Cmd.Shut{} : Cmd.Menu}
      {==}

# no menu after a word that names no child of q
def pms_miss(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +more: List<&2, List<&2, Nat>>, -p: List<&2, Nat>) -> {Cmd.menu.at(Cmd.walk(more, t, LA.cb_miss(t, q, w)), t, p) == Cmd.Shut{} : Cmd.Menu}:
  match q:
    case Nil{}:
      %Equal.sym(Cmd.St, Cmd.walk(more, t, Cmd.Stray{}), Cmd.Stray{}, LA.cb_walk_stray(more, t)) : {Cmd.menu.at(_, t, p) == Cmd.Shut{} : Cmd.Menu}
      {==}
    case Con{+y, +ys}:
      pms_free(Command.cmd_free(t, y <> ys), t, y <> ys, w, more, p)

def Command.command_menu_shut_off_path(t, q, w, more, p, ok, on, word, after, last, miss):
  +k = ok
  +o = on
  +wd = word
  +mp = List.append(&2, List<&2, Nat>, more, [p])
  +d = List.append(&2, List<&2, Nat>, q, w <> more)
  +hs = LA.cb_all_spaceless_app(q, w <> mp, LA.cb_names_spaceless(q, LA.cb_walks_names(t, q, k, o)), LBool.cb_and_intro(Command.cmd_spaceless(w), Command.cmd_all_spaceless(mp), LA.cb_typed_spaceless(w, wd), LA.cb_all_spaceless_app(more, [p], after, LBool.cb_and_intro(Command.cmd_spaceless(p), True{}, last, {==}))))
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(Command.cmd_render(List.append(&2, List<&2, Nat>, q, w <> mp))), List.append(&2, List<&2, Nat>, q, w <> mp), LA.cb_words_render_app(q, w, mp, hs)) : {Cmd.menu.cut(Cmd.cut(_), t) == Cmd.Shut{} : Cmd.Menu}
  %LList.cb_app_assoc(List<&2, Nat>, q, w <> more, [p]) : {Cmd.menu.cut(Cmd.cut(_), t) == Cmd.Shut{} : Cmd.Menu}
  %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(List.append(&2, List<&2, Nat>, d, [p])), (d, p), LA.cb_cut(d, p)) : {Cmd.menu.cut(_, t) == Cmd.Shut{} : Cmd.Menu}
  %Equal.sym(Cmd.Menu, Cmd.menu.go(d, p, t), Cmd.menu.at(Cmd.walk(d, t, Cmd.Top{}), t, p), pms_go(q, w, more, p, t)) : {_ == Cmd.Shut{} : Cmd.Menu}
  %Equal.sym(Cmd.St, Cmd.walk(d, t, Cmd.Top{}), Cmd.walk(more, t, LA.cb_miss(t, q, w)), LA.cb_walk_miss(t, q, w, more, k, o, wd, miss)) : {Cmd.menu.at(_, t, p) == Cmd.Shut{} : Cmd.Menu}
  pms_miss(t, q, w, more, p)
