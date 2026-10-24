# eukhe: the proof of LAW command_menu_space_gap
#
# PROOF of LAW command_menu_space_gap: the words of the line of a
# declared path q, a space and text are q and the words of the text
# (LSp.sp_words_render); a second space adds one empty word between
# them. The words of the text are never none (LSp.sp_words_ne), so both
# cuts take their last word from the text and keep q, with or without
# the empty word, before the rest (msg_cut_mid). The walk over q lands on
# q, where the empty word changes nothing (LSp.sp_walk_gap), so both
# menus are the menu at the same state below the same last word.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA
import ./base/space.bend as LSp

# the words a, then the words before the last of a cut c, and its last
def msg_pre(a: List<&2, List<&2, Nat>>, c: List<&2, List<&2, Nat>> & List<&2, Nat>) -> List<&2, List<&2, Nat>> & List<&2, Nat>:
  match c:
    case (d, p):
      (List.append(&2, List<&2, Nat>, a, d), p)

def msg_pre_one(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +x: List<&2, Nat>) -> {Cmd.cut.cons(x, c) == msg_pre([x], c) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  match c:
    case (d, p):
      {==}

def msg_pre_cons(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +x: List<&2, Nat>, -a: List<&2, List<&2, Nat>>) -> {Cmd.cut.cons(x, msg_pre(a, c)) == msg_pre(x <> a, c) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  match c:
    case (d, p):
      {==}

# the cut of x, a, v and b: x and a before the cut of v and b
def msg_cut_mid(a: List<&2, List<&2, Nat>>, +v: List<&2, Nat>, +b: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Cmd.cut.go(List.append(&2, List<&2, Nat>, a, v <> b), x) == msg_pre(x <> a, Cmd.cut.go(b, v)) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  match a:
    case Nil{}:
      msg_pre_one(Cmd.cut.go(b, v), x)
    case Con{+y, +ys}:
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut.go(List.append(&2, List<&2, Nat>, ys, v <> b), y), msg_pre(y <> ys, Cmd.cut.go(b, v)), msg_cut_mid(ys, v, b, y)) : {Cmd.cut.cons(x, _) == msg_pre(x <> y <> ys, Cmd.cut.go(b, v)) : List<&2, List<&2, Nat>> & List<&2, Nat>}
      msg_pre_cons(Cmd.cut.go(b, v), x, y <> ys)

def msg_pair(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +x: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, ok: {Command.cmd_wf(t) == True{} : Bool}, on: {Command.cmd_walks(t, x <> rest) == True{} : Bool}) -> {Cmd.menu.cut(msg_pre(x <> rest, Cmd.cut.cons(Nil{}, c)), t) == Cmd.menu.cut(msg_pre(x <> rest, c), t) : Cmd.Menu}:
  match c:
    case (d, p):
      %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, x <> rest, Nil{} <> d), t, Cmd.Top{}), Cmd.walk(List.append(&2, List<&2, Nat>, x <> rest, d), t, Cmd.Top{}), LSp.sp_walk_gap(t, x <> rest, d, ok, on)) : {Cmd.menu.at(_, t, p) == Cmd.menu.at(Cmd.walk(List.append(&2, List<&2, Nat>, x <> rest, d), t, Cmd.Top{}), t, p) : Cmd.Menu}
      {==}

def msg_gap(ws: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, ok: {Command.cmd_wf(t) == True{} : Bool}, on: {Command.cmd_walks(t, x <> rest) == True{} : Bool}, h: {LSp.sp_ne(ws) == True{} : Bool}) -> {Cmd.menu.cut(Cmd.cut(x <> List.append(&2, List<&2, Nat>, rest, Nil{} <> ws)), t) == Cmd.menu.cut(Cmd.cut(x <> List.append(&2, List<&2, Nat>, rest, ws)), t) : Cmd.Menu}:
  match ws:
    case Nil{}:
      LLogicLogic.cb_absurd({Cmd.menu.cut(Cmd.cut(x <> List.append(&2, List<&2, Nat>, rest, [Nil{}])), t) == Cmd.menu.cut(Cmd.cut(x <> List.append(&2, List<&2, Nat>, rest, Nil{})), t) : Cmd.Menu}, h)
    case Con{+w0, +w2}:
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut.go(List.append(&2, List<&2, Nat>, rest, Nil{} <> w0 <> w2), x), msg_pre(x <> rest, Cmd.cut.go(w0 <> w2, Nil{})), msg_cut_mid(rest, Nil{}, w0 <> w2, x)) : {Cmd.menu.cut(_, t) == Cmd.menu.cut(Cmd.cut.go(List.append(&2, List<&2, Nat>, rest, w0 <> w2), x), t) : Cmd.Menu}
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut.go(List.append(&2, List<&2, Nat>, rest, w0 <> w2), x), msg_pre(x <> rest, Cmd.cut.go(w2, w0)), msg_cut_mid(rest, w0, w2, x)) : {Cmd.menu.cut(msg_pre(x <> rest, Cmd.cut.go(w0 <> w2, Nil{})), t) == Cmd.menu.cut(_, t) : Cmd.Menu}
      msg_pair(Cmd.cut.go(w2, w0), x, rest, t, ok, on)

def Command.command_menu_space_gap(t, q, line, ok, on):
  match q:
    case Nil{}:
      LLogicLogic.cb_absurd({Cmd.menu(t, List.append(&2, Nat, Command.cmd_render(Nil{}), 32n <> 32n <> line)) == Cmd.menu(t, List.append(&2, Nat, Command.cmd_render(Nil{}), 32n <> line)) : Cmd.Menu}, on)
    case Con{+x, +rest}:
      +k = ok
      +o = on
      +hs = LA.cb_names_spaceless(x <> rest, LA.cb_walks_names(t, x <> rest, k, o))
      +w = Cmd.words(line)
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(List.append(&2, Nat, Command.cmd_render(x <> rest), 32n <> 32n <> line)), x <> List.append(&2, List<&2, Nat>, rest, Nil{} <> w), LSp.sp_words_render(x, rest, 32n <> 32n <> line, Nil{} <> w, hs, {==})) : {Cmd.menu.cut(Cmd.cut(_), t) == Cmd.menu(t, List.append(&2, Nat, Command.cmd_render(x <> rest), 32n <> line)) : Cmd.Menu}
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(List.append(&2, Nat, Command.cmd_render(x <> rest), 32n <> line)), x <> List.append(&2, List<&2, Nat>, rest, w), LSp.sp_words_render(x, rest, 32n <> line, w, hs, {==})) : {Cmd.menu.cut(Cmd.cut(x <> List.append(&2, List<&2, Nat>, rest, Nil{} <> w)), t) == Cmd.menu.cut(Cmd.cut(_), t) : Cmd.Menu}
      msg_gap(w, x, rest, t, k, o, LSp.sp_words_ne(line))
