# eukhe: the proof of LAW command_answers_declared_path
#
# PROOF of LAW command_answers_declared_path: an invariant of the walk:
# every walk state names a declared path, or none (dp_st). The root and a
# stray word name none; a word that names a child steps onto the entry the
# search finds, whose path the table declares (the search is cmd_named:
# LANamed.nm_search, LANamed.nm_named_decl); a word that names none stays
# at the path walked (argument text, an unknown word), and so do empty
# words and every word after (dp_step, dp_walk). The answer of a walk
# names the path of its last state (dp_fin).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ../../laws/command/whole.bend as CommandWhole
import ./base.bend as LA
import ./base/named.bend as LANamed

# the path a walk state names is declared (the root and a stray word name
# none)
def dp_st(+t: List<&2, Cmd.Ent>, s: Cmd.St) -> Bool:
  match s:
    case Cmd.Top{}:
      True{}
    case Cmd.Walk{q, e}:
      Command.cmd_declared(t, q)
    case Cmd.Rest{q, ws}:
      Command.cmd_declared(t, q)
    case Cmd.Lost{q, w}:
      Command.cmd_declared(t, q)
    case Cmd.Stray{}:
      True{}

# m is none, or an entry whose path t declares
def dp_m(+t: List<&2, Cmd.Ent>, m: Maybe<&2, Cmd.Ent>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{e}:
      Command.cmd_declared(t, Cmd.Ent.path(e))

def dp_named_at(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, hm: {CommandNamed.cmd_named(t, q, w) == m : Maybe<&2, Cmd.Ent>}) -> {dp_m(t, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+e}:
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.Ent.path(e), Command.cmd_ent_path(e), LA.cb_ent_path(e)) : {Command.cmd_declared(t, _) == True{} : Bool}
      LANamed.nm_named_decl(t, q, w, e, hm)

# the entry the search finds is declared
def dp_search(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>) -> {dp_m(t, Cmd.search(t, q, Cmd.lows(w))) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.search(t, q, Cmd.lows(w)), CommandNamed.cmd_named(t, q, w), LANamed.nm_search(t, q, w)) : {dp_m(t, _) == True{} : Bool}
  dp_named_at(CommandNamed.cmd_named(t, q, w), t, q, w, {==})

def dp_top(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, h: {dp_m(t, m) == True{} : Bool}) -> {dp_st(t, Cmd.step.top(m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      h

def dp_walk_step(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, -q: List<&2, List<&2, Nat>>, f: Bool, -w: List<&2, Nat>, hm: {dp_m(t, m) == True{} : Bool}, hq: {Command.cmd_declared(t, q) == True{} : Bool}) -> {dp_st(t, Cmd.step.walk(m, q, f, w)) == True{} : Bool}:
  match m:
    case None{}:
      match f:
        case True{}:
          hq
        case False{}:
          hq
    case Some{e}:
      hm

# a step keeps the invariant
def dp_step(s: Cmd.St, +t: List<&2, Cmd.Ent>, w: List<&2, Nat>, h: {dp_st(t, s) == True{} : Bool}) -> {dp_st(t, Cmd.step(s, t, w)) == True{} : Bool}:
  match s:
    case Cmd.Top{}:
      match w:
        case Nil{}:
          {==}
        case Con{+c, +r}:
          dp_top(Cmd.search(t, Nil{}, Cmd.lows(c <> r)), t, dp_search(t, Nil{}, c <> r))
    case Cmd.Walk{+q, +e}:
      match w:
        case Nil{}:
          h
        case Con{+c, +r}:
          dp_walk_step(Cmd.search(t, q, Cmd.lows(c <> r)), t, q, Cmd.Ent.free(e), c <> r, dp_search(t, q, c <> r), h)
    case Cmd.Rest{q, ws}:
      match w:
        case Nil{}:
          h
        case Con{c, r}:
          h
    case Cmd.Lost{q, x}:
      match w:
        case Nil{}:
          h
        case Con{c, r}:
          h
    case Cmd.Stray{}:
      match w:
        case Nil{}:
          {==}
        case Con{c, r}:
          {==}

# ... and so does a walk
def dp_walk(ws: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +s: Cmd.St, h: {dp_st(t, s) == True{} : Bool}) -> {dp_st(t, Cmd.walk(ws, t, s)) == True{} : Bool}:
  match ws:
    case Nil{}:
      h
    case Con{+w, rest}:
      dp_walk(rest, t, Cmd.step(s, t, w), dp_step(s, t, w, h))

def dp_fin_at(d: Bool, +t: List<&2, Cmd.Ent>, -q: List<&2, List<&2, Nat>>, h: {Command.cmd_declared(t, q) == True{} : Bool}) -> {CommandWhole.cmd_answer_declared(t, Cmd.finish.at(d, q)) == True{} : Bool}:
  match d:
    case True{}:
      h
    case False{}:
      h

# the answer of a walk names the path of its last state
def dp_fin(s: Cmd.St, +t: List<&2, Cmd.Ent>, h: {dp_st(t, s) == True{} : Bool}) -> {CommandWhole.cmd_answer_declared(t, Cmd.finish(s, t)) == True{} : Bool}:
  match s:
    case Cmd.Top{}:
      {==}
    case Cmd.Walk{q, +e}:
      dp_fin_at(Cmd.done(t, e), t, q, h)
    case Cmd.Rest{q, ws}:
      h
    case Cmd.Lost{q, w}:
      h
    case Cmd.Stray{}:
      {==}

def CommandWhole.command_answers_declared_path(t, line):
  dp_fin(Cmd.walk(Cmd.words(line), t, Cmd.Top{}), t, dp_walk(Cmd.words(line), t, Cmd.Top{}, {==}))
