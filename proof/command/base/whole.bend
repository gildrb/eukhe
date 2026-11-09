# eukhe: lemmas of area command: the model's walk, resolve, menu and key
# are the spec's of laws/command/whole.bend, step by step

import Base
import ../../../bend/command.bend as Cmd
import ../../../laws/command/paths.bend as Command
import ../../../laws/command/named.bend as CommandNamed
import ../../../laws/command/whole.bend as CommandWhole
import ../base.bend as LA
import ./named.bend as LANamed
import ../command_menu_lists_children.bend as PCommandMenuListsChildren

def pwh.top(m: Maybe<&2, Cmd.Ent>) -> {Cmd.step.top(m) == CommandWhole.cmd_sp_top(m) : Cmd.St}:
  match m:
    case Some{e}:
      match e:
        case Cmd.Ent{p, a, r, f, g}:
          {==}
    case None{}:
      {==}

def pwh.next(m: Maybe<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, free: Bool, w: List<&2, Nat>) -> {Cmd.step.walk(m, q, free, w) == CommandWhole.cmd_sp_next(m, q, free, w) : Cmd.St}:
  match m:
    case Some{e}:
      match e:
        case Cmd.Ent{p, a, r, f, g}:
          {==}
    case None{}:
      match free:
        case True{}:
          {==}
        case False{}:
          {==}

def pwh.free(e: Cmd.Ent) -> {Cmd.Ent.free(e) == CommandWhole.cmd_sp_free(e) : Bool}:
  match e:
    case Cmd.Ent{p, a, r, f, g}:
      {==}

def pwh.word(s: Cmd.St, +t: List<&2, Cmd.Ent>, +w: List<&2, Nat>) -> {Cmd.step.word(s, t, w) == CommandWhole.cmd_sp_word(s, t, w) : Cmd.St}:
  match s:
    case Cmd.Top{}:
      %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.search(t, Nil{}, Cmd.lows(w)), CommandNamed.cmd_named(t, Nil{}, w), LANamed.nm_search(t, Nil{}, w)) : {Cmd.step.top(_) == CommandWhole.cmd_sp_top(CommandNamed.cmd_named(t, Nil{}, w)) : Cmd.St}
      pwh.top(CommandNamed.cmd_named(t, Nil{}, w))
    case Cmd.Walk{+q, +e}:
      %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.search(t, q, Cmd.lows(w)), CommandNamed.cmd_named(t, q, w), LANamed.nm_search(t, q, w)) : {Cmd.step.walk(_, q, Cmd.Ent.free(e), w) == CommandWhole.cmd_sp_next(CommandNamed.cmd_named(t, q, w), q, CommandWhole.cmd_sp_free(e), w) : Cmd.St}
      %Equal.sym(Bool, Cmd.Ent.free(e), CommandWhole.cmd_sp_free(e), pwh.free(e)) : {Cmd.step.walk(CommandNamed.cmd_named(t, q, w), q, _, w) == CommandWhole.cmd_sp_next(CommandNamed.cmd_named(t, q, w), q, CommandWhole.cmd_sp_free(e), w) : Cmd.St}
      pwh.next(CommandNamed.cmd_named(t, q, w), q, CommandWhole.cmd_sp_free(e), w)
    case Cmd.Rest{q, ws}:
      {==}
    case Cmd.OffPath{q, x}:
      {==}
    case Cmd.Stray{}:
      {==}

def pwh.gap(s: Cmd.St) -> {Cmd.step.empty(s) == CommandWhole.cmd_sp_gap(s) : Cmd.St}:
  match s:
    case Cmd.Top{}:
      {==}
    case Cmd.Walk{q, e}:
      {==}
    case Cmd.Rest{q, ws}:
      {==}
    case Cmd.OffPath{q, x}:
      {==}
    case Cmd.Stray{}:
      {==}

def pwh.step(s: Cmd.St, +t: List<&2, Cmd.Ent>, w: List<&2, Nat>) -> {Cmd.step(s, t, w) == CommandWhole.cmd_sp_step(s, t, w) : Cmd.St}:
  match w:
    case Nil{}:
      pwh.gap(s)
    case Con{+c, +r}:
      pwh.word(s, t, c <> r)

# the model's walk is the spec's
def pwh.walk(ws: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +s: Cmd.St) -> {Cmd.walk(ws, t, s) == CommandWhole.cmd_sp_walk(ws, t, s) : Cmd.St}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, rest}:
      %Equal.sym(Cmd.St, Cmd.step(s, t, w), CommandWhole.cmd_sp_step(s, t, w), pwh.step(s, t, w)) : {Cmd.walk(rest, t, _) == CommandWhole.cmd_sp_walk(rest, t, CommandWhole.cmd_sp_step(s, t, w)) : Cmd.St}
      pwh.walk(rest, t, CommandWhole.cmd_sp_step(s, t, w))

def pwh.fin_at(b: Bool, q: List<&2, List<&2, Nat>>) -> {Cmd.finish.at(b, q) == Command.cmd_ended.at(b, q) : Cmd.Res}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pwh.finish(s: Cmd.St, +t: List<&2, Cmd.Ent>) -> {Cmd.finish(s, t) == CommandWhole.cmd_sp_finish(s, t) : Cmd.Res}:
  match s:
    case Cmd.Top{}:
      {==}
    case Cmd.Walk{+q, e}:
      match e:
        case Cmd.Ent{+p, a, +r, f, g}:
          %Equal.sym(Bool, Cmd.kids.any(t, p), Command.cmd_has_kid(t, p), LA.cb_kids_any(t, p)) : {Cmd.finish.at(Bool.or(r, Bool.not(_)), q) == Command.cmd_ended.at(Bool.or(r, Bool.not(Command.cmd_has_kid(t, p))), q) : Cmd.Res}
          pwh.fin_at(Bool.or(r, Bool.not(Command.cmd_has_kid(t, p))), q)
    case Cmd.Rest{+q, +ws}:
      Equal.cong(List<&2, Nat>, Cmd.Res, z => Cmd.Runs{q, z}, Cmd.join(ws), Command.cmd_render(ws), LA.cb_join(ws))
    case Cmd.OffPath{q, w}:
      {==}
    case Cmd.Stray{}:
      {==}

# the model's resolve is the spec's
def pwh.resolve(+t: List<&2, Cmd.Ent>, +line: List<&2, Nat>) -> {Cmd.resolve(t, line) == CommandWhole.cmd_sp_resolve(t, line) : Cmd.Res}:
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(line), t, Cmd.Top{}), CommandWhole.cmd_sp_walk(Cmd.words(line), t, Cmd.Top{}), pwh.walk(Cmd.words(line), t, Cmd.Top{})) : {Cmd.finish(_, t) == CommandWhole.cmd_sp_finish(CommandWhole.cmd_sp_walk(Cmd.words(line), t, Cmd.Top{}), t) : Cmd.Res}
  pwh.finish(CommandWhole.cmd_sp_walk(Cmd.words(line), t, Cmd.Top{}), t)

# the model's cut is the words before the last, and the last
def pwh.cut_go(zs: List<&2, List<&2, Nat>>, +z: List<&2, Nat>) -> {Cmd.cut.go(zs, z) == (Command.cmd_init.go(zs, z), Command.cmd_last.go(zs, z)) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  match zs:
    case Nil{}:
      {==}
    case Con{+y, +more}:
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut.go(more, y), (Command.cmd_init.go(more, y), Command.cmd_last.go(more, y)), pwh.cut_go(more, y)) : {Cmd.cut.cons(z, _) == (z <> Command.cmd_init.go(more, y), Command.cmd_last.go(more, y)) : List<&2, List<&2, Nat>> & List<&2, Nat>}
      {==}

def pwh.cut(ws: List<&2, List<&2, Nat>>) -> {Cmd.cut(ws) == (Command.cmd_init(ws), Command.cmd_last(ws)) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+z, +zs}:
      pwh.cut_go(zs, z)

def pwh.menu_at(s: Cmd.St, +t: List<&2, Cmd.Ent>, +p: List<&2, Nat>) -> {Cmd.menu.at(s, t, p) == CommandWhole.cmd_sp_menu.at(s, t, p) : Cmd.Menu}:
  match s:
    case Cmd.Top{}:
      {==}
    case Cmd.Walk{+q, e}:
      %Equal.sym(List<&2, Nat>, Cmd.lows(p), Command.cmd_lower(p), LA.cb_lows(p)) : {Cmd.Kids{q, Cmd.items(t, 0n, q, _)} == Cmd.Kids{q, Command.cmd_rows(t, 0n, q, Command.cmd_lower(p))} : Cmd.Menu}
      %Equal.sym(List<&2, Nat>, Cmd.items(t, 0n, q, Command.cmd_lower(p)), Command.cmd_rows(t, 0n, q, Command.cmd_lower(p)), PCommandMenuListsChildren.cb_items(t, 0n, q, Command.cmd_lower(p))) : {Cmd.Kids{q, _} == Cmd.Kids{q, Command.cmd_rows(t, 0n, q, Command.cmd_lower(p))} : Cmd.Menu}
      {==}
    case Cmd.Rest{q, ws}:
      {==}
    case Cmd.OffPath{q, w}:
      {==}
    case Cmd.Stray{}:
      {==}

def pwh.menu_go(d: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +t: List<&2, Cmd.Ent>) -> {Cmd.menu.go(d, p, t) == CommandWhole.cmd_sp_menu.go(d, p, t) : Cmd.Menu}:
  match d:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      %Equal.sym(Cmd.St, Cmd.walk(w <> rest, t, Cmd.Top{}), CommandWhole.cmd_sp_walk(w <> rest, t, Cmd.Top{}), pwh.walk(w <> rest, t, Cmd.Top{})) : {Cmd.menu.at(_, t, p) == CommandWhole.cmd_sp_menu.at(CommandWhole.cmd_sp_walk(w <> rest, t, Cmd.Top{}), t, p) : Cmd.Menu}
      pwh.menu_at(CommandWhole.cmd_sp_walk(w <> rest, t, Cmd.Top{}), t, p)

# the model's menu is the spec's
def pwh.menu(+t: List<&2, Cmd.Ent>, +line: List<&2, Nat>) -> {Cmd.menu(t, line) == CommandWhole.cmd_sp_menu(t, line) : Cmd.Menu}:
  +W = Cmd.words(line)
  %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(W), (Command.cmd_init(W), Command.cmd_last(W)), pwh.cut(W)) : {Cmd.menu.cut(_, t) == CommandWhole.cmd_sp_menu.go(Command.cmd_init(W), Command.cmd_last(W), t) : Cmd.Menu}
  pwh.menu_go(Command.cmd_init(W), Command.cmd_last(W), t)

def pwh.key_at(s: Cmd.St, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, +p: List<&2, Nat>, +sel: Cmd.Sel, +k: Cmd.Press) -> {Cmd.key.at(s, t, line, p, sel, k) == CommandWhole.cmd_sp_key.at(s, t, line, p, sel, k) : Cmd.Out}:
  match s:
    case Cmd.Top{}:
      LANamed.nm_key_row(sel, t, Nil{}, line, p, k)
    case Cmd.Walk{+q, e}:
      LANamed.nm_key_row(sel, t, q, line, p, k)
    case Cmd.Rest{q, ws}:
      LANamed.nm_bare(k, t, line)
    case Cmd.OffPath{q, w}:
      LANamed.nm_bare(k, t, line)
    case Cmd.Stray{}:
      LANamed.nm_bare(k, t, line)

# the model's key is the spec's
def pwh.key(+t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, +sel: Cmd.Sel, +k: Cmd.Press) -> {Cmd.key(t, line, sel, k) == CommandWhole.cmd_sp_key(t, line, sel, k) : Cmd.Out}:
  +W = Cmd.words(line)
  %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(W), (Command.cmd_init(W), Command.cmd_last(W)), pwh.cut(W)) : {Cmd.key.cut(_, t, line, sel, k) == CommandWhole.cmd_sp_key(t, line, sel, k) : Cmd.Out}
  %Equal.sym(Cmd.St, Cmd.walk(Command.cmd_init(W), t, Cmd.Top{}), CommandWhole.cmd_sp_walk(Command.cmd_init(W), t, Cmd.Top{}), pwh.walk(Command.cmd_init(W), t, Cmd.Top{})) : {Cmd.key.at(_, t, line, Command.cmd_last(W), sel, k) == CommandWhole.cmd_sp_key(t, line, sel, k) : Cmd.Out}
  pwh.key_at(CommandWhole.cmd_sp_walk(Command.cmd_init(W), t, Cmd.Top{}), t, line, Command.cmd_last(W), sel, k)
