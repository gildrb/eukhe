# eukhe: the laws of area command, section whole: the model's answers
# (resolve, menu, key) for every table, every line, every selection and
# every key are the spec's (bend/command.bend)

import Base
import ../../bend/command.bend as Cmd
import ./paths.bend as Paths
import ./named.bend as Named

# LAWS: the laws of laws/command/paths.bend and named.bend pin the model
# on well-formed tables (lowercase names) and on lines of given shapes; the
# entry (laws/command/entry.bend) answers the model. These pin each answer
# of the model, for every input the entry can carry, to a spec built from
# the spec helpers of paths.bend and named.bend:
#
#   R21 a line's words are the spaceless words it renders (split at every
#       space, an empty word between two spaces)   command_words_exact
#   R22 a line resolves by walking its words from the root: an empty word
#       is skipped, except in argument text, which keeps it; a word names
#       a child of the path walked (cmd_named: its name in lowercase, else
#       an alias) and walks into it; a word naming none starts the
#       argument text of a path that takes text, else it is unknown below
#       that path; a first word naming no command is no command. A walk
#       that ends at an entry runs it when it has a default or no child,
#       else its menu opens; argument text runs its path with the words
#       after it, as typed                    command_resolve_spec
#   R23 the menu of a line: the command names while its first word is
#       typed; after more words, the children of the path the words before
#       the last walk to whose name or alias starts with the last word (any
#       case), else none                       command_menu_spec
#   R24 Tab and Enter: on a line whose words before the last walk to a
#       path (or the root), a selected child of it is the row (Tab
#       completes it, Enter as on a row), any other selection acts as no
#       row; anywhere else as no row            command_key_spec
#   anchor                                     command_whole_example

# Spec helpers
# ------------

# the entry's own path
def cmd_sp_path(e: Cmd.Ent) -> List<&2, List<&2, Nat>>:
  match e:
    case Cmd.Ent{p, a, r, f, g}:
      p

# the entry takes argument text
def cmd_sp_free(e: Cmd.Ent) -> Bool:
  match e:
    case Cmd.Ent{p, a, r, f, g}:
      f

# the first word, looked up at the root: the entry it names, else a stray
def cmd_sp_top(m: Maybe<&2, Cmd.Ent>) -> Cmd.St:
  match m:
    case Some{+e}:
      Cmd.Walk{cmd_sp_path(e), e}
    case None{}:
      Cmd.Stray{}

# a word below the path q (whose entry takes text when free): the child
# it names, else the start of the argument text, else an unknown word
def cmd_sp_next(m: Maybe<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, free: Bool, w: List<&2, Nat>) -> Cmd.St:
  match m:
    case Some{+e}:
      Cmd.Walk{cmd_sp_path(e), e}
    case None{}:
      match free:
        case True{}:
          Cmd.Rest{q, [w]}
        case False{}:
          Cmd.Lost{q, w}

# one typed word (not empty)
def cmd_sp_word(s: Cmd.St, +t: List<&2, Cmd.Ent>, +w: List<&2, Nat>) -> Cmd.St:
  match s:
    case Cmd.Top{}:
      cmd_sp_top(Named.cmd_named(t, Nil{}, w))
    case Cmd.Walk{+q, e}:
      cmd_sp_next(Named.cmd_named(t, q, w), q, cmd_sp_free(e), w)
    case Cmd.Rest{q, ws}:
      Cmd.Rest{q, List.append(&2, List<&2, Nat>, ws, [w])}
    case Cmd.Lost{q, x}:
      Cmd.Lost{q, x}
    case Cmd.Stray{}:
      Cmd.Stray{}

# an empty word: argument text keeps it, anything else skips it
def cmd_sp_gap(s: Cmd.St) -> Cmd.St:
  match s:
    case Cmd.Top{}:
      Cmd.Top{}
    case Cmd.Walk{q, e}:
      Cmd.Walk{q, e}
    case Cmd.Rest{q, ws}:
      Cmd.Rest{q, List.append(&2, List<&2, Nat>, ws, [Nil{}])}
    case Cmd.Lost{q, x}:
      Cmd.Lost{q, x}
    case Cmd.Stray{}:
      Cmd.Stray{}

def cmd_sp_step(s: Cmd.St, +t: List<&2, Cmd.Ent>, w: List<&2, Nat>) -> Cmd.St:
  match w:
    case Nil{}:
      cmd_sp_gap(s)
    case Con{c, r}:
      cmd_sp_word(s, t, c <> r)

# the state after the words ws, from s
def cmd_sp_walk(ws: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, s: Cmd.St) -> Cmd.St:
  match ws:
    case Nil{}:
      s
    case Con{w, rest}:
      cmd_sp_walk(rest, t, cmd_sp_step(s, t, w))

# what a walk that ends in s does
def cmd_sp_finish(s: Cmd.St, +t: List<&2, Cmd.Ent>) -> Cmd.Res:
  match s:
    case Cmd.Top{}:
      Cmd.NoCmd{}
    case Cmd.Walk{q, e}:
      match e:
        case Cmd.Ent{+p, a, r, f, g}:
          Paths.cmd_ended.at(Bool.or(r, Bool.not(Paths.cmd_has_kid(t, p))), q)
    case Cmd.Rest{q, ws}:
      Cmd.Runs{q, Paths.cmd_render(ws)}
    case Cmd.Lost{q, w}:
      Cmd.Unknown{q, w}
    case Cmd.Stray{}:
      Cmd.NoCmd{}

# R22: what a submitted line does
def cmd_sp_resolve(+t: List<&2, Cmd.Ent>, line: List<&2, Nat>) -> Cmd.Res:
  cmd_sp_finish(cmd_sp_walk(Cmd.words(line), t, Cmd.Top{}), t)

def cmd_sp_menu.at(s: Cmd.St, +t: List<&2, Cmd.Ent>, p: List<&2, Nat>) -> Cmd.Menu:
  match s:
    case Cmd.Top{}:
      Cmd.Shut{}
    case Cmd.Walk{+q, e}:
      Cmd.Kids{q, Paths.cmd_rows(t, 0n, q, Paths.cmd_lower(p))}
    case Cmd.Rest{q, ws}:
      Cmd.Shut{}
    case Cmd.Lost{q, w}:
      Cmd.Shut{}
    case Cmd.Stray{}:
      Cmd.Shut{}

# d: the words before the last, p: the last word
def cmd_sp_menu.go(d: List<&2, List<&2, Nat>>, p: List<&2, Nat>, +t: List<&2, Cmd.Ent>) -> Cmd.Menu:
  match d:
    case Nil{}:
      Cmd.Names{}
    case Con{w, rest}:
      cmd_sp_menu.at(cmd_sp_walk(w <> rest, t, Cmd.Top{}), t, p)

# R23: the menu of a typed line
def cmd_sp_menu(+t: List<&2, Cmd.Ent>, line: List<&2, Nat>) -> Cmd.Menu:
  +ws = Cmd.words(line)
  cmd_sp_menu.go(Paths.cmd_init(ws), Paths.cmd_last(ws), t)

def cmd_sp_key.at(s: Cmd.St, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press) -> Cmd.Out:
  match s:
    case Cmd.Top{}:
      Named.cmd_key_at(t, Nil{}, line, p, sel, k)
    case Cmd.Walk{q, e}:
      Named.cmd_key_at(t, q, line, p, sel, k)
    case Cmd.Rest{q, ws}:
      Named.cmd_key_bare(t, line, k)
    case Cmd.Lost{q, w}:
      Named.cmd_key_bare(t, line, k)
    case Cmd.Stray{}:
      Named.cmd_key_bare(t, line, k)

# R24: what Tab or Enter does to a typed line (cmd_key_at and cmd_key_bare
# read Cmd.resolve for Enter with no row: command_resolve_spec pins it)
def cmd_sp_key(+t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press) -> Cmd.Out:
  +ws = Cmd.words(line)
  cmd_sp_key.at(cmd_sp_walk(Paths.cmd_init(ws), t, Cmd.Top{}), t, line, Paths.cmd_last(ws), sel, k)

# Laws
# ----

# LAW command_words_exact (R21): the words of every line are spaceless,
# never none, and rendered with one space between two words they give the
# line back (one list of words does that)
# EXCLUDES: a word split elsewhere than at a space (a space kept in a
#   word, two spaces read as one, a word dropped or repeated), which every
#   spec below reads through Cmd.words
law command_words_exact:
  for +line: List<&2, Nat>
  {(Paths.cmd_render(Cmd.words(line)), (Paths.cmd_all_spaceless(Cmd.words(line)), List.is_empty(&2, List<&2, Nat>, Cmd.words(line)))) == (line, (True{}, False{})) : List<&2, Nat> & (Bool & Bool)}

# LAW command_resolve_spec (R22): every line resolves, in every table, as
# the spec's walk of its words says
# EXCLUDES: any table the earlier laws leave free (names in capitals, a
#   name with a space, an empty name, a path declared twice, an alias on a
#   path that is no child) answered other than the spec's walk; a lookup
#   other than cmd_named, an end other than cmd_ended.at, argument text
#   other than the words as typed
law command_resolve_spec:
  for +t: List<&2, Cmd.Ent>
  for +line: List<&2, Nat>
  {Cmd.resolve(t, line) == cmd_sp_resolve(t, line) : Cmd.Res}

# LAW command_menu_spec (R23): the menu of every line, in every table, is
# the spec's
# EXCLUDES: a menu other than the children rows cmd_rows lists for the
#   walked path (another path's rows, a row out of table order, a row the
#   last word does not start), names after the first word, a children
#   menu below argument text, an unknown or a stray word
law command_menu_spec:
  for +t: List<&2, Cmd.Ent>
  for +line: List<&2, Nat>
  {Cmd.menu(t, line) == cmd_sp_menu(t, line) : Cmd.Menu}

# LAW command_key_spec (R24): Tab and Enter on every line, with every
# selection, in every table, act as the spec says
# EXCLUDES: a row honoured off the walked path, a row ignored on it, Tab or
#   Enter on a row that act otherwise than cmd_tab and cmd_enter, a key
#   with no row other than cmd_key_bare
law command_key_spec:
  for +t: List<&2, Cmd.Ent>
  for +line: List<&2, Nat>
  for +sel: Cmd.Sel
  for +k: Cmd.Press
  {Cmd.key(t, line, sel, k) == cmd_sp_key(t, line, sel, k) : Cmd.Out}

# LAW command_whole_example: anchor: in a table whose name is in capitals
# (MEM), neither `MEM` nor `mem` names it; `  ` then Enter submits; the
# words of `a  b ` are a, an empty word, b and an empty word
# EXCLUDES: a capitalized table name matched by lowercasing it too; a
#   blank line rewritten
law command_whole_example:
  {(Cmd.resolve([Cmd.Ent{[[77n, 69n, 77n]], [], True{}, False{}, False{}}], [77n, 69n, 77n]), (Cmd.resolve([Cmd.Ent{[[77n, 69n, 77n]], [], True{}, False{}, False{}}], [109n, 101n, 109n]), (Cmd.key([], [32n, 32n], Cmd.NoRow{}, Cmd.Enter{}), Cmd.words([97n, 32n, 32n, 98n, 32n])))) == (Cmd.NoCmd{}, (Cmd.NoCmd{}, (Cmd.Out{[32n, 32n], False{}, True{}}, [[97n], [], [98n], []]))) : Cmd.Res & (Cmd.Res & (Cmd.Out & List<&2, List<&2, Nat>>))}
