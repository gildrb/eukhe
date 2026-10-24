# eukhe: the laws of area command, section named: a path typed by any of
# its spellings (names in any case, aliases, any spacing), and the keys on
# the path a menu lists (bend/command.bend)

import Base
import ../../bend/command.bend as Cmd
import ./paths.bend as Paths

# LAWS: the laws of laws/command/paths.bend type each path by its
# canonical names; these carry them to every spelling of a path, and pin
# Tab and Enter on every line by the menu it shows.
#
#   R17 a word that names a child of a typed path by its name in any case,
#       or by an alias, walks into that child: the line resolves, and its
#       menu shows, as with the child's canonical name in its place, the
#       spacing and whatever follows kept
#                                     command_named_word_resolves,
#                                     command_named_word_menu
#       in every table (a table may declare a path twice): a line that
#       ends at the word answers as its own entry; the menu after it is
#       the canonical one; the text after it resolves as after the
#       canonical name when the path's entries run and take text alike
#                                     command_named_word_ends,
#                                     command_named_word_menu_any,
#                                     command_named_word_resolves_alike
#   R18 on a line whose menu lists the children of a path, Tab and Enter
#       act on that path: a selected child is the row, any other selection
#       acts as no row             command_key_follows_menu
#   R19 on a line whose menu is shut after a typed word (argument text, an
#       unknown word, a stray first word), a selection is ignored
#                                     command_row_ignored_shut_menu
#   R20 an empty or blank line is no command
#                                     command_blank_runs_nothing
#   anchors and witnesses             command_named_example,
#                                     command_named_dup_example,
#                                     command_named_premises_witness
#
# Not pinned: a table that declares one path twice with different run or
# free flags, and a word naming the later entry followed by more text:
# the model then answers by the named entry's own flags.

# Spec helpers
# ------------

# e is a child of q with the alias x
def cmd_alias_hit(+q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, e: Cmd.Ent) -> Bool:
  match e:
    case Cmd.Ent{p, a, r, f, g}:
      Bool.and(Paths.cmd_is_kid(q, p), Paths.cmd_in(x, a))

# the first child of q in t with the alias x
def cmd_alias_ent(t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> Maybe<&2, Cmd.Ent>:
  match t:
    case Nil{}:
      None{}
    case Con{+e, rest}:
      Paths.cmd_first.at(cmd_alias_hit(q, x, e), e, cmd_alias_ent(rest, q, x))

def cmd_named.at(m: Maybe<&2, Cmd.Ent>, t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> Maybe<&2, Cmd.Ent>:
  match m:
    case None{}:
      cmd_alias_ent(t, q, x)
    case Some{e}:
      Some{e}

# the entry of the child of q a typed word w names: the first entry of
# q and w in lowercase, else the first child of q with that alias
def cmd_named(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, w: List<&2, Nat>) -> Maybe<&2, Cmd.Ent>:
  +x = Paths.cmd_lower(w)
  cmd_named.at(Paths.cmd_lookup(t, List.append(&2, List<&2, Nat>, q, [x])), t, q, x)

# the answer of a line that ends at the path of the entry e: e runs when
# it has a default or no child, else its menu opens
def cmd_ent_ended(+t: List<&2, Cmd.Ent>, e: Cmd.Ent) -> Cmd.Res:
  match e:
    case Cmd.Ent{+p, a, r, f, g}:
      Paths.cmd_ended.at(Bool.or(r, Bool.not(Paths.cmd_has_kid(t, p))), p)

# two flags are the same
def cmd_flag_eq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}
    case False{} False{}:
      True{}

# a and b run bare alike and take text alike
def cmd_alike(a: Cmd.Ent, b: Cmd.Ent) -> Bool:
  match a b:
    case Cmd.Ent{p, x, r, f, g} Cmd.Ent{p2, x2, r2, f2, g2}:
      Bool.and(cmd_flag_eq(r, r2), cmd_flag_eq(f, f2))

# s is empty or starts with a space: the words before it stay whole
def cmd_cuts(s: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{c, r}:
      Nat.is_eq(c, 32n)

# every char of s is a space
def cmd_blank(s: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{+c, r}:
      Bool.and(Nat.is_eq(c, 32n), cmd_blank(r))

# Tab or Enter with no row: Tab keeps the line and opens its menu; Enter
# as command_enter_without_row
def cmd_key_bare(+t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, k: Cmd.Press) -> Cmd.Out:
  match k:
    case Cmd.Tab{}:
      Cmd.Out{line, True{}, False{}}
    case Cmd.Enter{}:
      Paths.cmd_enter_bare(Cmd.resolve(t, line), line)

# a selected entry c: the row when it is a child (b) of the path
def cmd_key_kid(b: Bool, c: Cmd.Ent, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, p: List<&2, Nat>, k: Cmd.Press) -> Cmd.Out:
  match b:
    case True{}:
      match k:
        case Cmd.Tab{}:
          Paths.cmd_tab(t, c)
        case Cmd.Enter{}:
          Paths.cmd_enter(t, c, p, line)
    case False{}:
      cmd_key_bare(t, line, k)

def cmd_key_row(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +line: List<&2, Nat>, p: List<&2, Nat>, k: Cmd.Press) -> Cmd.Out:
  match m:
    case None{}:
      cmd_key_bare(t, line, k)
    case Some{+c}:
      cmd_key_kid(Paths.cmd_is_kid(q, Paths.cmd_ent_path(c)), c, t, line, p, k)

# what Tab or Enter does on the line, its last word p typed below the path
# q: the selected place, when it holds a child of q, is the row (Tab
# completes it, Enter as on a row); any other selection acts as no row
def cmd_key_at(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +line: List<&2, Nat>, p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press) -> Cmd.Out:
  match sel:
    case Cmd.NoRow{}:
      cmd_key_bare(t, line, k)
    case Cmd.Row{i}:
      cmd_key_row(List.get(&2, Cmd.Ent, t, i), t, q, line, p, k)

# the example table with an alias: /memory (a default; view, model with
# the alias m) and /goal (text)
def cmd_example_alias_table() -> List<&2, Cmd.Ent>:
  [Cmd.Ent{[Paths.cmd_example_memory()], [], True{}, False{}, False{}}, Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_view()], [], True{}, True{}, False{}}, Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_model()], [[109n]], True{}, True{}, False{}}, Cmd.Ent{[Paths.cmd_example_goal()], [], True{}, True{}, True{}}]

# Laws: named words
# -----------------

# LAW command_named_word_resolves: below a walked path q, a word that names
# a child by its name in any case or by an alias resolves as the child's
# canonical path, whatever spacing the line has and whatever follows
# (repeated, every spelling of a path resolves as its canonical names)
# EXCLUDES: an alias ignored (`/memory m`, m an alias of model, answered
#   unknown or run as /memory), a name typed in capitals read as unknown,
#   an alias that walks into another child, a spelling that changes the
#   argument text after it
law command_named_word_resolves:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +w: List<&2, Nat>
  for +e: Cmd.Ent
  for +gs: List<&2, Nat>
  for +s: List<&2, Nat>
  for ok: {Paths.cmd_wf(t) == True{} : Bool}
  for on: {Paths.cmd_walks(t, q) == True{} : Bool}
  for word: {Paths.cmd_typed(w) == True{} : Bool}
  for hit: {cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}
  for first: {Paths.cmd_lookup(t, Paths.cmd_ent_path(e)) == Some{e} : Maybe<&2, Cmd.Ent>}
  for gap: {cmd_cuts(s) == True{} : Bool}
  {Cmd.resolve(t, List.append(&2, Nat, Paths.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), s)) == Cmd.resolve(t, List.append(&2, Nat, Paths.cmd_loose(Paths.cmd_ent_path(e), gs), s)) : Cmd.Res}

# LAW command_named_word_menu: below a walked path q, a word that names a
# child by its name in any case or by an alias, then a space, shows the
# menu its canonical name shows, whatever spacing and whatever follows
# EXCLUDES: `/memory m ` (m an alias of model) that hides model's children
#   or shows memory's, a capitalized name that shuts the menu
law command_named_word_menu:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +w: List<&2, Nat>
  for +e: Cmd.Ent
  for +gs: List<&2, Nat>
  for +s: List<&2, Nat>
  for ok: {Paths.cmd_wf(t) == True{} : Bool}
  for on: {Paths.cmd_walks(t, q) == True{} : Bool}
  for word: {Paths.cmd_typed(w) == True{} : Bool}
  for hit: {cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}
  for first: {Paths.cmd_lookup(t, Paths.cmd_ent_path(e)) == Some{e} : Maybe<&2, Cmd.Ent>}
  {Cmd.menu(t, List.append(&2, Nat, Paths.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> s)) == Cmd.menu(t, List.append(&2, Nat, Paths.cmd_loose(Paths.cmd_ent_path(e), gs), 32n <> s)) : Cmd.Menu}

# LAW command_blank_runs_nothing: an empty line, or one of spaces only, is
# no command: nothing runs
# EXCLUDES: `/` (or `/` and spaces) then Enter that runs the first command
#   of the table, a default, or opens a menu of paths
law command_blank_runs_nothing:
  for +t: List<&2, Cmd.Ent>
  for +line: List<&2, Nat>
  for blank: {cmd_blank(line) == True{} : Bool}
  {Cmd.resolve(t, line) == Cmd.NoCmd{} : Cmd.Res}

# LAW command_named_word_ends: below a walked path q, a line that ends at
# a word naming a child (its name in any case, or an alias) answers as
# that child's own entry: it runs when the entry has a default or no
# child, else its menu opens; in every table, also one that declares a
# path twice
# EXCLUDES: an alias ignored on an entry that repeats a declared path
#   (`/memory m` answered unknown), an alias that runs the parent
law command_named_word_ends:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +w: List<&2, Nat>
  for +e: Cmd.Ent
  for +gs: List<&2, Nat>
  for ok: {Paths.cmd_wf(t) == True{} : Bool}
  for on: {Paths.cmd_walks(t, q) == True{} : Bool}
  for word: {Paths.cmd_typed(w) == True{} : Bool}
  for hit: {cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}
  {Cmd.resolve(t, Paths.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs)) == cmd_ent_ended(t, e) : Cmd.Res}

# LAW command_named_word_menu_any: command_named_word_menu in every
# table: after a word that names a child and a space, the menu is the one
# the child's canonical name shows, also when the table declares that
# path twice
# EXCLUDES: an alias whose menu shuts or lists another path's children
#   when its entry repeats a declared path
law command_named_word_menu_any:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +w: List<&2, Nat>
  for +e: Cmd.Ent
  for +gs: List<&2, Nat>
  for +s: List<&2, Nat>
  for ok: {Paths.cmd_wf(t) == True{} : Bool}
  for on: {Paths.cmd_walks(t, q) == True{} : Bool}
  for word: {Paths.cmd_typed(w) == True{} : Bool}
  for hit: {cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}
  {Cmd.menu(t, List.append(&2, Nat, Paths.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> s)) == Cmd.menu(t, List.append(&2, Nat, Paths.cmd_loose(Paths.cmd_ent_path(e), gs), 32n <> s)) : Cmd.Menu}

# LAW command_named_word_resolves_alike: command_named_word_resolves when
# the table declares the child's path more than once, as long as the
# first entry of that path runs bare and takes text as the named one
# EXCLUDES: an alias ignored, or read as another path, before more words
#   when its entry repeats a declared path
law command_named_word_resolves_alike:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +w: List<&2, Nat>
  for +e: Cmd.Ent
  for +e1: Cmd.Ent
  for +gs: List<&2, Nat>
  for +s: List<&2, Nat>
  for ok: {Paths.cmd_wf(t) == True{} : Bool}
  for on: {Paths.cmd_walks(t, q) == True{} : Bool}
  for word: {Paths.cmd_typed(w) == True{} : Bool}
  for hit: {cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}
  for first: {Paths.cmd_lookup(t, Paths.cmd_ent_path(e)) == Some{e1} : Maybe<&2, Cmd.Ent>}
  for alike: {cmd_alike(e1, e) == True{} : Bool}
  for gap: {cmd_cuts(s) == True{} : Bool}
  {Cmd.resolve(t, List.append(&2, Nat, Paths.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), s)) == Cmd.resolve(t, List.append(&2, Nat, Paths.cmd_loose(Paths.cmd_ent_path(e), gs), s)) : Cmd.Res}

# Laws: keys on every line
# ------------------------

# LAW command_key_follows_menu: on a line whose last word p follows a
# space and whose menu lists the children of q (q typed by any spelling),
# Tab and Enter act on q: a selected child of q is the row (Tab completes
# it, Enter as on a row typed p), any other selection acts as no row
# EXCLUDES: Tab or Enter on a row that act on another path than the menu
#   shows (an aliased or capitalized path whose row completes elsewhere,
#   is ignored, or runs the parent), a row honoured that the menu does
#   not list
law command_key_follows_menu:
  for +t: List<&2, Cmd.Ent>
  for +pre: List<&2, Nat>
  for +p: List<&2, Nat>
  for +q: List<&2, List<&2, Nat>>
  for +xs: List<&2, Nat>
  for +sel: Cmd.Sel
  for +k: Cmd.Press
  for word: {Paths.cmd_spaceless(p) == True{} : Bool}
  for kids: {Cmd.menu(t, List.append(&2, Nat, pre, 32n <> p)) == Cmd.Kids{q, xs} : Cmd.Menu}
  {Cmd.key(t, List.append(&2, Nat, pre, 32n <> p), sel, k) == cmd_key_at(t, q, List.append(&2, Nat, pre, 32n <> p), p, sel, k) : Cmd.Out}

# LAW command_row_ignored_shut_menu: on a line whose menu is shut after a
# typed word (argument text, an unknown word, a stray first word, however
# the path before it is spelled), a selected place acts as no row
# EXCLUDES: a stale row that completes or submits a command after
#   `/memory m x` (m an alias), after argument text, or after a typo
law command_row_ignored_shut_menu:
  for +t: List<&2, Cmd.Ent>
  for +pre: List<&2, Nat>
  for +p: List<&2, Nat>
  for +i: Nat
  for +k: Cmd.Press
  for word: {Paths.cmd_spaceless(p) == True{} : Bool}
  for typed: {cmd_blank(pre) == False{} : Bool}
  for shut: {Cmd.menu(t, List.append(&2, Nat, pre, 32n <> p)) == Cmd.Shut{} : Cmd.Menu}
  {Cmd.key(t, List.append(&2, Nat, pre, 32n <> p), Cmd.Row{i}, k) == Cmd.key(t, List.append(&2, Nat, pre, 32n <> p), Cmd.NoRow{}, k) : Cmd.Out}

# LAW command_named_example: anchor: with m an alias of memory model,
# `memory m` and `MEMORY  M` run memory model, `memory m ` lists model's
# (no) children, and Enter on `memory m` submits it
law command_named_example:
  {(Cmd.resolve(cmd_example_alias_table(), List.append(&2, Nat, Paths.cmd_example_memory(), [32n, 109n])), (Cmd.resolve(cmd_example_alias_table(), [77n, 69n, 77n, 79n, 82n, 89n, 32n, 32n, 77n]), (Cmd.menu(cmd_example_alias_table(), List.append(&2, Nat, Paths.cmd_example_memory(), [32n, 109n, 32n])), Cmd.key(cmd_example_alias_table(), List.append(&2, Nat, Paths.cmd_example_memory(), [32n, 109n]), Cmd.NoRow{}, Cmd.Enter{})))) == (Cmd.Runs{[Paths.cmd_example_memory(), Paths.cmd_example_model()], Nil{}}, (Cmd.Runs{[Paths.cmd_example_memory(), Paths.cmd_example_model()], Nil{}}, (Cmd.Kids{[Paths.cmd_example_memory(), Paths.cmd_example_model()], Nil{}}, Cmd.Out{List.append(&2, Nat, Paths.cmd_example_memory(), [32n, 109n]), False{}, True{}}))) : Cmd.Res & (Cmd.Res & (Cmd.Menu & Cmd.Out))}

# LAW command_named_dup_example: anchor: in a table that declares memory
# model twice, the alias m only on the second entry, `memory m` runs
# memory model and `memory m ` lists model's (no) children
law command_named_dup_example:
  {(Cmd.resolve([Cmd.Ent{[Paths.cmd_example_memory()], [], True{}, False{}, False{}}, Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_model()], [], True{}, True{}, False{}}, Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_model()], [[109n]], True{}, True{}, False{}}], List.append(&2, Nat, Paths.cmd_example_memory(), [32n, 109n])), Cmd.menu([Cmd.Ent{[Paths.cmd_example_memory()], [], True{}, False{}, False{}}, Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_model()], [], True{}, True{}, False{}}, Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_model()], [[109n]], True{}, True{}, False{}}], List.append(&2, Nat, Paths.cmd_example_memory(), [32n, 109n, 32n]))) == (Cmd.Runs{[Paths.cmd_example_memory(), Paths.cmd_example_model()], Nil{}}, Cmd.Kids{[Paths.cmd_example_memory(), Paths.cmd_example_model()], Nil{}}) : Cmd.Res & Cmd.Menu}

# LAW command_named_premises_witness: witness: an alias names its child
# (the first entry of its path), a line with a typed word is not blank
# and one of spaces is,
# and lines with a menu of children and with a shut menu exist
# EXCLUDES: a vacuous law whose premises no table, word or line meets
law command_named_premises_witness:
  {(cmd_named(cmd_example_alias_table(), [Paths.cmd_example_memory()], [109n]), Paths.cmd_lookup(cmd_example_alias_table(), [Paths.cmd_example_memory(), Paths.cmd_example_model()])) == (Some{Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_model()], [[109n]], True{}, True{}, False{}}}, Some{Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_model()], [[109n]], True{}, True{}, False{}}}) : Maybe<&2, Cmd.Ent> & Maybe<&2, Cmd.Ent>} & {(Bool.and(Paths.cmd_wf(cmd_example_alias_table()), Bool.and(cmd_cuts(Nil{}), Bool.and(cmd_cuts([32n]), cmd_blank([32n, 32n])))), cmd_blank(Paths.cmd_example_goal())) == (True{}, False{}) : Bool & Bool} & {(Cmd.menu(cmd_example_alias_table(), List.append(&2, Nat, Paths.cmd_example_memory(), [32n])), Cmd.menu(cmd_example_alias_table(), List.append(&2, Nat, Paths.cmd_example_goal(), [32n, 120n, 32n]))) == (Cmd.Kids{[Paths.cmd_example_memory()], [1n, 2n]}, Cmd.Shut{}) : Cmd.Menu & Cmd.Menu}
