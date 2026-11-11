# eukhe: the laws of area command, section named: a path typed by any of
# its spellings (names in any case, aliases, any spacing), and the keys on
# the path a menu lists (bend/command.bend)

# LAWS: the laws of laws/command/paths.bend type each path by its
# canonical names; these carry them to every spelling of a path, and pin
# Tab and Enter on a selected row of every line by the path its menu
# shows.
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
#                                     command_named_word_resolves_alike,
#       and after the word, in every table: spaces only, a child of it,
#       or a word naming none of its children
#                                     command_named_word_then_blank,
#                                     command_named_word_then_child,
#                                     command_named_word_then_other
#   R18 on a line whose keys act below a path q (its last word is the
#       first word and q the root, or its menu lists q's children, any
#       spelling or spacing before the last word): a selected child of q
#       is the row, any other selection acts as no row; Tab completes the
#       row (R8), Enter on it as R9 says
#                                     command_tab_row_completes,
#                                     command_enter_row_typed_in_part,
#                                     command_enter_row_typed_in_full,
#                                     command_row_not_child_ignored
#   R19 on a line whose menu is shut after a typed word (argument text, an
#       unknown word, a stray first word), a selection is ignored
#                                     command_row_ignored_shut_menu
#   R20 an empty or blank line is no command
#                                     command_blank_runs_nothing
#   anchors and witnesses             command_named_example,
#                                     command_named_dup_example,
#                                     command_named_premises_witness,
#                                     command_keys_premises_witness

import Base
import ../../bend/command.bend as Cmd
import ./paths.bend as Paths

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

# after a named entry, a word x naming none of its children: when the
# entry takes text it runs with x and the rest as typed, else x is unknown
def cmd_named_miss.at(f: Bool, p: List<&2, List<&2, Nat>>, x: List<&2, Nat>, s: List<&2, Nat>) -> Cmd.Res:
  match f:
    case True{}:
      Cmd.Runs{p, List.append(&2, Nat, x, s)}
    case False{}:
      Cmd.Unknown{p, x}

def cmd_named_miss(e: Cmd.Ent, x: List<&2, Nat>, s: List<&2, Nat>) -> Cmd.Res:
  match e:
    case Cmd.Ent{p, a, r, f, g}:
      cmd_named_miss.at(f, p, x, s)

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

# The keys on a selected row
# --------------------------

# the last char of l is a space
def cmd_ends_space.go(rest: List<&2, Nat>, c: Nat) -> Bool:
  match rest:
    case Nil{}:
      Nat.is_eq(c, 32n)
    case Con{d, more}:
      cmd_ends_space.go(more, d)

def cmd_ends_space(l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{c, rest}:
      cmd_ends_space.go(rest, c)

def cmd_below.at(b: Bool, +t: List<&2, Cmd.Ent>, +pre: List<&2, Nat>, +p: List<&2, Nat>, +q: List<&2, List<&2, Nat>>) -> Bool:
  match b:
    case True{}:
      Paths.cmd_path_eq(q, Nil{})
    case False{}:
      Bool.and(cmd_ends_space(pre), Paths.cmd_lists_kids(Cmd.menu(t, List.append(&2, Nat, pre, p)), q))

# the keys of the line pre ++ p, p its last word, act below the path q:
# nothing but spaces comes before p and q is the root, or pre ends in a
# space and the menu of the line lists children of q
def cmd_below(+t: List<&2, Cmd.Ent>, +pre: List<&2, Nat>, +p: List<&2, Nat>, +q: List<&2, List<&2, Nat>>) -> Bool:
  cmd_below.at(cmd_blank(pre), t, pre, p, q)

# x is the last name of e's path or one of e's aliases: e typed in full
def cmd_names(+x: List<&2, Nat>, e: Cmd.Ent) -> Bool:
  match e:
    case Cmd.Ent{p, a, r, f, g}:
      Bool.or(Paths.cmd_eq(x, Paths.cmd_last(p)), Paths.cmd_in(x, a))

# e expects text after it
def cmd_ent_arg(e: Cmd.Ent) -> Bool:
  match e:
    case Cmd.Ent{p, a, r, f, g}:
      g

def cmd_closed.at(b: Bool, l: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      l
    case False{}:
      List.append(&2, Nat, l, [32n])

# l, and a space after it unless it ends in one
def cmd_closed(+l: List<&2, Nat>) -> List<&2, Nat>:
  cmd_closed.at(cmd_ends_space(l), l)

# a key's answer seen by its parts: its line closed by a space, whether
# the line ends in a space, whether the menu opens, whether it is
# submitted
def cmd_out_shape(o: Cmd.Out) -> List<&2, Nat> & (Bool & (Bool & Bool)):
  match o:
    case Cmd.Out{+l, a, b}:
      (cmd_closed(l), (cmd_ends_space(l), (a, b)))

# o, submitted exactly when s
def cmd_resubmit(o: Cmd.Out, s: Bool) -> Cmd.Out:
  match o:
    case Cmd.Out{l, a, b}:
      Cmd.Out{l, a, s}

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

# LAW command_blank_runs_nothing (R20): in every table, an empty line, or
# one of spaces only, resolves to no command: nothing runs, no menu opens
# EXCLUDES: a blank line (`/`, or `/` and spaces) resolved as the first
#   command of the table, a default, or a bare path whose menu opens
#   (Enter with no row then submits it to the interface,
#   command_enter_without_row_submits; a selected row is another key,
#   command_enter_row_typed_in_part)
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

# LAW command_named_word_then_blank: a line that ends at a word naming a
# child and spaces answers as that child's own entry, in every table
# EXCLUDES: `/memory m ` (m an alias) answered unknown or as /memory
law command_named_word_then_blank:
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
  for blank: {cmd_blank(s) == True{} : Bool}
  {Cmd.resolve(t, List.append(&2, Nat, Paths.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> s)) == cmd_ent_ended(t, e) : Cmd.Res}

# LAW command_named_word_then_child: after a word naming a child, spaces
# and a word x that names a child of it: the line resolves as with the
# child's canonical path, in every table (the entry the first word names
# no longer matters)
# EXCLUDES: a path continued below an alias that runs nothing, runs the
#   parent, or answers another path, when the alias's entry repeats a
#   declared path
law command_named_word_then_child:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +w: List<&2, Nat>
  for +e: Cmd.Ent
  for +gs: List<&2, Nat>
  for +n: Nat
  for +x: List<&2, Nat>
  for +e2: Cmd.Ent
  for +s: List<&2, Nat>
  for ok: {Paths.cmd_wf(t) == True{} : Bool}
  for on: {Paths.cmd_walks(t, q) == True{} : Bool}
  for word: {Paths.cmd_typed(w) == True{} : Bool}
  for hit: {cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}
  for next: {Paths.cmd_typed(x) == True{} : Bool}
  for kid: {cmd_named(t, Paths.cmd_ent_path(e), x) == Some{e2} : Maybe<&2, Cmd.Ent>}
  for gap: {cmd_cuts(s) == True{} : Bool}
  {Cmd.resolve(t, List.append(&2, Nat, Paths.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> List.append(&2, Nat, Paths.cmd_spaces(n), List.append(&2, Nat, x, s)))) == Cmd.resolve(t, List.append(&2, Nat, Paths.cmd_loose(Paths.cmd_ent_path(e), gs), 32n <> List.append(&2, Nat, Paths.cmd_spaces(n), List.append(&2, Nat, x, s)))) : Cmd.Res}

# LAW command_named_word_then_other: after a word naming a child, spaces
# and a word x that names none of its children: the named entry decides,
# in every table: when it takes text it runs with x and the rest as
# typed, else x is unknown below it
# EXCLUDES: argument text after an alias dropped, read as no command, or
#   decided by another entry of the same path
law command_named_word_then_other:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +w: List<&2, Nat>
  for +e: Cmd.Ent
  for +gs: List<&2, Nat>
  for +n: Nat
  for +x: List<&2, Nat>
  for +s: List<&2, Nat>
  for ok: {Paths.cmd_wf(t) == True{} : Bool}
  for on: {Paths.cmd_walks(t, q) == True{} : Bool}
  for word: {Paths.cmd_typed(w) == True{} : Bool}
  for hit: {cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}
  for next: {Paths.cmd_typed(x) == True{} : Bool}
  for miss: {Paths.cmd_takes(t, Paths.cmd_ent_path(e), Paths.cmd_lower(x)) == False{} : Bool}
  for gap: {cmd_cuts(s) == True{} : Bool}
  {Cmd.resolve(t, List.append(&2, Nat, Paths.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> List.append(&2, Nat, Paths.cmd_spaces(n), List.append(&2, Nat, x, s)))) == cmd_named_miss(e, x, s) : Cmd.Res}

# Laws: keys on every line
# ------------------------

# LAW command_tab_row_completes (R8, R15, R18): in a well-formed table, on
# a line pre ++ p whose last word p (no space in it, maybe empty) is keyed
# below a path q (cmd_below: only spaces before p and q the root, or pre
# ends in a space and the line's menu lists children of q, whatever the
# spelling and spacing of pre), Tab on a selected place i holding an entry
# e that is a child of q completes e: the new line is e's canonical path,
# then a space exactly when e has a child or expects text; the menu opens
# exactly when e has a child; nothing is submitted
# EXCLUDES: Tab that keeps the typed prefix, alias or capitals, completes
#   another path or the parent, leaves no space before the next level
#   (/mem Tab leaving the menu shut), leaves a space after a leaf that
#   takes no text, opens no menu below a path with children, or submits
law command_tab_row_completes:
  for +t: List<&2, Cmd.Ent>
  for +pre: List<&2, Nat>
  for +p: List<&2, Nat>
  for +q: List<&2, List<&2, Nat>>
  for +i: Nat
  for +e: Cmd.Ent
  for ok: {Paths.cmd_wf(t) == True{} : Bool}
  for word: {Paths.cmd_spaceless(p) == True{} : Bool}
  for below: {cmd_below(t, pre, p, q) == True{} : Bool}
  for at: {List.get(&2, Cmd.Ent, t, i) == Some{e} : Maybe<&2, Cmd.Ent>}
  for child: {Paths.cmd_is_kid(q, Paths.cmd_ent_path(e)) == True{} : Bool}
  {cmd_out_shape(Cmd.key(t, List.append(&2, Nat, pre, p), Cmd.Row{i}, Cmd.Tab{})) == (List.append(&2, Nat, Paths.cmd_render(Paths.cmd_ent_path(e)), [32n]), (Bool.or(Paths.cmd_has_kid(t, Paths.cmd_ent_path(e)), cmd_ent_arg(e)), (Paths.cmd_has_kid(t, Paths.cmd_ent_path(e)), False{}))) : List<&2, Nat> & (Bool & (Bool & Bool))}

# LAW command_enter_row_typed_in_part (R9, R15, R18): in every table, on
# a line pre ++ p keyed below q (as command_tab_row_completes), Enter on a
# selected place i holding a child e of q, when p in lowercase is neither
# e's last name nor one of its aliases (e typed in part), answers as Tab on
# that row (e completed, its menu open when it has a child) and is
# submitted exactly when e has no child and expects no text
# EXCLUDES: Enter on /memory mo that runs /memory (the user's bug), Enter
#   on /mem that runs /memory before its subcommand is chosen, Enter that
#   submits a path still waiting for a choice or for text, Enter on a
#   leaf that completes it without submitting
law command_enter_row_typed_in_part:
  for +t: List<&2, Cmd.Ent>
  for +pre: List<&2, Nat>
  for +p: List<&2, Nat>
  for +q: List<&2, List<&2, Nat>>
  for +i: Nat
  for +e: Cmd.Ent
  for word: {Paths.cmd_spaceless(p) == True{} : Bool}
  for below: {cmd_below(t, pre, p, q) == True{} : Bool}
  for at: {List.get(&2, Cmd.Ent, t, i) == Some{e} : Maybe<&2, Cmd.Ent>}
  for child: {Paths.cmd_is_kid(q, Paths.cmd_ent_path(e)) == True{} : Bool}
  for part: {cmd_names(Paths.cmd_lower(p), e) == False{} : Bool}
  {Cmd.key(t, List.append(&2, Nat, pre, p), Cmd.Row{i}, Cmd.Enter{}) == cmd_resubmit(Cmd.key(t, List.append(&2, Nat, pre, p), Cmd.Row{i}, Cmd.Tab{}), Bool.not(Bool.or(Paths.cmd_has_kid(t, Paths.cmd_ent_path(e)), cmd_ent_arg(e)))) : Cmd.Out}

# LAW command_enter_row_typed_in_full (R9, R18): in every table, on a line
# pre ++ p keyed below q (as command_tab_row_completes) whose last word p
# (not empty, no space) names the child e of q the line walks into
# (cmd_named: its name in any case, else an alias), Enter on a selected
# place i holding e answers as Enter with no row: the line is submitted as
# typed when e runs bare, else e's menu opens
# (command_enter_without_row_submits, command_enter_without_row_opens)
# EXCLUDES: Enter on a fully typed /memory model that completes it again
#   or runs /memory, an aliased or capitalized row that answers unlike its
#   line, Enter that rewrites the typed line it submits
law command_enter_row_typed_in_full:
  for +t: List<&2, Cmd.Ent>
  for +pre: List<&2, Nat>
  for +p: List<&2, Nat>
  for +q: List<&2, List<&2, Nat>>
  for +i: Nat
  for +e: Cmd.Ent
  for word: {Paths.cmd_typed(p) == True{} : Bool}
  for below: {cmd_below(t, pre, p, q) == True{} : Bool}
  for at: {List.get(&2, Cmd.Ent, t, i) == Some{e} : Maybe<&2, Cmd.Ent>}
  for hit: {cmd_named(t, q, p) == Some{e} : Maybe<&2, Cmd.Ent>}
  {Cmd.key(t, List.append(&2, Nat, pre, p), Cmd.Row{i}, Cmd.Enter{}) == Cmd.key(t, List.append(&2, Nat, pre, p), Cmd.NoRow{}, Cmd.Enter{}) : Cmd.Out}

# LAW command_row_not_child_ignored (R12, R18): in every table, on a line
# pre ++ p keyed below q (as command_tab_row_completes), a selected place
# that holds no child of q (a stale menu, past the table) acts as no row,
# for Tab and for Enter
# EXCLUDES: a stale selection that completes or runs another command on
#   an aliased, capitalized or loosely spaced line, or on the first word
law command_row_not_child_ignored:
  for +t: List<&2, Cmd.Ent>
  for +pre: List<&2, Nat>
  for +p: List<&2, Nat>
  for +q: List<&2, List<&2, Nat>>
  for +i: Nat
  for +k: Cmd.Press
  for word: {Paths.cmd_spaceless(p) == True{} : Bool}
  for below: {cmd_below(t, pre, p, q) == True{} : Bool}
  for stale: {Paths.cmd_row(t, i, q) == False{} : Bool}
  {Cmd.key(t, List.append(&2, Nat, pre, p), Cmd.Row{i}, k) == Cmd.key(t, List.append(&2, Nat, pre, p), Cmd.NoRow{}, k) : Cmd.Out}

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

# LAW command_keys_premises_witness: witness: in the example table with an
# alias, the first word `mem` is keyed below the root, `memory mo` and
# `memory m` below memory; mo types the model row in part, m names it in
# full (place 2); place 0 holds no child of memory; `goal x` resolves to
# no menu, and a bare memory with no default opens its menu
# EXCLUDES: a vacuous key law whose premises no line, row or table meets
law command_keys_premises_witness:
  {(cmd_below(cmd_example_alias_table(), Nil{}, [109n, 101n, 109n], Nil{}), (cmd_below(cmd_example_alias_table(), List.append(&2, Nat, Paths.cmd_example_memory(), [32n]), [109n, 111n], [Paths.cmd_example_memory()]), (cmd_below(cmd_example_alias_table(), List.append(&2, Nat, Paths.cmd_example_memory(), [32n]), [109n], [Paths.cmd_example_memory()]), (cmd_names(Paths.cmd_lower([109n, 111n]), Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_model()], [[109n]], True{}, True{}, False{}}), (Paths.cmd_row(cmd_example_alias_table(), 0n, [Paths.cmd_example_memory()]), Paths.cmd_opens(Cmd.resolve(cmd_example_alias_table(), [103n, 111n, 97n, 108n, 32n, 120n]))))))) == (True{}, (True{}, (True{}, (False{}, (False{}, False{}))))) : Bool & (Bool & (Bool & (Bool & (Bool & Bool))))} & {(List.get(&2, Cmd.Ent, cmd_example_alias_table(), 2n), cmd_named(cmd_example_alias_table(), [Paths.cmd_example_memory()], [109n])) == (Some{Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_model()], [[109n]], True{}, True{}, False{}}}, Some{Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_model()], [[109n]], True{}, True{}, False{}}}) : Maybe<&2, Cmd.Ent> & Maybe<&2, Cmd.Ent>} & {Cmd.resolve([Cmd.Ent{[Paths.cmd_example_memory()], [], False{}, False{}, False{}}, Cmd.Ent{[Paths.cmd_example_memory(), Paths.cmd_example_view()], [], True{}, True{}, False{}}], Paths.cmd_example_memory()) == Cmd.Opens{[Paths.cmd_example_memory()]} : Cmd.Res}

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
