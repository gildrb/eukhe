# eukhe: the laws of area command

import Base
import ../bend/command.bend as Cmd
import ../bend/ffi_command.bend as FCmd
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- commands ----

# LAWS (slash commands; docs/interface.md "Slash commands"): the path a
# typed command line names, the menu below its last word, and what Tab
# and Enter do. Each law is an open claim about the model in
# bend/command.bend and its entry bend/ffi_command.bend (the Rust code,
# crates/eukhe-tui/src/command_paths.rs, builds the table from the
# registry of crates/eukhe-types/src/slash_commands.rs and the argument
# lists, and asks the entry). The proofs are proof/<law>.bend, imported
# from PROOF.bend; shared lemmas in proof/base.bend.
#
#   R1  a declared path typed in full runs itself, never its parent; a
#       bare path with children and no default opens its menu
#                                     command_path_runs_itself
#   R2  a word below a path that takes no text and names none of its
#       children runs nothing: it is unknown
#                                     command_unknown_runs_nothing
#   R3  a word below a path that takes text starts the argument text,
#       kept as typed                 command_free_takes_rest
#   R4  a first word that names no command is the interface's own (a
#       typo note, or a prompt)       command_stray_is_not_a_command
#   R5  the menu below a path: exactly its children whose name or alias
#       starts with the typed word (any case), in table order; never the
#       path itself or a deeper path  command_menu_lists_children
#   R6  the first word's menu is the command names (the interface's
#       fuzzy ranking)                command_menu_names_first_word
#   R7  no menu below argument text or an unknown word
#                                     command_menu_shut_off_path
#   R8  Tab on a row completes it (a space after it when it has children
#       or expects text) and opens its children
#                                     command_tab_completes_row
#   R9  Enter on a row typed in full submits a path that runs bare, else
#       opens its children; on a row typed in part it completes the row,
#       then descends into its children, waits for its text, or submits
#                                     command_enter_on_row
#   R10 Enter with no row submits the line, unless it is a bare path with
#       no default (its menu opens)   command_enter_without_row
#   R11 Tab with no row opens the menu of the line
#                                     command_tab_without_row
#   R12 a selected row that is not a child of the typed path is ignored
#                                     command_stale_row_ignored
#   R13 the user's bug (/memory + space + model + Enter ran /memory):
#       closed examples               command_memory_model_example,
#                                     command_memory_model_keys_example
#   R14 the entry reads every request that fits back whole, answers the
#       model, refuses input left over and malformed input; every reply
#       reads back                    command_ffi_*
#
# Not pinned here: the fuzzy ranking of the command names (the
# interface's), the descriptions and usage hints the menu shows (the
# registry's), and the suggestion for an unknown word (the interface's
# edit distance over the children of the path the model names).

# Spec helpers
# ------------

# a and b are the same chars
def cmd_eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, ys}:
      False{}
    case Con{x, xs} Nil{}:
      False{}
    case Con{x, xs} Con{y, ys}:
      Bool.and(Nat.is_eq(x, y), cmd_eq(xs, ys))

# a and b are the same path
def cmd_path_eq(a: List<&2, List<&2, Nat>>, b: List<&2, List<&2, Nat>>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, ys}:
      False{}
    case Con{x, xs} Nil{}:
      False{}
    case Con{x, xs} Con{y, ys}:
      Bool.and(cmd_eq(x, y), cmd_path_eq(xs, ys))

# x is one of xs
def cmd_in(+x: List<&2, Nat>, xs: List<&2, List<&2, Nat>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(cmd_eq(x, y), cmd_in(x, rest))

# x is a prefix of n
def cmd_prefix(x: List<&2, Nat>, n: List<&2, Nat>) -> Bool:
  match x n:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, ys}:
      True{}
    case Con{a, as} Nil{}:
      False{}
    case Con{a, as} Con{y, ys}:
      Bool.and(Nat.is_eq(a, y), cmd_prefix(as, ys))

# x is a prefix of one of xs
def cmd_prefix_in(+x: List<&2, Nat>, xs: List<&2, List<&2, Nat>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(cmd_prefix(x, y), cmd_prefix_in(x, rest))

def cmd_lower.up(b: Bool, c: Nat) -> Nat:
  match b:
    case True{}:
      Nat.add(c, 32n)
    case False{}:
      c

# a char as the model reads a typed word: A-Z in lowercase
def cmd_lower.c(+c: Nat) -> Nat:
  cmd_lower.up(Bool.and(Bool.not(Nat.is_lt(c, 65n)), Nat.is_lt(c, 91n)), c)

def cmd_lower(w: List<&2, Nat>) -> List<&2, Nat>:
  match w:
    case Nil{}:
      Nil{}
    case Con{+c, rest}:
      cmd_lower.c(c) <> cmd_lower(rest)

# no char of w is a space
def cmd_spaceless(w: List<&2, Nat>) -> Bool:
  match w:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.and(Bool.not(Nat.is_eq(c, 32n)), cmd_spaceless(rest))

# no word of ws has a space (a word may be empty)
def cmd_all_spaceless(ws: List<&2, List<&2, Nat>>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{w, rest}:
      Bool.and(cmd_spaceless(w), cmd_all_spaceless(rest))

# a typed word: at least one char, no space
def cmd_typed(w: List<&2, Nat>) -> Bool:
  match w:
    case Nil{}:
      False{}
    case Con{c, rest}:
      cmd_spaceless(c <> rest)

# a name of the table: at least one char, no space, already lowercase
def cmd_name_ok(+w: List<&2, Nat>) -> Bool:
  Bool.and(cmd_typed(w), cmd_eq(cmd_lower(w), w))

def cmd_names_ok(ws: List<&2, List<&2, Nat>>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+w, rest}:
      Bool.and(cmd_name_ok(w), cmd_names_ok(rest))

# a well-formed table: every name of every path and every alias is a
# name (the Rust code sends the registry's lowercase names)
def cmd_wf(t: List<&2, Cmd.Ent>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Con{Cmd.Ent{p, a, r, f, g}, rest}:
      Bool.and(Bool.and(cmd_names_ok(p), cmd_names_ok(a)), cmd_wf(rest))

# a space, then each word of ws, with a space between two words
def cmd_sep(ws: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      32n <> List.append(&2, Nat, w, cmd_sep(rest))

# a line: the words of ws with a space between two words
def cmd_render(ws: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      List.append(&2, Nat, w, cmd_sep(rest))

def cmd_ent_path(e: Cmd.Ent) -> List<&2, List<&2, Nat>>:
  match e:
    case Cmd.Ent{p, a, r, f, g}:
      p

def cmd_first.at(hit: Bool, e: Cmd.Ent, rest: Maybe<&2, Cmd.Ent>) -> Maybe<&2, Cmd.Ent>:
  match hit:
    case True{}:
      Some{e}
    case False{}:
      rest

# the first entry of t with path p
def cmd_lookup(t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>) -> Maybe<&2, Cmd.Ent>:
  match t:
    case Nil{}:
      None{}
    case Con{+e, rest}:
      cmd_first.at(cmd_path_eq(cmd_ent_path(e), p), e, cmd_lookup(rest, p))

def cmd_some(m: Maybe<&2, Cmd.Ent>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{e}:
      True{}

# t declares path p
def cmd_declared(+t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>) -> Bool:
  cmd_some(cmd_lookup(t, p))

# from path acc, every path that adds the names of rest one by one is
# declared
def cmd_walks.go(rest: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, acc: List<&2, List<&2, Nat>>) -> Bool:
  match rest:
    case Nil{}:
      True{}
    case Con{r, more}:
      +a = List.append(&2, List<&2, Nat>, acc, [r])
      Bool.and(cmd_declared(t, a), cmd_walks.go(more, t, a))

# every nonempty prefix of p is declared: p is the root or a path of the
# table's tree
def cmd_walks(+t: List<&2, Cmd.Ent>, p: List<&2, List<&2, Nat>>) -> Bool:
  cmd_walks.go(p, t, Nil{})

# p is a path of the table's tree (not the root)
def cmd_path(+t: List<&2, Cmd.Ent>, p: List<&2, List<&2, Nat>>) -> Bool:
  match p:
    case Nil{}:
      False{}
    case Con{x, rest}:
      cmd_walks(t, x <> rest)

def cmd_init.go(rest: List<&2, List<&2, Nat>>, x: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match rest:
    case Nil{}:
      Nil{}
    case Con{y, more}:
      x <> cmd_init.go(more, y)

# p without its last name
def cmd_init(p: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match p:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      cmd_init.go(rest, x)

def cmd_last.go(rest: List<&2, List<&2, Nat>>, x: List<&2, Nat>) -> List<&2, Nat>:
  match rest:
    case Nil{}:
      x
    case Con{y, more}:
      cmd_last.go(more, y)

# the last name of p
def cmd_last(p: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match p:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      cmd_last.go(rest, x)

# p is a child of q: q and one more name
def cmd_is_kid(q: List<&2, List<&2, Nat>>, p: List<&2, List<&2, Nat>>) -> Bool:
  match p:
    case Nil{}:
      False{}
    case Con{x, rest}:
      cmd_path_eq(cmd_init(x <> rest), q)

# q has a child in t
def cmd_has_kid(t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>) -> Bool:
  match t:
    case Nil{}:
      False{}
    case Con{Cmd.Ent{p, a, r, f, g}, rest}:
      Bool.or(cmd_is_kid(q, p), cmd_has_kid(rest, q))

# a child of q has the alias x
def cmd_alias_kid(t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> Bool:
  match t:
    case Nil{}:
      False{}
    case Con{Cmd.Ent{p, a, r, f, g}, rest}:
      Bool.or(Bool.and(cmd_is_kid(q, p), cmd_in(x, a)), cmd_alias_kid(rest, q, x))

# the word x (lowercase) names a child of q, by its name or an alias
def cmd_takes(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> Bool:
  Bool.or(cmd_declared(t, List.append(&2, List<&2, Nat>, q, [x])), cmd_alias_kid(t, q, x))

def cmd_free.of(m: Maybe<&2, Cmd.Ent>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Cmd.Ent{p, a, r, f, g}}:
      f

# the entry of path p takes free text
def cmd_free(+t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>) -> Bool:
  cmd_free.of(cmd_lookup(t, p))

def cmd_ended.at(b: Bool, p: List<&2, List<&2, Nat>>) -> Cmd.Res:
  match b:
    case True{}:
      Cmd.Runs{p, Nil{}}
    case False{}:
      Cmd.Opens{p}

def cmd_ended.of(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>) -> Cmd.Res:
  match m:
    case None{}:
      Cmd.NoCmd{}
    case Some{Cmd.Ent{q, a, r, f, g}}:
      cmd_ended.at(Bool.or(r, Bool.not(cmd_has_kid(t, p))), p)

# what a declared path typed in full does: it runs with no text when it
# has a default or no child, else its menu opens
def cmd_ended(+t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>) -> Cmd.Res:
  cmd_ended.of(cmd_lookup(t, p), t, p)

def cmd_rows.at(b: Bool, i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      i <> rest
    case False{}:
      rest

# the places (from i) of the children of q whose last name or an alias
# starts with x
def cmd_rows(t: List<&2, Cmd.Ent>, +i: Nat, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> List<&2, Nat>:
  match t:
    case Nil{}:
      Nil{}
    case Con{Cmd.Ent{+p, a, r, f, g}, rest}:
      cmd_rows.at(Bool.and(cmd_is_kid(q, p), Bool.or(cmd_prefix(x, cmd_last(p)), cmd_prefix_in(x, a))), i, cmd_rows(rest, 1n+i, q, x))

def cmd_space_if(b: Bool, l: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      List.append(&2, Nat, l, [32n])
    case False{}:
      l

def cmd_tab.at(+k: Bool, g: Bool, l: List<&2, Nat>) -> Cmd.Out:
  Cmd.Out{cmd_space_if(Bool.or(k, g), l), k, False{}}

# Tab on the row e: its path, a space after it when it has children or
# expects text; its children's menu opens when it has children
def cmd_tab(+t: List<&2, Cmd.Ent>, e: Cmd.Ent) -> Cmd.Out:
  match e:
    case Cmd.Ent{+p, a, r, f, g}:
      cmd_tab.at(cmd_has_kid(t, p), g, cmd_render(p))

def cmd_enter.fresh(k: Bool, g: Bool, l: List<&2, Nat>) -> Cmd.Out:
  match k:
    case True{}:
      Cmd.Out{List.append(&2, Nat, l, [32n]), True{}, False{}}
    case False{}:
      match g:
        case True{}:
          Cmd.Out{List.append(&2, Nat, l, [32n]), False{}, False{}}
        case False{}:
          Cmd.Out{l, False{}, True{}}

def cmd_enter.typed(d: Bool, l: List<&2, Nat>, line: List<&2, Nat>) -> Cmd.Out:
  match d:
    case True{}:
      Cmd.Out{line, False{}, True{}}
    case False{}:
      Cmd.Out{List.append(&2, Nat, l, [32n]), True{}, False{}}

def cmd_enter.at(full: Bool, +k: Bool, r: Bool, g: Bool, l: List<&2, Nat>, line: List<&2, Nat>) -> Cmd.Out:
  match full:
    case True{}:
      cmd_enter.typed(Bool.or(r, Bool.not(k)), l, line)
    case False{}:
      cmd_enter.fresh(k, g, l)

# Enter on the row e with the typed word w on the line: typed in full
# (its last name or an alias, any case), it is submitted when it runs
# bare (a default, or no child), else its children's menu opens; typed
# in part, it completes and descends into its children, waits for the
# text it expects, or is submitted
def cmd_enter(+t: List<&2, Cmd.Ent>, e: Cmd.Ent, +w: List<&2, Nat>, line: List<&2, Nat>) -> Cmd.Out:
  match e:
    case Cmd.Ent{+p, +a, r, f, g}:
      cmd_enter.at(Bool.or(cmd_eq(cmd_lower(w), cmd_last(p)), cmd_in(cmd_lower(w), a)), cmd_has_kid(t, p), r, g, cmd_render(p), line)

# Enter with no row, after the line resolves to r: a bare path with no
# default opens its menu (a space after it); anything else is submitted
def cmd_enter_bare(r: Cmd.Res, line: List<&2, Nat>) -> Cmd.Out:
  match r:
    case Cmd.Runs{q, x}:
      Cmd.Out{line, False{}, True{}}
    case Cmd.Opens{q}:
      Cmd.Out{List.append(&2, Nat, cmd_render(q), [32n]), True{}, False{}}
    case Cmd.Unknown{q, w}:
      Cmd.Out{line, False{}, True{}}
    case Cmd.NoCmd{}:
      Cmd.Out{line, False{}, True{}}

def cmd_row.of(m: Maybe<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{e}:
      cmd_is_kid(q, cmd_ent_path(e))

# place i of t holds a child of q
def cmd_row(t: List<&2, Cmd.Ent>, i: Nat, +q: List<&2, List<&2, Nat>>) -> Bool:
  cmd_row.of(List.get(&2, Cmd.Ent, t, i), q)

# The example table: /memory (view, model; a default) and /goal (text)
def cmd_example_memory() -> List<&2, Nat>:
  [109n, 101n, 109n, 111n, 114n, 121n]

def cmd_example_view() -> List<&2, Nat>:
  [118n, 105n, 101n, 119n]

def cmd_example_model() -> List<&2, Nat>:
  [109n, 111n, 100n, 101n, 108n]

def cmd_example_goal() -> List<&2, Nat>:
  [103n, 111n, 97n, 108n]

def cmd_example_table() -> List<&2, Cmd.Ent>:
  [Cmd.Ent{[cmd_example_memory()], [], True{}, False{}, False{}}, Cmd.Ent{[cmd_example_memory(), cmd_example_view()], [], True{}, True{}, False{}}, Cmd.Ent{[cmd_example_memory(), cmd_example_model()], [], True{}, True{}, False{}}, Cmd.Ent{[cmd_example_goal()], [], True{}, True{}, True{}}]

# Laws: paths
# -----------

# LAW command_path_runs_itself: a declared path typed in full runs itself
# with no text (a bare path with children and no default opens its
# menu), in any well-formed table
# EXCLUDES: a subcommand that runs its parent with the subcommand as its
#   text (/memory model ran /memory), a path that runs another path, a
#   bare path with no default that runs anyway
law command_path_runs_itself:
  for +t: List<&2, Cmd.Ent>
  for +p: List<&2, List<&2, Nat>>
  for ok: {cmd_wf(t) == True{} : Bool}
  for on: {cmd_path(t, p) == True{} : Bool}
  {Cmd.resolve(t, cmd_render(p)) == cmd_ended(t, p) : Cmd.Res}

# LAW command_unknown_runs_nothing: below a path that takes no text, a
# word that names none of its children (by name or alias, in any case)
# runs nothing, whatever follows: the answer is that word, unknown,
# below the path
# EXCLUDES: an unknown subcommand that runs its parent (/memory x ran
#   /memory), one that runs a sibling or a default
law command_unknown_runs_nothing:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +w: List<&2, Nat>
  for +more: List<&2, List<&2, Nat>>
  for ok: {cmd_wf(t) == True{} : Bool}
  for on: {cmd_path(t, q) == True{} : Bool}
  for shut: {cmd_free(t, q) == False{} : Bool}
  for word: {cmd_typed(w) == True{} : Bool}
  for after: {cmd_all_spaceless(more) == True{} : Bool}
  for miss: {cmd_takes(t, q, cmd_lower(w)) == False{} : Bool}
  {Cmd.resolve(t, cmd_render(List.append(&2, List<&2, Nat>, q, w <> more))) == Cmd.Unknown{q, w} : Cmd.Res}

# LAW command_free_takes_rest: below a path that takes text, a word that
# names none of its children starts the text: the path runs with the
# rest of the line as typed (its spacing kept)
# EXCLUDES: text that loses a word or a space, text read as a subcommand
#   it does not name, a path that drops its text
law command_free_takes_rest:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +w: List<&2, Nat>
  for +more: List<&2, List<&2, Nat>>
  for ok: {cmd_wf(t) == True{} : Bool}
  for on: {cmd_path(t, q) == True{} : Bool}
  for open: {cmd_free(t, q) == True{} : Bool}
  for word: {cmd_typed(w) == True{} : Bool}
  for after: {cmd_all_spaceless(more) == True{} : Bool}
  for miss: {cmd_takes(t, q, cmd_lower(w)) == False{} : Bool}
  {Cmd.resolve(t, cmd_render(List.append(&2, List<&2, Nat>, q, w <> more))) == Cmd.Runs{q, cmd_render(w <> more)} : Cmd.Res}

# LAW command_stray_is_not_a_command: a first word that names no command
# (by name or alias, in any case) is no command of the table: the
# interface handles it (a typo note, or a prompt)
# EXCLUDES: a stray word that runs a command, or opens a menu
law command_stray_is_not_a_command:
  for +t: List<&2, Cmd.Ent>
  for +w: List<&2, Nat>
  for +more: List<&2, List<&2, Nat>>
  for word: {cmd_typed(w) == True{} : Bool}
  for after: {cmd_all_spaceless(more) == True{} : Bool}
  for miss: {cmd_takes(t, Nil{}, cmd_lower(w)) == False{} : Bool}
  {Cmd.resolve(t, cmd_render(w <> more)) == Cmd.NoCmd{} : Cmd.Res}

# LAW command_memory_model_example: in the example table, `memory model`
# runs memory model, `memory` runs memory, `memory x` is unknown below
# memory, and `goal memory model` runs goal with its text
law command_memory_model_example:
  {[Cmd.resolve(cmd_example_table(), List.append(&2, Nat, cmd_example_memory(), 32n <> cmd_example_model())), Cmd.resolve(cmd_example_table(), cmd_example_memory()), Cmd.resolve(cmd_example_table(), List.append(&2, Nat, cmd_example_memory(), [32n, 120n])), Cmd.resolve(cmd_example_table(), List.append(&2, Nat, cmd_example_goal(), 32n <> List.append(&2, Nat, cmd_example_memory(), 32n <> cmd_example_model())))] == [Cmd.Runs{[cmd_example_memory(), cmd_example_model()], Nil{}}, Cmd.Runs{[cmd_example_memory()], Nil{}}, Cmd.Unknown{[cmd_example_memory()], [120n]}, Cmd.Runs{[cmd_example_goal()], List.append(&2, Nat, cmd_example_memory(), 32n <> cmd_example_model())}] : List<&2, Cmd.Res>}

# LAW command_memory_model_keys_example: in the example table, `mem` with
# the memory row and Tab is `memory ` with its menu open; `memory ` lists
# view and model; `memory mo` lists model, and Enter on that row submits
# `memory model`
law command_memory_model_keys_example:
  {(Cmd.key(cmd_example_table(), [109n, 101n, 109n], Cmd.Row{0n}, Cmd.Tab{}), (Cmd.menu(cmd_example_table(), List.append(&2, Nat, cmd_example_memory(), [32n])), (Cmd.menu(cmd_example_table(), List.append(&2, Nat, cmd_example_memory(), [32n, 109n, 111n])), Cmd.key(cmd_example_table(), List.append(&2, Nat, cmd_example_memory(), [32n, 109n, 111n]), Cmd.Row{2n}, Cmd.Enter{})))) == (Cmd.Out{List.append(&2, Nat, cmd_example_memory(), [32n]), True{}, False{}}, (Cmd.Kids{[cmd_example_memory()], [1n, 2n]}, (Cmd.Kids{[cmd_example_memory()], [2n]}, Cmd.Out{List.append(&2, Nat, cmd_example_memory(), 32n <> cmd_example_model()), False{}, True{}}))) : Cmd.Out & (Cmd.Menu & (Cmd.Menu & Cmd.Out))}

# Laws: menus
# -----------

# LAW command_menu_lists_children: the menu below a declared path lists
# exactly its children whose last name or an alias starts with the typed
# word (any case), by their places in the table, in table order
# EXCLUDES: a menu that closes after the space (the old /memory + space),
#   one that lists the path itself, a grandchild, a sibling, a child the
#   word does not start, or drops one
law command_menu_lists_children:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for ok: {cmd_wf(t) == True{} : Bool}
  for on: {cmd_path(t, q) == True{} : Bool}
  for word: {cmd_spaceless(p) == True{} : Bool}
  {Cmd.menu(t, cmd_render(List.append(&2, List<&2, Nat>, q, [p]))) == Cmd.Kids{q, cmd_rows(t, 0n, q, cmd_lower(p))} : Cmd.Menu}

# LAW command_menu_names_first_word: while the first word is typed, the
# menu is the command names (the interface ranks them)
# EXCLUDES: a children menu before a command is chosen
law command_menu_names_first_word:
  for +t: List<&2, Cmd.Ent>
  for +p: List<&2, Nat>
  for word: {cmd_spaceless(p) == True{} : Bool}
  {Cmd.menu(t, p) == Cmd.Names{} : Cmd.Menu}

# LAW command_menu_shut_off_path: after a word that names no child of the
# path before it (argument text, an unknown word, or a stray first
# word), no menu opens, whatever follows
# EXCLUDES: argument text that opens a command's menu (/goal memory then
#   a space listing memory's children)
law command_menu_shut_off_path:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +w: List<&2, Nat>
  for +more: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for ok: {cmd_wf(t) == True{} : Bool}
  for on: {cmd_walks(t, q) == True{} : Bool}
  for word: {cmd_typed(w) == True{} : Bool}
  for after: {cmd_all_spaceless(more) == True{} : Bool}
  for last: {cmd_spaceless(p) == True{} : Bool}
  for miss: {cmd_takes(t, q, cmd_lower(w)) == False{} : Bool}
  {Cmd.menu(t, cmd_render(List.append(&2, List<&2, Nat>, q, w <> List.append(&2, List<&2, Nat>, more, [p])))) == Cmd.Shut{} : Cmd.Menu}

# Laws: keys
# ----------

# LAW command_tab_completes_row: Tab on a row that is a child of the
# typed path completes it (its canonical path), a space after it when it
# has children or expects text, and opens its children; it never
# submits
# EXCLUDES: Tab that completes without opening the next level (/mem Tab
#   left the menu shut), Tab that submits, one that keeps the typed
#   prefix
law command_tab_completes_row:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for +i: Nat
  for +e: Cmd.Ent
  for ok: {cmd_wf(t) == True{} : Bool}
  for on: {cmd_walks(t, q) == True{} : Bool}
  for word: {cmd_spaceless(p) == True{} : Bool}
  for at: {List.get(&2, Cmd.Ent, t, i) == Some{e} : Maybe<&2, Cmd.Ent>}
  for child: {cmd_is_kid(q, cmd_ent_path(e)) == True{} : Bool}
  {Cmd.key(t, cmd_render(List.append(&2, List<&2, Nat>, q, [p])), Cmd.Row{i}, Cmd.Tab{}) == cmd_tab(t, e) : Cmd.Out}

# LAW command_enter_on_row: Enter on a row that is a child of the typed
# path: typed in full, a path that runs bare is submitted as typed and
# any other opens its children; typed in part, the row completes and
# descends into its children (no submit), waits for the text it expects
# (no submit), or is submitted
# EXCLUDES: Enter on /memory mo that runs /memory, Enter on /mem that
#   runs /memory before its subcommand is chosen, Enter that submits a
#   bare path with no default
law command_enter_on_row:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for +i: Nat
  for +e: Cmd.Ent
  for ok: {cmd_wf(t) == True{} : Bool}
  for on: {cmd_walks(t, q) == True{} : Bool}
  for word: {cmd_spaceless(p) == True{} : Bool}
  for at: {List.get(&2, Cmd.Ent, t, i) == Some{e} : Maybe<&2, Cmd.Ent>}
  for child: {cmd_is_kid(q, cmd_ent_path(e)) == True{} : Bool}
  {Cmd.key(t, cmd_render(List.append(&2, List<&2, Nat>, q, [p])), Cmd.Row{i}, Cmd.Enter{}) == cmd_enter(t, e, p, cmd_render(List.append(&2, List<&2, Nat>, q, [p]))) : Cmd.Out}

# LAW command_enter_without_row: Enter with no row submits the line as
# typed, unless it resolves to a bare path with no default: then the
# line becomes that path and a space, and its menu opens
# EXCLUDES: Enter that submits a path that needs a choice, Enter that
#   rewrites a line it submits
law command_enter_without_row:
  for +t: List<&2, Cmd.Ent>
  for +line: List<&2, Nat>
  {Cmd.key(t, line, Cmd.NoRow{}, Cmd.Enter{}) == cmd_enter_bare(Cmd.resolve(t, line), line) : Cmd.Out}

# LAW command_tab_without_row: Tab with no row keeps the line and opens
# its menu
# EXCLUDES: Tab that submits, or edits a line with no row
law command_tab_without_row:
  for +t: List<&2, Cmd.Ent>
  for +line: List<&2, Nat>
  {Cmd.key(t, line, Cmd.NoRow{}, Cmd.Tab{}) == Cmd.Out{line, True{}, False{}} : Cmd.Out}

# LAW command_stale_row_ignored: a selected place that holds no child of
# the typed path (a stale menu, or past the table) acts as no row
# EXCLUDES: a stale selection that completes or runs another command
law command_stale_row_ignored:
  for +t: List<&2, Cmd.Ent>
  for +q: List<&2, List<&2, Nat>>
  for +p: List<&2, Nat>
  for +i: Nat
  for +k: Cmd.Press
  for ok: {cmd_wf(t) == True{} : Bool}
  for on: {cmd_walks(t, q) == True{} : Bool}
  for word: {cmd_spaceless(p) == True{} : Bool}
  for stale: {cmd_row(t, i, q) == False{} : Bool}
  {Cmd.key(t, cmd_render(List.append(&2, List<&2, Nat>, q, [p])), Cmd.Row{i}, k) == Cmd.key(t, cmd_render(List.append(&2, List<&2, Nat>, q, [p])), Cmd.NoRow{}, k) : Cmd.Out}

# The entry (bend/ffi_command.bend)
# ---------------------------------

# every string of xs fits the wire
def cmd_strs_all(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(LawsBase.wire_fits(String.length(x)), cmd_strs_all(rest))

# every string of xs fits the wire, and so does their count
def cmd_strs_fit(+xs: List<&2, String>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), cmd_strs_all(xs))

def cmd_ent_fits(e: FCmd.EntW) -> Bool:
  match e:
    case FCmd.EntW{p, a, r, f, g}:
      Bool.and(cmd_strs_fit(p), cmd_strs_fit(a))

def cmd_ents_all(t: List<&2, FCmd.EntW>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.and(cmd_ent_fits(e), cmd_ents_all(rest))

def cmd_sel_fits(x: Cmd.Sel) -> Bool:
  match x:
    case Cmd.NoRow{}:
      True{}
    case Cmd.Row{i}:
      LawsBase.wire_fits(i)

def cmd_query_fits(q: FCmd.Query) -> Bool:
  match q:
    case FCmd.QResolve{l}:
      LawsBase.wire_fits(String.length(l))
    case FCmd.QMenu{l}:
      LawsBase.wire_fits(String.length(l))
    case FCmd.QKey{l, x, k}:
      Bool.and(LawsBase.wire_fits(String.length(l)), cmd_sel_fits(x))

# every count, length and place of a request fits the wire
def cmd_req_fits(r: FCmd.Req) -> Bool:
  match r:
    case FCmd.Req{+t, q}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, FCmd.EntW, t)), cmd_ents_all(t)), cmd_query_fits(q))

def cmd_res_fits(r: FCmd.ResW) -> Bool:
  match r:
    case FCmd.RunsW{p, a}:
      Bool.and(cmd_strs_fit(p), LawsBase.wire_fits(String.length(a)))
    case FCmd.OpensW{p}:
      cmd_strs_fit(p)
    case FCmd.UnknownW{p, w}:
      Bool.and(cmd_strs_fit(p), LawsBase.wire_fits(String.length(w)))
    case FCmd.NoCmdW{}:
      True{}

def cmd_menu_fits(m: FCmd.MenuW) -> Bool:
  match m:
    case FCmd.NamesW{}:
      True{}
    case FCmd.KidsW{p, +xs}:
      Bool.and(cmd_strs_fit(p), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)))
    case FCmd.ShutW{}:
      True{}

def cmd_out_fits(o: FCmd.OutW) -> Bool:
  match o:
    case FCmd.OutW{l, a, b}:
      LawsBase.wire_fits(String.length(l))

# LAW command_ffi_round_trip: every request that fits the wire reads back
# as itself, and its reading consumes exactly its encoding
# EXCLUDES: a name, flag, line, row or key lost, swapped or misread on
#   the way to the model
law command_ffi_round_trip:
  for +r: FCmd.Req
  for +rest: String
  for h: {cmd_req_fits(r) == True{} : Bool}
  {FCmd.get_req(FCmd.put_req(r, rest)) == Wr.Got{r, rest} : Wr.Dec<FCmd.Req>}

# LAW command_ffi_answers: the entry answers a request with the model's
# answer about the table it carries
# EXCLUDES: an entry that answers another question, another table, or a
#   default
law command_ffi_answers:
  for +r: FCmd.Req
  for h: {cmd_req_fits(r) == True{} : Bool}
  {FCmd.ffi(FCmd.put_req(r, "")) == FCmd.ffi.run(r) : String}

# LAW command_ffi_left_over: a request with input left over after it is
# refused
# EXCLUDES: trailing input read as part of a request, or ignored
law command_ffi_left_over:
  for +r: FCmd.Req
  for +rest: String
  for h: {cmd_req_fits(r) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FCmd.ffi(FCmd.put_req(r, rest)) == Wr.err("command: input left over") : String}

# LAW command_ffi_malformed: a malformed request answers the error form,
# never an answer
# EXCLUDES: a default answer (a run, a menu) for input the entry cannot
#   read
law command_ffi_malformed:
  for +s: String
  for bad: {FCmd.get_req(s) == Wr.Bad{} : Wr.Dec<FCmd.Req>}
  {FCmd.ffi(s) == Wr.err("command: malformed request") : String}

# LAW command_ffi_res_round_trip: every resolve reply that fits reads
# back as itself (Rust's Reader reads the same grammar)
# EXCLUDES: two answers with one encoding, an answer Rust misreads
law command_ffi_res_round_trip:
  for +x: FCmd.ResW
  for +rest: String
  for h: {cmd_res_fits(x) == True{} : Bool}
  {FCmd.get_res(FCmd.put_res(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FCmd.ResW>}

# LAW command_ffi_menu_round_trip: every menu reply that fits reads back
# as itself
# EXCLUDES: two menus with one encoding, a menu Rust misreads
law command_ffi_menu_round_trip:
  for +x: FCmd.MenuW
  for +rest: String
  for h: {cmd_menu_fits(x) == True{} : Bool}
  {FCmd.get_menu(FCmd.put_menu(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FCmd.MenuW>}

# LAW command_ffi_out_round_trip: every key reply that fits reads back as
# itself
# EXCLUDES: a new line, menu flag or submit flag Rust misreads
law command_ffi_out_round_trip:
  for +x: FCmd.OutW
  for +rest: String
  for h: {cmd_out_fits(x) == True{} : Bool}
  {FCmd.get_out(FCmd.put_out(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FCmd.OutW>}

# LAW command_ffi_witness: a request that fits exists, a malformed one
# exists, and input can be left over
law command_ffi_witness:
  exs r: FCmd.Req
  exs s: String
  exs rest: String
  {(cmd_req_fits(r), (FCmd.get_req(s), String.is_empty(rest))) == (True{}, (Wr.Bad{}, False{})) : Bool & (Wr.Dec<FCmd.Req> & Bool)}
