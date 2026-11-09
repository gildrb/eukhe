# eukhe: the laws of area command, section whole: the model's answers
# (resolve, menu, key) for every table and every line (bend/command.bend)

# LAWS: the laws of laws/command/paths.bend and named.bend pin the model
# on well-formed tables (lowercase names) and on lines of given shapes; the
# entry (laws/command/entry.bend) answers the model. These hold for every
# table the entry can carry and every line:
#
#   R21 a line's words are the spaceless words it renders (split at every
#       space, an empty word between two spaces)   command_words_exact
#   R22 a line resolves by walking its words from the root: a word names a
#       child of the path walked (its name in lowercase, else an alias) and
#       walks into it; a word naming none starts the argument text of a
#       path that takes text, else it is unknown below that path; a first
#       word naming no command is no command; an answer names only a path
#       the table declares        command_answers_declared_path, and on
#                                 well-formed tables the laws of R1-R4,
#                                 R15, R17 and R20
#   R23 the menu of a line: the command names while its first word is
#       typed; after more words, the children of the path the words before
#       the last walk to whose name or alias starts with the last word (any
#       case), in table order, else none
#                                 command_menu_rows_listed, and the laws of
#                                 R5-R7, R15 and R17
#   R24 Tab and Enter: on a line keyed below a path (or the root), a
#       selected child of it is the row (Tab completes it, Enter as on a
#       row), any other selection acts as no row; anywhere else as no row
#                                 the laws of R8-R12, R16, R18 and R19
#   anchor                        command_whole_example

import Base
import ../../bend/command.bend as Cmd
import ./paths.bend as Paths

# Spec helpers
# ------------

# the answer r names only a path t declares
def cmd_answer_declared(+t: List<&2, Cmd.Ent>, r: Cmd.Res) -> Bool:
  match r:
    case Cmd.Runs{q, a}:
      Paths.cmd_declared(t, q)
    case Cmd.Opens{q}:
      Paths.cmd_declared(t, q)
    case Cmd.Unknown{q, w}:
      Paths.cmd_declared(t, q)
    case Cmd.NoCmd{}:
      True{}

# Laws
# ----

# LAW command_words_exact (R21): the words of every line are spaceless,
# never none, and rendered with one space between two words they give the
# line back (one list of words does that)
# EXCLUDES: a word split elsewhere than at a space (a space kept in a
#   word, two spaces read as one, a word dropped or repeated) in the words
#   the model walks
law command_words_exact:
  for +line: List<&2, Nat>
  {(Paths.cmd_render(Cmd.words(line)), (Paths.cmd_all_spaceless(Cmd.words(line)), List.is_empty(&2, List<&2, Nat>, Cmd.words(line)))) == (line, (True{}, False{})) : List<&2, Nat> & (Bool & Bool)}

# LAW command_answers_declared_path (R22): in every table, the answer of
# every line names only a path the table declares: the path it runs (with
# or without text), the path whose menu opens, or the path below which a
# word is unknown
# EXCLUDES: a resolver that invents a path (typed words glued into a path
#   the table lacks, a child's name put below a parent that does not have
#   it), or answers below a path no entry declares
law command_answers_declared_path:
  for +t: List<&2, Cmd.Ent>
  for +line: List<&2, Nat>
  {cmd_answer_declared(t, Cmd.resolve(t, line)) == True{} : Bool}

# LAW command_whole_example: anchor: in a table whose name is in capitals
# (MEM), neither `MEM` nor `mem` names it; `  ` then Enter submits; the
# words of `a  b ` are a, an empty word, b and an empty word
# EXCLUDES: a capitalized table name matched by lowercasing it too; a
#   blank line rewritten
law command_whole_example:
  {(Cmd.resolve([Cmd.Ent{[[77n, 69n, 77n]], [], True{}, False{}, False{}}], [77n, 69n, 77n]), (Cmd.resolve([Cmd.Ent{[[77n, 69n, 77n]], [], True{}, False{}, False{}}], [109n, 101n, 109n]), (Cmd.key([], [32n, 32n], Cmd.NoRow{}, Cmd.Enter{}), Cmd.words([97n, 32n, 32n, 98n, 32n])))) == (Cmd.NoCmd{}, (Cmd.NoCmd{}, (Cmd.Out{[32n, 32n], False{}, True{}}, [[97n], [], [98n], []]))) : Cmd.Res & (Cmd.Res & (Cmd.Out & List<&2, List<&2, Nat>>))}
