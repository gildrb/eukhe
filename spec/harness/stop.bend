# stop (spec): the Directors at a candidate stop of the run loop (omp2
# ADR 0015: at a stop the loop walks its Directors inside to outside,
# each saying Pass, Continue or Yield), restated without the code
# (bend/stop.bend): the walk as one decision per case, where the code
# walks a list of Directors and their verdicts. The laws of area stop
# (laws/stop.bend) state that the code refines it. A spec: the shipped
# code never calls it.
#
# S1: a candidate stop is a reply with no tool call; its facts: cut (the
#     stop reason is length), text (a text block that is not blank),
#     broken (tool-call markup in the text that the harness could not
#     read), pending (the session owns running work: jobs, children,
#     workflow runs). What the text says is no fact: a whole, readable
#     reply stands, whatever it says.
# S2: the verdicts: LengthStop continues a cut reply, EmptyStop a reply
#     with no text, MarkupStop a broken reply; PendingWork yields when
#     work is pending. Every other verdict passes.
# S3: the walk, inside to outside (LengthStop, EmptyStop, MarkupStop,
#     PendingWork): the first Director that does not pass decides;
#     Continue goes on with it, Yield makes the stop stand; with all
#     passing the stop stands.
# S4: the caps: 3 empty notes in a row.
# S5: the note: "Harness note, attempt <a>: " then, for a cut reply with
#     text, "your previous reply hit <limit> before it finished, ..." with
#     "Length note <row> of <cap>."; <limit> is "the output limit" for 0
#     tokens, else "the <tokens>-token output limit".
# S6: the round note after `done` tool rounds of `max`: left = max - 1 -
#     done (0 at least): the rounds whose results the model still reads.
#     A note when left <= 10: none left, 1 left, or <left> left.
# S7: a length stop with no text (the model still reasoned) climbs a
#     ladder: when the window ran out (a window is known, the output is
#     below the model's catalog max output, prompt + output + 8192 >=
#     window) and a compaction can run, compact and send again (no note);
#     else, under the cap of `long` length notes in a row, the next note;
#     else, once, when a level below the agent's exists, the next note
#     with the request one thinking level lower; else the run fails.

import Base
import ../../bend/stop.bend as S

# S3: the walk
# ------------

def pick(f: S.Facts) -> S.Pick:
  match f:
    case S.Facts{cut, text, broken, pending}:
      match cut:
        case True{}:
          S.Goes{S.LengthStop{}}
        case False{}:
          match text:
            case False{}:
              S.Goes{S.EmptyStop{}}
            case True{}:
              match broken:
                case True{}:
                  S.Goes{S.MarkupStop{}}
                case False{}:
                  S.Stands{}

# S5: the note
# ------------

def limit(tokens: Nat) -> String:
  match tokens:
    case 0n:
      "the output limit"
    case 1n+t:
      String.concat(["the ", Nat.show(1n+t), "-token output limit"])

def note(a: Nat, n: S.Note) -> String:
  match n:
    case S.Cut{t, r, k}:
      String.concat(["Harness note, attempt ", Nat.show(a), ": your previous reply hit ", limit(t), " before it finished, so the harness did not take its cut text as your answer. Reason only about the next step, then call its tool. For a large answer (a file, a document, a long text), write a minimal working version first, then extend it with further edits in this turn. Length note ", Nat.show(r), " of ", Nat.show(k), "."])

# S6: the round note
# ------------------

def round_text(left: Nat, +max: Nat) -> String:
  match left:
    case 0n:
      String.concat(["Harness note: no tool round remains in this turn (maxToolRounds ", Nat.show(max), "): a tool call now ends the turn unfinished at the cap. End with a final answer that states what is done and exactly what remains."])
    case 1n:
      String.concat(["Harness note: 1 tool round remains in this turn (maxToolRounds ", Nat.show(max), "). Use it for the remaining work; if the work cannot finish in it, end with a final answer that states what is done and exactly what remains."])
    case 2n+p:
      String.concat(["Harness note: ", Nat.show(2n+p), " tool rounds remain in this turn (maxToolRounds ", Nat.show(max), "). Use them for the remaining work; if the work cannot finish in them, end with a final answer that states what is done and exactly what remains."])

def round_at(near: Bool, +left: Nat, +max: Nat) -> Maybe<&2, String>:
  match near:
    case True{}:
      Some{round_text(left, max)}
    case False{}:
      None{}

def rounds(+max: Nat, +done: Nat) -> Maybe<&2, String>:
  +left = Nat.sub(Nat.sub(max, 1n), done)
  round_at(Nat.is_le(left, 10n), left, max)

# S7: the ladder of a length stop with no text
# --------------------------------------------

# a rung remains: a compaction, a note under the cap, or the lower note
def rung_left(shrink: Bool, lower: Bool, +n: Nat, +long: Nat) -> Bool:
  Bool.or(shrink, Bool.or(Nat.is_lt(n, long), Bool.and(lower, Nat.is_eq(n, long))))
