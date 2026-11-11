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
#     workflow runs), full (S5). What the text says is no fact: a whole,
#     readable reply stands, whatever it says.
# S2: the verdicts: LengthStop decides every cut reply: it continues one
#     with no text and one that is full, and yields at one with text that
#     is not full (the truncated reply is kept as the answer, as omp keeps
#     a truncated turn that delivered text while the window has room);
#     EmptyStop continues a reply with no text, MarkupStop a broken reply;
#     PendingWork yields when work is pending. Every other verdict passes.
# S3: the walk, inside to outside (LengthStop, EmptyStop, MarkupStop,
#     PendingWork): the first Director that does not pass decides;
#     Continue goes on with it, Yield makes the stop stand; with all
#     passing the stop stands.
# S4: the caps: 3 empty notes in a row.
# S5: full: at a cut reply, the window is what ran out (S7's test) and a
#     compaction can run. Rust gathers the window's facts only at a cut
#     reply: no other reply reads them.
# S6: the round note after `done` tool rounds of `max`: left = max - 1 -
#     done (0 at least): the rounds whose results the model still reads.
#     A note when left <= 10: none left, 1 left, or <left> left.
# S7: a length stop that LengthStop continues climbs a ladder: when the
#     window ran out (a window is known, the output is below the model's
#     catalog max output, prompt + output + 8192 >= window) and a
#     compaction can run (full), compact and send again (no note); else,
#     under the cap of `long` length notes in a row, the next note; else,
#     once, when a level below the agent's exists, the next note with the
#     request one thinking level lower; else the run fails. A continued
#     reply with text is full, so it compacts.

import Base
import ../../bend/stop.bend as S
import ../../bend/run/decision.bend as RnDecision

# S2: the verdicts
# ----------------

def go_if(b: Bool) -> S.Verdict:
  match b:
    case True{}:
      S.Continue{}
    case False{}:
      S.Pass{}

def cut_verdict(text: Bool, full: Bool) -> S.Verdict:
  match text:
    case False{}:
      S.Continue{}
    case True{}:
      match full:
        case True{}:
          S.Continue{}
        case False{}:
          S.Yield{}

def verdict(d: S.Dir, f: S.Facts) -> S.Verdict:
  match d:
    case S.LengthStop{}:
      match f:
        case S.Facts{cut, text, broken, pending, full}:
          match cut:
            case True{}:
              cut_verdict(text, full)
            case False{}:
              S.Pass{}
    case S.EmptyStop{}:
      match f:
        case S.Facts{cut, text, broken, pending, full}:
          match text:
            case True{}:
              S.Pass{}
            case False{}:
              S.Continue{}
    case S.MarkupStop{}:
      match f:
        case S.Facts{cut, text, broken, pending, full}:
          go_if(broken)
    case S.PendingWork{}:
      match f:
        case S.Facts{cut, text, broken, pending, full}:
          match pending:
            case True{}:
              S.Yield{}
            case False{}:
              S.Pass{}

# S3: the walk
# ------------

# a cut reply: kept (the stop stands) when it has text and is not full
def cut_pick(text: Bool, full: Bool) -> S.Pick:
  match text:
    case False{}:
      S.Goes{S.LengthStop{}}
    case True{}:
      match full:
        case True{}:
          S.Goes{S.LengthStop{}}
        case False{}:
          S.Stands{}

def pick(f: S.Facts) -> S.Pick:
  match f:
    case S.Facts{cut, text, broken, pending, full}:
      match cut:
        case True{}:
          cut_pick(text, full)
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

# S4: the caps
# ------------

def empty_cap() -> Nat:
  3n

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

# S7: the ladder of a length stop
# -------------------------------

# the window ran out: a window is known, the output is below the catalog
# max output, and the prompt and the output reach the window within 8192
# tokens
def ran_out(+window: Nat, +catalog: Nat, +prompt: Nat, +out: Nat) -> Bool:
  match window:
    case 0n:
      False{}
    case 1n+w:
      Bool.and(Nat.is_lt(out, catalog), Nat.is_le(1n+w, Nat.add(Nat.add(prompt, out), 8192n)))

# S5: full: the window ran out and a compaction can run
def full(+window: Nat, +catalog: Nat, +prompt: Nat, +out: Nat, cuttable: Bool) -> Bool:
  Bool.and(cuttable, ran_out(window, catalog, prompt, out))

# S1, S5: the facts of the stop Rust describes: what the reply holds, and
# the window's facts at a cut reply
def facts(cut: Bool, text: Bool, broken: Bool, pending: Bool, +window: Nat, +catalog: Nat, +prompt: Nat, +out: Nat, cuttable: Bool) -> S.Facts:
  S.Facts{cut, text, broken, pending, full(window, catalog, prompt, out, cuttable)}

def at_cap(lowers: Bool, +n: Nat) -> RnDecision.Help:
  match lowers:
    case True{}:
      RnDecision.Lowers{1n+n}
    case False{}:
      RnDecision.Quits{}

def under(lt: Bool, lower: Bool, +n: Nat, +long: Nat) -> RnDecision.Help:
  match lt:
    case True{}:
      RnDecision.Redoes{1n+n}
    case False{}:
      at_cap(Bool.and(lower, Nat.is_eq(n, long)), n)

# the rung after n length notes in a row, of the cap `long`: compact when
# the window ran out and a compaction can run (shrink); else the next note
# under the cap; else, when a level below the agent's exists and n is the
# cap, the next note one level lower; else the run fails
def ladder(shrink: Bool, lower: Bool, +n: Nat, +long: Nat) -> RnDecision.Help:
  match shrink:
    case True{}:
      RnDecision.Compacts{}
    case False{}:
      under(Nat.is_lt(n, long), lower, n, long)

# a rung remains: a compaction, a note under the cap, or the lower note
def rung_left(shrink: Bool, lower: Bool, +n: Nat, +long: Nat) -> Bool:
  Bool.or(shrink, Bool.or(Nat.is_lt(n, long), Bool.and(lower, Nat.is_eq(n, long))))
