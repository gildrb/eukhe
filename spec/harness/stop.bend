# stop (spec): the Directors at a candidate stop of the run loop (omp2
# ADR 0015: at a stop the loop walks its Directors inside to outside,
# each saying Pass, Continue or Yield), restated without the code
# (bend/stop.bend): the walk as one decision per case, where the code
# walks a list of Directors and their verdicts; the tables as lists of
# phrases, where the code builds them. The laws of area stop
# (laws/stop.bend) state that the code refines it. A spec: the shipped
# code never calls it.
#
# S1: a candidate stop is a reply with no tool call; its facts: cut (the
#     stop reason is length), text (a text block that is not blank),
#     broken (tool-call markup in the text that the harness could not
#     read), pending (the session owns running work: jobs, children,
#     workflow runs), said (its text).
# S2: the end of a reply is its last 400 chars (all of it when shorter),
#     folded (laws/text_pat.bend: A-Z as a-z, the Kelvin sign as k, the
#     long s as s). It announces a next step when it holds, starting a
#     word (laws/phrase.bend: the char before is no ASCII letter, digit or
#     `_`, or there is none), one of: "i'll ", "we'll ", "i'm going to ",
#     "i'm about to ", "let's " (each with the apostrophe ' and with ’),
#     "i will ", "we will ", "i am going to ", "let me ", "next, i ",
#     "next i ", "now running", "now i ", "then i ". It asks the user when
#     it holds a question mark (? or the fullwidth ？) anywhere, or,
#     starting a word, one of: "let me know", "let us know", "would you
#     like", "do you want", "should i ", "shall i ", "please confirm",
#     "can you confirm", "your call".
# S3: the verdicts: LengthStop continues a cut reply, EmptyStop a reply
#     with no text, MarkupStop a broken reply, UnexpectedStop a reply that
#     announces a next step and asks the user nothing; PendingWork yields
#     when work is pending. Every other verdict passes.
# S4: the walk, inside to outside (LengthStop, EmptyStop, MarkupStop,
#     PendingWork, UnexpectedStop): the first Director that does not pass
#     decides; Continue goes on with it, Yield makes the stop stand; with
#     all passing the stop stands.
# S5: the caps: 3 empty notes in a row, 3 stop notes in a row.
# S6: the notes: "Harness note, attempt <a>: " then, for a cut reply with
#     text, "your previous reply hit <limit> before it finished, ..." with
#     "Length note <row> of <cap>."; for an announced step, "you announced
#     more work but ended the turn. ..." with "Stop note <row> of 3.";
#     <limit> is "the output limit" for 0 tokens, else "the <tokens>-token
#     output limit".
# S7: the round note after `done` tool rounds of `max`: left = max - 1 -
#     done (0 at least): the rounds whose results the model still reads.
#     A note when left <= 10: none left, 1 left, or <left> left.

import Base
import ../../bend/stop.bend as S
import ../../bend/phrase.bend as P
import ../../laws/text_pat.bend as TextPat
import ../../laws/phrase.bend as Phrase

# S2: the end of a reply
# ----------------------

def drop(k: Nat, s: String) -> String:
  match k s:
    case 0n s:
      s
    case 1n+j SNil{}:
      SNil{}
    case 1n+j SCon{c, t}:
      drop(j, t)

def tail(+s: String) -> String:
  drop(Nat.sub(String.length(s), 400n), s)

def heard(+said: String) -> String:
  TextPat.sp_fold(tail(said))

# the chars of s, one item each, before rest
def chars(s: String, rest: List<&2, P.It>) -> List<&2, P.It>:
  match s:
    case SNil{}:
      rest
    case SCon{+c, t}:
      P.One{P.CIn{Char.to_u32(c), Char.to_u32(c)}} <> chars(t, rest)

# each text of xs, starting a word
def word_starts(xs: List<&2, String>) -> List<&2, P.Ph>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      P.Ph{P.EWord{}, chars(x, []), P.EFree{}} <> word_starts(t)

def promise_table() -> List<&2, P.Ph>:
  word_starts(["i'll ", "i’ll ", "we'll ", "we’ll ", "i'm going to ", "i’m going to ", "i'm about to ", "i’m about to ", "let's ", "let’s ", "i will ", "we will ", "i am going to ", "let me ", "next, i ", "next i ", "now running", "now i ", "then i "])

def ask_table() -> List<&2, P.Ph>:
  P.Ph{P.EFree{}, chars("?", []), P.EFree{}} <> P.Ph{P.EFree{}, chars("？", []), P.EFree{}} <> word_starts(["let me know", "let us know", "would you like", "do you want", "should i ", "shall i ", "please confirm", "can you confirm", "your call"])

def promises(+said: String) -> Bool:
  Phrase.sp_any(heard(said), promise_table())

def asks(+said: String) -> Bool:
  Phrase.sp_any(heard(said), ask_table())

# S3: the verdicts
# ----------------

def go_if(b: Bool) -> S.Verdict:
  match b:
    case True{}:
      S.Continue{}
    case False{}:
      S.Pass{}

# an announced step: asked, the user decides (Pass); else Continue when
# the reply announces a next step
def unexpected(ask: Bool, promise: Bool) -> S.Verdict:
  match ask:
    case True{}:
      S.Pass{}
    case False{}:
      go_if(promise)

def verdict(d: S.Dir, f: S.Facts) -> S.Verdict:
  match d:
    case S.LengthStop{}:
      match f:
        case S.Facts{cut, text, broken, pending, said}:
          go_if(cut)
    case S.EmptyStop{}:
      match f:
        case S.Facts{cut, text, broken, pending, said}:
          match text:
            case True{}:
              S.Pass{}
            case False{}:
              S.Continue{}
    case S.MarkupStop{}:
      match f:
        case S.Facts{cut, text, broken, pending, said}:
          go_if(broken)
    case S.PendingWork{}:
      match f:
        case S.Facts{cut, text, broken, pending, said}:
          match pending:
            case True{}:
              S.Yield{}
            case False{}:
              S.Pass{}
    case S.UnexpectedStop{}:
      match f:
        case S.Facts{cut, text, broken, pending, +said}:
          unexpected(asks(said), promises(said))

# S4: the walk
# ------------

def announced(ask: Bool, promise: Bool) -> S.Pick:
  match ask:
    case True{}:
      S.Stands{}
    case False{}:
      match promise:
        case True{}:
          S.Goes{S.UnexpectedStop{}}
        case False{}:
          S.Stands{}

def pick(f: S.Facts) -> S.Pick:
  match f:
    case S.Facts{cut, text, broken, pending, +said}:
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
                  match pending:
                    case True{}:
                      S.Stands{}
                    case False{}:
                      announced(asks(said), promises(said))

# S5: the caps
# ------------

def empty_cap() -> Nat:
  3n

def promise_cap() -> Nat:
  3n

# S6: the notes
# -------------

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
    case S.Promised{r}:
      String.concat(["Harness note, attempt ", Nat.show(a), ": you announced more work but ended the turn. The task is incomplete: call the next concrete tool now. If the task is done, give the final answer without announcing more work. Stop note ", Nat.show(r), " of 3."])

# S7: the round note
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
