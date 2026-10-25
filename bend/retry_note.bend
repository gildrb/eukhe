# retry_note: the note at the end of a retry's request (docs/harness.md
# H4.7, H4.8; the Rust host is
# crates/eukhe-durable/src/harness/generation/note.rs). After a noted reply
# the retry must not send the same request again: its request ends with a
# note that names the retry's attempt and what went wrong, and tells the
# model what to do instead. The model writes the note's text from the
# attempt and the cause. The host gives a repeated line already written as
# a quoted literal (Rust's `{:?}` of the line) and the cap of each recovery
# (LENGTH_NOTES, LEAK_NOTES, REDIRECT_NOTES of decide.rs). Pure: no IO, no
# @unsafe. laws/retry_note.bend states its laws.

import Base

# Types
# -----

# one call of a repeated round: its tool and its arguments (canonical JSON,
# cut by the host)
type Call is Data:
  Call{tool: String, args: String}

# what went wrong with the noted reply
type Cause is Data:
  # the repetition guard cut a cycle of `period` lines ending with `line`
  # (quoted)
  Repeated{period: Nat, line: String}
  # no text and no tool call
  NoAnswer{}
  # the output limit (`tokens`, 0: not reported) while still reasoning; the
  # length note `row` of `cap`
  Length{tokens: Nat, row: Nat, cap: Nat}
  # tool calls written as `markup` text that could not be read, for
  # `reason`; the leak note `row` of `cap`
  Leaked{markup: String, reason: String, row: Nat, cap: Nat}
  # the same `calls` would make `rounds` rounds in a row with the same
  # results; the redirect note `row` of `cap`
  Redirect{calls: List<&2, Call>, rounds: Nat, row: Nat, cap: Nat}
  # no stream event for `idle_ms`
  Stalled{idle_ms: Nat}

# Texts
# -----

# the limit a length note names
def limit(tokens: Nat) -> String:
  match tokens:
    case 0n:
      "the output limit"
    case 1n+t:
      String.concat(["the ", Nat.show(1n+t), "-token output limit"])

# "`tool` with `args`"
def call(c: Call) -> String:
  match c:
    case Call{t, a}:
      String.concat(["`", t, "` with `", a, "`"])

# the calls after the first, each after "; "
def calls.rest(cs: List<&2, Call>) -> String:
  match cs:
    case Nil{}:
      ""
    case c <> r:
      String.append("; ", String.append(call(c), calls.rest(r)))

# the calls, joined by "; "
def calls(cs: List<&2, Call>) -> String:
  match cs:
    case Nil{}:
      ""
    case c <> r:
      String.append(call(c), calls.rest(r))

def repeated.cycle(period: Nat, line: String) -> String:
  String.concat(["your previous reply repeated a cycle of ", Nat.show(period), " lines, ending with the line ", line, ", until it was cut. Give the answer again; never repeat the same lines."])

# one repeated line, or a cycle of several (0 never comes from the host;
# it reads as a cycle)
def repeated(period: Nat, line: String) -> String:
  match period:
    case 0n:
      repeated.cycle(0n, line)
    case 1n:
      String.concat(["your previous reply repeated the line ", line, " until it was cut. Give the answer again; never list the same item twice."])
    case 2n+p:
      repeated.cycle(2n+p, line)

# the calls made `rounds` times in a row, `listed`; the redirect note `row`
# of `cap`
def redirect(rounds: Nat, row: Nat, cap: Nat, listed: String) -> String:
  String.concat(["you made the same tool calls ", Nat.show(rounds), " times in a row, and they gave the same results each time: ", listed, ". The harness did not run them again. Do not make these calls with these arguments again in this turn. Use different arguments, use a different tool, or give your answer with what you found. Redirect note ", Nat.show(row), " of ", Nat.show(cap), "."])

# what went wrong, and what to do instead
def body(c: Cause) -> String:
  match c:
    case Repeated{p, l}:
      repeated(p, l)
    case NoAnswer{}:
      "your previous reply gave no text and no tool call. Give the answer again, as text or as a tool call."
    case Length{t, r, k}:
      String.concat(["your previous reply hit ", limit(t), " while it was still reasoning. It gave no text and no tool call, so the harness discarded it with every tool call that it planned. If you plan the whole task again in your reasoning, you hit the same limit. Reason only about the next step, then call its tool. For a large answer (a file, a document, a long text), write a minimal working version first, then extend it with more edits in later turns. Length note ", Nat.show(r), " of ", Nat.show(k), "."])
    case Leaked{m, why, r, k}:
      String.concat(["your previous reply wrote a tool call as ", m, " markup in its text, and the harness could not read it (", why, "). No tool ran. Make the call again through the tool-calling interface, with its arguments as one JSON object that agrees with the schema of the tool. Do not write a tool call as text. If you need no tool, give the answer as plain text. Leak note ", Nat.show(r), " of ", Nat.show(k), "."])
    case Redirect{cs, n, r, k}:
      redirect(n, r, k, calls(cs))
    case Stalled{ms}:
      String.concat(["your previous reply produced no output for ", Nat.show(Nat.div(ms, 1000n)), " s, so the harness cut it. Reason briefly, then act: give the answer or call the tool of the next step."])

# the text of the note of a retry of `attempt` for cause c
def text(attempt: Nat, c: Cause) -> String:
  String.append("Harness note, attempt ", String.append(Nat.show(attempt), String.append(": ", body(c))))
