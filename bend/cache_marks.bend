# cache_marks: the cache-mark budget of one provider request (Rust:
# eukhe-ai api/cache_breakpoints.rs, asked by the Anthropic Messages,
# OpenAI-compatible and Bedrock Converse request builders). A request
# carries at most four cache marks. The marked user text blocks and the
# end-of-request mark are placed first; the provider's optional marks
# (system prompt, tools, the OAuth identity block) then take the slots
# left, in the provider's priority order, each only when the request
# wants it. More than three marked blocks is a caller bug: the request
# fails with a fixed text before it is sent. Pure: no IO, no @unsafe.

import Base

# Cache marks one request may carry (the Anthropic and Bedrock limit)
def marks() -> Nat:
  4n

# Marked blocks one request may carry: one slot stays for the end mark
def marked_max() -> Nat:
  3n

# Excess
# ------

def excess.of(over: Bool, +marked: Nat) -> Maybe<&2, String>:
  match over:
    case True{}:
      Some{String.concat(["Too many cache breakpoints: the request marks ", Nat.show(marked), " blocks, at most ", Nat.show(marked_max()), " are allowed"])}
    case False{}:
      None{}

# the error of a request that marks `marked` user text blocks, if too many
def excess(+marked: Nat) -> Maybe<&2, String>:
  excess.of(Nat.is_lt(marked_max(), marked), marked)

# Budget
# ------

# each wanted mark, in order, while `free` slots are left
def grant.go(wants: List<&2, Bool>, free: Nat) -> List<&2, Bool>:
  match wants:
    case Nil{}:
      Nil{}
    case w <> t:
      match w:
        case False{}:
          False{} <> grant.go(t, free)
        case True{}:
          match free:
            case 0n:
              False{} <> grant.go(t, 0n)
            case 1n+f:
              True{} <> grant.go(t, f)

# which optional marks the request carries, after `placed` marks on its
# messages (the marked blocks and the end mark): one answer per wanted
# mark, in the provider's priority order
def grant(+placed: Nat, wants: List<&2, Bool>) -> List<&2, Bool>:
  grant.go(wants, Nat.sub(marks(), placed))
