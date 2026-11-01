# tool_result: the blocks a tool result sends to a provider that takes only
# text in a result marked as an error (Rust: eukhe-ai
# api/anthropic_messages/params.rs convert_tool_result, Anthropic Messages:
# "all content must be type `text` if `is_error` is true", a 400 that stays
# in the transcript and fails every later request of the session;
# api/bedrock_converse_stream/convert.rs convert_tool_result_content, the
# same models on Bedrock Converse). An error result sends every text block
# unchanged and each image as the text line "[image omitted: error
# result]", in order; a successful result sends its blocks unchanged.
#
# Rust asks the plan (`plan`, through bend/ffi_tool_result.bend): one
# answer per block, keep it or send it as a text line; it then applies the
# answers to its blocks (`apply`). `sent` is that composition: the blocks
# Rust sends. Pure: no IO, no @unsafe.

import Base

# a block of a tool result's content: a text with its chars, or an image
# (abstract: `id` tells images apart, its bytes never matter here)
type Blk is Data:
  Txt{text: String}
  Pic{id: Nat}

# the answer for one block: send it as it is, or as a text line
type Out is Data:
  Keep{}
  Omit{line: String}

# the line an image of an error result becomes
def omitted() -> String:
  "[image omitted: error result]"

# Plan
# ----

# the answer for one block: an image of an error result becomes the line
def plan.one(img: Bool, err: Bool) -> Out:
  match img:
    case True{}:
      match err:
        case True{}:
          Omit{omitted()}
        case False{}:
          Keep{}
    case False{}:
      Keep{}

# one answer per block, in order: `imgs` says which blocks are images
def plan(+err: Bool, imgs: List<&2, Bool>) -> List<&2, Out>:
  match imgs:
    case Nil{}:
      Nil{}
    case i <> t:
      plan.one(i, err) <> plan(err, t)

# Apply (what Rust does with the answers)
# -----

def is_pic(b: Blk) -> Bool:
  match b:
    case Txt{s}:
      False{}
    case Pic{i}:
      True{}

# which blocks of bs are images, in order
def kinds(bs: List<&2, Blk>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> t:
      is_pic(b) <> kinds(t)

def apply.one(b: Blk, o: Out) -> Blk:
  match o:
    case Keep{}:
      b
    case Omit{s}:
      Txt{s}

# each block with its answer, in order (Rust refuses a reply whose count
# is not the blocks')
def apply(bs: List<&2, Blk>, os: List<&2, Out>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> t:
      match os:
        case Nil{}:
          Nil{}
        case o <> u:
          apply.one(b, o) <> apply(t, u)

# the blocks a tool result sends: its blocks with the plan's answers
def sent(+err: Bool, +bs: List<&2, Blk>) -> List<&2, Blk>:
  apply(bs, plan(err, kinds(bs)))
