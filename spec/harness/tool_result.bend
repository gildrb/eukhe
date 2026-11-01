# tool_result (spec): the blocks a tool result sends to a provider that
# takes only text in a result marked as an error (Anthropic Messages:
# "all content must be type `text` if `is_error` is true"; the same models
# on Bedrock Converse), restated without the code (bend/tool_result.bend):
# one block at a time, where the code plans per block and then applies the
# plan. The laws of area tool_result (laws/tool_result.bend) state that the
# code refines it. A spec: the shipped code never calls it; it uses only
# the block type of bend/tool_result.bend.
#
# S1: an error result sends only text blocks: each text block as it is,
#     each image as exactly one text block "[image omitted: error result]",
#     in the result's order: nothing dropped, added or moved.
# S2: a successful result sends every block as it is, images included.

import Base
import ../../bend/tool_result.bend as Tr

# S1: the text an image of an error result is sent as
def line() -> String:
  "[image omitted: error result]"

# S1, S2: the block an image sends: the line in an error result, else
# the image
def pic(err: Bool, i: Nat) -> Tr.Blk:
  match err:
    case True{}:
      Tr.Txt{line()}
    case False{}:
      Tr.Pic{i}

# S1, S2: the block one block of a result sends
def block(+err: Bool, b: Tr.Blk) -> Tr.Blk:
  match b:
    case Tr.Txt{s}:
      Tr.Txt{s}
    case Tr.Pic{i}:
      pic(err, i)

# S1, S2: the blocks a result sends, one per block, in order
def sent(+err: Bool, bs: List<&2, Tr.Blk>) -> List<&2, Tr.Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> t:
      block(err, b) <> sent(err, t)

def is_text(b: Tr.Blk) -> Bool:
  match b:
    case Tr.Txt{s}:
      True{}
    case Tr.Pic{i}:
      False{}

# S1: every block of bs is a text block
def all_text(bs: List<&2, Tr.Blk>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case b <> t:
      Bool.and(is_text(b), all_text(t))
