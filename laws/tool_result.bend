# eukhe: the laws of area tool_result

import Base
import ../bend/tool_result.bend as Tr
import ../bend/ffi_tool_result.bend as FTr
import ../bend/wire.bend as Wr
import ../spec/harness/tool_result.bend as S
import ./base.bend as LawsBase

# (H8) An error tool result sends only text
# -----------------------------------------
# spec/README.md H8. bend/tool_result.bend: the blocks a tool result sends
# to Anthropic Messages (eukhe-ai api/anthropic_messages/params.rs) and
# Bedrock Converse (api/bedrock_converse_stream/convert.rs). Anthropic
# refuses a tool_result marked is_error that carries an image block ("all
# content must be type `text` if `is_error` is true"), and the result
# stays in the transcript, so every later request of the session failed
# with 400. The plan (one answer per block) runs as the compiled core by
# bend/ffi_tool_result.bend (eukhe-bend rules/tool_result.rs); Rust
# applies it to its blocks (Tr.apply), and Tr.sent is that composition.
# spec/harness/tool_result.bend restates the rule (S1, S2). Every input
# is free: any flag, any blocks, any text, any image.
#
# R1: an error result sends only text blocks: each text block unchanged
#     and in place, each image as exactly one text block "[image omitted:
#     error result]" in place; nothing dropped, added or moved (S1).
# R2: a successful result sends every block unchanged, images included
#     (S2).
# R3: the entry answers each request Rust writes (the count within the
#     wire) with the model's plan, one answer per block, reads exactly the
#     request and nothing after it, and answers any other input with the
#     exact error form `E tool_result: malformed request`.
# R4: the plan answers each block alone, in its place: an image of an
#     error result with exactly the line (R1), any text block and any
#     image of a successful result Keep (R1, R2), so Rust's application
#     of it sends R1 and R2.
# Not pinned here: the JSON each provider builds from the blocks (the
# Rust conversions; their regression tests pin it).

# Spec helpers
# ------------

# R3: the items of a list of Bools, each spelled, then rest
def sp_w_bools(xs: List<&2, Bool>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      Wr.put_bool(x, sp_w_bools(t, rest))

# R3: the spelling of a request: err, then the count of blocks, then one
# Bool per block (T an image)
def sp_w_req(q: FTr.Req, rest: String) -> String:
  match q:
    case FTr.Req{e, +ks}:
      Wr.put_bool(e, Wr.put_nat(List.length(&2, Bool, ks), sp_w_bools(ks, rest)))

# the count of blocks fits the wire
def sp_fit_req(q: FTr.Req) -> Bool:
  match q:
    case FTr.Req{e, ks}:
      LawsBase.wire_fits(List.length(&2, Bool, ks))

# R3: the items of a plan, each spelled (0: keep; 1, then the line), then
# rest
def sp_w_outs(os: List<&2, Tr.Out>, rest: String) -> String:
  match os:
    case Nil{}:
      rest
    case o <> t:
      match o:
        case Tr.Keep{}:
          Wr.put_nat(0n, sp_w_outs(t, rest))
        case Tr.Omit{l}:
          Wr.put_nat(1n, Wr.put_str(l, sp_w_outs(t, rest)))

# R3: the reply of a request: the model's plan, its count first
def sp_w_reply(q: FTr.Req) -> String:
  match q:
    case FTr.Req{e, ks}:
      +p = Tr.plan(e, ks)
      Wr.put_nat(List.length(&2, Tr.Out, p), sp_w_outs(p, ""))

# Laws: the blocks sent (R1, R2)
# ------------------------------

# LAW tool_result_spec (R1, R2): the blocks every result sends, error or
# not, are the spec's: each block on its own, in order
# EXCLUDES: any block sent other than the spec says (an image kept in an
#   error result, an image of a successful result dropped, a text changed,
#   a block dropped, added or moved)
law tool_result_spec:
  for +err: Bool
  for +bs: List<&2, Tr.Blk>
  {Tr.sent(err, bs) == S.sent(err, bs) : List<&2, Tr.Blk>}

# LAW tool_result_error_text_only (R1): every block an error result sends
# is a text block, whatever its content
# EXCLUDES: an image block in an error result (the 400 that failed every
#   later request of the session), an image kept when the result also has
#   text
law tool_result_error_text_only:
  for +bs: List<&2, Tr.Blk>
  {S.all_text(Tr.sent(True{}, bs)) == True{} : Bool}

# LAW tool_result_success_keeps (R2): a successful result sends exactly its
# blocks
# EXCLUDES: an image of a successful result dropped or replaced, a text
#   changed, a block reordered
law tool_result_success_keeps:
  for +bs: List<&2, Tr.Blk>
  {Tr.sent(False{}, bs) == bs : List<&2, Tr.Blk>}

# LAW tool_result_error_keeps_text (R1): in an error result, a text block
# is sent unchanged, in its place: the blocks before it send what they
# send alone, then the text, then what the blocks after it send alone
# EXCLUDES: a text of an error result changed, dropped, repeated or moved,
#   a block's answer that depends on its neighbours
law tool_result_error_keeps_text:
  for +pre: List<&2, Tr.Blk>
  for +s: String
  for +post: List<&2, Tr.Blk>
  {Tr.sent(True{}, List.append(&2, Tr.Blk, pre, Tr.Txt{s} <> post)) == List.append(&2, Tr.Blk, Tr.sent(True{}, pre), Tr.Txt{s} <> Tr.sent(True{}, post)) : List<&2, Tr.Blk>}

# LAW tool_result_error_image_line (R1): in an error result, an image is
# sent as exactly one text block "[image omitted: error result]", in its
# place
# EXCLUDES: an image of an error result dropped (its trace lost), sent as
#   two lines or another text, moved to the end
law tool_result_error_image_line:
  for +pre: List<&2, Tr.Blk>
  for +i: Nat
  for +post: List<&2, Tr.Blk>
  {Tr.sent(True{}, List.append(&2, Tr.Blk, pre, Tr.Pic{i} <> post)) == List.append(&2, Tr.Blk, Tr.sent(True{}, pre), Tr.Txt{S.line()} <> Tr.sent(True{}, post)) : List<&2, Tr.Blk>}

# LAW tool_result_count (R1, R2): every result sends as many blocks as it
# holds
# EXCLUDES: a block lost or invented, error or not
law tool_result_count:
  for +err: Bool
  for +bs: List<&2, Tr.Blk>
  {List.length(&2, Tr.Blk, Tr.sent(err, bs)) == List.length(&2, Tr.Blk, bs) : Nat}

# LAW tool_result_plan_one_each (R3): the plan answers exactly once per
# block, so Rust's check that the reply's count is the blocks' never
# refuses a reply of the core
# EXCLUDES: a plan that drops or adds an answer (Rust would then pair a
#   block with another block's answer, or panic)
law tool_result_plan_one_each:
  for +err: Bool
  for +ks: List<&2, Bool>
  {List.length(&2, Tr.Out, Tr.plan(err, ks)) == List.length(&2, Bool, ks) : Nat}

# LAW tool_result_example (R1, R2): anchor: the result of the Rust
# regression tests, the text "failed" then an image: as an error, the text
# then the line; as a success, both blocks unchanged
# EXCLUDES: a spec that drifts from the Rust it replaced
law tool_result_example:
  {(Tr.sent(True{}, [Tr.Txt{"failed"}, Tr.Pic{0n}]), Tr.sent(False{}, [Tr.Txt{"failed"}, Tr.Pic{0n}])) == ([Tr.Txt{"failed"}, Tr.Txt{"[image omitted: error result]"}], [Tr.Txt{"failed"}, Tr.Pic{0n}]) : List<&2, Tr.Blk> & List<&2, Tr.Blk>}

# Laws: the entry (R3)
# --------------------

# LAW tool_result_entry_is_model (R3): the entry answers every request Rust
# spells, the count within the wire, with the model's plan, spelled
# EXCLUDES: the flag ignored or inverted, an image read as a text, an
#   answer dropped or reordered, a default, another reply spelling
law tool_result_entry_is_model:
  for +q: FTr.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FTr.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW tool_result_entry_reads (R3): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law tool_result_entry_reads:
  for +q: FTr.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FTr.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FTr.Req>}

# LAW tool_result_entry_exact (R3): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (a missing flag, a
#   malformed count or block, input left over)
law tool_result_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FTr.ffi(s)) == False{} : Bool}
  exs r: FTr.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW tool_result_entry_refuses (R3): every error the entry answers is
# exactly `E tool_result: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law tool_result_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FTr.ffi(s)) == True{} : Bool}
  {FTr.ffi(s) == Wr.err("tool_result: malformed request") : String}

# LAW tool_result_entry_example (R3): anchor: the wire strings Rust sends
# and the replies it reads (an error result with a text and an image, the
# same as a success, no blocks); a malformed flag, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law tool_result_entry_example:
  {[FTr.ffi("T2,FT"), FTr.ffi("F2,FT"), FTr.ffi("T0,"), FTr.ffi("X0,"), FTr.ffi("T1,Fx")] == ["2,0,1,29,[image omitted: error result]", "2,0,0,", "0,", Wr.err("tool_result: malformed request"), Wr.err("tool_result: malformed request")] : List<&2, String>}

# Laws: the plan (R4)
# -------------------

# LAW tool_result_plan_error_image (R4, R1): in the plan of an error
# result, an image is answered with exactly the line "[image omitted:
# error result]", in its place: the blocks before it answered as they are
# alone, then the line, then the blocks after it as they are alone
# EXCLUDES: an image of an error result kept (after the first image, or
#   anywhere), dropped, answered with another line, an answer that depends
#   on the blocks around it
law tool_result_plan_error_image:
  for +pre: List<&2, Bool>
  for +post: List<&2, Bool>
  {Tr.plan(True{}, List.append(&2, Bool, pre, True{} <> post)) == List.append(&2, Tr.Out, Tr.plan(True{}, pre), Tr.Omit{S.line()} <> Tr.plan(True{}, post)) : List<&2, Tr.Out>}

# LAW tool_result_plan_text_keeps (R4, R1, R2): in the plan of every
# result, error or not, a text block is answered Keep, in its place
# EXCLUDES: a text block answered with the line or dropped, an answer that
#   depends on the blocks around it
law tool_result_plan_text_keeps:
  for +err: Bool
  for +pre: List<&2, Bool>
  for +post: List<&2, Bool>
  {Tr.plan(err, List.append(&2, Bool, pre, False{} <> post)) == List.append(&2, Tr.Out, Tr.plan(err, pre), Tr.Keep{} <> Tr.plan(err, post)) : List<&2, Tr.Out>}

# LAW tool_result_plan_success_image (R4, R2): in the plan of a
# successful result, an image is answered Keep, in its place
# EXCLUDES: a successful result's image omitted or dropped
law tool_result_plan_success_image:
  for +pre: List<&2, Bool>
  for +post: List<&2, Bool>
  {Tr.plan(False{}, List.append(&2, Bool, pre, True{} <> post)) == List.append(&2, Tr.Out, Tr.plan(False{}, pre), Tr.Keep{} <> Tr.plan(False{}, post)) : List<&2, Tr.Out>}

# LAW tool_result_entry_images_example (R4): anchor: error results with
# several images (two images; a text then two images) send every image as
# the line; the same success keeps both
# EXCLUDES: a plan that omits only the first image of an error result
law tool_result_entry_images_example:
  {[FTr.ffi("T2,TT"), FTr.ffi("T3,FTT"), FTr.ffi("F2,TT")] == ["2,1,29,[image omitted: error result]1,29,[image omitted: error result]", "3,0,1,29,[image omitted: error result]1,29,[image omitted: error result]", "2,0,0,"] : List<&2, String>}
