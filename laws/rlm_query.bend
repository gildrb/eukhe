# eukhe: the laws of area rlm_query

import Base
import ../bend/rlm_query.bend as Rq
import ../bend/ffi_rlm_query.bend as FRq
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/rlm/query.bend as QSpec

# (Q1) rlm.query: admission and result cut
# ----------------------------------------
# bend/rlm_query.bend, run as the compiled core by bend/ffi_rlm_query.bend
# (eukhe-bend rules/rlm_query.rs; asked by eukhe-core for rlm.query and
# rlm.query_batch). The spec is spec/rlm/query.bend (S1-S4).
# Every input is free: any running count, cap, width, budget, spent bytes,
# sizes, limit and text.
#
# R1: the decision on a batch is the spec's (S1-S3): the code refines it.
#     The budget is checked first, then the cap; an admitted batch runs in
#     waves that never put more than the cap's room (nor the caller's
#     width) at once, and plan every call of the batch exactly once.
# R2: the refusal texts, byte for byte, as the host's contract states them
#     (rq_text: the texts crates/eukhe-bend/src/rules/rlm_query.rs and
#     crates/eukhe-core/src/durable/rlm/tests/query.rs expect); the entry's
#     reply carries them for every refusal (rlm_query_entry_answers).
# R3: the cut of a result is the spec's (S4): whole chars, at most the
#     limit in UTF-8 bytes, the longest such prefix; a text cut in pieces
#     cuts as the whole text (the host sends a long text in pieces).
# R4: the entry answers each request Rust writes (tag 0: the running count,
#     the cap, the width, the budget, the spent bytes, then the sizes as
#     List<Nat>; tag 1: the limit, then the text; every number, count and
#     length within the wire) with the decision (plan: 0 then the waves |
#     1 then the refusal's text; cut: 0 | 1 then the bytes kept), reads
#     exactly the request and nothing after it, and answers any other
#     input with the exact error form `E rlm_query: malformed request`.

# Spec helpers
# ------------

# a plan admits
def rq_admitted(p: Rq.Plan) -> Bool:
  match p:
    case Rq.Waves{ws}:
      True{}
    case Rq.Refused{f}:
      False{}

# every wave holds a call, and r running plus the wave stay within the cap c
def rq_capped(+r: Nat, +c: Nat, ws: List<&2, Nat>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Bool.and(Nat.is_lt(0n, x), Nat.is_le(Nat.add(r, x), c)), rq_capped(r, c, t))

# every wave is at most w
def rq_narrow(+w: Nat, ws: List<&2, Nat>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(Nat.is_le(x, w), rq_narrow(w, t))

# R2: the text of a refusal
def rq_text(f: Rq.Refusal) -> String:
  match f:
    case Rq.OverBudget{t, l, b}:
      String.append("rlm.query needs ", String.append(Nat.show(t), String.append(" bytes of input; the session's query budget has ", String.append(Nat.show(l), String.append(" of ", String.append(Nat.show(b), " bytes left (rlm.queryBudgetBytes)"))))))
    case Rq.Full{c}:
      String.append("rlm.query concurrency limit ", String.append(Nat.show(c), " is already full"))

# R3: a cut of the text after n bytes of text before it
def rq_shift(+n: Nat, x: Rq.Trim) -> Rq.Trim:
  match x:
    case Rq.Fits{}:
      Rq.Fits{}
    case Rq.CutAt{k}:
      Rq.CutAt{Nat.add(n, k)}

# R3: the cut of a ++ b under m, from the cut of a: a cut of a stands; a
# that fits leaves its bytes' room to b
def rq_cut_then(x: Rq.Trim, +m: Nat, +a: String, b: String) -> Rq.Trim:
  match x:
    case Rq.Fits{}:
      rq_shift(QSpec.utf8(a), Rq.cut(Nat.sub(m, QSpec.utf8(a)), b))
    case Rq.CutAt{k}:
      Rq.CutAt{k}

# R4: the spelling of a request and of its reply

def rq_w_req(q: FRq.Req, rest: String) -> String:
  match q:
    case FRq.QPlan{r, c, w, b, u, +ss}:
      Wr.put_nat(0n, Wr.put_nat(r, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(u, LawsBase.wire_spell_nats(ss, rest)))))))
    case FRq.QCut{m, t}:
      Wr.put_nat(1n, Wr.put_nat(m, Wr.put_str(t, rest)))

def rq_w_plan(p: Rq.Plan) -> String:
  match p:
    case Rq.Waves{+ws}:
      Wr.put_nat(0n, LawsBase.wire_spell_nats(ws, ""))
    case Rq.Refused{f}:
      Wr.put_nat(1n, Wr.put_str(rq_text(f), ""))

def rq_w_trim(x: Rq.Trim) -> String:
  match x:
    case Rq.Fits{}:
      Wr.put_nat(0n, "")
    case Rq.CutAt{k}:
      Wr.put_nat(1n, Wr.put_nat(k, ""))

def rq_w_reply(q: FRq.Req) -> String:
  match q:
    case FRq.QPlan{+r, +c, +w, +b, +u, +ss}:
      rq_w_plan(QSpec.plan(r, c, w, b, u, ss))
    case FRq.QCut{+m, +t}:
      rq_w_trim(QSpec.cut(m, t))

# every number, count and length of the request fits the wire
def rq_fit_req(q: FRq.Req) -> Bool:
  match q:
    case FRq.QPlan{r, c, w, b, u, +ss}:
      Bool.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(u), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ss)), LawsBase.wire_nats_fit(ss)))))))
    case FRq.QCut{m, +t}:
      Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(t)))

# Laws: the plan (R1, R2)
# -----------------------

# LAW rlm_query_plan_spec (R1, S1-S3): the decision on every batch is the
# spec's
# EXCLUDES: the cap checked before the budget, the budget compared with
#   >= or without the spent bytes, a budget of 0 read as spent, waves of
#   the cap instead of its room, the width ignored or read as a minimum,
#   a lost or extra last wave, another total, left or cap named
law rlm_query_plan_spec:
  for +r: Nat
  for +c: Nat
  for +w: Nat
  for +b: Nat
  for +u: Nat
  for +sizes: List<&2, Nat>
  {Rq.plan(r, c, w, b, u, sizes) == QSpec.plan(r, c, w, b, u, sizes) : Rq.Plan}

# LAW rlm_query_budget_refuses (R1, S1): a batch whose bytes, with the
# spent ones, pass a set budget is refused for the budget, naming its
# bytes, what is left and the budget, whatever the running count, cap
# and width
# EXCLUDES: the cap refusal hiding the budget, the left bytes not
#   saturated or swapped with the total, a batch over budget admitted
law rlm_query_budget_refuses:
  for +r: Nat
  for +c: Nat
  for +w: Nat
  for +b: Nat
  for +u: Nat
  for +sizes: List<&2, Nat>
  for set: {Nat.is_lt(0n, b) == True{} : Bool}
  for over: {Nat.is_lt(b, Nat.add(u, QSpec.total(sizes))) == True{} : Bool}
  {Rq.plan(r, c, w, b, u, sizes) == Rq.Refused{Rq.OverBudget{QSpec.total(sizes), Nat.sub(b, u), b}} : Rq.Plan}

# LAW rlm_query_full_refuses (R1, S2): within the budget (or none), a
# session whose running queries fill the cap is refused for it
# EXCLUDES: a batch admitted past the cap, another cap named, a cap of 0
#   read as no cap
law rlm_query_full_refuses:
  for +r: Nat
  for +c: Nat
  for +w: Nat
  for +b: Nat
  for +u: Nat
  for +sizes: List<&2, Nat>
  for within: {Bool.or(Nat.is_eq(b, 0n), Nat.is_le(Nat.add(u, QSpec.total(sizes)), b)) == True{} : Bool}
  for full: {Nat.is_le(c, r) == True{} : Bool}
  {Rq.plan(r, c, w, b, u, sizes) == Rq.Refused{Rq.Full{c}} : Rq.Plan}

# LAW rlm_query_admits (R1, S1-S3): within the budget (or none) and below
# the cap, a batch is admitted
# EXCLUDES: a refusal of a batch that fits (a budget exactly met refused,
#   an off-by-one cap)
law rlm_query_admits:
  for +r: Nat
  for +c: Nat
  for +w: Nat
  for +b: Nat
  for +u: Nat
  for +sizes: List<&2, Nat>
  for within: {Bool.or(Nat.is_eq(b, 0n), Nat.is_le(Nat.add(u, QSpec.total(sizes)), b)) == True{} : Bool}
  for room: {Nat.is_lt(r, c) == True{} : Bool}
  {rq_admitted(Rq.plan(r, c, w, b, u, sizes)) == True{} : Bool}

# LAW rlm_query_cap_bound (R1, S3): every wave of an admitted batch holds
# a call, and the running calls plus the wave stay within the cap
# EXCLUDES: waves of the cap that ignore the running calls, an empty wave,
#   a first wave past the cap's room
law rlm_query_cap_bound:
  for +r: Nat
  for +c: Nat
  for +w: Nat
  for +b: Nat
  for +u: Nat
  for +sizes: List<&2, Nat>
  for +ws: List<&2, Nat>
  for e: {Rq.plan(r, c, w, b, u, sizes) == Rq.Waves{ws} : Rq.Plan}
  {rq_capped(r, c, ws) == True{} : Bool}

# LAW rlm_query_width_bound (R1, S3): with a width, every wave of an
# admitted batch is at most it
# EXCLUDES: the caller's concurrency= ignored, the width read as a minimum
law rlm_query_width_bound:
  for +r: Nat
  for +c: Nat
  for +w: Nat
  for +b: Nat
  for +u: Nat
  for +sizes: List<&2, Nat>
  for +ws: List<&2, Nat>
  for set: {Nat.is_lt(0n, w) == True{} : Bool}
  for e: {Rq.plan(r, c, w, b, u, sizes) == Rq.Waves{ws} : Rq.Plan}
  {rq_narrow(w, ws) == True{} : Bool}

# LAW rlm_query_covers (R1, S3): the waves of an admitted batch plan every
# call exactly once: they add up to the batch (in order: each wave is the
# next run of calls)
# EXCLUDES: a lost last wave, a call planned twice, a wave per call
#   counted wrong
law rlm_query_covers:
  for +r: Nat
  for +c: Nat
  for +w: Nat
  for +b: Nat
  for +u: Nat
  for +sizes: List<&2, Nat>
  for +ws: List<&2, Nat>
  for e: {Rq.plan(r, c, w, b, u, sizes) == Rq.Waves{ws} : Rq.Plan}
  {QSpec.total(ws) == List.length(&2, Nat, sizes) : Nat}

# LAW rlm_query_plan_example (R1): anchor: ten calls under the cap 4 run
# 4, 4, 2; with width 3, 3, 3, 3, 1; with 3 of 4 running, one at a time;
# 10 bytes with 4 spent of 10 are refused for the budget; a full cap is
# refused; no calls, no waves
# EXCLUDES: a spec that drifts from the host's contract
law rlm_query_plan_example:
  {[Rq.plan(0n, 4n, 0n, 0n, 0n, [1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n]), Rq.plan(0n, 4n, 3n, 0n, 0n, [1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n]), Rq.plan(3n, 4n, 0n, 0n, 0n, [1n, 1n, 1n]), Rq.plan(0n, 4n, 0n, 10n, 4n, [5n, 5n]), Rq.plan(0n, 4n, 0n, 10n, 4n, [3n, 3n]), Rq.plan(4n, 4n, 0n, 0n, 0n, [1n]), Rq.plan(0n, 4n, 0n, 0n, 0n, [])] == [Rq.Waves{[4n, 4n, 2n]}, Rq.Waves{[3n, 3n, 3n, 1n]}, Rq.Waves{[1n, 1n, 1n]}, Rq.Refused{Rq.OverBudget{10n, 6n, 10n}}, Rq.Waves{[2n]}, Rq.Refused{Rq.Full{4n}}, Rq.Waves{[]}] : List<&2, Rq.Plan>}

# LAW rlm_query_text_example (R2): anchor: the texts the host shows
# EXCLUDES: a text that drifts from the host's contract
law rlm_query_text_example:
  {[Rq.text(Rq.OverBudget{10n, 6n, 10n}), Rq.text(Rq.Full{4n})] == ["rlm.query needs 10 bytes of input; the session's query budget has 6 of 10 bytes left (rlm.queryBudgetBytes)", "rlm.query concurrency limit 4 is already full"] : List<&2, String>}

# Laws: the cut (R3)
# ------------------

# LAW rlm_query_cut_spec (R3, S4): the cut of every text under every limit
# is the spec's
# EXCLUDES: a cut inside a char, a cut counted in chars, a cut short of
#   the longest prefix that fits, a text that fits cut
law rlm_query_cut_spec:
  for +m: Nat
  for +t: String
  {Rq.cut(m, t) == QSpec.cut(m, t) : Rq.Trim}

# LAW rlm_query_cut_within (R3, S4): a cut keeps at most the limit
# EXCLUDES: a cut after the char that passes the limit
law rlm_query_cut_within:
  for +m: Nat
  for +t: String
  for +k: Nat
  for e: {Rq.cut(m, t) == Rq.CutAt{k} : Rq.Trim}
  {Nat.is_le(k, m) == True{} : Bool}

# LAW rlm_query_cut_append (R3): the cut of a ++ b is the cut of a when a
# is cut, else b's cut in the room a leaves, after a's bytes: so the host
# may send a long text in pieces
# EXCLUDES: a cut that depends on how the text was split, the room of b
#   not less a's bytes
law rlm_query_cut_append:
  for +m: Nat
  for +a: String
  for +b: String
  {Rq.cut(m, String.append(a, b)) == rq_cut_then(Rq.cut(m, a), m, a, b) : Rq.Trim}

# LAW rlm_query_cut_example (R3, S4): anchor: "héllo" under 2 keeps "h";
# "ab" under 2 fits; an emoji past the limit is dropped whole; the chars
# U+7F, U+80, U+7FF, U+800, U+FFFF, U+10000 take 1, 2, 2, 3, 3, 4 bytes
# EXCLUDES: another UTF-8 width table (each width is pinned by a limit at
#   its prefix's bytes)
law rlm_query_cut_example:
  {[Rq.cut(2n, "héllo"), Rq.cut(2n, "ab"), Rq.cut(3n, "a😀"), Rq.cut(0n, "a"), Rq.cut(1n, SCon{Chr{127}, SCon{Chr{128}, SCon{Chr{2047}, SCon{Chr{2048}, SCon{Chr{65535}, SCon{Chr{65536}, SNil{}}}}}}}), Rq.cut(4n, SCon{Chr{127}, SCon{Chr{128}, SCon{Chr{2047}, SCon{Chr{2048}, SCon{Chr{65535}, SCon{Chr{65536}, SNil{}}}}}}}), Rq.cut(5n, SCon{Chr{127}, SCon{Chr{128}, SCon{Chr{2047}, SCon{Chr{2048}, SCon{Chr{65535}, SCon{Chr{65536}, SNil{}}}}}}}), Rq.cut(10n, SCon{Chr{127}, SCon{Chr{128}, SCon{Chr{2047}, SCon{Chr{2048}, SCon{Chr{65535}, SCon{Chr{65536}, SNil{}}}}}}}), Rq.cut(14n, SCon{Chr{127}, SCon{Chr{128}, SCon{Chr{2047}, SCon{Chr{2048}, SCon{Chr{65535}, SCon{Chr{65536}, SNil{}}}}}}}), Rq.cut(15n, SCon{Chr{127}, SCon{Chr{128}, SCon{Chr{2047}, SCon{Chr{2048}, SCon{Chr{65535}, SCon{Chr{65536}, SNil{}}}}}}})] == [Rq.CutAt{1n}, Rq.Fits{}, Rq.CutAt{1n}, Rq.CutAt{0n}, Rq.CutAt{1n}, Rq.CutAt{3n}, Rq.CutAt{5n}, Rq.CutAt{8n}, Rq.CutAt{11n}, Rq.Fits{}] : List<&2, Rq.Trim>}

# Laws: the entry (R4)
# --------------------

# LAW rlm_query_entry_answers (R4): the entry answers every request Rust
# spells, every number, count and length within the wire, with the spec's
# decision spelled
# EXCLUDES: fields read in another order, the budget and the spent bytes
#   swapped, a size lost, the tags swapped, a default
law rlm_query_entry_answers:
  for +q: FRq.Req
  for fit: {rq_fit_req(q) == True{} : Bool}
  {FRq.ffi(rq_w_req(q, "")) == rq_w_reply(q) : String}

# LAW rlm_query_entry_left_over (R4): a spelled request followed by more
# input answers the error form
# EXCLUDES: the input after the request ignored or read into a field
law rlm_query_entry_left_over:
  for +q: FRq.Req
  for +ch: Char
  for +t: String
  for fit: {rq_fit_req(q) == True{} : Bool}
  {FRq.ffi(rq_w_req(q, SCon{ch, t})) == Wr.err("rlm_query: malformed request") : String}

# LAW rlm_query_entry_reads (R4): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown tag, a
#   short field, a list shorter than its count, input left over)
law rlm_query_entry_reads:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FRq.ffi(s)) == False{} : Bool}
  exs q: FRq.Req
  {s == rq_w_req(q, "") : String} & {rq_fit_req(q) == True{} : Bool}

# LAW rlm_query_entry_malformed_exact (R4): every error the entry answers
# is exactly `E rlm_query: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law rlm_query_entry_malformed_exact:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FRq.ffi(s)) == True{} : Bool}
  {FRq.ffi(s) == Wr.err("rlm_query: malformed request") : String}

# LAW rlm_query_entry_example (R4): anchor: the wire strings Rust sends and
# the replies it reads
# EXCLUDES: another spelling of a request or of a reply
law rlm_query_entry_example:
  {[FRq.ffi("0,0,4,0,0,0,3,1,1,1,"), FRq.ffi("0,4,4,0,0,0,1,1,"), FRq.ffi("1,2,5,héllo"), FRq.ffi("1,2,2,ab"), FRq.ffi("1,2,5,héllo!"), FRq.ffi("2,"), FRq.ffi("0,0,4,0,0,0,2,1,")] == ["0,1,3,", "1,45,rlm.query concurrency limit 4 is already full", "1,1,", "0,", Wr.err("rlm_query: malformed request"), Wr.err("rlm_query: malformed request"), Wr.err("rlm_query: malformed request")] : List<&2, String>}
