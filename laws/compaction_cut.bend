# eukhe: the laws of area compaction_cut

import Base
import ../bend/context_order.bend as Co
import ../bend/compaction_cut.bend as Cc
import ../bend/ffi_compaction_cut.bend as FCc
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./context_order.bend as ContextOrder

# LAWS (R1-R3): where a compaction cuts the model context of one
# conversation and what the summarizer's answer is
# (bend/compaction_cut.bend, the port of eukhe-durable
# harness/compaction/range.rs `select_cut` with `is_candidate`, and
# compaction/prompt.rs `summary_text` and `summary_failure`). Each law is
# an open claim about Cc.cands, Cc.cut or Cc.summary; PROOF.bend proves
# them (as CompactionCut.<law>) with the lemmas of proof/compaction_cut/.
#
# The host gives each contribution of the context (the head marker's
# first when there is one) as its estimated tokens and its messages'
# facts (laws/context_order.bend: user, system, an assistant answer with
# its stop reason and call ids, a tool result with its call id; ids
# interned, free), and the limit: Below{k} (keep walking while fewer
# than k tokens are kept) or Never.
#
# R1: walking back from the last contribution to the first one after the
#     head marker (the first one when there is none), the tokens of the
#     contributions walked add up; the walk stops at the first
#     contribution where they reach k (none under Never or when they
#     never do).
# R2: a contribution is a candidate when its first message is an
#     assistant answer, or when it is a user message and either the last
#     assistant answer before it (in any earlier contribution) has no
#     call, or no result of one of its calls comes from this contribution
#     on before the next assistant answer. A contribution that starts with
#     a system message or a tool result, or has no message, is no
#     candidate. Only contributions after the head marker count.
# R3: the cut is the first candidate at or after where the walk stopped,
#     else the last candidate; none when the walk never stops, when there
#     is no candidate, or when no contribution after the marker and
#     before the cut has a message.
# R4: the summarizer's answer (its stop reason, whether it called a tool,
#     whether its trimmed text is not blank, its error message) is a
#     summary when it stopped as stop, called no tool and has text; else
#     a failure: an error or aborted answer "Summarization failed: " and
#     its error message, else its stop reason ("error", "aborted"); a
#     length answer "Summarization hit the token limit; the summary is
#     incomplete"; one that called a tool "Summarization attempted to call
#     a tool"; any other "Summarization produced no text".

# Terms
# -----

# R1: the tokens of the contributions cs
def total(cs: List<&2, Cc.Contrib>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case c <> t:
      match c:
        case Cc.Contrib{tok, ms}:
          Nat.add(total(t), tok)

def reach_spec.pick(r: Maybe<&2, Nat>, ok: Bool, i: Nat) -> Maybe<&2, Nat>:
  match r:
    case Some{a}:
      Some{a}
    case None{}:
      match ok:
        case True{}:
          Some{i}
        case False{}:
          None{}

# R1: the last contribution of cs (the first at index i), from the start,
# from which the tokens to the end are k or more
def reach_spec.go(cs: List<&2, Cc.Contrib>, +i: Nat, +start: Nat, +k: Nat) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      None{}
    case +c <> +t:
      reach_spec.pick(reach_spec.go(t, 1n+i, start, k), Bool.and(Bool.not(Nat.is_lt(i, start)), Bool.not(Nat.is_lt(total(c <> t), k))), i)

# R1: where the walk back stops
def reach_spec(+start: Nat, lim: Cc.Limit, cs: List<&2, Cc.Contrib>) -> Maybe<&2, Nat>:
  match lim:
    case Cc.Never{}:
      None{}
    case Cc.Below{k}:
      reach_spec.go(cs, 0n, start, k)

def last_spec.pick(r: Maybe<&2, List<&2, Nat>>, m: Co.Msg) -> Maybe<&2, List<&2, Nat>>:
  match r:
    case Some{x}:
      Some{x}
    case None{}:
      match m:
        case Co.MUser{}:
          None{}
        case Co.MSystem{}:
          None{}
        case Co.MAsst{s, cs}:
          Some{cs}
        case Co.MRes{c}:
          None{}

# R2: the calls of the last assistant answer of ms
def last_spec(ms: List<&2, Co.Msg>) -> Maybe<&2, List<&2, Nat>>:
  match ms:
    case Nil{}:
      None{}
    case +m <> t:
      last_spec.pick(last_spec(t), m)

# the messages of the contributions cs, in order
def flat(cs: List<&2, Cc.Contrib>) -> List<&2, Co.Msg>:
  match cs:
    case Nil{}:
      []
    case c <> t:
      match c:
        case Cc.Contrib{tok, ms}:
          List.append(&2, Co.Msg, ms, flat(t))

def calls_of(r: Maybe<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match r:
    case None{}:
      []
    case Some{x}:
      x

# R2: the calls of the last assistant answer of the contributions pre
def calls_before(pre: List<&2, Cc.Contrib>) -> List<&2, Nat>:
  calls_of(last_spec(flat(pre)))

def member(xs: List<&2, Nat>, +c: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Nat.is_eq(x, c), member(t, c))

def clear.res(b: Bool, rest: Bool) -> Bool:
  match b:
    case True{}:
      False{}
    case False{}:
      rest

# R2: the first of ms that is an assistant answer or a result of one of
# the calls is no such result (none: clear)
def clear(ms: List<&2, Co.Msg>, +calls: List<&2, Nat>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      match m:
        case Co.MUser{}:
          clear(t, calls)
        case Co.MSystem{}:
          clear(t, calls)
        case Co.MAsst{s, cs}:
          True{}
        case Co.MRes{d}:
          clear.res(member(calls, d), clear(t, calls))

def user_spec(calls: List<&2, Nat>, ms: List<&2, Co.Msg>) -> Bool:
  match calls:
    case Nil{}:
      True{}
    case x <> xs:
      clear(ms, x <> xs)

def cand_spec.first(m: Co.Msg, calls: List<&2, Nat>, ms: List<&2, Co.Msg>) -> Bool:
  match m:
    case Co.MUser{}:
      user_spec(calls, ms)
    case Co.MSystem{}:
      False{}
    case Co.MAsst{s, cs}:
      True{}
    case Co.MRes{c}:
      False{}

# R2: the first of the contributions here, after the contributions pre,
# is a candidate
def cand_spec(+pre: List<&2, Cc.Contrib>, +here: List<&2, Cc.Contrib>) -> Bool:
  match here:
    case Nil{}:
      False{}
    case c <> t:
      match c:
        case Cc.Contrib{tok, ms}:
          match ms:
            case Nil{}:
              False{}
            case m <> u:
              cand_spec.first(m, calls_before(pre), flat(here))

def cands_spec.one(b: Bool, i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      i <> rest
    case False{}:
      rest

# R2: the candidates among here (the first at index i, the contributions
# pre before them) from the start
def cands_spec.go(here: List<&2, Cc.Contrib>, +pre: List<&2, Cc.Contrib>, +i: Nat, +start: Nat) -> List<&2, Nat>:
  match here:
    case Nil{}:
      []
    case +c <> +t:
      cands_spec.one(Bool.and(Bool.not(Nat.is_lt(i, start)), cand_spec(pre, c <> t)), i, cands_spec.go(t, List.append(&2, Cc.Contrib, pre, [c]), 1n+i, start))

# R2: the candidates of cs from the start
def cands_spec(+start: Nat, cs: List<&2, Cc.Contrib>) -> List<&2, Nat>:
  cands_spec.go(cs, [], 0n, start)

def at_or_after.pick(b: Bool, x: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      rest
    case False{}:
      Some{x}

# R3: the first of xs that is not before r
def at_or_after(xs: List<&2, Nat>, +r: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case +x <> t:
      at_or_after.pick(Nat.is_lt(x, r), x, at_or_after(t, r))

def final.pick(r: Maybe<&2, Nat>, x: Nat) -> Maybe<&2, Nat>:
  match r:
    case None{}:
      Some{x}
    case Some{y}:
      Some{y}

# R3: the last of xs
def final(xs: List<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case x <> t:
      final.pick(final(t), x)

def chosen_spec.or(m: Maybe<&2, Nat>, xs: List<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case Some{x}:
      Some{x}
    case None{}:
      final(xs)

# R3: the first candidate at or after r, else the last
def chosen_spec(+xs: List<&2, Nat>, +r: Nat) -> Maybe<&2, Nat>:
  chosen_spec.or(at_or_after(xs, r), xs)

def has_msg(ms: List<&2, Co.Msg>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case m <> t:
      True{}

def filled_spec.at(inside: Bool, ms: List<&2, Co.Msg>, rest: Bool) -> Bool:
  match inside:
    case True{}:
      Bool.or(has_msg(ms), rest)
    case False{}:
      rest

# R3: some contribution of cs (the first at index i) from the start and
# before x has a message
def filled_spec(cs: List<&2, Cc.Contrib>, +i: Nat, +start: Nat, +x: Nat) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> t:
      match c:
        case Cc.Contrib{tok, ms}:
          filled_spec.at(Bool.and(Bool.not(Nat.is_lt(i, start)), Nat.is_lt(i, x)), ms, filled_spec(t, 1n+i, start, x))

def head_start(head: Bool) -> Nat:
  match head:
    case True{}:
      1n
    case False{}:
      0n

def cut_spec.keep(b: Bool, x: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      None{}

def cut_spec.at(m: Maybe<&2, Nat>, +start: Nat, cs: List<&2, Cc.Contrib>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{+x}:
      cut_spec.keep(filled_spec(cs, 0n, start, x), x)

def cut_spec.from(r: Maybe<&2, Nat>, +start: Nat, +cs: List<&2, Cc.Contrib>) -> Maybe<&2, Nat>:
  match r:
    case None{}:
      None{}
    case Some{a}:
      cut_spec.at(chosen_spec(cands_spec(start, cs), a), start, cs)

# R1-R3: the cut
def cut_spec(+head: Bool, lim: Cc.Limit, +cs: List<&2, Cc.Contrib>) -> Maybe<&2, Nat>:
  cut_spec.from(reach_spec(head_start(head), lim, cs), head_start(head), cs)

def fail_text(b: Bool) -> Cc.Outcome:
  match b:
    case True{}:
      Cc.Failed{"Summarization attempted to call a tool"}
    case False{}:
      Cc.Failed{"Summarization produced no text"}

def fail_with(err: Maybe<&2, String>, reason: String) -> Cc.Outcome:
  match err:
    case None{}:
      Cc.Failed{String.append("Summarization failed: ", reason)}
    case Some{e}:
      Cc.Failed{String.append("Summarization failed: ", e)}

def stop_text(calls: Bool, text: Bool) -> Cc.Outcome:
  match calls:
    case True{}:
      fail_text(True{})
    case False{}:
      match text:
        case True{}:
          Cc.Summary{}
        case False{}:
          fail_text(False{})

# R4: what the summarizer's answer is
def summary_spec(s: Co.Stop, calls: Bool, text: Bool, err: Maybe<&2, String>) -> Cc.Outcome:
  match s:
    case Co.SPending{}:
      fail_text(calls)
    case Co.SStop{}:
      stop_text(calls, text)
    case Co.SLength{}:
      Cc.Failed{"Summarization hit the token limit; the summary is incomplete"}
    case Co.SToolUse{}:
      fail_text(calls)
    case Co.SError{}:
      fail_with(err, "error")
    case Co.SAborted{}:
      fail_with(err, "aborted")
    case Co.SDeferred{}:
      fail_text(calls)

# Laws
# ----

# LAW compaction_cut_candidates_exact: the candidates are exactly R2's: an assistant answer first, or a user message first that no result of the previous assistant's calls follows before the next assistant answer
# EXCLUDES: a cut at a system entry, a tool result or an empty entry; a
#   cut at a user message that would split an assistant from its results;
#   the calls of an older assistant; a result after the next assistant
#   counted; a candidate before the marker
law compaction_cut_candidates_exact:
  for +start: Nat
  for +cs: List<&2, Cc.Contrib>
  {Cc.cands(start, cs) == cands_spec(start, cs) : List<&2, Nat>}

# LAW compaction_cut_exact: the cut is R1-R3's: the first candidate at or after the contribution where the tokens kept walking back reach the limit, else the last candidate, only when a contribution after the marker and before it has a message
# EXCLUDES: a cut that keeps fewer tokens than the limit, a cut before
#   the reach point while a later candidate exists, `<=` for `<` at the
#   limit, the marker's tokens counted, a cut that summarizes nothing, a
#   cut under Never
law compaction_cut_exact:
  for head: Bool
  for +lim: Cc.Limit
  for +cs: List<&2, Cc.Contrib>
  {Cc.cut(head, lim, cs) == cut_spec(head, lim, cs) : Maybe<&2, Nat>}

# LAW compaction_cut_summary_exact: the summarizer's answer is a summary only for a stop with no tool call and text, else exactly R4's failure text for its stop reason, error message and tool call
# EXCLUDES: a tool call or a blank text taken as a summary, a length or
#   error stop taken as a summary, another failure text, the stop reason
#   shown over the error message, a tool-call failure for an error answer
law compaction_cut_summary_exact:
  for s: Co.Stop
  for calls: Bool
  for text: Bool
  for err: Maybe<&2, String>
  {Cc.summary(s, calls, text, err) == summary_spec(s, calls, text, err) : Cc.Outcome}

# LAW compaction_cut_example: anchor: a cut at the first candidate after the reach point, a user entry that a later result blocks, Never, the marker alone, the failure texts
# EXCLUDES: a spec that is wrong on the shipped cases
law compaction_cut_example:
  {Cc.cut(False{}, Cc.Below{50n}, [Cc.Contrib{100n, [Co.MUser{}]}, Cc.Contrib{10n, [Co.MAsst{Co.SToolUse{}, [1n]}]}, Cc.Contrib{10n, [Co.MRes{1n}]}, Cc.Contrib{100n, [Co.MUser{}]}, Cc.Contrib{10n, [Co.MAsst{Co.SStop{}, []}]}]) == Some{3n} : Maybe<&2, Nat>} &
  {Cc.cut(False{}, Cc.Below{0n}, [Cc.Contrib{0n, [Co.MAsst{Co.SToolUse{}, [1n]}]}, Cc.Contrib{0n, [Co.MUser{}]}, Cc.Contrib{0n, [Co.MRes{1n}]}]) == None{} : Maybe<&2, Nat>} &
  {Cc.cut(False{}, Cc.Never{}, [Cc.Contrib{5n, [Co.MUser{}]}]) == None{} : Maybe<&2, Nat>} &
  {Cc.cut(True{}, Cc.Below{1n}, [Cc.Contrib{0n, [Co.MUser{}]}, Cc.Contrib{9n, [Co.MUser{}]}]) == None{} : Maybe<&2, Nat>} &
  {Cc.summary(Co.SError{}, True{}, True{}, Some{"boom"}) == Cc.Failed{"Summarization failed: boom"} : Cc.Outcome} &
  {Cc.summary(Co.SAborted{}, False{}, False{}, None{}) == Cc.Failed{"Summarization failed: aborted"} : Cc.Outcome} &
  {Cc.summary(Co.SStop{}, False{}, True{}, None{}) == Cc.Summary{} : Cc.Outcome}

# LAWS (R5): the entry of the compiled Bend core
# (bend/ffi_compaction_cut.bend, called by crates/eukhe-durable
# harness/compaction through `eukhe_bend::rules::compaction_cut`). Each
# law is an open claim about FCc.ffi, stated with spec spellers built
# only from the wire primitives of bend/wire.bend (their round trips:
# laws/wire.bend) and the message spellers of laws/context_order.bend.
#
# R5: a request is a question: tag 0 the cut: a Bool (a head marker
#     leads), the limit (0 never, 1 then k), a List of contributions (its
#     tokens, then its List<Msg>), answered with a Maybe<Nat> (0 none, 1
#     then the index of the first contribution kept); tag 1 the
#     summarizer's answer: its Stop, a Bool (it called a tool), a Bool
#     (its trimmed text is not blank), a Maybe<String> (its error
#     message), answered with 0 (a summary) or 1 then the failure text
#     (a String). Every input that is not exactly one request whose
#     counts, tokens, ids and lengths fit the wire answers the error form
#     "compaction_cut: malformed request"; never a default.

# Spec spellers
# -------------

def spell_limit(l: Cc.Limit, rest: String) -> String:
  match l:
    case Cc.Never{}:
      Wr.put_nat(0n, rest)
    case Cc.Below{k}:
      Wr.put_nat(1n, Wr.put_nat(k, rest))

def spell_contrib(c: Cc.Contrib, rest: String) -> String:
  match c:
    case Cc.Contrib{tok, ms}:
      Wr.put_nat(tok, ContextOrder.spell_msgs(ms, rest))

def spell_contribs.items(cs: List<&2, Cc.Contrib>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      spell_contrib(c, spell_contribs.items(t, rest))

def spell_err(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{e}:
      Wr.put_nat(1n, Wr.put_str(e, rest))

# a request, then rest
def spell_req(q: FCc.Req, rest: String) -> String:
  match q:
    case FCc.QCut{h, l, +cs}:
      Wr.put_nat(0n, Wr.put_bool(h, spell_limit(l, Wr.put_nat(List.length(&2, Cc.Contrib, cs), spell_contribs.items(cs, rest)))))
    case FCc.QSummary{s, c, x, e}:
      Wr.put_nat(1n, ContextOrder.spell_stop(s, Wr.put_bool(c, Wr.put_bool(x, spell_err(e, rest)))))

def spell_outcome(o: Cc.Outcome) -> String:
  match o:
    case Cc.Summary{}:
      Wr.put_nat(0n, "")
    case Cc.Failed{text}:
      Wr.put_nat(1n, Wr.put_str(text, ""))

# the reply Rust reads: the spelled answer of the model
def spell_reply(q: FCc.Req) -> String:
  match q:
    case FCc.QCut{h, l, cs}:
      ContextOrder.spell_mnat(Cc.cut(h, l, cs), "")
    case FCc.QSummary{s, c, x, e}:
      spell_outcome(Cc.summary(s, c, x, e))

def limit_fits(l: Cc.Limit) -> Bool:
  match l:
    case Cc.Never{}:
      True{}
    case Cc.Below{k}:
      LawsBase.wire_fits(k)

def contrib_fits(c: Cc.Contrib) -> Bool:
  match c:
    case Cc.Contrib{tok, ms}:
      Bool.and(LawsBase.wire_fits(tok), ContextOrder.msgs_fit(ms))

def contribs_all(cs: List<&2, Cc.Contrib>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> t:
      Bool.and(contrib_fits(c), contribs_all(t))

def err_fits(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{e}:
      LawsBase.wire_fits(String.length(e))

# every count, token count, id and length of the request fits the wire
def req_fits(q: FCc.Req) -> Bool:
  match q:
    case FCc.QCut{h, l, +cs}:
      Bool.and(limit_fits(l), Bool.and(LawsBase.wire_fits(List.length(&2, Cc.Contrib, cs)), contribs_all(cs)))
    case FCc.QSummary{s, c, x, e}:
      err_fits(e)

# Laws
# ----

# LAW compaction_cut_ffi_answers: a spelled request whose numbers fit the wire answers the spelled answer of the model
# EXCLUDES: a fact misread (a tag off by one, the head flag or a stop
#   reason swapped, tokens lost), an answer spelled with another tag, a
#   question answered by another model function
law compaction_cut_ffi_answers:
  for +q: FCc.Req
  for h: {req_fits(q) == True{} : Bool}
  {FCc.ffi(spell_req(q, "")) == spell_reply(q) : String}

# LAW compaction_cut_ffi_reads: the entry's decoder reads a spelled request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law compaction_cut_ffi_reads:
  for +q: FCc.Req
  for +rest: String
  for h: {req_fits(q) == True{} : Bool}
  {FCc.get_req(spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FCc.Req>}

# LAW compaction_cut_ffi_exact: every input the entry does not answer with the error form is a spelled request that fits the wire
# EXCLUDES: an answer made for input that is no request (an unknown tag,
#   a missing field, a Nat of 15 or more digits, a short string, input
#   left over)
law compaction_cut_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCc.ffi(s)) == False{} : Bool}
  exs q: FCc.Req
  {s == spell_req(q, "") : String} & {req_fits(q) == True{} : Bool}

# LAW compaction_cut_ffi_refuses: every error the entry answers is exactly "compaction_cut: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law compaction_cut_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FCc.ffi(s)) == True{} : Bool}
  {FCc.ffi(s) == Wr.err("compaction_cut: malformed request") : String}

# LAW compaction_cut_ffi_example: anchor: the bytes Rust sends and reads: a cut, Never, a failed and a clean summary, an unknown tag, input left over
# EXCLUDES: another spelling of a fact or an answer
law compaction_cut_ffi_example:
  {[FCc.ffi("0,F1,50,5,100,1,0,10,1,2,1,1,1,10,1,3,1,100,1,0,10,1,2,1,0,"), FCc.ffi("0,F0,1,5,1,0,"), FCc.ffi("1,4,FT1,4,boom"), FCc.ffi("1,1,FT0,"), FCc.ffi("2,"), FCc.ffi("1,1,FT0,x")] == ["1,3,", "0,", "1,26,Summarization failed: boom", "0,", Wr.err("compaction_cut: malformed request"), Wr.err("compaction_cut: malformed request")] : List<&2, String>}
