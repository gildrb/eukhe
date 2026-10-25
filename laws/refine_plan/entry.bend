# eukhe: the laws of area refine_plan: the entry (bend/ffi_refine_plan.bend)

import Base
import ../../bend/refine_plan.bend as Rp
import ../../bend/ffi_refine_plan.bend as FRp
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ./model.bend as RefinePlan

# (D2) The entry
# --------------
# R9: the entry answers each request Rust writes with the spec's answer,
#     reads exactly the request and nothing after it, and answers any other
#     input with the exact error form `E refine_plan: malformed request`.
#     A request: its tag then its fields: 0 ids: the edits; 1 plan: the
#     options (factory opt-in, baseline given: Bools), the edits; 2 back:
#     the result's id, its rows (applied, with a before, with an after:
#     Bools); 3 norm: the summary, rationale and expected outcome (each a
#     Maybe<String>); 4 scan: the text; 5 fit: the window (context window,
#     max tokens, output reserve, system prompt length: Nats), the
#     conversation's length, where the walk is (0 full | 1 probe: low,
#     high, length | 2 final), the prompt's length. An edit: its action
#     (Maybe of 0 create | 1 update | 2 delete), its kind (Maybe of 0
#     prompt | 1 memory | 2 skill | 3 subagent | 4 factory), its id and
#     title (Maybe<String>), has content (Bool), its reference (Maybe of
#     type, import, python_import, callable, call_pattern: each a
#     Maybe<String>), its arguments (Maybe of dag, machine: each 0 missing
#     | 1 null | 2 object | 3 other), stored, changed since the baseline,
#     held (Bools); a list is its count then its items; every count,
#     length and Nat within the wire. A reply: ids: the computed ids
#     (List<Maybe<String>>); plan: the rows (each the action, the kind,
#     the id, then 0 invalid: the message | 1 refused: the message | 2
#     removed | 3 written), then the change lines (List<String>); back:
#     the summary, rationale, expected outcome, reason (Strings), then the
#     edits (each the row's index, the action); norm: the three texts;
#     scan: the Bool; fit: 0 try: the length, where the walk then is | 1
#     the max tokens | 2 the refusal text.

# Spellers
# --------

def rp_w_verb(x: Rp.Verb, rest: String) -> String:
  match x:
    case Rp.ACreate{}:
      Wr.put_nat(0n, rest)
    case Rp.AUpdate{}:
      Wr.put_nat(1n, rest)
    case Rp.ADelete{}:
      Wr.put_nat(2n, rest)

def rp_w_comp(x: Rp.Comp, rest: String) -> String:
  match x:
    case Rp.KPrompt{}:
      Wr.put_nat(0n, rest)
    case Rp.KMemory{}:
      Wr.put_nat(1n, rest)
    case Rp.KSkill{}:
      Wr.put_nat(2n, rest)
    case Rp.KSubagent{}:
      Wr.put_nat(3n, rest)
    case Rp.KFactory{}:
      Wr.put_nat(4n, rest)

def rp_w_val(x: Rp.Val, rest: String) -> String:
  match x:
    case Rp.VMissing{}:
      Wr.put_nat(0n, rest)
    case Rp.VNull{}:
      Wr.put_nat(1n, rest)
    case Rp.VObject{}:
      Wr.put_nat(2n, rest)
    case Rp.VOther{}:
      Wr.put_nat(3n, rest)

def rp_w_ms(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

def rp_w_pyref(x: Rp.Pyref, rest: String) -> String:
  match x:
    case Rp.Pyref{ty, imp, pyimp, call, pat}:
      rp_w_ms(ty, rp_w_ms(imp, rp_w_ms(pyimp, rp_w_ms(call, rp_w_ms(pat, rest)))))

def rp_w_args(x: Rp.Args, rest: String) -> String:
  match x:
    case Rp.Args{dag, machine}:
      rp_w_val(dag, rp_w_val(machine, rest))

def rp_w_mverb(m: Maybe<&2, Rp.Verb>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, rp_w_verb(x, rest))

def rp_w_mcomp(m: Maybe<&2, Rp.Comp>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, rp_w_comp(x, rest))

def rp_w_mpyref(m: Maybe<&2, Rp.Pyref>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, rp_w_pyref(x, rest))

def rp_w_margs(m: Maybe<&2, Rp.Args>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, rp_w_args(x, rest))

def rp_w_ed(x: Rp.Ed, rest: String) -> String:
  match x:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      rp_w_mverb(verb, rp_w_mcomp(comp, rp_w_ms(id, rp_w_ms(title, Wr.put_bool(content, rp_w_mpyref(pyref, rp_w_margs(args, Wr.put_bool(exists, Wr.put_bool(differs, Wr.put_bool(held, rest))))))))))

def rp_w_eds.items(xs: List<&2, Rp.Ed>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, u}:
      rp_w_ed(x, rp_w_eds.items(u, rest))

def rp_w_eds(+xs: List<&2, Rp.Ed>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Rp.Ed, xs), rp_w_eds.items(xs, rest))

def rp_w_opts(x: Rp.Opts, rest: String) -> String:
  match x:
    case Rp.Opts{factory, baseline}:
      Wr.put_bool(factory, Wr.put_bool(baseline, rest))

def rp_w_was(x: Rp.Was, rest: String) -> String:
  match x:
    case Rp.Was{applied, before, after}:
      Wr.put_bool(applied, Wr.put_bool(before, Wr.put_bool(after, rest)))

def rp_w_wl.items(xs: List<&2, Rp.Was>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, u}:
      rp_w_was(x, rp_w_wl.items(u, rest))

def rp_w_wl(+xs: List<&2, Rp.Was>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Rp.Was, xs), rp_w_wl.items(xs, rest))

def rp_w_win(x: Rp.Win, rest: String) -> String:
  match x:
    case Rp.Win{window, max, reserve, system}:
      Wr.put_nat(window, Wr.put_nat(max, Wr.put_nat(reserve, Wr.put_nat(system, rest))))

def rp_w_search(x: Rp.Search, rest: String) -> String:
  match x:
    case Rp.SFull{}:
      Wr.put_nat(0n, rest)
    case Rp.SProbe{low, high, len}:
      Wr.put_nat(1n, Wr.put_nat(low, Wr.put_nat(high, Wr.put_nat(len, rest))))
    case Rp.SFinal{}:
      Wr.put_nat(2n, rest)

def rp_w_req(x: FRp.Req, rest: String) -> String:
  match x:
    case FRp.QIds{eds}:
      Wr.put_nat(0n, rp_w_eds(eds, rest))
    case FRp.QPlan{opts, eds}:
      Wr.put_nat(1n, rp_w_opts(opts, rp_w_eds(eds, rest)))
    case FRp.QBack{id, was}:
      Wr.put_nat(2n, Wr.put_str(id, rp_w_wl(was, rest)))
    case FRp.QNorm{summary, rationale, outcome}:
      Wr.put_nat(3n, rp_w_ms(summary, rp_w_ms(rationale, rp_w_ms(outcome, rest))))
    case FRp.QScan{text}:
      Wr.put_nat(4n, Wr.put_str(text, rest))
    case FRp.QFit{win, conv, search, plen}:
      Wr.put_nat(5n, rp_w_win(win, Wr.put_nat(conv, rp_w_search(search, Wr.put_nat(plen, rest)))))

def rp_w_mss.items(xs: List<&2, Maybe<&2, String>>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, u}:
      rp_w_ms(x, rp_w_mss.items(u, rest))

def rp_w_mss(+xs: List<&2, Maybe<&2, String>>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Maybe<&2, String>, xs), rp_w_mss.items(xs, rest))

def rp_w_out(x: Rp.Out, rest: String) -> String:
  match x:
    case Rp.OInvalid{msg}:
      Wr.put_nat(0n, Wr.put_str(msg, rest))
    case Rp.ORefused{msg}:
      Wr.put_nat(1n, Wr.put_str(msg, rest))
    case Rp.ORemoved{}:
      Wr.put_nat(2n, rest)
    case Rp.OWritten{}:
      Wr.put_nat(3n, rest)

def rp_w_row(x: Rp.Row, rest: String) -> String:
  match x:
    case Rp.Row{verb, comp, id, out}:
      rp_w_verb(verb, rp_w_comp(comp, Wr.put_str(id, rp_w_out(out, rest))))

def rp_w_rows.items(xs: List<&2, Rp.Row>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, u}:
      rp_w_row(x, rp_w_rows.items(u, rest))

def rp_w_rows(+xs: List<&2, Rp.Row>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Rp.Row, xs), rp_w_rows.items(xs, rest))

def rp_w_strs.items(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, u}:
      Wr.put_str(x, rp_w_strs.items(u, rest))

def rp_w_strs(+xs: List<&2, String>, rest: String) -> String:
  Wr.put_nat(List.length(&2, String, xs), rp_w_strs.items(xs, rest))

def rp_w_plan(x: Rp.Plan, rest: String) -> String:
  match x:
    case Rp.Plan{rows, changes}:
      rp_w_rows(rows, rp_w_strs(changes, rest))

def rp_w_pick(x: Rp.Pick, rest: String) -> String:
  match x:
    case Rp.Pick{at, verb}:
      Wr.put_nat(at, rp_w_verb(verb, rest))

def rp_w_picks.items(xs: List<&2, Rp.Pick>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, u}:
      rp_w_pick(x, rp_w_picks.items(u, rest))

def rp_w_picks(+xs: List<&2, Rp.Pick>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Rp.Pick, xs), rp_w_picks.items(xs, rest))

def rp_w_back(x: Rp.Back, rest: String) -> String:
  match x:
    case Rp.Back{summary, rationale, outcome, reason, picks}:
      Wr.put_str(summary, Wr.put_str(rationale, Wr.put_str(outcome, Wr.put_str(reason, rp_w_picks(picks, rest)))))

def rp_w_texts(x: Rp.Texts, rest: String) -> String:
  match x:
    case Rp.Texts{summary, rationale, outcome}:
      Wr.put_str(summary, Wr.put_str(rationale, Wr.put_str(outcome, rest)))

def rp_w_step(x: Rp.Step, rest: String) -> String:
  match x:
    case Rp.TTry{len, next}:
      Wr.put_nat(0n, Wr.put_nat(len, rp_w_search(next, rest)))
    case Rp.TOk{max}:
      Wr.put_nat(1n, Wr.put_nat(max, rest))
    case Rp.TNo{text}:
      Wr.put_nat(2n, Wr.put_str(text, rest))

# the reply Rust reads: the spec's answer, spelled
def rp_w_reply(q: FRp.Req) -> String:
  match q:
    case FRp.QIds{eds}:
      rp_w_mss(RefinePlan.rp_ids(eds), "")
    case FRp.QPlan{opts, eds}:
      rp_w_plan(RefinePlan.rp_plan(opts, eds), "")
    case FRp.QBack{id, was}:
      rp_w_back(RefinePlan.rp_back(id, was), "")
    case FRp.QNorm{summary, rationale, outcome}:
      rp_w_texts(RefinePlan.rp_norm(summary, rationale, outcome), "")
    case FRp.QScan{text}:
      Wr.put_bool(RefinePlan.rp_incomplete(text), "")
    case FRp.QFit{win, conv, search, plen}:
      rp_w_step(RefinePlan.rp_fit(win, conv, search, plen), "")

# Fits: every count, length and Nat of a request within the wire
# ---------------------------------------------------------------

def rp_fit_ms(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      LawsBase.wire_fits(String.length(x))

def rp_fit_pyref(x: Rp.Pyref) -> Bool:
  match x:
    case Rp.Pyref{ty, imp, pyimp, call, pat}:
      Bool.and(rp_fit_ms(ty), Bool.and(rp_fit_ms(imp), Bool.and(rp_fit_ms(pyimp), Bool.and(rp_fit_ms(call), rp_fit_ms(pat)))))

def rp_fit_mpyref(m: Maybe<&2, Rp.Pyref>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      rp_fit_pyref(x)

def rp_fit_ed(x: Rp.Ed) -> Bool:
  match x:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      Bool.and(rp_fit_ms(id), Bool.and(rp_fit_ms(title), rp_fit_mpyref(pyref)))

def rp_fit_eds.items(xs: List<&2, Rp.Ed>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, u}:
      Bool.and(rp_fit_ed(x), rp_fit_eds.items(u))

def rp_fit_eds(+xs: List<&2, Rp.Ed>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Rp.Ed, xs)), rp_fit_eds.items(xs))

def rp_fit_wl(xs: List<&2, Rp.Was>) -> Bool:
  LawsBase.wire_fits(List.length(&2, Rp.Was, xs))

def rp_fit_win(x: Rp.Win) -> Bool:
  match x:
    case Rp.Win{window, max, reserve, system}:
      Bool.and(LawsBase.wire_fits(window), Bool.and(LawsBase.wire_fits(max), Bool.and(LawsBase.wire_fits(reserve), LawsBase.wire_fits(system))))

def rp_fit_search(x: Rp.Search) -> Bool:
  match x:
    case Rp.SFull{}:
      True{}
    case Rp.SProbe{low, high, len}:
      Bool.and(LawsBase.wire_fits(low), Bool.and(LawsBase.wire_fits(high), LawsBase.wire_fits(len)))
    case Rp.SFinal{}:
      True{}

def rp_fit_req(x: FRp.Req) -> Bool:
  match x:
    case FRp.QIds{eds}:
      rp_fit_eds(eds)
    case FRp.QPlan{opts, eds}:
      rp_fit_eds(eds)
    case FRp.QBack{id, was}:
      Bool.and(LawsBase.wire_fits(String.length(id)), rp_fit_wl(was))
    case FRp.QNorm{summary, rationale, outcome}:
      Bool.and(rp_fit_ms(summary), Bool.and(rp_fit_ms(rationale), rp_fit_ms(outcome)))
    case FRp.QScan{text}:
      LawsBase.wire_fits(String.length(text))
    case FRp.QFit{win, conv, search, plen}:
      Bool.and(rp_fit_win(win), Bool.and(LawsBase.wire_fits(conv), Bool.and(rp_fit_search(search), LawsBase.wire_fits(plen))))

# Laws: the entry (R9)
# --------------------

# LAW refine_plan_entry_answers (R9): the entry answers every request Rust
# spells, every count, length and Nat within the wire, with the spec's
# answer spelled
# EXCLUDES: fields read in another order, a tag misread, a Bool fact
#   swapped with another, an edit lost, a reply in another constructor or
#   order, a default
law refine_plan_entry_answers:
  for +q: FRp.Req
  for fit: {rp_fit_req(q) == True{} : Bool}
  {FRp.ffi(rp_w_req(q, "")) == rp_w_reply(q) : String}

# LAW refine_plan_entry_left_over (R9): a spelled request followed by more
# input answers the error form
# EXCLUDES: the input after the request ignored or read into a field
law refine_plan_entry_left_over:
  for +q: FRp.Req
  for +c: Char
  for +t: String
  for fit: {rp_fit_req(q) == True{} : Bool}
  {FRp.ffi(rp_w_req(q, SCon{c, t})) == Wr.err("refine_plan: malformed request") : String}

# LAW refine_plan_entry_exact (R9): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown tag, an
#   action tag past 2, a kind tag past 4, a spec key tag past 3, a walk tag
#   past 2, a Maybe tag past 1, a count past the items, a short field,
#   input left over)
law refine_plan_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FRp.ffi(s)) == False{} : Bool}
  exs q: FRp.Req
  {s == rp_w_req(q, "") : String} & {rp_fit_req(q) == True{} : Bool}

# LAW refine_plan_entry_refuses (R9): every error the entry answers is
# exactly `E refine_plan: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law refine_plan_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FRp.ffi(s)) == True{} : Bool}
  {FRp.ffi(s) == Wr.err("refine_plan: malformed request") : String}

# LAW refine_plan_entry_example (R9): anchor: the wire strings Rust sends
# and the replies it reads
# EXCLUDES: another spelling of a request or of a reply
law refine_plan_entry_example:
  {[FRp.ffi("0,1,1,0,1,1,1,1,m0,T0,0,FFT"), FRp.ffi("1,FF1,1,0,1,4,1,1,f1,1,TT0,1,0,2,FFT"), FRp.ffi("2,1,r2,TFTFTT"), FRp.ffi("3,0,1,1,r0,"), FRp.ffi("4,2,{\""), FRp.ffi("5,9,0,0,0,0,0,0,"), FRp.ffi("6,"), FRp.ffi("4,1,ab"), FRp.ffi("0,1,1,3,")] == ["1,1,1,m", "1,0,4,1,f1,53,the factory is disabled; run /factory on to enable it0,", "21,Rollback refinement r61,Restores continual harness state snapshots from refinement r.37,Faulty refinement edits are reverted.10,Rollback r1,0,2,", "31,Refined continual harness state1,r0,", "T", "2,104,Refinement prompt leaves no room for output in the model's context window; retry with a smaller request.", Wr.err("refine_plan: malformed request"), Wr.err("refine_plan: malformed request"), Wr.err("refine_plan: malformed request")] : List<&2, String>}

# LAW refine_plan_entry_witness: the entry laws' premises hold for a
# request, and a malformed input exists
# EXCLUDES: vacuous entry laws
law refine_plan_entry_witness:
  {rp_fit_req(FRp.QScan{"x"}) == True{} : Bool} & {FRp.ffi("6,") == Wr.err("refine_plan: malformed request") : String}
