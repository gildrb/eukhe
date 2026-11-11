# eukhe: the laws of area glob, section entry (R7): bend/ffi_glob.bend
# reads the request Rust spells and answers the model's answer, spelled
# (the requirement table is in laws/glob.bend)

import Base
import ../../bend/glob/parse.bend as GParse
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/queries.bend as GQuery
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# R7: the spelling of a request and of its reply

def sp_w_req(q: FG.Req, rest: String) -> String:
  match q:
    case FG.QCheck{p}:
      Wr.put_nat(0n, Wr.put_str(p, rest))
    case FG.QMatch{sep, fold, ps, ss, ks}:
      Wr.put_nat(1n, Wr.put_bool(sep, Wr.put_bool(fold, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_strs(ss, LawsBase.wire_spell_nats(ks, rest))))))
    case FG.QAllow{sel, ps}:
      Wr.put_nat(2n, Wr.put_str(sel, LawsBase.wire_spell_strs(ps, rest)))
    case FG.QRules{sep, fold, ps, ss, ks}:
      Wr.put_nat(3n, Wr.put_bool(sep, Wr.put_bool(fold, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_strs(ss, LawsBase.wire_spell_nats(ks, rest))))))
    case FG.QIgnore{ps, cs, es}:
      Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_nats(cs, LawsBase.wire_spell_strs(es, rest))))

def sp_w_err(e: GParse.Err) -> String:
  match e:
    case GParse.EClass{}:
      Wr.put_nat(0n, "")
    case GParse.ERange{lo, hi}:
      Wr.put_nat(1n, Wr.put_nat(U32.to_nat(Char.to_u32(lo)), Wr.put_nat(U32.to_nat(Char.to_u32(hi)), "")))
    case GParse.EUnopened{}:
      Wr.put_nat(2n, "")
    case GParse.EUnclosed{}:
      Wr.put_nat(3n, "")
    case GParse.EEscape{}:
      Wr.put_nat(4n, "")

def sp_w_check(r: Result<&2, &2, GParse.Err, GParse.Glob>) -> String:
  match r:
    case Fail{e}:
      Wr.put_nat(1n, sp_w_err(e))
    case Done{g}:
      Wr.put_nat(0n, "")

def sp_w_bools.items(xs: List<&2, Bool>) -> String:
  match xs:
    case Nil{}:
      ""
    case b <> r:
      Wr.put_bool(b, sp_w_bools.items(r))

def sp_w_bools(+xs: List<&2, Bool>) -> String:
  Wr.put_nat(List.length(&2, Bool, xs), sp_w_bools.items(xs))

# R7: the spelled answer: the model's answer to the request (pinned by
# the laws of R1 to R6)
def sp_w_reply(q: FG.Req) -> String:
  match q:
    case FG.QCheck{p}:
      sp_w_check(GParse.parse(p))
    case FG.QMatch{sep, fold, ps, ss, ks}:
      sp_w_bools(GQuery.match_groups(GItems.Opts{sep, fold}, ps, ss, ks))
    case FG.QAllow{sel, ps}:
      Wr.put_bool(GQuery.allowed(sel, ps), "")
    case FG.QRules{sep, fold, ps, ss, ks}:
      sp_w_bools(GQuery.rules(ks, GItems.Opts{sep, fold}, ps, ss))
    case FG.QIgnore{ps, cs, es}:
      sp_w_bools(GQuery.ignored(ps, cs, es))

# every number and length of the request fits the wire
def sp_fit_req(q: FG.Req) -> Bool:
  match q:
    case FG.QCheck{p}:
      LawsBase.wire_fits(String.length(p))
    case FG.QMatch{sep, fold, ps, ss, +ks}:
      Bool.and(LawsBase.wire_strs_fit(ps), Bool.and(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks))))
    case FG.QAllow{sel, ps}:
      Bool.and(LawsBase.wire_fits(String.length(sel)), LawsBase.wire_strs_fit(ps))
    case FG.QRules{sep, fold, ps, ss, +ks}:
      Bool.and(LawsBase.wire_strs_fit(ps), Bool.and(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks))))
    case FG.QIgnore{ps, +cs, es}:
      Bool.and(LawsBase.wire_strs_fit(ps), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs)), LawsBase.wire_strs_fit(es)))

# Laws: the entry (R7)
# --------------------

# LAW glob_entry_answers (R7): the entry answers every request Rust
# spells, every number and length within the wire, with the model's
# answer spelled (sp_w_reply: the parse's error, or the answers of
# match_groups, allowed, rules, ignored, which the laws of R1 to R6 pin)
# EXCLUDES: the fields read in another order, a request read as another,
#   an error spelled with another tag, a default
law glob_entry_answers:
  for +q: FG.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FG.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW glob_entry_reads (R7): the entry's decoder reads a spelled request
# back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law glob_entry_reads:
  for +q: FG.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FG.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FG.Req>}

# LAW glob_entry_exact (R7): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown question, a
#   malformed field or list, input left over)
law glob_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FG.ffi(s)) == False{} : Bool}
  exs r: FG.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW glob_entry_refuses (R7): every error the entry answers is exactly
# `E glob: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law glob_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FG.ffi(s)) == True{} : Bool}
  {FG.ffi(s) == Wr.err("glob: malformed request") : String}

# LAW glob_entry_example (R7): anchor: the wire strings Rust sends and the
# replies it reads; an unknown question, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law glob_entry_example:
  {[FG.ffi("0,4,a{b,"), FG.ffi("0,5,[z-a]"), FG.ffi("0,4,*.rs"), FG.ffi("1,TF2,4,*.rs7,**/*.md3,4,a.rs3,b/c4,x.md2,1,2,"), FG.ffi("2,3,z/g1,3,z/*"), FG.ffi("3,TT2,5,gpt-*1,x2,5,GPT-51,b1,2,"), FG.ffi("4,2,4,venv1,x2,0,4,3,4,venv2,x/5,x/abc"), FG.ffi("5,"), FG.ffi("0,1,ax")] == ["1,3,", "1,1,122,97,", "0,", "2,TT", "T", "1,T", "3,TTF", Wr.err("glob: malformed request"), Wr.err("glob: malformed request")] : List<&2, String>}
