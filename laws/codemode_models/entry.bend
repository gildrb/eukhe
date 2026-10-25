# eukhe: the laws of area codemode_models: the entry

import Base
import ../../bend/codemode_models.bend as Mod
import ../../bend/ffi_codemode_models.bend as FMod
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# LAWS (R11): the entry of the compiled Bend core
# (bend/ffi_codemode_models.bend, called by crates/eukhe-durable
# codemode/models.rs and call.rs through
# `eukhe_bend::rules::codemode_models`). Each law is an open claim about
# FMod.ffi, stated with spec spellers built only from the wire primitives
# of bend/wire.bend (their round trips: laws/wire.bend).
#
# R11: a request is a question, its grammar the header of
#      bend/ffi_codemode_models.bend restates: tag 0 a classifier context,
#      1 an images context, 2 the model a call names, 3 a catalog call, 4 a
#      global, 5 a result, 6 serde's error, 7 the model calls that run at
#      once; each answered with the model's answer spelled as that header
#      says. Every input that is not exactly one request whose counts,
#      numbers and lengths fit the wire answers the error form
#      "codemode_models: malformed request"; never a default.

# Spec spellers
# -------------

def spell_desc(d: Mod.Desc, rest: String) -> String:
  match d:
    case Mod.DUndef{}:
      Wr.put_nat(0n, rest)
    case Mod.DNull{}:
      Wr.put_nat(1n, rest)
    case Mod.DBool{}:
      Wr.put_nat(2n, rest)
    case Mod.DNum{}:
      Wr.put_nat(3n, rest)
    case Mod.DStr{}:
      Wr.put_nat(4n, rest)
    case Mod.DArr{e}:
      Wr.put_nat(5n, Wr.put_bool(e, rest))
    case Mod.DObj{ks}:
      Wr.put_nat(6n, LawsBase.wire_spell_strs(ks, rest))

def spell_descs.items(ds: List<&2, Mod.Desc>, rest: String) -> String:
  match ds:
    case Nil{}:
      rest
    case Con{d, r}:
      spell_desc(d, spell_descs.items(r, rest))

def spell_descs(+ds: List<&2, Mod.Desc>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Mod.Desc, ds), spell_descs.items(ds, rest))

def spell_txt(t: Mod.Txt, rest: String) -> String:
  match t:
    case Mod.NoTxt{}:
      Wr.put_nat(0n, rest)
    case Mod.Txt{s}:
      Wr.put_nat(1n, Wr.put_str(s, rest))

def spell_blk(b: Mod.Blk, rest: String) -> String:
  match b:
    case Mod.Blk{k, t, x, d, m}:
      spell_desc(k, spell_txt(t, spell_desc(x, spell_desc(d, spell_desc(m, rest)))))

def spell_blks.items(bs: List<&2, Mod.Blk>, rest: String) -> String:
  match bs:
    case Nil{}:
      rest
    case Con{b, r}:
      spell_blk(b, spell_blks.items(r, rest))

def spell_blks(+bs: List<&2, Mod.Blk>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Mod.Blk, bs), spell_blks.items(bs, rest))

def spell_q(x: Mod.Q, rest: String) -> String:
  match x:
    case Mod.Q{id, q, ins, kind, json, c, vs, yes, no}:
      Wr.put_str(id, spell_desc(q, spell_desc(ins, spell_txt(kind, Wr.put_str(json, spell_desc(c, spell_descs(vs, spell_desc(yes, spell_desc(no, rest)))))))))

def spell_qs.items(qs: List<&2, Mod.Q>, rest: String) -> String:
  match qs:
    case Nil{}:
      rest
    case Con{q, r}:
      spell_q(q, spell_qs.items(r, rest))

def spell_qs(+qs: List<&2, Mod.Q>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Mod.Q, qs), spell_qs.items(qs, rest))

def spell_mtype(t: Mod.MType, rest: String) -> String:
  match t:
    case Mod.TChat{}:
      Wr.put_nat(0n, rest)
    case Mod.TImage{}:
      Wr.put_nat(1n, rest)
    case Mod.TClassifier{}:
      Wr.put_nat(2n, rest)

def spell_found(m: Maybe<&2, Mod.MType>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{t}:
      Wr.put_nat(1n, spell_mtype(t, rest))

def spell_call(c: Mod.Call, rest: String) -> String:
  match c:
    case Mod.CClassify{}:
      Wr.put_nat(0n, rest)
    case Mod.CImages{}:
      Wr.put_nat(1n, rest)

# a request, then rest
def spell_req(q: FMod.Req, rest: String) -> String:
  match q:
    case FMod.QClassify{x}:
      match x:
        case Mod.Ctx{c, st, im, +bs, qd, +qs}:
          Wr.put_nat(0n, spell_desc(c, spell_desc(st, spell_desc(im, spell_blks(bs, spell_desc(qd, spell_qs(qs, rest)))))))
    case FMod.QImages{x}:
      match x:
        case Mod.ICtx{c, i, +bs}:
          Wr.put_nat(1n, spell_desc(c, spell_desc(i, spell_blks(bs, rest))))
    case FMod.QResolve{x}:
      match x:
        case Mod.Res{c, d, m, p, i, fc, fi, fk}:
          Wr.put_nat(2n, spell_call(c, Wr.put_bool(d, spell_desc(m, spell_txt(p, spell_txt(i, spell_found(fc, spell_found(fi, spell_found(fk, rest)))))))))
    case FMod.QCatalog{x}:
      match x:
        case Mod.Cat{n, +a, k, j}:
          Wr.put_nat(3n, Wr.put_str(n, spell_descs(a, spell_txt(k, Wr.put_str(j, rest)))))
    case FMod.QTool{g}:
      Wr.put_nat(4n, Wr.put_str(g, rest))
    case FMod.QResult{c, p, i, st, e}:
      Wr.put_nat(5n, spell_call(c, Wr.put_str(p, Wr.put_str(i, Wr.put_str(st, spell_txt(e, rest))))))
    case FMod.QUnread{c, e}:
      Wr.put_nat(6n, spell_call(c, Wr.put_str(e, rest)))
    case FMod.QCap{}:
      Wr.put_nat(7n, rest)

def spell_problem(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{t}:
      Wr.put_nat(1n, Wr.put_str(t, ""))

def spell_rans(a: Mod.RAns) -> String:
  match a:
    case Mod.RFail{t}:
      Wr.put_nat(0n, Wr.put_str(t, ""))
    case Mod.RDefault{}:
      Wr.put_nat(1n, "")
    case Mod.RFound{}:
      Wr.put_nat(2n, "")

def spell_cans(a: Mod.CAns) -> String:
  match a:
    case Mod.CFail{t}:
      Wr.put_nat(0n, Wr.put_str(t, ""))
    case Mod.CModels{t, g}:
      Wr.put_nat(1n, spell_mtype(t, Wr.put_bool(g, "")))
    case Mod.CAvailable{t, g}:
      Wr.put_nat(2n, spell_mtype(t, Wr.put_bool(g, "")))
    case Mod.COne{t}:
      Wr.put_nat(3n, spell_mtype(t, ""))

def spell_tool(m: Maybe<&2, Mod.Call>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{c}:
      Wr.put_nat(1n, spell_call(c, ""))

def spell_result(r: Bool & String) -> String:
  match r:
    case (ok, t):
      Wr.put_bool(ok, Wr.put_str(t, ""))

# the reply Rust reads: the spelled answer of the model
def spell_reply(q: FMod.Req) -> String:
  match q:
    case FMod.QClassify{x}:
      spell_problem(Mod.classify(x))
    case FMod.QImages{x}:
      spell_problem(Mod.images(x))
    case FMod.QResolve{x}:
      spell_rans(Mod.resolve(x))
    case FMod.QCatalog{x}:
      spell_cans(Mod.catalog(x))
    case FMod.QTool{g}:
      spell_tool(Mod.tool(g))
    case FMod.QResult{c, p, i, st, e}:
      spell_result(Mod.result(c, p, i, st, e))
    case FMod.QUnread{c, e}:
      Wr.put_str(Mod.unread(c, e), "")
    case FMod.QCap{}:
      Wr.put_nat(Mod.max_calls(), "")

def str_fits(+s: String) -> Bool:
  LawsBase.wire_fits(String.length(s))

def desc_fits(d: Mod.Desc) -> Bool:
  match d:
    case Mod.DObj{ks}:
      LawsBase.wire_strs_fit(ks)
    case Mod.DUndef{}:
      True{}
    case Mod.DNull{}:
      True{}
    case Mod.DBool{}:
      True{}
    case Mod.DNum{}:
      True{}
    case Mod.DStr{}:
      True{}
    case Mod.DArr{e}:
      True{}

def descs_all(ds: List<&2, Mod.Desc>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, r}:
      Bool.and(desc_fits(d), descs_all(r))

def descs_fit(+ds: List<&2, Mod.Desc>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Mod.Desc, ds)), descs_all(ds))

def txt_fits(t: Mod.Txt) -> Bool:
  match t:
    case Mod.NoTxt{}:
      True{}
    case Mod.Txt{s}:
      str_fits(s)

def blk_fits(b: Mod.Blk) -> Bool:
  match b:
    case Mod.Blk{k, t, x, d, m}:
      Bool.and(desc_fits(k), Bool.and(txt_fits(t), Bool.and(desc_fits(x), Bool.and(desc_fits(d), desc_fits(m)))))

def blks_all(bs: List<&2, Mod.Blk>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, r}:
      Bool.and(blk_fits(b), blks_all(r))

def blks_fit(+bs: List<&2, Mod.Blk>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Mod.Blk, bs)), blks_all(bs))

def q_fits(x: Mod.Q) -> Bool:
  match x:
    case Mod.Q{id, q, ins, kind, json, c, vs, yes, no}:
      Bool.and(str_fits(id), Bool.and(desc_fits(q), Bool.and(desc_fits(ins), Bool.and(txt_fits(kind), Bool.and(str_fits(json), Bool.and(desc_fits(c), Bool.and(descs_fit(vs), Bool.and(desc_fits(yes), desc_fits(no)))))))))

def qs_all(qs: List<&2, Mod.Q>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{q, r}:
      Bool.and(q_fits(q), qs_all(r))

def qs_fit(+qs: List<&2, Mod.Q>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Mod.Q, qs)), qs_all(qs))

# every count, number and length of the request fits the wire
def req_fits(q: FMod.Req) -> Bool:
  match q:
    case FMod.QClassify{x}:
      match x:
        case Mod.Ctx{c, st, im, +bs, qd, +qs}:
          Bool.and(desc_fits(c), Bool.and(desc_fits(st), Bool.and(desc_fits(im), Bool.and(blks_fit(bs), Bool.and(desc_fits(qd), qs_fit(qs))))))
    case FMod.QImages{x}:
      match x:
        case Mod.ICtx{c, i, +bs}:
          Bool.and(desc_fits(c), Bool.and(desc_fits(i), blks_fit(bs)))
    case FMod.QResolve{x}:
      match x:
        case Mod.Res{c, d, m, p, i, fc, fi, fk}:
          Bool.and(desc_fits(m), Bool.and(txt_fits(p), txt_fits(i)))
    case FMod.QCatalog{x}:
      match x:
        case Mod.Cat{n, +a, k, j}:
          Bool.and(str_fits(n), Bool.and(descs_fit(a), Bool.and(txt_fits(k), str_fits(j))))
    case FMod.QTool{g}:
      str_fits(g)
    case FMod.QResult{c, p, i, st, e}:
      Bool.and(str_fits(p), Bool.and(str_fits(i), Bool.and(str_fits(st), txt_fits(e))))
    case FMod.QUnread{c, e}:
      str_fits(e)
    case FMod.QCap{}:
      True{}

# LAW codemode_models_ffi_answers: a spelled request whose numbers fit the wire answers the spelled answer of the model
# EXCLUDES: a fact misread (a kind, a key, a text or a found type swapped,
#   a tag off by one), an answer spelled with another tag, a question
#   answered by another model function
law codemode_models_ffi_answers:
  for +q: FMod.Req
  for h: {req_fits(q) == True{} : Bool}
  {FMod.ffi(spell_req(q, "")) == spell_reply(q) : String}

# LAW codemode_models_ffi_reads: the entry's decoder reads a spelled request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law codemode_models_ffi_reads:
  for +q: FMod.Req
  for +rest: String
  for h: {req_fits(q) == True{} : Bool}
  {FMod.get_req(spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FMod.Req>}

# LAW codemode_models_ffi_exact: every input the entry does not answer with the error form is a spelled request that fits the wire
# EXCLUDES: an answer made for input that is no request (an unknown tag,
#   a missing field, a Nat of 15 or more digits, a short string, input
#   left over)
law codemode_models_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FMod.ffi(s)) == False{} : Bool}
  exs q: FMod.Req
  {s == spell_req(q, "") : String} & {req_fits(q) == True{} : Bool}

# LAW codemode_models_ffi_refuses: every error the entry answers is exactly "codemode_models: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law codemode_models_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FMod.ffi(s)) == True{} : Bool}
  {FMod.ffi(s) == Wr.err("codemode_models: malformed request") : String}

# LAW codemode_models_ffi_example: anchor: the bytes Rust sends and reads: a global's tool, a catalog error, serde's error, an images context, the cap, an unknown tag, input left over
# EXCLUDES: another spelling of a fact or an answer
law codemode_models_ffi_example:
  {[FMod.ffi("4,15,models.classify"), FMod.ffi("4,3,abc"), FMod.ffi("3,21,models.getModelOfType2,4,4,1,10,classifier12,\"classifier\""), FMod.ffi("6,0,4,boom"), FMod.ffi("1,6,1,5,input5,F2,6,2,4,type4,text1,4,text4,0,0,6,1,4,text0,4,0,0,"), FMod.ffi("7,"), FMod.ffi("8,"), FMod.ffi("4,1,xx")] == ["1,0,", "0,", "0,213,models.getModelOfType(type, provider, id) expects three strings, got (a string, a string). The provider and the id are separate arguments, for example models.getModelOfType(\"classifier\", \"typesafe\", \"jev-latest\").", "50,models.classify() could not read its context: boom", "1,218,models.generateImages() context.input[1] must be a text or image block, got { text }. Expected context: { input: [{ type: \"text\", text: <prompt> }, ...optional { type: \"image\", data: <base64>, mimeType } references] }.", "4,", Wr.err("codemode_models: malformed request"), Wr.err("codemode_models: malformed request")] : List<&2, String>}
