# eukhe: lemmas of the entry proofs of area codemode_models: the replies
#
# The entry's encoders are the spec's spellers
# (laws/codemode_models/entry.bend spell_problem, spell_rans, spell_cans,
# spell_tool, spell_result), so its answer is the spelled answer of the
# model (cmy.answer), and no answer opens with 'E' (cmy.not_err).

import Base
import ../../../bend/codemode_models.bend as Mod
import ../../../bend/ffi_codemode_models.bend as FMod
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/codemode_models/entry.bend as CodemodeModelsEntry
import ../../base/wire.bend as LWire
import ../../base/logic/string.bend as LLogicString

def cmy.problem(m: Maybe<&2, String>) -> {FMod.put_problem(m) == CodemodeModelsEntry.spell_problem(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      {==}

def cmy.rans(a: Mod.RAns) -> {FMod.put_rans(a) == CodemodeModelsEntry.spell_rans(a) : String}:
  match a:
    case Mod.RFail{t}:
      {==}
    case Mod.RDefault{}:
      {==}
    case Mod.RFound{}:
      {==}

def cmy.mtype(t: Mod.MType, +rest: String) -> {FMod.put_mtype(t, rest) == CodemodeModelsEntry.spell_mtype(t, rest) : String}:
  match t:
    case Mod.TChat{}:
      {==}
    case Mod.TImage{}:
      {==}
    case Mod.TClassifier{}:
      {==}

def cmy.cans(a: Mod.CAns) -> {FMod.put_cans(a) == CodemodeModelsEntry.spell_cans(a) : String}:
  match a:
    case Mod.CFail{t}:
      {==}
    case Mod.CModels{+t, +g}:
      Equal.cong(String, String, x => Wr.put_nat(1n, x), FMod.put_mtype(t, Wr.put_bool(g, "")), CodemodeModelsEntry.spell_mtype(t, Wr.put_bool(g, "")), cmy.mtype(t, Wr.put_bool(g, "")))
    case Mod.CAvailable{+t, +g}:
      Equal.cong(String, String, x => Wr.put_nat(2n, x), FMod.put_mtype(t, Wr.put_bool(g, "")), CodemodeModelsEntry.spell_mtype(t, Wr.put_bool(g, "")), cmy.mtype(t, Wr.put_bool(g, "")))
    case Mod.COne{+t}:
      Equal.cong(String, String, x => Wr.put_nat(3n, x), FMod.put_mtype(t, ""), CodemodeModelsEntry.spell_mtype(t, ""), cmy.mtype(t, ""))

def cmy.tool(m: Maybe<&2, Mod.Call>) -> {FMod.put_tool(m) == CodemodeModelsEntry.spell_tool(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      match c:
        case Mod.CClassify{}:
          {==}
        case Mod.CImages{}:
          {==}

def cmy.result(r: Bool & String) -> {FMod.put_result(r) == CodemodeModelsEntry.spell_result(r) : String}:
  match r:
    case (ok, t):
      {==}

# the entry's answer is the spelled answer of the model
def cmy.answer(q: FMod.Req) -> {FMod.answer(q) == CodemodeModelsEntry.spell_reply(q) : String}:
  match q:
    case FMod.QClassify{x}:
      cmy.problem(Mod.classify(x))
    case FMod.QImages{x}:
      cmy.problem(Mod.images(x))
    case FMod.QResolve{x}:
      cmy.rans(Mod.resolve(x))
    case FMod.QCatalog{x}:
      cmy.cans(Mod.catalog(x))
    case FMod.QTool{g}:
      cmy.tool(Mod.tool(g))
    case FMod.QResult{c, p, i, st, e}:
      cmy.result(Mod.result(c, p, i, st, e))
    case FMod.QUnread{c, e}:
      {==}
    case FMod.QCap{}:
      {==}

def cmy.problem_ne(m: Maybe<&2, String>) -> {LawsBase.wire_opens_err(FMod.put_problem(m)) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{t}:
      Wire.wire_nat_not_err(1n, Wr.put_str(t, ""))

def cmy.rans_ne(a: Mod.RAns) -> {LawsBase.wire_opens_err(FMod.put_rans(a)) == False{} : Bool}:
  match a:
    case Mod.RFail{t}:
      Wire.wire_nat_not_err(0n, Wr.put_str(t, ""))
    case Mod.RDefault{}:
      Wire.wire_nat_not_err(1n, "")
    case Mod.RFound{}:
      Wire.wire_nat_not_err(2n, "")

def cmy.cans_ne(a: Mod.CAns) -> {LawsBase.wire_opens_err(FMod.put_cans(a)) == False{} : Bool}:
  match a:
    case Mod.CFail{t}:
      Wire.wire_nat_not_err(0n, Wr.put_str(t, ""))
    case Mod.CModels{t, g}:
      Wire.wire_nat_not_err(1n, FMod.put_mtype(t, Wr.put_bool(g, "")))
    case Mod.CAvailable{t, g}:
      Wire.wire_nat_not_err(2n, FMod.put_mtype(t, Wr.put_bool(g, "")))
    case Mod.COne{t}:
      Wire.wire_nat_not_err(3n, FMod.put_mtype(t, ""))

def cmy.tool_ne(m: Maybe<&2, Mod.Call>) -> {LawsBase.wire_opens_err(FMod.put_tool(m)) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{c}:
      Wire.wire_nat_not_err(1n, FMod.put_call(c, ""))

def cmy.result_ne(r: Bool & String) -> {LawsBase.wire_opens_err(FMod.put_result(r)) == False{} : Bool}:
  match r:
    case (ok, t):
      Wire.wire_bool_not_err(ok, Wr.put_str(t, ""))

def cmy.str_ne(+a: String) -> {LawsBase.wire_opens_err(Wr.put_str(a, "")) == False{} : Bool}:
  %Equal.sym(String, Wr.put_str(a, ""), Wr.put_nat(String.length(a), LLogicString.wr_app(a, "")), LWire.wr_put_str(a, "")) : {LawsBase.wire_opens_err(_) == False{} : Bool}
  Wire.wire_nat_not_err(String.length(a), LLogicString.wr_app(a, ""))

# no answer of the entry opens with 'E'
def cmy.not_err(q: FMod.Req) -> {LawsBase.wire_opens_err(FMod.answer(q)) == False{} : Bool}:
  match q:
    case FMod.QClassify{x}:
      cmy.problem_ne(Mod.classify(x))
    case FMod.QImages{x}:
      cmy.problem_ne(Mod.images(x))
    case FMod.QResolve{x}:
      cmy.rans_ne(Mod.resolve(x))
    case FMod.QCatalog{x}:
      cmy.cans_ne(Mod.catalog(x))
    case FMod.QTool{g}:
      cmy.tool_ne(Mod.tool(g))
    case FMod.QResult{c, p, i, st, e}:
      cmy.result_ne(Mod.result(c, p, i, st, e))
    case FMod.QUnread{c, e}:
      cmy.str_ne(Mod.unread(c, e))
    case FMod.QCap{}:
      Wire.wire_nat_not_err(Mod.max_calls(), "")
