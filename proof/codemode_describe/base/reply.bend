# eukhe: lemmas of the entry proofs of area codemode_describe: the replies
#
# The entry's encoders are the spec's spellers (laws/codemode_describe.bend
# spell_mnats, spell_parts, spell_section), so its answer is the spelled
# answer of the model (cdy.answer), and no answer opens with 'E'
# (cdy.not_err).

import Base
import ../../../bend/codemode_describe.bend as Dsc
import ../../../bend/ffi_codemode_describe.bend as FDsc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/codemode_describe.bend as CodemodeDescribe
import ../../base/wire.bend as LWire
import ../../base/logic/string.bend as LLogicString

def cdy.mnats(xs: List<&2, Maybe<&2, Nat>>, +rest: String) -> {FDsc.put_mnats(xs, rest) == CodemodeDescribe.spell_mnats(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      match x:
        case None{}:
          %cdy.mnats(r, rest) : {Wr.put_nat(0n, FDsc.put_mnats(r, rest)) == Wr.put_nat(0n, _) : String}
          {==}
        case Some{+n}:
          %cdy.mnats(r, rest) : {Wr.put_nat(1n, Wr.put_nat(n, FDsc.put_mnats(r, rest))) == Wr.put_nat(1n, Wr.put_nat(n, _)) : String}
          {==}

def cdy.parts(ps: List<&2, Dsc.Part>, +rest: String) -> {FDsc.put_parts(ps, rest) == CodemodeDescribe.spell_parts(ps, rest) : String}:
  match ps:
    case Nil{}:
      {==}
    case Con{p, +r}:
      match p:
        case Dsc.Lit{+t}:
          %cdy.parts(r, rest) : {Wr.put_nat(0n, Wr.put_str(t, FDsc.put_parts(r, rest))) == Wr.put_nat(0n, Wr.put_str(t, _)) : String}
          {==}
        case Dsc.Sect{+n}:
          %cdy.parts(r, rest) : {Wr.put_nat(1n, Wr.put_nat(n, FDsc.put_parts(r, rest))) == Wr.put_nat(1n, Wr.put_nat(n, _)) : String}
          {==}

def cdy.section(m: Maybe<&2, List<&2, Dsc.Part>>) -> {FDsc.put_section(m) == CodemodeDescribe.spell_section(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{+ps}:
      %cdy.parts(ps, "") : {Wr.put_nat(1n, Wr.put_nat(List.length(&2, Dsc.Part, ps), FDsc.put_parts(ps, ""))) == Wr.put_nat(1n, Wr.put_nat(List.length(&2, Dsc.Part, ps), _)) : String}
      {==}

def cdy.spaces(ns: List<&2, String>, +ps: List<&2, String>) -> {FDsc.spaces_of(ns, ps) == CodemodeDescribe.spaces_spec(ns, ps) : List<&2, Maybe<&2, Nat>>}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +r}:
      %cdy.spaces(r, ps) : {Dsc.space_of(n, ps) <> FDsc.spaces_of(r, ps) == Dsc.space_of(n, ps) <> _ : List<&2, Maybe<&2, Nat>>}
      {==}

# the entry's answer is the spelled answer of the model
def cdy.answer(q: FDsc.Req) -> {FDsc.answer(q) == CodemodeDescribe.spell_reply(q) : String}:
  match q:
    case FDsc.QSpaces{+ns, +ps}:
      +xs = FDsc.spaces_of(ns, ps)
      %cdy.spaces(ns, ps) : {Wr.put_nat(List.length(&2, Maybe<&2, Nat>, xs), FDsc.put_mnats(xs, "")) == Wr.put_nat(List.length(&2, Maybe<&2, Nat>, _), CodemodeDescribe.spell_mnats(_, "")) : String}
      %cdy.mnats(xs, "") : {Wr.put_nat(List.length(&2, Maybe<&2, Nat>, xs), FDsc.put_mnats(xs, "")) == Wr.put_nat(List.length(&2, Maybe<&2, Nat>, xs), _) : String}
      {==}
    case FDsc.QSection{ts, ss, b}:
      cdy.section(Dsc.section(ts, ss, b))
    case FDsc.QDescribe{m, c}:
      {==}

def cdy.section_ne(m: Maybe<&2, List<&2, Dsc.Part>>) -> {LawsBase.wire_opens_err(FDsc.put_section(m)) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{+ps}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(List.length(&2, Dsc.Part, ps), FDsc.put_parts(ps, "")))

def cdy.str_ne(+a: String) -> {LawsBase.wire_opens_err(Wr.put_str(a, "")) == False{} : Bool}:
  %Equal.sym(String, Wr.put_str(a, ""), Wr.put_nat(String.length(a), LLogicString.wr_app(a, "")), LWire.wr_put_str(a, "")) : {LawsBase.wire_opens_err(_) == False{} : Bool}
  Wire.wire_nat_not_err(String.length(a), LLogicString.wr_app(a, ""))

# no answer of the entry opens with 'E'
def cdy.not_err(q: FDsc.Req) -> {LawsBase.wire_opens_err(FDsc.answer(q)) == False{} : Bool}:
  match q:
    case FDsc.QSpaces{+ns, +ps}:
      +xs = FDsc.spaces_of(ns, ps)
      Wire.wire_nat_not_err(List.length(&2, Maybe<&2, Nat>, xs), FDsc.put_mnats(xs, ""))
    case FDsc.QSection{ts, ss, b}:
      cdy.section_ne(Dsc.section(ts, ss, b))
    case FDsc.QDescribe{m, c}:
      cdy.str_ne(Dsc.description(m, c))
