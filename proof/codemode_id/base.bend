# eukhe: lemmas of the proofs of area codemode_id

import Base
import ../../bend/codemode_id.bend as Ci
import ../../bend/ffi_codemode_id.bend as FCi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_str_exact.bend as PWireStrExact
import ../base/wire.bend as LWire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../../laws/codemode_id.bend as CodemodeId

def ci_keep_fix(b: Bool, c: Char) -> {Ci.keep(b, c) == CodemodeId.fix_spec(b, c) : Char}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ci_or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ci_and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.absurd({False{} == True{} : Bool}, e)

def ci_and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LLogicLogic.absurd({b == True{} : Bool}, e)

def ci_keep_true(b: Bool, -c: Char, e: {b == True{} : Bool}) -> {Ci.keep(b, c) == c : Char}:
  match b:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.absurd({'_' == c : Char}, e)

def ci_rest(t: String) -> {Ci.rest(t) == CodemodeId.id_spec.go(t, False{}) : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, r}:
      match c:
        case Chr{+x}:
          %ci_rest(r) : {SCon{Ci.keep(Ci.part(Chr{x}), Chr{x}), Ci.rest(r)} == SCon{CodemodeId.fix_spec(CodemodeId.ok_spec(False{}, x), Chr{x}), _} : String}
          %ci_keep_fix(Ci.part(Chr{x}), Chr{x}) : {SCon{Ci.keep(Ci.part(Chr{x}), Chr{x}), Ci.rest(r)} == SCon{_, Ci.rest(r)} : String}
          {==}

# a later char of an identifier, kept or `_`, may continue it
def ci_parts_at(b: Bool, +x: U32, e: {Ci.part(Chr{x}) == b : Bool}, -r: String, ih: {CodemodeId.parts_spec(r) == True{} : Bool}) -> {CodemodeId.parts_spec(SCon{Ci.keep(b, Chr{x}), r}) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Ci.part(Chr{x}), True{}, e) : {Bool.and(_, CodemodeId.parts_spec(r)) == True{} : Bool}
      ih
    case False{}:
      ih

def ci_parts(t: String) -> {CodemodeId.parts_spec(Ci.rest(t)) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, r}:
      match c:
        case Chr{+x}:
          ci_parts_at(Ci.part(Chr{x}), x, {==}, Ci.rest(r), ci_parts(r))

def ci_head_at(b: Bool, +x: U32, e: {Ci.start(Chr{x}) == b : Bool}, +r: String) -> {CodemodeId.ident_spec(SCon{Ci.keep(b, Chr{x}), Ci.rest(r)}) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Ci.start(Chr{x}), True{}, e) : {Bool.and(Bool.or(_, False{}), CodemodeId.parts_spec(Ci.rest(r))) == True{} : Bool}
      ci_parts(r)
    case False{}:
      ci_parts(r)

# a string whose chars may all continue an identifier keeps them all
def ci_rest_keeps(+t: String, +ok: {CodemodeId.parts_spec(t) == True{} : Bool}) -> {Ci.rest(t) == t : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, r}:
      match c:
        case Chr{+x}:
          +h = ci_and_l(Ci.part(Chr{x}), CodemodeId.parts_spec(r), ok)
          %ci_keep_true(Ci.part(Chr{x}), Chr{x}, h) : {SCon{Ci.keep(Ci.part(Chr{x}), Chr{x}), Ci.rest(r)} == SCon{_, r} : String}
          %ci_rest_keeps(r, ci_and_r(Ci.part(Chr{x}), CodemodeId.parts_spec(r), ok)) : {SCon{Ci.keep(Ci.part(Chr{x}), Chr{x}), Ci.rest(r)} == SCon{Ci.keep(Ci.part(Chr{x}), Chr{x}), _} : String}
          {==}

def ci_and_both(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case True{}:
      ({==}, e)
    case False{}:
      LLogicLogic.absurd({False{} == True{} : Bool} & {b == True{} : Bool}, e)

def ci_start_true(a: Bool, e: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def ci_keeps_head(+x: U32, +t: String, hs: {Bool.or(Ci.start(Chr{x}), False{}) == True{} : Bool} & {CodemodeId.parts_spec(t) == True{} : Bool}) -> {Ci.of(SCon{Chr{x}, t}) == SCon{Chr{x}, t} : String}:
  (h1, h2) = hs
  %ci_keep_true(Ci.start(Chr{x}), Chr{x}, ci_start_true(Ci.start(Chr{x}), h1)) : {SCon{Ci.keep(Ci.start(Chr{x}), Chr{x}), Ci.rest(t)} == SCon{_, t} : String}
  %ci_rest_keeps(t, h2) : {SCon{Ci.keep(Ci.start(Chr{x}), Chr{x}), Ci.rest(t)} == SCon{Ci.keep(Ci.start(Chr{x}), Chr{x}), _} : String}
  {==}


def ci_parts_eq(t: String) -> {Ci.parts(t) == CodemodeId.parts_spec(t) : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, r}:
      match c:
        case Chr{+x}:
          %ci_parts_eq(r) : {Bool.and(Ci.part(Chr{x}), Ci.parts(r)) == Bool.and(Ci.part(Chr{x}), _) : Bool}
          {==}

# s is the tag t, then s1, and s1 is x
def ci_sub(-t: Nat, -s: String, -s1: String, -x: String, e1: {s1 == x : String}, es: {s == Wr.put_nat(t, s1) : String}) -> {s == Wr.put_nat(t, x) : String}:
  %e1 : {s == Wr.put_nat(t, _) : String}
  es

def ci_ex_id(+s: String, +s1: String, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}, es: {s == Wr.put_nat(0n, s1) : String}, ok: {LawsBase.wire_opens_err(FCi.ffi.got(FCi.get_id(d))) == False{} : Bool}) -> Sigma<&1, &1, FCi.Req, q => {s == CodemodeId.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+n, r}:
      match r:
        case SNil{}:
          (FCi.QId{n}, ci_sub(0n, s, s1, Wr.put_str(n, ""), Wire.wire_str_exact(s1, n, "", ed), es))
        case SCon{x, y}:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FCi.Req, q => {s == CodemodeId.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FCi.Req, q => {s == CodemodeId.spell_req(q, "") : String}>, ok)

def ci_ex_is(+s: String, +s1: String, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}, es: {s == Wr.put_nat(1n, s1) : String}, ok: {LawsBase.wire_opens_err(FCi.ffi.got(FCi.get_is(d))) == False{} : Bool}) -> Sigma<&1, &1, FCi.Req, q => {s == CodemodeId.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+n, r}:
      match r:
        case SNil{}:
          (FCi.QIs{n}, ci_sub(1n, s, s1, Wr.put_str(n, ""), Wire.wire_str_exact(s1, n, "", ed), es))
        case SCon{x, y}:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FCi.Req, q => {s == CodemodeId.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FCi.Req, q => {s == CodemodeId.spell_req(q, "") : String}>, ok)

# a reply that is no error comes from a spelled request
def ci_ex_top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FCi.ffi.got(FCi.get_req.start(d))) == False{} : Bool}) -> Sigma<&1, &1, FCi.Req, q => {s == CodemodeId.spell_req(q, "") : String}>:
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          ci_ex_id(s, s1, Wr.get_str(s1), {==}, Wire.wire_nat_exact(s, 0n, s1, ed), ok)
        case 1n:
          ci_ex_is(s, s1, Wr.get_str(s1), {==}, Wire.wire_nat_exact(s, 1n, s1, ed), ok)
        case 2n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, FCi.Req, q => {s == CodemodeId.spell_req(q, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, FCi.Req, q => {s == CodemodeId.spell_req(q, "") : String}>, ok)

def ci_bad_id(d: Wr.Dec<String>, bad: {CodemodeId.bad_spec.str(d) == True{} : Bool}) -> {FCi.ffi.got(FCi.get_id(d)) == Wr.err("codemode_id: malformed request") : String}:
  match d:
    case Wr.Got{n, r}:
      LLogicLogic.absurd({FCi.ffi.got(FCi.get_id(Wr.Got{n, r})) == Wr.err("codemode_id: malformed request") : String}, bad)
    case Wr.Bad{}:
      {==}

def ci_bad_is(d: Wr.Dec<String>, bad: {CodemodeId.bad_spec.str(d) == True{} : Bool}) -> {FCi.ffi.got(FCi.get_is(d)) == Wr.err("codemode_id: malformed request") : String}:
  match d:
    case Wr.Got{n, r}:
      LLogicLogic.absurd({FCi.ffi.got(FCi.get_is(Wr.Got{n, r})) == Wr.err("codemode_id: malformed request") : String}, bad)
    case Wr.Bad{}:
      {==}

def ci_bad(d: Wr.Dec<Nat>, bad: {CodemodeId.bad_spec(d) == True{} : Bool}) -> {FCi.ffi.got(FCi.get_req.start(d)) == Wr.err("codemode_id: malformed request") : String}:
  match d:
    case Wr.Got{t, s1}:
      match t:
        case 0n:
          ci_bad_id(Wr.get_str(s1), bad)
        case 1n:
          ci_bad_is(Wr.get_str(s1), bad)
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}
