# eukhe: lemmas of the proofs of area codemode_id

import Base
import ../../bend/codemode_id.bend as Ci
import ../../bend/ffi_codemode_id.bend as FCi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../base/wire.bend as LWire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../../laws/codemode_id.bend as CodemodeId

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

# The identifier, char by char (R1)
# ---------------------------------

def ci_keep_false(b: Bool, -c: Char, e: {b == False{} : Bool}) -> {Ci.keep(b, c) == '_' : Char}:
  match b:
    case True{}:
      LLogicLogic.pt.absurd({c == '_' : Char}, e)
    case False{}:
      {==}

def ci_start_false(a: Bool, e: {Bool.or(a, False{}) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

# the later chars keep their count
def ci_len_rest(t: String) -> {String.length(Ci.rest(t)) == String.length(t) : Nat}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, r}:
      Equal.cong(Nat, Nat, n => 1n+n, String.length(Ci.rest(r)), String.length(r), ci_len_rest(r))

# the later char of code x after the chars t stands where it stood, kept or `_` by its class
def ci_rest_get(t: String, +x: U32, b: String) -> {String.get(Ci.rest(String.append(t, SCon{Chr{x}, b})), String.length(t)) == Some{Ci.keep(Ci.part(Chr{x}), Chr{x})} : Maybe<&2, Char>}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, r}:
      ci_rest_get(r, x, b)

# The test (R1)
# -------------

def ci_word_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case True{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, ci_word_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}
            case False{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, ci_word_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}

def ci_u32_refl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      ci_word_refl(32n, w)

def ci_go_lt(a: String, b: String) -> {String.order.go(a, b, LT{}) == LT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def ci_go_gt(a: String, b: String) -> {String.order.go(a, b, GT{}) == GT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

# two texts with the same first char compare as the rest
def ci_eq_same(+x: U32, a: String, b: String) -> {String.eq(SCon{Chr{x}, a}, SCon{Chr{x}, b}) == String.eq(a, b) : Bool}:
  %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, ci_u32_refl(x)) : {Cmp.is_eq(String.order.go(a, b, _)) == String.eq(a, b) : Bool}
  {==}

# `_` first is not the char of code x first, when x is not `_`
def ci_eq_under(+x: U32, +a: String, +b: String, c: Cmp, ec: {U32.cmp(95, x) == c : Cmp}, hx: {95 == x : U32} -> {False{} == True{} : Bool}) -> {String.eq(SCon{'_', a}, SCon{Chr{x}, b}) == False{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(95, x), LT{}, ec) : {Cmp.is_eq(String.order.go(a, b, _)) == False{} : Bool}
      %Equal.sym(Cmp, String.order.go(a, b, LT{}), LT{}, ci_go_lt(a, b)) : {Cmp.is_eq(_) == False{} : Bool}
      {==}
    case EQ{}:
      LLogicLogic.absurd({String.eq(SCon{'_', a}, SCon{Chr{x}, b}) == False{} : Bool}, hx(PWireBoolExact.wr_cmp_eq(95, x)(ec)))
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(95, x), GT{}, ec) : {Cmp.is_eq(String.order.go(a, b, _)) == False{} : Bool}
      %Equal.sym(Cmp, String.order.go(a, b, GT{}), GT{}, ci_go_gt(a, b)) : {Cmp.is_eq(_) == False{} : Bool}
      {==}

# a char of code x the continue class refuses is not `_` (which it takes)
def ci_not_under_part(+x: U32, h: {Ci.part(Chr{x}) == False{} : Bool}, e: {95 == x : U32}) -> {False{} == True{} : Bool}:
  +ef = Equal.cong(U32, Bool, u => Ci.part(Chr{u}), 95, x, e)
  Equal.trans(Bool, False{}, Ci.part(Chr{x}), True{}, Equal.sym(Bool, Ci.part(Chr{x}), False{}, h), Equal.sym(Bool, True{}, Ci.part(Chr{x}), ef))

# a char of code x the start class refuses is not `_` (which it takes)
def ci_not_under_start(+x: U32, h: {Ci.start(Chr{x}) == False{} : Bool}, e: {95 == x : U32}) -> {False{} == True{} : Bool}:
  +ef = Equal.cong(U32, Bool, u => Ci.start(Chr{u}), 95, x, e)
  Equal.trans(Bool, False{}, Ci.start(Chr{x}), True{}, Equal.sym(Bool, Ci.start(Chr{x}), False{}, h), Equal.sym(Bool, True{}, Ci.start(Chr{x}), ef))

def ci_rest_step(b: Bool, +x: U32, +r: String, eb: {Ci.part(Chr{x}) == b : Bool}, ih: {String.eq(Ci.rest(r), r) == Ci.parts(r) : Bool}) -> {String.eq(SCon{Ci.keep(b, Chr{x}), Ci.rest(r)}, SCon{Chr{x}, r}) == Bool.and(b, Ci.parts(r)) : Bool}:
  match b:
    case True{}:
      Equal.trans(Bool, String.eq(SCon{Chr{x}, Ci.rest(r)}, SCon{Chr{x}, r}), String.eq(Ci.rest(r), r), Ci.parts(r), ci_eq_same(x, Ci.rest(r), r), ih)
    case False{}:
      ci_eq_under(x, Ci.rest(r), r, U32.cmp(95, x), {==}, e => ci_not_under_part(x, eb, e))

# the later chars are their own when every one may continue an identifier
def ci_rest_eq(t: String) -> {String.eq(Ci.rest(t), t) == Ci.parts(t) : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+x}:
          ci_rest_step(Ci.part(Chr{x}), x, r, {==}, ci_rest_eq(r))

def ci_test_step(b: Bool, +x: U32, +t: String, eb: {Ci.start(Chr{x}) == b : Bool}) -> {Bool.and(b, Ci.parts(t)) == String.eq(SCon{Ci.keep(b, Chr{x}), Ci.rest(t)}, SCon{Chr{x}, t}) : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, String.eq(SCon{Chr{x}, Ci.rest(t)}, SCon{Chr{x}, t}), Ci.parts(t), Equal.trans(Bool, String.eq(SCon{Chr{x}, Ci.rest(t)}, SCon{Chr{x}, t}), String.eq(Ci.rest(t), t), Ci.parts(t), ci_eq_same(x, Ci.rest(t), t), ci_rest_eq(t)))
    case False{}:
      Equal.sym(Bool, String.eq(SCon{'_', Ci.rest(t)}, SCon{Chr{x}, t}), False{}, ci_eq_under(x, Ci.rest(t), t, U32.cmp(95, x), {==}, e => ci_not_under_start(x, eb, e)))

# The entry (R2)
# --------------

def ci_mu_goal(+s: String) -> Type:
  &q: FCi.Req -> &rest: String -> {(s, CodemodeId.req_fits(q)) == (CodemodeId.spell_req(q, rest), True{}) : String & Bool}

def ci_mu_pair(+s: String, +q: FCi.Req, +rest: String, e1: {s == CodemodeId.spell_req(q, rest) : String}, e2: {CodemodeId.req_fits(q) == True{} : Bool}) -> {(s, CodemodeId.req_fits(q)) == (CodemodeId.spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, CodemodeId.spell_req(q, rest), e1) : {(_, CodemodeId.req_fits(q)) == (CodemodeId.spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, CodemodeId.req_fits(q), True{}, e2) : {(CodemodeId.spell_req(q, rest), _) == (CodemodeId.spell_req(q, rest), True{}) : String & Bool}
  {==}

def ci_mu_id(+s: String, +s1: String, d: Wr.Dec<String>, +ed: {Wr.get_str(s1) == d : Wr.Dec<String>}, es: {s == Wr.put_nat(0n, s1) : String}, other: {String.eq(FCi.ffi.got(FCi.get_id(d)), Wr.err("codemode_id: malformed request")) == False{} : Bool}) -> ci_mu_goal(s):
  match d:
    case Wr.Got{+n, +r}:
      (FCi.QId{n}, (r, ci_mu_pair(s, FCi.QId{n}, r, ci_sub(0n, s, s1, Wr.put_str(n, r), Wire.wire_str_exact(s1, n, r, ed), es), Wire.wire_str_decoded_fits(s1, n, r, ed))))
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(ci_mu_goal(s), other)

def ci_mu_is(+s: String, +s1: String, d: Wr.Dec<String>, +ed: {Wr.get_str(s1) == d : Wr.Dec<String>}, es: {s == Wr.put_nat(1n, s1) : String}, other: {String.eq(FCi.ffi.got(FCi.get_is(d)), Wr.err("codemode_id: malformed request")) == False{} : Bool}) -> ci_mu_goal(s):
  match d:
    case Wr.Got{+n, +r}:
      (FCi.QIs{n}, (r, ci_mu_pair(s, FCi.QIs{n}, r, ci_sub(1n, s, s1, Wr.put_str(n, r), Wire.wire_str_exact(s1, n, r, ed), es), Wire.wire_str_decoded_fits(s1, n, r, ed))))
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(ci_mu_goal(s), other)

# an answer that is not the malformed error comes from a spelled request that fits
def ci_mu_top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, other: {String.eq(FCi.ffi.got(FCi.get_req.start(d)), Wr.err("codemode_id: malformed request")) == False{} : Bool}) -> ci_mu_goal(s):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          ci_mu_id(s, s1, Wr.get_str(s1), {==}, Wire.wire_nat_exact(s, 0n, s1, ed), other)
        case 1n:
          ci_mu_is(s, s1, Wr.get_str(s1), {==}, Wire.wire_nat_exact(s, 1n, s1, ed), other)
        case 2n+u:
          LLogicLogic.pt.absurd(ci_mu_goal(s), other)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(ci_mu_goal(s), other)
