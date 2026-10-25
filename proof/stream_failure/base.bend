# eukhe: lemmas shared by the proofs of area stream_failure: the code's
# list of tests is the spec's chain of choices, each test is the spec's
# (the searches by text_pat_hit, the tables computing alike), and each
# text part is the spec's

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/stream_failure.bend as Sf
import ../../bend/ffi_stream_failure.bend as FSf
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as OverflowLaws
import ../../laws/stream_failure.bend as StreamFailure
import ../text_pat/text_pat_hit.bend as PTextPatHit
import ../text_pat/text_pat_lower.bend as PTextPatLower

# Choices
# -------

# the code's list of tests as the spec's chain of choices
def sfb.chain(cs: List<&2, Sf.Test>, d: Sf.Cause) -> Sf.Cause:
  match cs:
    case Nil{}:
      d
    case c <> rest:
      match c:
        case Sf.Test{b, k}:
          StreamFailure.sp_pick(b, k, sfb.chain(rest, d))

def sfb.pick_cong(-b: Bool, -b2: Bool, k: Sf.Cause, -x: Sf.Cause, -y: Sf.Cause, eb: {b == b2 : Bool}, ex: {x == y : Sf.Cause}) -> {StreamFailure.sp_pick(b, k, x) == StreamFailure.sp_pick(b2, k, y) : Sf.Cause}:
  Equal.trans(Sf.Cause, StreamFailure.sp_pick(b, k, x), StreamFailure.sp_pick(b2, k, x), StreamFailure.sp_pick(b2, k, y), Equal.cong(Bool, Sf.Cause, z => StreamFailure.sp_pick(z, k, x), b, b2, eb), Equal.cong(Sf.Cause, Sf.Cause, z => StreamFailure.sp_pick(b2, k, z), x, y, ex))

def sfb.st(st: Maybe<&2, Nat>, +n: Nat) -> {Sf.is_status(st, n) == StreamFailure.sp_st(st, n) : Bool}:
  match st:
    case None{}:
      {==}
    case Some{s}:
      {==}

def sfb.st5(st: Maybe<&2, Nat>) -> {Sf.is_5xx(st) == StreamFailure.sp_st5(st) : Bool}:
  match st:
    case None{}:
      {==}
    case Some{s}:
      {==}

def sfb.lit(s: String, rest: List<&2, Tp.It>) -> {Sf.lit(s, rest) == OverflowLaws.sp_s(s, rest) : List<&2, Tp.It>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(List<&2, Tp.It>, Sf.lit(t, rest), OverflowLaws.sp_s(t, rest), sfb.lit(t, rest)) : {Tp.One{Tp.CLit{c}} <> _ == Tp.One{Tp.CLit{c}} <> OverflowLaws.sp_s(t, rest) : List<&2, Tp.It>}
      {==}

def sfb.lits(xs: List<&2, String>) -> {Sf.lits.go(xs) == OverflowLaws.sp_lits(xs) : List<&2, List<&2, Tp.It>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(List<&2, List<&2, Tp.It>>, Sf.lits.go(t), OverflowLaws.sp_lits(t), sfb.lits(t)) : {Sf.lit(x, []) <> _ == OverflowLaws.sp_s(x, Nil{}) <> OverflowLaws.sp_lits(t) : List<&2, List<&2, Tp.It>>}
      %Equal.sym(List<&2, Tp.It>, Sf.lit(x, []), OverflowLaws.sp_s(x, Nil{}), sfb.lit(x, [])) : {_ <> OverflowLaws.sp_lits(t) == OverflowLaws.sp_s(x, Nil{}) <> OverflowLaws.sp_lits(t) : List<&2, List<&2, Tp.It>>}
      {==}

# the code's needle test is the spec's
def sfb.has(+t: String, +xs: List<&2, String>) -> {Sf.has(t, xs) == StreamFailure.sp_has(t, xs) : Bool}:
  %Equal.sym(List<&2, List<&2, Tp.It>>, Sf.lits.go(xs), OverflowLaws.sp_lits(xs), sfb.lits(xs)) : {Tp.hit(t, Tp.Pat{False{}, _}) == StreamFailure.sp_has(t, xs) : Bool}
  TextPat.text_pat_hit(t, Tp.Pat{False{}, OverflowLaws.sp_lits(xs)})

def sfb.or_cong(-a: Bool, -a2: Bool, -b: Bool, -b2: Bool, ea: {a == a2 : Bool}, eb: {b == b2 : Bool}) -> {Bool.or(a, b) == Bool.or(a2, b2) : Bool}:
  Equal.trans(Bool, Bool.or(a, b), Bool.or(a2, b), Bool.or(a2, b2), Equal.cong(Bool, Bool, z => Bool.or(z, b), a, a2, ea), Equal.cong(Bool, Bool, z => Bool.or(a2, z), b, b2, eb))

# the code's first test that holds is the spec's chain
def sfb.first(cs: List<&2, Sf.Test>, d: Sf.Cause) -> {Sf.first(cs, d) == sfb.chain(cs, d) : Sf.Cause}:
  match cs:
    case Nil{}:
      {==}
    case c <> +rest:
      match c:
        case Sf.Test{b, k}:
          match b:
            case True{}:
              {==}
            case False{}:
              sfb.first(rest, d)

# the code's cause of a lowered type is the spec's
def sfb.cause(+t: String, +st: Maybe<&2, Nat>) -> {Sf.classify.go(t, st) == StreamFailure.sp_cause(t, st) : Sf.Cause}:
  Equal.trans(Sf.Cause, Sf.first([Sf.Test{Sf.is_status(st, 402n), Sf.KPayment{}}, Sf.Test{String.eq(t, "refusal"), Sf.KRefusal{}}, Sf.Test{Tp.hit(t, Sf.safety_pat()), Sf.KSafety{}}, Sf.Test{Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Sf.KOverloaded{}}, Sf.Test{Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}}, Sf.Test{Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}}, Sf.Test{Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}}, Sf.Test{Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}}, Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], Sf.KUnknown{}), sfb.chain([Sf.Test{Sf.is_status(st, 402n), Sf.KPayment{}}, Sf.Test{String.eq(t, "refusal"), Sf.KRefusal{}}, Sf.Test{Tp.hit(t, Sf.safety_pat()), Sf.KSafety{}}, Sf.Test{Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Sf.KOverloaded{}}, Sf.Test{Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}}, Sf.Test{Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}}, Sf.Test{Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}}, Sf.Test{Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}}, Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], Sf.KUnknown{}), StreamFailure.sp_cause(t, st), sfb.first([Sf.Test{Sf.is_status(st, 402n), Sf.KPayment{}}, Sf.Test{String.eq(t, "refusal"), Sf.KRefusal{}}, Sf.Test{Tp.hit(t, Sf.safety_pat()), Sf.KSafety{}}, Sf.Test{Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Sf.KOverloaded{}}, Sf.Test{Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}}, Sf.Test{Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}}, Sf.Test{Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}}, Sf.Test{Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}}, Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], Sf.KUnknown{}), sfb.pick_cong(Sf.is_status(st, 402n), StreamFailure.sp_st(st, 402n), Sf.KPayment{}, StreamFailure.sp_pick(String.eq(t, "refusal"), Sf.KRefusal{}, StreamFailure.sp_pick(Tp.hit(t, Sf.safety_pat()), Sf.KSafety{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Sf.KOverloaded{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(Sf.has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}, Sf.KUnknown{}))))))))), StreamFailure.sp_pick(String.eq(t, "refusal"), Sf.KRefusal{}, StreamFailure.sp_pick(TextPat.sp_any(t, [StreamFailure.sp_safety()]), Sf.KSafety{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["overloaded"]), StreamFailure.sp_st(st, 529n)), Sf.KOverloaded{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), StreamFailure.sp_st(st, 429n)), Sf.KRateLimit{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["authentication", "unauthorized"]), StreamFailure.sp_st(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(TextPat.sp_any(t, [StreamFailure.sp_permission()]), StreamFailure.sp_st(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["invalid_request", "not_found_error"]), Bool.or(StreamFailure.sp_st(st, 400n), StreamFailure.sp_st(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(StreamFailure.sp_has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_st5(st)), Sf.KServer{}, Sf.KUnknown{}))))))))), sfb.st(st, 402n), sfb.pick_cong(String.eq(t, "refusal"), String.eq(t, "refusal"), Sf.KRefusal{}, StreamFailure.sp_pick(Tp.hit(t, Sf.safety_pat()), Sf.KSafety{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Sf.KOverloaded{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(Sf.has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}, Sf.KUnknown{})))))))), StreamFailure.sp_pick(TextPat.sp_any(t, [StreamFailure.sp_safety()]), Sf.KSafety{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["overloaded"]), StreamFailure.sp_st(st, 529n)), Sf.KOverloaded{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), StreamFailure.sp_st(st, 429n)), Sf.KRateLimit{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["authentication", "unauthorized"]), StreamFailure.sp_st(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(TextPat.sp_any(t, [StreamFailure.sp_permission()]), StreamFailure.sp_st(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["invalid_request", "not_found_error"]), Bool.or(StreamFailure.sp_st(st, 400n), StreamFailure.sp_st(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(StreamFailure.sp_has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_st5(st)), Sf.KServer{}, Sf.KUnknown{})))))))), {==}, sfb.pick_cong(Tp.hit(t, Sf.safety_pat()), TextPat.sp_any(t, [StreamFailure.sp_safety()]), Sf.KSafety{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Sf.KOverloaded{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(Sf.has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}, Sf.KUnknown{}))))))), StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["overloaded"]), StreamFailure.sp_st(st, 529n)), Sf.KOverloaded{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), StreamFailure.sp_st(st, 429n)), Sf.KRateLimit{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["authentication", "unauthorized"]), StreamFailure.sp_st(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(TextPat.sp_any(t, [StreamFailure.sp_permission()]), StreamFailure.sp_st(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["invalid_request", "not_found_error"]), Bool.or(StreamFailure.sp_st(st, 400n), StreamFailure.sp_st(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(StreamFailure.sp_has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_st5(st)), Sf.KServer{}, Sf.KUnknown{}))))))), TextPat.text_pat_hit(t, Sf.safety_pat()), sfb.pick_cong(Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Bool.or(StreamFailure.sp_has(t, ["overloaded"]), StreamFailure.sp_st(st, 529n)), Sf.KOverloaded{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(Sf.has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}, Sf.KUnknown{})))))), StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), StreamFailure.sp_st(st, 429n)), Sf.KRateLimit{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["authentication", "unauthorized"]), StreamFailure.sp_st(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(TextPat.sp_any(t, [StreamFailure.sp_permission()]), StreamFailure.sp_st(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["invalid_request", "not_found_error"]), Bool.or(StreamFailure.sp_st(st, 400n), StreamFailure.sp_st(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(StreamFailure.sp_has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_st5(st)), Sf.KServer{}, Sf.KUnknown{})))))), sfb.or_cong(Sf.has(t, ["overloaded"]), StreamFailure.sp_has(t, ["overloaded"]), Sf.is_status(st, 529n), StreamFailure.sp_st(st, 529n), sfb.has(t, ["overloaded"]), sfb.st(st, 529n)), sfb.pick_cong(Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Bool.or(StreamFailure.sp_has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), StreamFailure.sp_st(st, 429n)), Sf.KRateLimit{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(Sf.has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}, Sf.KUnknown{}))))), StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["authentication", "unauthorized"]), StreamFailure.sp_st(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(TextPat.sp_any(t, [StreamFailure.sp_permission()]), StreamFailure.sp_st(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["invalid_request", "not_found_error"]), Bool.or(StreamFailure.sp_st(st, 400n), StreamFailure.sp_st(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(StreamFailure.sp_has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_st5(st)), Sf.KServer{}, Sf.KUnknown{}))))), sfb.or_cong(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), StreamFailure.sp_has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n), StreamFailure.sp_st(st, 429n), sfb.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), sfb.st(st, 429n)), sfb.pick_cong(Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Bool.or(StreamFailure.sp_has(t, ["authentication", "unauthorized"]), StreamFailure.sp_st(st, 401n)), Sf.KAuth{}, StreamFailure.sp_pick(Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(Sf.has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}, Sf.KUnknown{})))), StreamFailure.sp_pick(Bool.or(TextPat.sp_any(t, [StreamFailure.sp_permission()]), StreamFailure.sp_st(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["invalid_request", "not_found_error"]), Bool.or(StreamFailure.sp_st(st, 400n), StreamFailure.sp_st(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(StreamFailure.sp_has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_st5(st)), Sf.KServer{}, Sf.KUnknown{})))), sfb.or_cong(Sf.has(t, ["authentication", "unauthorized"]), StreamFailure.sp_has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n), StreamFailure.sp_st(st, 401n), sfb.has(t, ["authentication", "unauthorized"]), sfb.st(st, 401n)), sfb.pick_cong(Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Bool.or(TextPat.sp_any(t, [StreamFailure.sp_permission()]), StreamFailure.sp_st(st, 403n)), Sf.KPermission{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(Sf.has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}, Sf.KUnknown{}))), StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["invalid_request", "not_found_error"]), Bool.or(StreamFailure.sp_st(st, 400n), StreamFailure.sp_st(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(StreamFailure.sp_has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_st5(st)), Sf.KServer{}, Sf.KUnknown{}))), sfb.or_cong(Tp.hit(t, Sf.permission_pat()), TextPat.sp_any(t, [StreamFailure.sp_permission()]), Sf.is_status(st, 403n), StreamFailure.sp_st(st, 403n), TextPat.text_pat_hit(t, Sf.permission_pat()), sfb.st(st, 403n)), sfb.pick_cong(Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Bool.or(StreamFailure.sp_has(t, ["invalid_request", "not_found_error"]), Bool.or(StreamFailure.sp_st(st, 400n), StreamFailure.sp_st(st, 404n))), Sf.KInvalid{}, StreamFailure.sp_pick(Sf.has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}, Sf.KUnknown{})), StreamFailure.sp_pick(StreamFailure.sp_has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_st5(st)), Sf.KServer{}, Sf.KUnknown{})), sfb.or_cong(Sf.has(t, ["invalid_request", "not_found_error"]), StreamFailure.sp_has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n)), Bool.or(StreamFailure.sp_st(st, 400n), StreamFailure.sp_st(st, 404n)), sfb.has(t, ["invalid_request", "not_found_error"]), sfb.or_cong(Sf.is_status(st, 400n), StreamFailure.sp_st(st, 400n), Sf.is_status(st, 404n), StreamFailure.sp_st(st, 404n), sfb.st(st, 400n), sfb.st(st, 404n))), sfb.pick_cong(Sf.has(t, ["malformed"]), StreamFailure.sp_has(t, ["malformed"]), Sf.KMalformed{}, StreamFailure.sp_pick(Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}, Sf.KUnknown{}), StreamFailure.sp_pick(Bool.or(StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_st5(st)), Sf.KServer{}, Sf.KUnknown{}), sfb.has(t, ["malformed"]), sfb.pick_cong(Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Bool.or(StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_st5(st)), Sf.KServer{}, Sf.KUnknown{}, Sf.KUnknown{}, sfb.or_cong(Sf.has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sp_has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st), StreamFailure.sp_st5(st), sfb.has(t, ["api_error", "server_error", "unavailable"]), sfb.st5(st)), {==})))))))))))

# the code's classification is the spec's
def sfb.classify(t: Maybe<&2, String>, +st: Maybe<&2, Nat>) -> {Sf.classify(t, st) == StreamFailure.sp_classify(t, st) : Sf.Cause}:
  match t:
    case None{}:
      sfb.cause("", st)
    case Some{+x}:
      %Equal.sym(String, Tp.lower(x), TextPat.sp_lower(x), TextPat.text_pat_lower(x)) : {Sf.classify.go(_, st) == StreamFailure.sp_cause(TextPat.sp_lower(x), st) : Sf.Cause}
      sfb.cause(TextPat.sp_lower(x), st)

# Messages
# --------

def sfb.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, String.append(t, SNil{}), t, sfb.app_nil(t)) : {SCon{c, _} == SCon{c, t} : String}
      {==}

def sfb.app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(String, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), sfb.app_assoc(t, b, c)) : {SCon{h, _} == SCon{h, String.append(t, String.append(b, c))} : String}
      {==}

def sfb.text(k: Sf.Cause) -> {Sf.kind_text(k) == StreamFailure.sp_text(k) : String}:
  match k:
    case Sf.KRefusal{}:
      {==}
    case Sf.KSafety{}:
      {==}
    case Sf.KPayment{}:
      {==}
    case Sf.KOverloaded{}:
      {==}
    case Sf.KRateLimit{}:
      {==}
    case Sf.KServer{}:
      {==}
    case Sf.KAuth{}:
      {==}
    case Sf.KPermission{}:
      {==}
    case Sf.KInvalid{}:
      {==}
    case Sf.KMalformed{}:
      {==}
    case Sf.KDrop{}:
      {==}
    case Sf.KStalled{}:
      {==}
    case Sf.KRepeating{}:
      {==}
    case Sf.KUnknown{}:
      {==}

def sfb.quals(t: Maybe<&2, String>, st: Maybe<&2, Nat>) -> {Sf.message.quals(Sf.quals(t, st)) == StreamFailure.sp_quals(t, st) : String}:
  match t st:
    case None{} None{}:
      {==}
    case Some{x} None{}:
      {==}
    case None{} Some{s}:
      {==}
    case Some{+x} Some{+s}:
      %Equal.sym(String, String.append(String.append(x, String.append(", ", Nat.show(s))), ")"), String.append(x, String.append(String.append(", ", Nat.show(s)), ")")), sfb.app_assoc(x, String.append(", ", Nat.show(s)), ")")) : {String.append(" (", _) == String.append(" (", String.append(x, String.append(", ", String.append(Nat.show(s), ")")))) : String}
      {==}

def sfb.detail(d: Maybe<&2, String>) -> {Sf.message.detail(d) == StreamFailure.sp_after(": ", d, "") : String}:
  match d:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(String, String.append(x, SNil{}), x, sfb.app_nil(x)) : {String.append(": ", x) == String.append(": ", _) : String}
      {==}

def sfb.rid(r: Maybe<&2, String>) -> {Sf.message.rid(r) == StreamFailure.sp_after(" [request_id: ", r, "]") : String}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      {==}

# the code's message is the spec's
def sfb.message(+k: Sf.Cause, +t: Maybe<&2, String>, +st: Maybe<&2, Nat>, +d: Maybe<&2, String>, +r: Maybe<&2, String>) -> {Sf.message(k, t, st, d, r) == StreamFailure.sp_message(k, t, st, d, r) : String}:
  %Equal.sym(String, Sf.kind_text(k), StreamFailure.sp_text(k), sfb.text(k)) : {String.concat([_, Sf.message.quals(Sf.quals(t, st)), Sf.message.detail(d), Sf.message.rid(r)]) == StreamFailure.sp_message(k, t, st, d, r) : String}
  %Equal.sym(String, Sf.message.quals(Sf.quals(t, st)), StreamFailure.sp_quals(t, st), sfb.quals(t, st)) : {String.concat([StreamFailure.sp_text(k), _, Sf.message.detail(d), Sf.message.rid(r)]) == StreamFailure.sp_message(k, t, st, d, r) : String}
  %Equal.sym(String, Sf.message.detail(d), StreamFailure.sp_after(": ", d, ""), sfb.detail(d)) : {String.concat([StreamFailure.sp_text(k), StreamFailure.sp_quals(t, st), _, Sf.message.rid(r)]) == StreamFailure.sp_message(k, t, st, d, r) : String}
  %Equal.sym(String, Sf.message.rid(r), StreamFailure.sp_after(" [request_id: ", r, "]"), sfb.rid(r)) : {String.concat([StreamFailure.sp_text(k), StreamFailure.sp_quals(t, st), StreamFailure.sp_after(": ", d, ""), _]) == StreamFailure.sp_message(k, t, st, d, r) : String}
  {==}

# HTTP errors
# -----------

def sfb.or(a: Maybe<&2, String>, b: Maybe<&2, String>) -> {Sf.or_else(a, b) == StreamFailure.sp_or(a, b) : Maybe<&2, String>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

def sfb.typeless(t: Maybe<&2, String>, k: Sf.Cause) -> {Bool.and(Sf.needs_type(k), Sf.is_none(t)) == StreamFailure.sp_typeless(t, k) : Bool}:
  match t:
    case None{}:
      match k:
        case Sf.KRefusal{}:
          {==}
        case Sf.KSafety{}:
          {==}
        case Sf.KPayment{}:
          {==}
        case Sf.KOverloaded{}:
          {==}
        case Sf.KRateLimit{}:
          {==}
        case Sf.KServer{}:
          {==}
        case Sf.KAuth{}:
          {==}
        case Sf.KPermission{}:
          {==}
        case Sf.KInvalid{}:
          {==}
        case Sf.KMalformed{}:
          {==}
        case Sf.KDrop{}:
          {==}
        case Sf.KStalled{}:
          {==}
        case Sf.KRepeating{}:
          {==}
        case Sf.KUnknown{}:
          {==}
    case Some{x}:
      match k:
        case Sf.KRefusal{}:
          {==}
        case Sf.KSafety{}:
          {==}
        case Sf.KPayment{}:
          {==}
        case Sf.KOverloaded{}:
          {==}
        case Sf.KRateLimit{}:
          {==}
        case Sf.KServer{}:
          {==}
        case Sf.KAuth{}:
          {==}
        case Sf.KPermission{}:
          {==}
        case Sf.KInvalid{}:
          {==}
        case Sf.KMalformed{}:
          {==}
        case Sf.KDrop{}:
          {==}
        case Sf.KStalled{}:
          {==}
        case Sf.KRepeating{}:
          {==}
        case Sf.KUnknown{}:
          {==}

def sfb.http_of(+k: Sf.Cause, +t: Maybe<&2, String>, +st: Maybe<&2, Nat>, +d: Maybe<&2, String>, +r: Maybe<&2, String>) -> {Sf.http.of(k, t, st, d, r) == StreamFailure.sp_http.of(k, t, st, d, r) : Sf.Http}:
  match k:
    case Sf.KRefusal{}:
      %Equal.sym(String, Sf.message(Sf.KRefusal{}, t, st, d, r), StreamFailure.sp_message(Sf.KRefusal{}, t, st, d, r), sfb.message(Sf.KRefusal{}, t, st, d, r)) : {Sf.Http{Sf.KRefusal{}, t, Some{_}} == Sf.Http{Sf.KRefusal{}, t, Some{StreamFailure.sp_message(Sf.KRefusal{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KSafety{}:
      %Equal.sym(String, Sf.message(Sf.KSafety{}, t, st, d, r), StreamFailure.sp_message(Sf.KSafety{}, t, st, d, r), sfb.message(Sf.KSafety{}, t, st, d, r)) : {Sf.Http{Sf.KSafety{}, t, Some{_}} == Sf.Http{Sf.KSafety{}, t, Some{StreamFailure.sp_message(Sf.KSafety{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KPayment{}:
      %Equal.sym(String, Sf.message(Sf.KPayment{}, t, st, d, r), StreamFailure.sp_message(Sf.KPayment{}, t, st, d, r), sfb.message(Sf.KPayment{}, t, st, d, r)) : {Sf.Http{Sf.KPayment{}, t, Some{_}} == Sf.Http{Sf.KPayment{}, t, Some{StreamFailure.sp_message(Sf.KPayment{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KOverloaded{}:
      %Equal.sym(String, Sf.message(Sf.KOverloaded{}, t, st, d, r), StreamFailure.sp_message(Sf.KOverloaded{}, t, st, d, r), sfb.message(Sf.KOverloaded{}, t, st, d, r)) : {Sf.Http{Sf.KOverloaded{}, t, Some{_}} == Sf.Http{Sf.KOverloaded{}, t, Some{StreamFailure.sp_message(Sf.KOverloaded{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KRateLimit{}:
      %Equal.sym(String, Sf.message(Sf.KRateLimit{}, t, st, d, r), StreamFailure.sp_message(Sf.KRateLimit{}, t, st, d, r), sfb.message(Sf.KRateLimit{}, t, st, d, r)) : {Sf.Http{Sf.KRateLimit{}, t, Some{_}} == Sf.Http{Sf.KRateLimit{}, t, Some{StreamFailure.sp_message(Sf.KRateLimit{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KServer{}:
      %Equal.sym(String, Sf.message(Sf.KServer{}, t, st, d, r), StreamFailure.sp_message(Sf.KServer{}, t, st, d, r), sfb.message(Sf.KServer{}, t, st, d, r)) : {Sf.Http{Sf.KServer{}, t, Some{_}} == Sf.Http{Sf.KServer{}, t, Some{StreamFailure.sp_message(Sf.KServer{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KAuth{}:
      %Equal.sym(String, Sf.message(Sf.KAuth{}, t, st, d, r), StreamFailure.sp_message(Sf.KAuth{}, t, st, d, r), sfb.message(Sf.KAuth{}, t, st, d, r)) : {Sf.Http{Sf.KAuth{}, t, Some{_}} == Sf.Http{Sf.KAuth{}, t, Some{StreamFailure.sp_message(Sf.KAuth{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KPermission{}:
      %Equal.sym(String, Sf.message(Sf.KPermission{}, t, st, d, r), StreamFailure.sp_message(Sf.KPermission{}, t, st, d, r), sfb.message(Sf.KPermission{}, t, st, d, r)) : {Sf.Http{Sf.KPermission{}, t, Some{_}} == Sf.Http{Sf.KPermission{}, t, Some{StreamFailure.sp_message(Sf.KPermission{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KInvalid{}:
      %Equal.sym(String, Sf.message(Sf.KInvalid{}, t, st, d, r), StreamFailure.sp_message(Sf.KInvalid{}, t, st, d, r), sfb.message(Sf.KInvalid{}, t, st, d, r)) : {Sf.Http{Sf.KInvalid{}, t, Some{_}} == Sf.Http{Sf.KInvalid{}, t, Some{StreamFailure.sp_message(Sf.KInvalid{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KMalformed{}:
      %Equal.sym(String, Sf.message(Sf.KMalformed{}, t, st, d, r), StreamFailure.sp_message(Sf.KMalformed{}, t, st, d, r), sfb.message(Sf.KMalformed{}, t, st, d, r)) : {Sf.Http{Sf.KMalformed{}, t, Some{_}} == Sf.Http{Sf.KMalformed{}, t, Some{StreamFailure.sp_message(Sf.KMalformed{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KDrop{}:
      %Equal.sym(String, Sf.message(Sf.KDrop{}, t, st, d, r), StreamFailure.sp_message(Sf.KDrop{}, t, st, d, r), sfb.message(Sf.KDrop{}, t, st, d, r)) : {Sf.Http{Sf.KDrop{}, t, Some{_}} == Sf.Http{Sf.KDrop{}, t, Some{StreamFailure.sp_message(Sf.KDrop{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KStalled{}:
      %Equal.sym(String, Sf.message(Sf.KStalled{}, t, st, d, r), StreamFailure.sp_message(Sf.KStalled{}, t, st, d, r), sfb.message(Sf.KStalled{}, t, st, d, r)) : {Sf.Http{Sf.KStalled{}, t, Some{_}} == Sf.Http{Sf.KStalled{}, t, Some{StreamFailure.sp_message(Sf.KStalled{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KRepeating{}:
      %Equal.sym(String, Sf.message(Sf.KRepeating{}, t, st, d, r), StreamFailure.sp_message(Sf.KRepeating{}, t, st, d, r), sfb.message(Sf.KRepeating{}, t, st, d, r)) : {Sf.Http{Sf.KRepeating{}, t, Some{_}} == Sf.Http{Sf.KRepeating{}, t, Some{StreamFailure.sp_message(Sf.KRepeating{}, t, st, d, r)}} : Sf.Http}
      {==}
    case Sf.KUnknown{}:
      {==}

def sfb.http_kind(k: Sf.Cause, b: Bool, +st: Maybe<&2, Nat>) -> {Sf.http.kind(k, b, st) == StreamFailure.sp_http.cause(b, k, st) : Sf.Cause}:
  match b:
    case True{}:
      sfb.classify(None{}, st)
    case False{}:
      {==}

# the code's HTTP cause is the spec's
def sfb.http(+m: String, +st: Maybe<&2, Nat>, +bt: Maybe<&2, String>, +d: Maybe<&2, String>, +code: Maybe<&2, String>, +sdk: Maybe<&2, String>, +r: Maybe<&2, String>) -> {Sf.http(m, st, bt, d, code, sdk, r) == StreamFailure.sp_http(m, st, bt, d, code, sdk, r) : Sf.Http}:
  %Equal.sym(Maybe<&2, String>, Sf.or_else(code, sdk), StreamFailure.sp_or(code, sdk), sfb.or(code, sdk)) : {Sf.http.of(Sf.http.kind(Sf.classify(Sf.or_else(Sf.or_else(bt, _), Some{m}), st), Bool.and(Sf.needs_type(Sf.classify(Sf.or_else(Sf.or_else(bt, _), Some{m}), st)), Sf.is_none(Sf.or_else(bt, _))), st), Sf.or_else(bt, _), st, d, r) == StreamFailure.sp_http(m, st, bt, d, code, sdk, r) : Sf.Http}
  +c = StreamFailure.sp_or(code, sdk)
  %Equal.sym(Maybe<&2, String>, Sf.or_else(bt, c), StreamFailure.sp_or(bt, c), sfb.or(bt, c)) : {Sf.http.of(Sf.http.kind(Sf.classify(Sf.or_else(_, Some{m}), st), Bool.and(Sf.needs_type(Sf.classify(Sf.or_else(_, Some{m}), st)), Sf.is_none(_)), st), _, st, d, r) == StreamFailure.sp_http(m, st, bt, d, code, sdk, r) : Sf.Http}
  +t = StreamFailure.sp_or(bt, c)
  %Equal.sym(Maybe<&2, String>, Sf.or_else(t, Some{m}), StreamFailure.sp_or(t, Some{m}), sfb.or(t, Some{m})) : {Sf.http.of(Sf.http.kind(Sf.classify(_, st), Bool.and(Sf.needs_type(Sf.classify(_, st)), Sf.is_none(t)), st), t, st, d, r) == StreamFailure.sp_http(m, st, bt, d, code, sdk, r) : Sf.Http}
  +q = StreamFailure.sp_or(t, Some{m})
  %Equal.sym(Sf.Cause, Sf.classify(q, st), StreamFailure.sp_classify(q, st), sfb.classify(q, st)) : {Sf.http.of(Sf.http.kind(_, Bool.and(Sf.needs_type(_), Sf.is_none(t)), st), t, st, d, r) == StreamFailure.sp_http(m, st, bt, d, code, sdk, r) : Sf.Http}
  +k = StreamFailure.sp_classify(q, st)
  %Equal.sym(Bool, Bool.and(Sf.needs_type(k), Sf.is_none(t)), StreamFailure.sp_typeless(t, k), sfb.typeless(t, k)) : {Sf.http.of(Sf.http.kind(k, _, st), t, st, d, r) == StreamFailure.sp_http(m, st, bt, d, code, sdk, r) : Sf.Http}
  %Equal.sym(Sf.Cause, Sf.http.kind(k, StreamFailure.sp_typeless(t, k), st), StreamFailure.sp_http.cause(StreamFailure.sp_typeless(t, k), k, st), sfb.http_kind(k, StreamFailure.sp_typeless(t, k), st)) : {Sf.http.of(_, t, st, d, r) == StreamFailure.sp_http(m, st, bt, d, code, sdk, r) : Sf.Http}
  sfb.http_of(StreamFailure.sp_http.cause(StreamFailure.sp_typeless(t, k), k, st), t, st, d, r)

# Stream ends
# -----------

# the code's failure of an ended stream is the spec's
def sfb.from_stop(raw: Maybe<&2, String>, +r: Maybe<&2, String>) -> {Sf.from_stop(raw, r) == StreamFailure.sp_from_stop(raw, r) : Sf.Named}:
  match raw:
    case None{}:
      %Equal.sym(String, Sf.message(Sf.KUnknown{}, None{}, None{}, Some{"stream ended with an error and no stop reason"}, r), StreamFailure.sp_message(Sf.KUnknown{}, None{}, None{}, Some{"stream ended with an error and no stop reason"}, r), sfb.message(Sf.KUnknown{}, None{}, None{}, Some{"stream ended with an error and no stop reason"}, r)) : {Sf.Named{Sf.KUnknown{}, _} == StreamFailure.sp_from_stop(None{}, r) : Sf.Named}
      {==}
    case Some{+x}:
      %Equal.sym(Sf.Cause, Sf.classify(Some{x}, None{}), StreamFailure.sp_classify(Some{x}, None{}), sfb.classify(Some{x}, None{})) : {Sf.from_stop.of(_, x, r) == StreamFailure.sp_from_stop(Some{x}, r) : Sf.Named}
      +k = StreamFailure.sp_classify(Some{x}, None{})
      %Equal.sym(String, Sf.message(k, Some{x}, None{}, None{}, r), StreamFailure.sp_message(k, Some{x}, None{}, None{}, r), sfb.message(k, Some{x}, None{}, None{}, r)) : {Sf.Named{k, _} == StreamFailure.sp_from_stop(Some{x}, r) : Sf.Named}
      {==}

def sfb.drop_detail(b: Sf.Block) -> {Sf.drop.detail(b) == StreamFailure.sp_drop_detail(b) : String}:
  match b:
    case Sf.BThinking{}:
      {==}
    case Sf.BText{}:
      {==}
    case Sf.BToolCall{}:
      {==}
    case Sf.BNone{}:
      {==}

# the code's messages of dropped and stalled streams are the spec's
def sfb.ends(+b: Sf.Block, +ms: String) -> {(Sf.drop(b), Sf.stalled(ms)) == (StreamFailure.sp_message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{}), StreamFailure.sp_message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{})) : String & String}:
  %Equal.sym(String, Sf.drop.detail(b), StreamFailure.sp_drop_detail(b), sfb.drop_detail(b)) : {(Sf.message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{_}, None{}), Sf.stalled(ms)) == (StreamFailure.sp_message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{}), StreamFailure.sp_message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{})) : String & String}
  %Equal.sym(String, Sf.message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{}), StreamFailure.sp_message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{}), sfb.message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{})) : {(_, Sf.stalled(ms)) == (StreamFailure.sp_message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{}), StreamFailure.sp_message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{})) : String & String}
  %Equal.sym(String, Sf.message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{}), StreamFailure.sp_message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{}), sfb.message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{})) : {(StreamFailure.sp_message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{}), _) == (StreamFailure.sp_message(Sf.KDrop{}, Some{"stream_drop"}, None{}, Some{StreamFailure.sp_drop_detail(b)}, None{}), StreamFailure.sp_message(Sf.KStalled{}, None{}, None{}, Some{String.concat(["no stream event for ", ms, "ms"])}, None{})) : String & String}
  {==}

# the shown line with n chars allowed
def sfb.pick_n(short: Bool, s: String, n: Nat) -> String:
  match short:
    case True{}:
      s
    case False{}:
      String.append(String.take(s, n), SCon{Chr{8230}, SNil{}})

def sfb.shown_cons(b: Bool, +c: Char, +t: String, +m: Nat) -> {SCon{c, sfb.pick_n(b, t, m)} == sfb.pick_n(b, SCon{c, t}, 1n+m) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sfb.shown_go(s: String, n: Nat) -> {Sf.shown.go(s, n) == sfb.pick_n(Nat.is_le(String.length(s), n), s, n) : String}:
  match s n:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+m:
      {==}
    case SCon{c, t} 0n:
      {==}
    case SCon{+c, +t} 1n++m:
      %Equal.sym(String, Sf.shown.go(t, m), sfb.pick_n(Nat.is_le(String.length(t), m), t, m), sfb.shown_go(t, m)) : {SCon{c, _} == sfb.pick_n(Nat.is_le(String.length(t), m), SCon{c, t}, 1n+m) : String}
      sfb.shown_cons(Nat.is_le(String.length(t), m), c, t, m)

def sfb.shown_pick(b: Bool, s: String) -> {sfb.pick_n(b, s, 80n) == StreamFailure.sp_shown.pick(b, s) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's shown line is the spec's
def sfb.shown(+s: String) -> {Sf.shown(s) == StreamFailure.sp_shown(s) : String}:
  Equal.trans(String, Sf.shown.go(s, 80n), sfb.pick_n(Nat.is_le(String.length(s), 80n), s, 80n), StreamFailure.sp_shown(s), sfb.shown_go(s, 80n), sfb.shown_pick(Nat.is_le(String.length(s), 80n), s))

def sfb.rep_detail(+limit: Nat, period: Nat, q: String) -> {Sf.repeating.detail(limit, period, q) == StreamFailure.sp_repeat_detail(Nat.is_le(period, 1n), limit, period, q) : String}:
  match period:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def sfb.rep_period(p: Nat) -> {Sf.repeating.period(p) == Nat.max(p, 1n) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      match q:
        case 0n:
          {==}
        case 1n+u:
          {==}

# the code's failure of a repeating stream is the spec's
def sfb.repeating(+limit: Nat, +period: Nat, +q: String) -> {Sf.repeating(limit, period, q) == StreamFailure.sp_repeating(limit, period, q) : Sf.Repeat}:
  %Equal.sym(String, Sf.repeating.detail(limit, period, q), StreamFailure.sp_repeat_detail(Nat.is_le(period, 1n), limit, period, q), sfb.rep_detail(limit, period, q)) : {Sf.Repeat{Sf.message(Sf.KRepeating{}, None{}, None{}, Some{_}, None{}), Sf.repeating.period(period)} == StreamFailure.sp_repeating(limit, period, q) : Sf.Repeat}
  +dd = StreamFailure.sp_repeat_detail(Nat.is_le(period, 1n), limit, period, q)
  %Equal.sym(String, Sf.message(Sf.KRepeating{}, None{}, None{}, Some{dd}, None{}), StreamFailure.sp_message(Sf.KRepeating{}, None{}, None{}, Some{dd}, None{}), sfb.message(Sf.KRepeating{}, None{}, None{}, Some{dd}, None{})) : {Sf.Repeat{_, Sf.repeating.period(period)} == StreamFailure.sp_repeating(limit, period, q) : Sf.Repeat}
  %Equal.sym(Nat, Sf.repeating.period(period), Nat.max(period, 1n), sfb.rep_period(period)) : {Sf.Repeat{StreamFailure.sp_message(Sf.KRepeating{}, None{}, None{}, Some{dd}, None{}), _} == StreamFailure.sp_repeating(limit, period, q) : Sf.Repeat}
  {==}
