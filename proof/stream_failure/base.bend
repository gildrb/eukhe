# eukhe: lemmas shared by the proofs of area stream_failure: the code's
# tests are the rules of R1's table (sfd.r_*), so the code's first test that
# holds is the first rule that holds (sfd.go, sfd.split, sfd.none); the
# message is built of parts (sfm.*); the HTTP cause's parts (sfh.*)

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
import ../base/logic/logic.bend as LLogicLogic

# Logic
# -----

def sfb.or_cong(-a: Bool, -a2: Bool, -b: Bool, -b2: Bool, ea: {a == a2 : Bool}, eb: {b == b2 : Bool}) -> {Bool.or(a, b) == Bool.or(a2, b2) : Bool}:
  Equal.trans(Bool, Bool.or(a, b), Bool.or(a2, b), Bool.or(a2, b2), Equal.cong(Bool, Bool, z => Bool.or(z, b), a, a2, ea), Equal.cong(Bool, Bool, z => Bool.or(a2, z), b, b2, eb))

def sfd.or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def sfd.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def sfd.fst(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.absurd({False{} == True{} : Bool}, e)

def sfd.snd(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LLogicLogic.absurd({b == True{} : Bool}, e)

def sfd.not_true(f: Bool, e: {Bool.not(f) == True{} : Bool}) -> {f == False{} : Bool}:
  match f:
    case True{}:
      LLogicLogic.absurd({True{} == False{} : Bool}, e)
    case False{}:
      {==}

# The rules (R1)
# --------------

# the statuses of a rule as the code tests them
def sfd.st0(st: Maybe<&2, Nat>) -> {StreamFailure.sf_status(st, [], None{}) == False{} : Bool}:
  match st:
    case None{}:
      {==}
    case Some{s}:
      {==}

def sfd.st1(st: Maybe<&2, Nat>, +n: Nat) -> {StreamFailure.sf_status(st, [n], None{}) == Sf.is_status(st, n) : Bool}:
  match st:
    case None{}:
      {==}
    case Some{+s}:
      sfd.or_false(Nat.is_eq(s, n))

def sfd.st2(st: Maybe<&2, Nat>, +a: Nat, +b: Nat) -> {StreamFailure.sf_status(st, [a, b], None{}) == Bool.or(Sf.is_status(st, a), Sf.is_status(st, b)) : Bool}:
  match st:
    case None{}:
      {==}
    case Some{+s}:
      %Equal.sym(Bool, Bool.or(Nat.is_eq(s, b), False{}), Nat.is_eq(s, b), sfd.or_false(Nat.is_eq(s, b))) : {Bool.or(Nat.is_eq(s, a), _) == Bool.or(Nat.is_eq(s, a), Nat.is_eq(s, b)) : Bool}
      {==}

def sfd.st5(st: Maybe<&2, Nat>) -> {StreamFailure.sf_status(st, [], Some{500n}) == Sf.is_5xx(st) : Bool}:
  match st:
    case None{}:
      {==}
    case Some{s}:
      {==}

# each rule holds exactly when the code's test of its cause does
def sfd.r_payment(+t: String, +st: Maybe<&2, Nat>) -> {StreamFailure.sf_fires(StreamFailure.sf_r_payment(), t, st) == Sf.is_status(st, 402n) : Bool}:
  sfd.st1(st, 402n)

def sfd.r_refusal(+t: String, +st: Maybe<&2, Nat>) -> {StreamFailure.sf_fires(StreamFailure.sf_r_refusal(), t, st) == String.eq(t, "refusal") : Bool}:
  %Equal.sym(Bool, StreamFailure.sf_status(st, [], None{}), False{}, sfd.st0(st)) : {Bool.or(String.eq(t, "refusal"), _) == String.eq(t, "refusal") : Bool}
  sfd.or_false(String.eq(t, "refusal"))

def sfd.r_safety(+t: String, +st: Maybe<&2, Nat>) -> {StreamFailure.sf_fires(StreamFailure.sf_r_safety(), t, st) == Tp.hit(t, Sf.safety_pat()) : Bool}:
  %Equal.sym(Bool, StreamFailure.sf_status(st, [], None{}), False{}, sfd.st0(st)) : {Bool.or(TextPat.sp_any(t, [StreamFailure.sp_safety()]), _) == Tp.hit(t, Sf.safety_pat()) : Bool}
  Equal.trans(Bool, Bool.or(TextPat.sp_any(t, [StreamFailure.sp_safety()]), False{}), TextPat.sp_any(t, [StreamFailure.sp_safety()]), Tp.hit(t, Sf.safety_pat()), sfd.or_false(TextPat.sp_any(t, [StreamFailure.sp_safety()])), Equal.sym(Bool, Tp.hit(t, Sf.safety_pat()), TextPat.sp_any(t, [StreamFailure.sp_safety()]), TextPat.text_pat_hit(t, Sf.safety_pat())))

def sfd.r_overloaded(+t: String, +st: Maybe<&2, Nat>) -> {StreamFailure.sf_fires(StreamFailure.sf_r_overloaded(), t, st) == Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)) : Bool}:
  sfb.or_cong(TextPat.sp_any(t, StreamFailure.sf_needles(["overloaded"])), Sf.has(t, ["overloaded"]), StreamFailure.sf_status(st, [529n], None{}), Sf.is_status(st, 529n), Equal.sym(Bool, Sf.has(t, ["overloaded"]), TextPat.sp_any(t, StreamFailure.sf_needles(["overloaded"])), TextPat.text_pat_hit(t, Tp.Pat{False{}, Sf.lits.go(["overloaded"])})), sfd.st1(st, 529n))

def sfd.r_rate(+t: String, +st: Maybe<&2, Nat>) -> {StreamFailure.sf_fires(StreamFailure.sf_r_rate(), t, st) == Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)) : Bool}:
  sfb.or_cong(TextPat.sp_any(t, StreamFailure.sf_needles(["rate_limit", "usage_limit", "usage_not_included", "throttl"])), Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), StreamFailure.sf_status(st, [429n], None{}), Sf.is_status(st, 429n), Equal.sym(Bool, Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), TextPat.sp_any(t, StreamFailure.sf_needles(["rate_limit", "usage_limit", "usage_not_included", "throttl"])), TextPat.text_pat_hit(t, Tp.Pat{False{}, Sf.lits.go(["rate_limit", "usage_limit", "usage_not_included", "throttl"])})), sfd.st1(st, 429n))

def sfd.r_auth(+t: String, +st: Maybe<&2, Nat>) -> {StreamFailure.sf_fires(StreamFailure.sf_r_auth(), t, st) == Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)) : Bool}:
  sfb.or_cong(TextPat.sp_any(t, StreamFailure.sf_needles(["authentication", "unauthorized"])), Sf.has(t, ["authentication", "unauthorized"]), StreamFailure.sf_status(st, [401n], None{}), Sf.is_status(st, 401n), Equal.sym(Bool, Sf.has(t, ["authentication", "unauthorized"]), TextPat.sp_any(t, StreamFailure.sf_needles(["authentication", "unauthorized"])), TextPat.text_pat_hit(t, Tp.Pat{False{}, Sf.lits.go(["authentication", "unauthorized"])})), sfd.st1(st, 401n))

def sfd.r_permission(+t: String, +st: Maybe<&2, Nat>) -> {StreamFailure.sf_fires(StreamFailure.sf_r_permission(), t, st) == Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)) : Bool}:
  sfb.or_cong(TextPat.sp_any(t, [StreamFailure.sp_permission()]), Tp.hit(t, Sf.permission_pat()), StreamFailure.sf_status(st, [403n], None{}), Sf.is_status(st, 403n), Equal.sym(Bool, Tp.hit(t, Sf.permission_pat()), TextPat.sp_any(t, [StreamFailure.sp_permission()]), TextPat.text_pat_hit(t, Sf.permission_pat())), sfd.st1(st, 403n))

def sfd.r_invalid(+t: String, +st: Maybe<&2, Nat>) -> {StreamFailure.sf_fires(StreamFailure.sf_r_invalid(), t, st) == Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))) : Bool}:
  sfb.or_cong(TextPat.sp_any(t, StreamFailure.sf_needles(["invalid_request", "not_found_error"])), Sf.has(t, ["invalid_request", "not_found_error"]), StreamFailure.sf_status(st, [400n, 404n], None{}), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n)), Equal.sym(Bool, Sf.has(t, ["invalid_request", "not_found_error"]), TextPat.sp_any(t, StreamFailure.sf_needles(["invalid_request", "not_found_error"])), TextPat.text_pat_hit(t, Tp.Pat{False{}, Sf.lits.go(["invalid_request", "not_found_error"])})), sfd.st2(st, 400n, 404n))

def sfd.r_malformed(+t: String, +st: Maybe<&2, Nat>) -> {StreamFailure.sf_fires(StreamFailure.sf_r_malformed(), t, st) == Sf.has(t, ["malformed"]) : Bool}:
  %Equal.sym(Bool, StreamFailure.sf_status(st, [], None{}), False{}, sfd.st0(st)) : {Bool.or(TextPat.sp_any(t, StreamFailure.sf_needles(["malformed"])), _) == Sf.has(t, ["malformed"]) : Bool}
  Equal.trans(Bool, Bool.or(TextPat.sp_any(t, StreamFailure.sf_needles(["malformed"])), False{}), TextPat.sp_any(t, StreamFailure.sf_needles(["malformed"])), Sf.has(t, ["malformed"]), sfd.or_false(TextPat.sp_any(t, StreamFailure.sf_needles(["malformed"]))), Equal.sym(Bool, Sf.has(t, ["malformed"]), TextPat.sp_any(t, StreamFailure.sf_needles(["malformed"])), TextPat.text_pat_hit(t, Tp.Pat{False{}, Sf.lits.go(["malformed"])})))

def sfd.r_server(+t: String, +st: Maybe<&2, Nat>) -> {StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st) == Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)) : Bool}:
  sfb.or_cong(TextPat.sp_any(t, StreamFailure.sf_needles(["api_error", "server_error", "unavailable"])), Sf.has(t, ["api_error", "server_error", "unavailable"]), StreamFailure.sf_status(st, [], Some{500n}), Sf.is_5xx(st), Equal.sym(Bool, Sf.has(t, ["api_error", "server_error", "unavailable"]), TextPat.sp_any(t, StreamFailure.sf_needles(["api_error", "server_error", "unavailable"])), TextPat.text_pat_hit(t, Tp.Pat{False{}, Sf.lits.go(["api_error", "server_error", "unavailable"])})), sfd.st5(st))

def sfd.tcons(-b: Bool, -b2: Bool, k: Sf.Cause, -x: List<&2, Sf.Test>, -y: List<&2, Sf.Test>, eb: {b == b2 : Bool}, ex: {x == y : List<&2, Sf.Test>}) -> {Sf.Test{b, k} <> x == Sf.Test{b2, k} <> y : List<&2, Sf.Test>}:
  %ex : {Sf.Test{b, k} <> x == Sf.Test{b2, k} <> _ : List<&2, Sf.Test>}
  %eb : {Sf.Test{b, k} <> x == Sf.Test{_, k} <> x : List<&2, Sf.Test>}
  {==}

# the rules as the code's tests
def sfd.tests(rs: List<&2, StreamFailure.SfRule>, +t: String, +st: Maybe<&2, Nat>) -> List<&2, Sf.Test>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> rest:
      Sf.Test{StreamFailure.sf_fires(r, t, st), StreamFailure.sf_cause(r)} <> sfd.tests(rest, t, st)

# the cause of the first rule that holds, else unknown
def sfd.decide(rs: List<&2, StreamFailure.SfRule>, +t: String, +st: Maybe<&2, Nat>) -> Sf.Cause:
  Sf.first(sfd.tests(rs, t, st), Sf.KUnknown{})

# the code's cause of a lowered type is the first rule that holds
def sfd.go(+t: String, +st: Maybe<&2, Nat>) -> {Sf.classify.go(t, st) == sfd.decide(StreamFailure.sf_rules(), t, st) : Sf.Cause}:
  %sfd.tcons(StreamFailure.sf_fires(StreamFailure.sf_r_payment(), t, st), Sf.is_status(st, 402n), Sf.KPayment{}, [Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_refusal(), t, st), Sf.KRefusal{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_safety(), t, st), Sf.KSafety{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_overloaded(), t, st), Sf.KOverloaded{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_rate(), t, st), Sf.KRateLimit{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_auth(), t, st), Sf.KAuth{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_permission(), t, st), Sf.KPermission{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_invalid(), t, st), Sf.KInvalid{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_malformed(), t, st), Sf.KMalformed{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st), Sf.KServer{}}], [Sf.Test{String.eq(t, "refusal"), Sf.KRefusal{}}, Sf.Test{Tp.hit(t, Sf.safety_pat()), Sf.KSafety{}}, Sf.Test{Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Sf.KOverloaded{}}, Sf.Test{Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}}, Sf.Test{Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}}, Sf.Test{Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}}, Sf.Test{Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}}, Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], sfd.r_payment(t, st), sfd.tcons(StreamFailure.sf_fires(StreamFailure.sf_r_refusal(), t, st), String.eq(t, "refusal"), Sf.KRefusal{}, [Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_safety(), t, st), Sf.KSafety{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_overloaded(), t, st), Sf.KOverloaded{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_rate(), t, st), Sf.KRateLimit{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_auth(), t, st), Sf.KAuth{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_permission(), t, st), Sf.KPermission{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_invalid(), t, st), Sf.KInvalid{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_malformed(), t, st), Sf.KMalformed{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st), Sf.KServer{}}], [Sf.Test{Tp.hit(t, Sf.safety_pat()), Sf.KSafety{}}, Sf.Test{Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Sf.KOverloaded{}}, Sf.Test{Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}}, Sf.Test{Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}}, Sf.Test{Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}}, Sf.Test{Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}}, Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], sfd.r_refusal(t, st), sfd.tcons(StreamFailure.sf_fires(StreamFailure.sf_r_safety(), t, st), Tp.hit(t, Sf.safety_pat()), Sf.KSafety{}, [Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_overloaded(), t, st), Sf.KOverloaded{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_rate(), t, st), Sf.KRateLimit{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_auth(), t, st), Sf.KAuth{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_permission(), t, st), Sf.KPermission{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_invalid(), t, st), Sf.KInvalid{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_malformed(), t, st), Sf.KMalformed{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st), Sf.KServer{}}], [Sf.Test{Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Sf.KOverloaded{}}, Sf.Test{Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}}, Sf.Test{Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}}, Sf.Test{Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}}, Sf.Test{Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}}, Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], sfd.r_safety(t, st), sfd.tcons(StreamFailure.sf_fires(StreamFailure.sf_r_overloaded(), t, st), Bool.or(Sf.has(t, ["overloaded"]), Sf.is_status(st, 529n)), Sf.KOverloaded{}, [Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_rate(), t, st), Sf.KRateLimit{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_auth(), t, st), Sf.KAuth{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_permission(), t, st), Sf.KPermission{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_invalid(), t, st), Sf.KInvalid{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_malformed(), t, st), Sf.KMalformed{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st), Sf.KServer{}}], [Sf.Test{Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}}, Sf.Test{Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}}, Sf.Test{Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}}, Sf.Test{Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}}, Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], sfd.r_overloaded(t, st), sfd.tcons(StreamFailure.sf_fires(StreamFailure.sf_r_rate(), t, st), Bool.or(Sf.has(t, ["rate_limit", "usage_limit", "usage_not_included", "throttl"]), Sf.is_status(st, 429n)), Sf.KRateLimit{}, [Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_auth(), t, st), Sf.KAuth{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_permission(), t, st), Sf.KPermission{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_invalid(), t, st), Sf.KInvalid{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_malformed(), t, st), Sf.KMalformed{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st), Sf.KServer{}}], [Sf.Test{Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}}, Sf.Test{Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}}, Sf.Test{Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}}, Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], sfd.r_rate(t, st), sfd.tcons(StreamFailure.sf_fires(StreamFailure.sf_r_auth(), t, st), Bool.or(Sf.has(t, ["authentication", "unauthorized"]), Sf.is_status(st, 401n)), Sf.KAuth{}, [Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_permission(), t, st), Sf.KPermission{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_invalid(), t, st), Sf.KInvalid{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_malformed(), t, st), Sf.KMalformed{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st), Sf.KServer{}}], [Sf.Test{Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}}, Sf.Test{Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}}, Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], sfd.r_auth(t, st), sfd.tcons(StreamFailure.sf_fires(StreamFailure.sf_r_permission(), t, st), Bool.or(Tp.hit(t, Sf.permission_pat()), Sf.is_status(st, 403n)), Sf.KPermission{}, [Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_invalid(), t, st), Sf.KInvalid{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_malformed(), t, st), Sf.KMalformed{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st), Sf.KServer{}}], [Sf.Test{Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}}, Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], sfd.r_permission(t, st), sfd.tcons(StreamFailure.sf_fires(StreamFailure.sf_r_invalid(), t, st), Bool.or(Sf.has(t, ["invalid_request", "not_found_error"]), Bool.or(Sf.is_status(st, 400n), Sf.is_status(st, 404n))), Sf.KInvalid{}, [Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_malformed(), t, st), Sf.KMalformed{}}, Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st), Sf.KServer{}}], [Sf.Test{Sf.has(t, ["malformed"]), Sf.KMalformed{}}, Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], sfd.r_invalid(t, st), sfd.tcons(StreamFailure.sf_fires(StreamFailure.sf_r_malformed(), t, st), Sf.has(t, ["malformed"]), Sf.KMalformed{}, [Sf.Test{StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st), Sf.KServer{}}], [Sf.Test{Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}}], sfd.r_malformed(t, st), sfd.tcons(StreamFailure.sf_fires(StreamFailure.sf_r_server(), t, st), Bool.or(Sf.has(t, ["api_error", "server_error", "unavailable"]), Sf.is_5xx(st)), Sf.KServer{}, [], [], sfd.r_server(t, st), {==})))))))))) : {Sf.first(_, Sf.KUnknown{}) == sfd.decide(StreamFailure.sf_rules(), t, st) : Sf.Cause}
  {==}

def sfd.classify(t: Maybe<&2, String>, +st: Maybe<&2, Nat>) -> {Sf.classify(t, st) == sfd.decide(StreamFailure.sf_rules(), StreamFailure.sf_lowered(t), st) : Sf.Cause}:
  match t:
    case None{}:
      sfd.go("", st)
    case Some{+x}:
      %Equal.sym(String, Tp.lower(x), TextPat.sp_lower(x), TextPat.text_pat_lower(x)) : {Sf.classify.go(_, st) == sfd.decide(StreamFailure.sf_rules(), TextPat.sp_lower(x), st) : Sf.Cause}
      sfd.go(TextPat.sp_lower(x), st)

# the first rule that holds, after rules none of which holds, decides
def sfd.split(pre: List<&2, StreamFailure.SfRule>, +x: StreamFailure.SfRule, +post: List<&2, StreamFailure.SfRule>, +t: String, +st: Maybe<&2, Nat>, +hp: {StreamFailure.sf_none_fire(pre, t, st) == True{} : Bool}, hx: {StreamFailure.sf_fires(x, t, st) == True{} : Bool}) -> {sfd.decide(List.append(&2, StreamFailure.SfRule, pre, x <> post), t, st) == StreamFailure.sf_cause(x) : Sf.Cause}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, StreamFailure.sf_fires(x, t, st), True{}, hx) : {Sf.first(Sf.Test{_, StreamFailure.sf_cause(x)} <> sfd.tests(post, t, st), Sf.KUnknown{}) == StreamFailure.sf_cause(x) : Sf.Cause}
      {==}
    case +p <> more:
      %Equal.sym(Bool, StreamFailure.sf_fires(p, t, st), False{}, sfd.not_true(StreamFailure.sf_fires(p, t, st), sfd.fst(Bool.not(StreamFailure.sf_fires(p, t, st)), StreamFailure.sf_none_fire(more, t, st), hp))) : {Sf.first(Sf.Test{_, StreamFailure.sf_cause(p)} <> sfd.tests(List.append(&2, StreamFailure.SfRule, more, x <> post), t, st), Sf.KUnknown{}) == StreamFailure.sf_cause(x) : Sf.Cause}
      sfd.split(more, x, post, t, st, sfd.snd(Bool.not(StreamFailure.sf_fires(p, t, st)), StreamFailure.sf_none_fire(more, t, st), hp), hx)

# when no rule holds the cause is unknown
def sfd.none(rs: List<&2, StreamFailure.SfRule>, +t: String, +st: Maybe<&2, Nat>, +hp: {StreamFailure.sf_none_fire(rs, t, st) == True{} : Bool}) -> {sfd.decide(rs, t, st) == Sf.KUnknown{} : Sf.Cause}:
  match rs:
    case Nil{}:
      {==}
    case +p <> more:
      %Equal.sym(Bool, StreamFailure.sf_fires(p, t, st), False{}, sfd.not_true(StreamFailure.sf_fires(p, t, st), sfd.fst(Bool.not(StreamFailure.sf_fires(p, t, st)), StreamFailure.sf_none_fire(more, t, st), hp))) : {Sf.first(Sf.Test{_, StreamFailure.sf_cause(p)} <> sfd.tests(more, t, st), Sf.KUnknown{}) == Sf.KUnknown{} : Sf.Cause}
      sfd.none(more, t, st, sfd.snd(Bool.not(StreamFailure.sf_fires(p, t, st)), StreamFailure.sf_none_fire(more, t, st), hp))

# Messages (R2)
# -------------

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


def sfm.quals1(+k: Sf.Cause, +x: String) -> {Sf.message(k, Some{x}, None{}, None{}, None{}) == String.concat([StreamFailure.sp_text(k), " (", x, ")"]) : String}:
  %Equal.sym(String, String.append(String.append(x, ")"), ""), String.append(x, ")"), sfb.app_nil(String.append(x, ")"))) : {String.append(Sf.kind_text(k), String.append(" (", _)) == String.concat([StreamFailure.sp_text(k), " (", x, ")"]) : String}
  %Equal.sym(String, Sf.kind_text(k), StreamFailure.sp_text(k), sfb.text(k)) : {String.append(_, String.append(" (", String.append(x, ")"))) == String.concat([StreamFailure.sp_text(k), " (", x, ")"]) : String}
  {==}

def sfm.quals2(+k: Sf.Cause, +s: Nat) -> {Sf.message(k, None{}, Some{s}, None{}, None{}) == String.concat([StreamFailure.sp_text(k), " (", Nat.show(s), ")"]) : String}:
  %Equal.sym(String, String.append(String.append(Nat.show(s), ")"), ""), String.append(Nat.show(s), ")"), sfb.app_nil(String.append(Nat.show(s), ")"))) : {String.append(Sf.kind_text(k), String.append(" (", _)) == String.concat([StreamFailure.sp_text(k), " (", Nat.show(s), ")"]) : String}
  %Equal.sym(String, Sf.kind_text(k), StreamFailure.sp_text(k), sfb.text(k)) : {String.append(_, String.append(" (", String.append(Nat.show(s), ")"))) == String.concat([StreamFailure.sp_text(k), " (", Nat.show(s), ")"]) : String}
  {==}

def sfm.quals3(+k: Sf.Cause, +x: String, +s: Nat) -> {Sf.message(k, Some{x}, Some{s}, None{}, None{}) == String.concat([StreamFailure.sp_text(k), " (", x, ", ", Nat.show(s), ")"]) : String}:
  %Equal.sym(String, String.append(String.append(String.append(x, String.append(", ", Nat.show(s))), ")"), ""), String.append(String.append(x, String.append(", ", Nat.show(s))), ")"), sfb.app_nil(String.append(String.append(x, String.append(", ", Nat.show(s))), ")"))) : {String.append(Sf.kind_text(k), String.append(" (", _)) == String.concat([StreamFailure.sp_text(k), " (", x, ", ", Nat.show(s), ")"]) : String}
  %Equal.sym(String, String.append(String.append(x, String.append(", ", Nat.show(s))), ")"), String.append(x, String.append(String.append(", ", Nat.show(s)), ")")), sfb.app_assoc(x, String.append(", ", Nat.show(s)), ")")) : {String.append(Sf.kind_text(k), String.append(" (", _)) == String.concat([StreamFailure.sp_text(k), " (", x, ", ", Nat.show(s), ")"]) : String}
  %Equal.sym(String, Sf.kind_text(k), StreamFailure.sp_text(k), sfb.text(k)) : {String.append(_, String.append(" (", String.append(x, String.append(String.append(", ", Nat.show(s)), ")")))) == String.concat([StreamFailure.sp_text(k), " (", x, ", ", Nat.show(s), ")"]) : String}
  {==}

# a detail follows the message without it
def sfm.detail(+k: Sf.Cause, +t: Maybe<&2, String>, +st: Maybe<&2, Nat>, +d: String) -> {Sf.message(k, t, st, Some{d}, None{}) == String.append(Sf.message(k, t, st, None{}, None{}), String.append(": ", d)) : String}:
  %Equal.sym(String, String.append(String.append(": ", d), ""), String.append(": ", d), sfb.app_nil(String.append(": ", d))) : {String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), _)) == String.append(String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), "")), String.append(": ", d)) : String}
  %Equal.sym(String, String.append(Sf.message.quals(Sf.quals(t, st)), ""), Sf.message.quals(Sf.quals(t, st)), sfb.app_nil(Sf.message.quals(Sf.quals(t, st)))) : {String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), String.append(": ", d))) == String.append(String.append(Sf.kind_text(k), _), String.append(": ", d)) : String}
  %Equal.sym(String, String.append(String.append(Sf.kind_text(k), Sf.message.quals(Sf.quals(t, st))), String.append(": ", d)), String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), String.append(": ", d))), sfb.app_assoc(Sf.kind_text(k), Sf.message.quals(Sf.quals(t, st)), String.append(": ", d))) : {String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), String.append(": ", d))) == _ : String}
  {==}

# a request id follows the message without it
def sfm.rid(+k: Sf.Cause, +t: Maybe<&2, String>, +st: Maybe<&2, Nat>, +d: Maybe<&2, String>, +r: String) -> {Sf.message(k, t, st, d, Some{r}) == String.append(Sf.message(k, t, st, d, None{}), String.concat([" [request_id: ", r, "]"])) : String}:
  %Equal.sym(String, String.append(String.concat([" [request_id: ", r, "]"]), ""), String.concat([" [request_id: ", r, "]"]), sfb.app_nil(String.concat([" [request_id: ", r, "]"]))) : {String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), String.append(Sf.message.detail(d), _))) == String.append(String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), String.append(Sf.message.detail(d), ""))), String.concat([" [request_id: ", r, "]"])) : String}
  %Equal.sym(String, String.append(Sf.message.detail(d), ""), Sf.message.detail(d), sfb.app_nil(Sf.message.detail(d))) : {String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), String.append(Sf.message.detail(d), String.concat([" [request_id: ", r, "]"])))) == String.append(String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), _)), String.concat([" [request_id: ", r, "]"])) : String}
  %Equal.sym(String, String.append(String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), Sf.message.detail(d))), String.concat([" [request_id: ", r, "]"])), String.append(Sf.kind_text(k), String.append(String.append(Sf.message.quals(Sf.quals(t, st)), Sf.message.detail(d)), String.concat([" [request_id: ", r, "]"]))), sfb.app_assoc(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), Sf.message.detail(d)), String.concat([" [request_id: ", r, "]"]))) : {String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), String.append(Sf.message.detail(d), String.concat([" [request_id: ", r, "]"])))) == _ : String}
  %Equal.sym(String, String.append(String.append(Sf.message.quals(Sf.quals(t, st)), Sf.message.detail(d)), String.concat([" [request_id: ", r, "]"])), String.append(Sf.message.quals(Sf.quals(t, st)), String.append(Sf.message.detail(d), String.concat([" [request_id: ", r, "]"]))), sfb.app_assoc(Sf.message.quals(Sf.quals(t, st)), Sf.message.detail(d), String.concat([" [request_id: ", r, "]"]))) : {String.append(Sf.kind_text(k), String.append(Sf.message.quals(Sf.quals(t, st)), String.append(Sf.message.detail(d), String.concat([" [request_id: ", r, "]"])))) == String.append(Sf.kind_text(k), _) : String}
  {==}

# HTTP errors (R3)
# ----------------

def sfh.or2(bt: Maybe<&2, String>, code: Maybe<&2, String>, sdk: Maybe<&2, String>) -> {Sf.or_else(bt, Sf.or_else(code, sdk)) == StreamFailure.sp_or(bt, StreamFailure.sp_or(code, sdk)) : Maybe<&2, String>}:
  match bt:
    case None{}:
      match code:
        case None{}:
          {==}
        case Some{c}:
          {==}
    case Some{b}:
      {==}

def sfh.needs(k: Sf.Cause) -> {Bool.and(Sf.needs_type(k), True{}) == StreamFailure.sf_auth_like(k) : Bool}:
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

def sfh.msg(k: Sf.Cause, t: Maybe<&2, String>, st: Maybe<&2, Nat>, d: Maybe<&2, String>, r: Maybe<&2, String>) -> {Sf.http.msg(k, t, st, d, r) == StreamFailure.sf_msg_of(k, t, st, d, r) : Maybe<&2, String>}:
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

# Stream ends (R4)
# ----------------

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

