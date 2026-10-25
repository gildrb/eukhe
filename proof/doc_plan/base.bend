# eukhe: lemmas of the proofs of area doc_plan

import Base
import ../../bend/doc_plan.bend as Dp
import ../../bend/ffi_doc_plan.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../base/wire.bend as LWire
import ../../laws/doc_plan.bend as DocPlan

# ---- logic ----

def dp.BD(b: Bool, T: Type, F: Type) -> Type:
  match b:
    case True{}:
      T
    case False{}:
      F

def dp.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : dp.BD(_, G, Unit)
  Unit{}

def dp.absurd_t(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : dp.BD(_, Unit, G)
  Unit{}

def dp.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      dp.absurd({False{} == True{} : Bool}, e)

def dp.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      dp.absurd({b == True{} : Bool}, e)

def dp.and2(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def dp.under(-s: String, -s1: String, -y: String, -f: String -> String, e: {s == f(s1) : String}, p: {s1 == y : String}) -> {s == f(y) : String}:
  %p : {s == f(_) : String}
  e

# ---- the model ----

def dp.pick(b: Bool, o: Bool) -> {Dp.content.pick(b, o) == DocPlan.content_spec.pick(b, o) : Dp.Content}:
  match b:
    case True{}:
      {==}
    case False{}:
      match o:
        case True{}:
          {==}
        case False{}:
          {==}

def dp.put_content(c: Dp.Content) -> {FDp.put_content(c) == DocPlan.spell_content(c) : String}:
  match c:
    case Dp.Kept{}:
      {==}
    case Dp.NewBase{}:
      {==}
    case Dp.NewDelta{}:
      {==}

# ---- round trips ----

def dp.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def dp.bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

def dp.change(c: Dp.Change, +re: Bool, +w: Bool, +rest: String) -> {FDp.get_publishes.change(re, Wr.get_nat(DocPlan.spell_change(c, Wr.put_bool(w, rest)))) == Wr.Got{FDp.QPublishes{re, c, w}, rest} : Wr.Dec<FDp.Req>}:
  match c:
    case Dp.NoChange{}:
      %dp.nat(0n, Wr.put_bool(w, rest), {==}) : {FDp.get_publishes.change(re, _) == Wr.Got{FDp.QPublishes{re, Dp.NoChange{}, w}, rest} : Wr.Dec<FDp.Req>}
      %dp.bool(w, rest) : {FDp.get_publishes.writes(re, Dp.NoChange{}, _) == Wr.Got{FDp.QPublishes{re, Dp.NoChange{}, w}, rest} : Wr.Dec<FDp.Req>}
      {==}
    case Dp.Fresh{}:
      %dp.nat(1n, Wr.put_bool(w, rest), {==}) : {FDp.get_publishes.change(re, _) == Wr.Got{FDp.QPublishes{re, Dp.Fresh{}, w}, rest} : Wr.Dec<FDp.Req>}
      %dp.bool(w, rest) : {FDp.get_publishes.writes(re, Dp.Fresh{}, _) == Wr.Got{FDp.QPublishes{re, Dp.Fresh{}, w}, rest} : Wr.Dec<FDp.Req>}
      {==}
    case Dp.OfLoaded{}:
      %dp.nat(2n, Wr.put_bool(w, rest), {==}) : {FDp.get_publishes.change(re, _) == Wr.Got{FDp.QPublishes{re, Dp.OfLoaded{}, w}, rest} : Wr.Dec<FDp.Req>}
      %dp.bool(w, rest) : {FDp.get_publishes.writes(re, Dp.OfLoaded{}, _) == Wr.Got{FDp.QPublishes{re, Dp.OfLoaded{}, w}, rest} : Wr.Dec<FDp.Req>}
      {==}

# a question that fits reads back: the entry is at its last step
def dp.reads(+q: FDp.Req, +rest: String, +h: {DocPlan.req_fits(q) == True{} : Bool}) -> {FDp.ffi(DocPlan.spell_req(q, rest)) == FDp.ffi.done(q, Wr.end(rest)) : String}:
  match q:
    case FDp.QContent{+s, +v, +o}:
      %dp.nat(0n, Wr.put_nat(s, Wr.put_nat(v, Wr.put_bool(o, rest))), {==}) : {FDp.ffi.got(FDp.get_req(_)) == FDp.ffi.done(FDp.QContent{s, v, o}, Wr.end(rest)) : String}
      %dp.nat(s, Wr.put_nat(v, Wr.put_bool(o, rest)), dp.and_l(LawsBase.wire_fits(s), LawsBase.wire_fits(v), h)) : {FDp.ffi.got(FDp.get_content(_)) == FDp.ffi.done(FDp.QContent{s, v, o}, Wr.end(rest)) : String}
      %dp.nat(v, Wr.put_bool(o, rest), dp.and_r(LawsBase.wire_fits(s), LawsBase.wire_fits(v), h)) : {FDp.ffi.got(FDp.get_content.version(s, _)) == FDp.ffi.done(FDp.QContent{s, v, o}, Wr.end(rest)) : String}
      %dp.bool(o, rest) : {FDp.ffi.got(FDp.get_content.ops(s, v, _)) == FDp.ffi.done(FDp.QContent{s, v, o}, Wr.end(rest)) : String}
      {==}
    case FDp.QPublishes{+re, +c, +w}:
      %dp.nat(1n, Wr.put_bool(re, DocPlan.spell_change(c, Wr.put_bool(w, rest))), {==}) : {FDp.ffi.got(FDp.get_req(_)) == FDp.ffi.done(FDp.QPublishes{re, c, w}, Wr.end(rest)) : String}
      %dp.bool(re, DocPlan.spell_change(c, Wr.put_bool(w, rest))) : {FDp.ffi.got(FDp.get_publishes(_)) == FDp.ffi.done(FDp.QPublishes{re, c, w}, Wr.end(rest)) : String}
      %Equal.sym(Wr.Dec<FDp.Req>, FDp.get_publishes.change(re, Wr.get_nat(DocPlan.spell_change(c, Wr.put_bool(w, rest)))), Wr.Got{FDp.QPublishes{re, c, w}, rest}, dp.change(c, re, w, rest)) : {FDp.ffi.got(_) == FDp.ffi.done(FDp.QPublishes{re, c, w}, Wr.end(rest)) : String}
      {==}

# ---- exactness: what the decoder reads is spelled and fits ----

def dp.PNF(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dp.pnf_go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dp.PNF(s, d):
  match d:
    case Wr.Got{+n, +r}:
      (Wire.wire_nat_exact(s, n, r, ed), Wire.wire_nat_decoded_fits(s, n, r, ed))
    case Wr.Bad{}:
      Unit{}

def dp.pnf(+s: String) -> dp.PNF(s, Wr.get_nat(s)):
  dp.pnf_go(s, Wr.get_nat(s), {==})

def dp.PB(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def dp.pb_go(+s: String, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> dp.PB(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def dp.pb(+s: String) -> dp.PB(s, Wr.get_bool(s)):
  dp.pb_go(s, Wr.get_bool(s), {==})

# what the request decoder's answer says about its input s
def dp.PR(s: String, d: Wr.Dec<FDp.Req>) -> Type:
  match d:
    case Wr.Got{+q, r}:
      {s == DocPlan.spell_req(q, r) : String} & {DocPlan.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dp.pc_o(-s: String, -st: Nat, -v: Nat, -s3: String, e: {s == Wr.put_nat(0n, Wr.put_nat(st, Wr.put_nat(v, s3))) : String}, fs: {LawsBase.wire_fits(st) == True{} : Bool}, fv: {LawsBase.wire_fits(v) == True{} : Bool}, d: Wr.Dec<Bool>, pb: dp.PB(s3, d)) -> dp.PR(s, FDp.get_content.ops(st, v, d)):
  match d:
    case Wr.Got{o, r}:
      (dp.under(s, s3, Wr.put_bool(o, r), z => Wr.put_nat(0n, Wr.put_nat(st, Wr.put_nat(v, z))), e, pb), dp.and2(LawsBase.wire_fits(st), LawsBase.wire_fits(v), fs, fv))
    case Wr.Bad{}:
      Unit{}

def dp.pc_v(-s: String, -st: Nat, -s2: String, e: {s == Wr.put_nat(0n, Wr.put_nat(st, s2)) : String}, fs: {LawsBase.wire_fits(st) == True{} : Bool}, d: Wr.Dec<Nat>, pn: dp.PNF(s2, d)) -> dp.PR(s, FDp.get_content.version(st, d)):
  match d:
    case Wr.Got{+v, +s3}:
      (e2, f2) = pn
      dp.pc_o(s, st, v, s3, dp.under(s, s2, Wr.put_nat(v, s3), z => Wr.put_nat(0n, Wr.put_nat(st, z)), e, e2), fs, f2, Wr.get_bool(s3), dp.pb(s3))
    case Wr.Bad{}:
      Unit{}

def dp.pc_s(-s: String, -s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, pn: dp.PNF(s1, d)) -> dp.PR(s, FDp.get_content(d)):
  match d:
    case Wr.Got{+st, +s2}:
      (e1, f1) = pn
      dp.pc_v(s, st, s2, dp.under(s, s1, Wr.put_nat(st, s2), z => Wr.put_nat(0n, z), e0, e1), f1, Wr.get_nat(s2), dp.pnf(s2))
    case Wr.Bad{}:
      Unit{}

def dp.pp_w(-s: String, -re: Bool, -c: Dp.Change, -s3: String, e: {s == Wr.put_nat(1n, Wr.put_bool(re, DocPlan.spell_change(c, s3))) : String}, d: Wr.Dec<Bool>, pb: dp.PB(s3, d)) -> dp.PR(s, FDp.get_publishes.writes(re, c, d)):
  match d:
    case Wr.Got{w, r}:
      (dp.under(s, s3, Wr.put_bool(w, r), z => Wr.put_nat(1n, Wr.put_bool(re, DocPlan.spell_change(c, z))), e, pb), {==})
    case Wr.Bad{}:
      Unit{}

def dp.pp_c(-s: String, -re: Bool, -s2: String, e: {s == Wr.put_nat(1n, Wr.put_bool(re, s2)) : String}, d: Wr.Dec<Nat>, pn: dp.PNF(s2, d)) -> dp.PR(s, FDp.get_publishes.change(re, d)):
  match d:
    case Wr.Got{t, +s3}:
      match t:
        case 0n:
          (e2, f2) = pn
          dp.pp_w(s, re, Dp.NoChange{}, s3, dp.under(s, s2, Wr.put_nat(0n, s3), z => Wr.put_nat(1n, Wr.put_bool(re, z)), e, e2), Wr.get_bool(s3), dp.pb(s3))
        case 1n:
          (e2, f2) = pn
          dp.pp_w(s, re, Dp.Fresh{}, s3, dp.under(s, s2, Wr.put_nat(1n, s3), z => Wr.put_nat(1n, Wr.put_bool(re, z)), e, e2), Wr.get_bool(s3), dp.pb(s3))
        case 2n:
          (e2, f2) = pn
          dp.pp_w(s, re, Dp.OfLoaded{}, s3, dp.under(s, s2, Wr.put_nat(2n, s3), z => Wr.put_nat(1n, Wr.put_bool(re, z)), e, e2), Wr.get_bool(s3), dp.pb(s3))
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def dp.pp_re(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, pb: dp.PB(s1, d)) -> dp.PR(s, FDp.get_publishes(d)):
  match d:
    case Wr.Got{+re, +s2}:
      dp.pp_c(s, re, s2, dp.under(s, s1, Wr.put_bool(re, s2), z => Wr.put_nat(1n, z), e0, pb), Wr.get_nat(s2), dp.pnf(s2))
    case Wr.Bad{}:
      Unit{}

def dp.pr_top(+s: String, d: Wr.Dec<Nat>, pn: dp.PNF(s, d)) -> dp.PR(s, FDp.get_req(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = pn
          dp.pc_s(s, s1, e0, Wr.get_nat(s1), dp.pnf(s1))
        case 1n:
          (e0, f0) = pn
          dp.pp_re(s, s1, e0, Wr.get_bool(s1), dp.pb(s1))
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every question the decoder reads is spelled, fits, and so is the input
# after it
def dp.pr(+s: String) -> dp.PR(s, FDp.get_req(Wr.get_nat(s))):
  dp.pr_top(s, Wr.get_nat(s), dp.pnf(s))

# ---- replies ----

def dp.content_not_err(c: Dp.Content) -> {LawsBase.wire_opens_err(FDp.put_content(c)) == False{} : Bool}:
  match c:
    case Dp.Kept{}:
      {==}
    case Dp.NewBase{}:
      {==}
    case Dp.NewDelta{}:
      {==}

# an answer is never the error form
def dp.answer_not_err(q: FDp.Req) -> {LawsBase.wire_opens_err(FDp.ffi.done(q, True{})) == False{} : Bool}:
  match q:
    case FDp.QContent{s, v, o}:
      dp.content_not_err(Dp.content(s, v, o))
    case FDp.QPublishes{re, c, w}:
      Wire.wire_bool_not_err(Dp.publishes(re, c, w), "")

