# eukhe: lemmas the proofs of area replace share

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../bend/replace.bend as Rp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/replace.bend as Replace
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/replace.bend as LReplace
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# x cannot be True and False
def pr.clash(-A: Type, -x: Bool, t: {x == True{} : Bool}, f: {x == False{} : Bool}) -> A:
  LLogicLogic.supervisor.ps.absurdF(A, Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, f), t))

def pr.VD(v: Rp.Verdict, A: Type) -> Type:
  match v:
    case Rp.Replace{}:
      A
    case Rp.Keep{r}:
      Unit

def pr.not_replace(-A: Type, -v: Rp.Verdict, e: {v == Rp.Replace{} : Rp.Verdict}, u: pr.VD(v, A)) -> A:
  %e : pr.VD(_, A)
  u

def pr.RD(r: Rp.Rel, A: Type) -> Type:
  match r:
    case Rp.Same{}:
      Unit
    case Rp.Older{}:
      A
    case Rp.Newer{}:
      Unit
    case Rp.Other{}:
      Unit

def pr.not_older(-A: Type, -r: Rp.Rel, e: {r == Rp.Older{} : Rp.Rel}, u: pr.RD(r, A)) -> A:
  %e : pr.RD(_, A)
  u

# The order
# ---------

def pr.lex_same(x: Nat, -t: Bool) -> {Rp.lex(x, x, t) == t : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      pr.lex_same(p, t)

def pr.lt_irrefl(xs: List<&2, Nat>) -> {Rp.lt(xs, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      Equal.trans(Bool, Rp.lex(x, x, Rp.lt(xr, xr)), Rp.lt(xr, xr), False{}, pr.lex_same(x, Rp.lt(xr, xr)), pr.lt_irrefl(xr))

def pr.lex_trans(x: Nat, y: Nat, z: Nat, -t1: Bool, -t2: Bool, -t3: Bool, h1: {Rp.lex(x, y, t1) == True{} : Bool}, h2: {Rp.lex(y, z, t2) == True{} : Bool}, k: {t1 == True{} : Bool} -> {t2 == True{} : Bool} -> {t3 == True{} : Bool}) -> {Rp.lex(x, z, t3) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      k(h1, h2)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      LLogicLogic.supervisor.ps.absurdF({Rp.lex(0n, 0n, t3) == True{} : Bool}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      LLogicLogic.supervisor.ps.absurdF({Rp.lex(1n+p, z, t3) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      LLogicLogic.supervisor.ps.absurdF({Rp.lex(1n+p, 0n, t3) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      pr.lex_trans(p, q, r, t1, t2, t3, h1, h2, k)

def pr.lt_trans(xs: List<&2, Nat>, ys: List<&2, Nat>, zs: List<&2, Nat>, h1: {Rp.lt(xs, ys) == True{} : Bool}, h2: {Rp.lt(ys, zs) == True{} : Bool}) -> {Rp.lt(xs, zs) == True{} : Bool}:
  match xs ys zs:
    case Nil{} Nil{} _:
      LLogicLogic.supervisor.ps.absurdF({Rp.lt(Nil{}, zs) == True{} : Bool}, h1)
    case Nil{} y <> yr Nil{}:
      LLogicLogic.supervisor.ps.absurdF({Rp.lt(Nil{}, Nil{}) == True{} : Bool}, h2)
    case Nil{} y <> yr z <> zr:
      {==}
    case x <> xr Nil{} _:
      LLogicLogic.supervisor.ps.absurdF({Rp.lt(x <> xr, zs) == True{} : Bool}, h1)
    case x <> xr y <> yr Nil{}:
      LLogicLogic.supervisor.ps.absurdF({Rp.lt(x <> xr, Nil{}) == True{} : Bool}, h2)
    case x <> +xr y <> +yr z <> +zr:
      pr.lex_trans(x, y, z, Rp.lt(xr, yr), Rp.lt(yr, zr), Rp.lt(xr, zr), h1, h2, a => b => pr.lt_trans(xr, yr, zr, a, b))

# The verdict
# -----------

def pr.put_replace(r: Rp.Rel, -k: Rp.Caller, e: {Rp.verdict.put(r, k) == Rp.Replace{} : Rp.Verdict}) -> {r == Rp.Older{} : Rp.Rel}:
  match r:
    case Rp.Same{}:
      pr.not_replace({Rp.Same{} == Rp.Older{} : Rp.Rel}, Rp.Keep{Rp.Same{}}, e, Unit{})
    case Rp.Older{}:
      {==}
    case Rp.Newer{}:
      pr.not_replace({Rp.Newer{} == Rp.Older{} : Rp.Rel}, Rp.Keep{Rp.Newer{}}, e, Unit{})
    case Rp.Other{}:
      pr.not_replace({Rp.Other{} == Rp.Older{} : Rp.Rel}, Rp.Keep{Rp.Other{}}, e, Unit{})

def pr.rel_older(same: Bool, older: Bool, newer: Bool, e: {Rp.rel.put(same, older, newer) == Rp.Older{} : Rp.Rel}) -> {older == True{} : Bool}:
  match same:
    case True{}:
      pr.not_older({older == True{} : Bool}, Rp.Same{}, e, Unit{})
    case False{}:
      match older:
        case True{}:
          {==}
        case False{}:
          match newer:
            case True{}:
              pr.not_older({False{} == True{} : Bool}, Rp.Newer{}, e, Unit{})
            case False{}:
              pr.not_older({False{} == True{} : Bool}, Rp.Other{}, e, Unit{})

# a replacement moves the daemon b to a client c of a higher rank
def pr.replace_older(c: Rp.Build, b: Rp.Build, -k: Rp.Caller, e: {Rp.verdict(c, b, k) == Rp.Replace{} : Rp.Verdict}) -> {Rp.lt(Rp.Build.rank(b), Rp.Build.rank(c)) == True{} : Bool}:
  match c b:
    case Rp.Build{+rc, +ic} Rp.Build{+rb, +ib}:
      pr.rel_older(String.eq(ic, ib), Rp.lt(rb, rc), Rp.lt(rc, rb), pr.put_replace(Rp.rel.put(String.eq(ic, ib), Rp.lt(rb, rc), Rp.lt(rc, rb)), k, e))

# The order and the verdict, exactly
def rk.lex_cmp(c: Cmp, -t: Bool) -> {Rp.lex.put(c, t) == Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), t)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def rk.lt_spec(xs: List<&2, Nat>, ys: List<&2, Nat>) -> {Rp.lt(xs, ys) == Replace.rank_below(xs, ys) : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      {==}
    case x <> xr Nil{}:
      {==}
    case +x <> +xr +y <> +yr:
      %rk.lt_spec(xr, yr) : {Rp.lex(x, y, Rp.lt(xr, yr)) == Bool.or(Nat.is_lt(x, y), Bool.and(Nat.is_eq(x, y), _)) : Bool}
      rk.lex_cmp(Nat.cmp(x, y), Rp.lt(xr, yr))

def rk.rel_pick(same: Bool, older: Bool, newer: Bool) -> {Rp.rel.put(same, older, newer) == Replace.rel_spec.pick(same, older, newer) : Rp.Rel}:
  match same older newer:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def rk.relation_exact(+c: Rp.Build, +d: Rp.Build) -> {Rp.relation(c, d) == Replace.rel_spec(c, d) : Rp.Rel}:
  match c d:
    case Rp.Build{+rc, +ic} Rp.Build{+rd, +id}:
      %rk.lt_spec(rd, rc) : {Rp.rel.put(String.eq(ic, id), Rp.lt(rd, rc), Rp.lt(rc, rd)) == Replace.rel_spec.pick(String.eq(ic, id), _, Replace.rank_below(rc, rd)) : Rp.Rel}
      %rk.lt_spec(rc, rd) : {Rp.rel.put(String.eq(ic, id), Rp.lt(rd, rc), Rp.lt(rc, rd)) == Replace.rel_spec.pick(String.eq(ic, id), Rp.lt(rd, rc), _) : Rp.Rel}
      rk.rel_pick(String.eq(ic, id), Rp.lt(rd, rc), Rp.lt(rc, rd))

# The spelled entry
# -----------------
# The entry bend/ffi_replace.bend against the laws' spellers (laws
# replace_ffi_*_spelled, _left_over, _reads_only_requests): a spelled
# request that fits reads back with the rest after it untouched
# (rfe.read), and the entry's answer is the spelled reply of the laws'
# decision (rfe.answer): the ranks are rank_spec (LReplace.rk.rank), the
# order rank_below (rk.lt_spec), and each tag the spelled one.

# the entry's Rel tags are the spelled ones
def rfe.rel(r: Rp.Rel, -rest: String) -> {FRp.put_rel(r, rest) == Replace.rp_spell_rel(r, rest) : String}:
  match r:
    case Rp.Same{}:
      {==}
    case Rp.Older{}:
      {==}
    case Rp.Newer{}:
      {==}
    case Rp.Other{}:
      {==}

# the entry's encoded verdict of the model is the spelled verdict_spec
def rfe.verdict(r: Rp.Rel, k: Rp.Caller, -rest: String) -> {FRp.put_verdict(Rp.verdict.put(r, k), rest) == Replace.rp_spell_verdict(Replace.verdict_spec(r, k), rest) : String}:
  match r k:
    case Rp.Same{} Rp.Interactive{}:
      {==}
    case Rp.Same{} Rp.Background{}:
      {==}
    case Rp.Older{} Rp.Interactive{}:
      {==}
    case Rp.Older{} Rp.Background{}:
      {==}
    case Rp.Newer{} Rp.Interactive{}:
      {==}
    case Rp.Newer{} Rp.Background{}:
      {==}
    case Rp.Other{} Rp.Interactive{}:
      {==}
    case Rp.Other{} Rp.Background{}:
      {==}

# the entry's relation of two versions is the laws' rp_rel_of
def rfe.relation(+c: String, +d: String, +same: Bool) -> {FRp.relation(c, d, same) == Replace.rp_rel_of(c, d, same) : Rp.Rel}:
  %LReplace.rk.rank(c) : {FRp.relation(c, d, same) == Replace.rel_spec.pick(same, Replace.rank_below(Replace.rank_spec(d), _), Replace.rank_below(_, Replace.rank_spec(d))) : Rp.Rel}
  %LReplace.rk.rank(d) : {FRp.relation(c, d, same) == Replace.rel_spec.pick(same, Replace.rank_below(_, Rp.rank(c)), Replace.rank_below(Rp.rank(c), _)) : Rp.Rel}
  %rk.lt_spec(Rp.rank(d), Rp.rank(c)) : {FRp.relation(c, d, same) == Replace.rel_spec.pick(same, _, Replace.rank_below(Rp.rank(c), Rp.rank(d))) : Rp.Rel}
  %rk.lt_spec(Rp.rank(c), Rp.rank(d)) : {FRp.relation(c, d, same) == Replace.rel_spec.pick(same, Rp.lt(Rp.rank(d), Rp.rank(c)), _) : Rp.Rel}
  rk.rel_pick(same, Rp.lt(Rp.rank(d), Rp.rank(c)), Rp.lt(Rp.rank(c), Rp.rank(d)))

# the entry answers a request with the spelled reply of the laws' decision
def rfe.answer(q: FRp.Req) -> {FRp.answer(q) == Replace.rp_spell_answer(q) : String}:
  match q:
    case FRp.ReqRelation{+c, +d, +same}:
      %rfe.relation(c, d, same) : {FRp.put_rel(FRp.relation(c, d, same), "") == Replace.rp_spell_rel(_, "") : String}
      rfe.rel(FRp.relation(c, d, same), "")
    case FRp.ReqVerdict{+c, +d, +same, +k}:
      %rfe.relation(c, d, same) : {FRp.put_verdict(Rp.verdict.put(FRp.relation(c, d, same), k), "") == Replace.rp_spell_verdict(Replace.verdict_spec(_, k), "") : String}
      rfe.verdict(FRp.relation(c, d, same), k, "")

# a spelled caller reads back
def rfe.caller_rt(k: Rp.Caller, +rest: String) -> {FRp.get_caller(Replace.rp_spell_caller(k, rest)) == Wr.Got{k, rest} : Wr.Dec<Rp.Caller>}:
  match k:
    case Rp.Interactive{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {FRp.get_caller.of(_) == Wr.Got{Rp.Interactive{}, rest} : Wr.Dec<Rp.Caller>}
      {==}
    case Rp.Background{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, rest)), Wr.Got{1n, rest}, Wire.wire_nat_round_trip(1n, rest, {==})) : {FRp.get_caller.of(_) == Wr.Got{Rp.Background{}, rest} : Wr.Dec<Rp.Caller>}
      {==}

# a spelled request that fits reads back, the rest after it untouched
def rfe.read(q: FRp.Req, +rest: String, +h: {Replace.rp_req_fits(q) == True{} : Bool}) -> {FRp.get_req(Replace.rp_spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FRp.Req>}:
  match q:
    case FRp.ReqRelation{+c, +d, +same}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, rest))))), Wr.Got{0n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, rest)))}, Wire.wire_nat_round_trip(0n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, rest))), {==})) : {FRp.get_req.of(_) == Wr.Got{FRp.ReqRelation{c, d, same}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, rest)))), Wr.Got{c, Wr.put_str(d, Wr.put_bool(same, rest))}, Wire.wire_str_round_trip(c, Wr.put_str(d, Wr.put_bool(same, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), h))) : {FRp.get_relation(_) == Wr.Got{FRp.ReqRelation{c, d, same}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(d, Wr.put_bool(same, rest))), Wr.Got{d, Wr.put_bool(same, rest)}, Wire.wire_str_round_trip(d, Wr.put_bool(same, rest), LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), h))) : {FRp.get_relation.d(c, _) == Wr.Got{FRp.ReqRelation{c, d, same}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(same, rest)), Wr.Got{same, rest}, Wire.wire_bool_round_trip(same, rest)) : {FRp.get_relation.same(c, d, _) == Wr.Got{FRp.ReqRelation{c, d, same}, rest} : Wr.Dec<FRp.Req>}
      {==}
    case FRp.ReqVerdict{+c, +d, +same, +k}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Replace.rp_spell_caller(k, rest)))))), Wr.Got{1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Replace.rp_spell_caller(k, rest))))}, Wire.wire_nat_round_trip(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Replace.rp_spell_caller(k, rest)))), {==})) : {FRp.get_req.of(_) == Wr.Got{FRp.ReqVerdict{c, d, same, k}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Replace.rp_spell_caller(k, rest))))), Wr.Got{c, Wr.put_str(d, Wr.put_bool(same, Replace.rp_spell_caller(k, rest)))}, Wire.wire_str_round_trip(c, Wr.put_str(d, Wr.put_bool(same, Replace.rp_spell_caller(k, rest))), LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), h))) : {FRp.get_verdict(_) == Wr.Got{FRp.ReqVerdict{c, d, same, k}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(d, Wr.put_bool(same, Replace.rp_spell_caller(k, rest)))), Wr.Got{d, Wr.put_bool(same, Replace.rp_spell_caller(k, rest))}, Wire.wire_str_round_trip(d, Wr.put_bool(same, Replace.rp_spell_caller(k, rest)), LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), h))) : {FRp.get_verdict.d(c, _) == Wr.Got{FRp.ReqVerdict{c, d, same, k}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(same, Replace.rp_spell_caller(k, rest))), Wr.Got{same, Replace.rp_spell_caller(k, rest)}, Wire.wire_bool_round_trip(same, Replace.rp_spell_caller(k, rest))) : {FRp.get_verdict.same(c, d, _) == Wr.Got{FRp.ReqVerdict{c, d, same, k}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<Rp.Caller>, FRp.get_caller(Replace.rp_spell_caller(k, rest)), Wr.Got{k, rest}, rfe.caller_rt(k, rest)) : {FRp.get_verdict.k(c, d, same, _) == Wr.Got{FRp.ReqVerdict{c, d, same, k}, rest} : Wr.Dec<FRp.Req>}
      {==}

# a spelled request that fits, alone, answers the spelled reply
def rfe.ffi(+q: FRp.Req, h: {Replace.rp_req_fits(q) == True{} : Bool}) -> {FRp.ffi(Replace.rp_spell_req(q, "")) == Replace.rp_spell_answer(q) : String}:
  %Equal.sym(Wr.Dec<FRp.Req>, FRp.get_req(Replace.rp_spell_req(q, "")), Wr.Got{q, ""}, rfe.read(q, "", h)) : {FRp.ffi.of(_) == Replace.rp_spell_answer(q) : String}
  rfe.answer(q)
