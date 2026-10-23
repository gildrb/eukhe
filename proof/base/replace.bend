# eukhe: lemmas the proofs of two or more areas share: replace

import Base
import ../../bend/replace.bend as Rp
import ../../bend/semver.bend as Sv
import ../../laws/base.bend as LawsBase
import ../../laws/replace.bend as Replace
import ./bool/misc.bend as LBoolMisc
import ./maybe.bend as LMaybe
import ./semver.bend as LSemver

def rk.fval(ds: List<&2, Sv.Dig>) -> {Rp.fval(ds) == Sv.Num.val(ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> +rest:
      %rk.fval(rest) : {Nat.add(Sv.Dig.val(d), Nat.mul(Rp.fval(rest), 10n)) == Nat.add(Sv.Dig.val(d), Sv.Num.ten(_)) : Nat}
      %LSemver.rk.ten_mul(Rp.fval(rest)) : {Nat.add(Sv.Dig.val(d), _) == Nat.add(Sv.Dig.val(d), Sv.Num.ten(Rp.fval(rest))) : Nat}
      {==}

def rk.canon_tail(rr: List<&2, Sv.Dig>, -r: Sv.Dig, h: {Bool.not(Rp.zero(Rp.top(rr, r))) == True{} : Bool}) -> {Rp.canon(r <> rr) == True{} : Bool}:
  match rr:
    case Nil{}:
      {==}
    case r2 <> rr2:
      h

# canonical digits are the digits semver.bend writes for their value
def rk.h1(ds: List<&2, Sv.Dig>, +h: {Rp.canon(ds) == True{} : Bool}) -> {Sv.Num.dec(Sv.Num.val(ds)) == ds : List<&2, Sv.Dig>}:
  match ds:
    case Nil{}:
      LBoolMisc.semver.ps.absurdF({Sv.Num.dec(Sv.Num.val(Nil{})) == Nil{} : List<&2, Sv.Dig>}, h)
    case +d <> rest:
      match rest:
        case Nil{}:
          LSemver.rk.h1_one(d)
        case +r <> +rr:
          LSemver.rk.h1_at(d, r <> rr, Sv.Num.val(r <> rr), {==}, e => LSemver.rk.pos(rr, r, h, e), rk.h1(r <> rr, rk.canon_tail(rr, r, h)))

def rk.canon_of_nz(ds: List<&2, Sv.Dig>, h: {LBoolMisc.rk.nz(ds) == True{} : Bool}) -> {Rp.canon(ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      LBoolMisc.semver.ps.absurdF({Rp.canon(Nil{}) == True{} : Bool}, h)
    case d <> rest:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h

def rk.inc_nz_cons(d: Sv.Dig, rest: List<&2, Sv.Dig>, +h: {Rp.canon(d <> rest) == True{} : Bool}, ih: {Rp.canon(rest) == True{} : Bool} -> {LBoolMisc.rk.nz(Sv.Num.inc(rest)) == True{} : Bool}) -> {LBoolMisc.rk.nz(Sv.Num.inc(d <> rest)) == True{} : Bool}:
  match d:
    case Sv.D0{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D1{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D2{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D3{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D4{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D5{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D6{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D7{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D8{}:
      match rest:
        case Nil{}:
          {==}
        case r <> rr:
          h
    case Sv.D9{}:
      match rest:
        case Nil{}:
          {==}
        case +r <> +rr:
          LSemver.rk.nz_d0(Sv.Num.inc(r <> rr), ih(rk.canon_tail(rr, r, h)))

# the next number of canonical digits has a most significant digit that is not 0
def rk.inc_nz(ds: List<&2, Sv.Dig>, h: {Rp.canon(ds) == True{} : Bool}) -> {LBoolMisc.rk.nz(Sv.Num.inc(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      LBoolMisc.semver.ps.absurdF({LBoolMisc.rk.nz(Sv.Num.inc(Nil{})) == True{} : Bool}, h)
    case d <> +rest:
      rk.inc_nz_cons(d, rest, h, c => rk.inc_nz(rest, c))

def rk.canon_dec(n: Nat) -> {Rp.canon(Sv.Num.dec(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      rk.canon_of_nz(Sv.Num.inc(Sv.Num.dec(p)), rk.inc_nz(Sv.Num.dec(p), rk.canon_dec(p)))

# digits semver.bend reads back as written are canonical
def rk.h2(+ds: List<&2, Sv.Dig>, h: {Sv.Num.digs_eq(Sv.Num.dec(Sv.Num.val(ds)), ds) == True{} : Bool}) -> {Rp.canon(ds) == True{} : Bool}:
  %LSemver.rk.digs_sound(Sv.Num.dec(Sv.Num.val(ds)), ds, h) : {Rp.canon(_) == True{} : Bool}
  rk.canon_dec(Sv.Num.val(ds))

def rk.fp(L: Bool, +ds: List<&2, Sv.Dig>) -> {Rp.field.put(Bool.and(L, True{}), ds) == LMaybe.rk.keepm(L, Sv.Num.val(ds)) : Maybe<&2, Nat>}:
  match L:
    case True{}:
      %rk.fval(ds) : {Some{Rp.fval(ds)} == Some{_} : Maybe<&2, Nat>}
      {==}
    case False{}:
      {==}

def rk.fp0(L: Bool, -ds: List<&2, Sv.Dig>) -> {Rp.field.put(Bool.and(L, False{}), ds) == None{} : Maybe<&2, Nat>}:
  match L:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.field_at(+ds: List<&2, Sv.Dig>, c: Bool, ec: {Rp.canon(ds) == c : Bool}) -> {Rp.field.put(Bool.and(Nat.is_le(List.length(&2, Sv.Dig, ds), 14n), c), ds) == LMaybe.rk.guard(Sv.Num.read(ds)) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      +L = Nat.is_le(List.length(&2, Sv.Dig, ds), 14n)
      +V = Sv.Num.val(ds)
      +E = Equal.sym(List<&2, Sv.Dig>, Sv.Num.dec(V), ds, rk.h1(ds, ec))
      %E : {Rp.field.put(Bool.and(L, True{}), ds) == LMaybe.rk.guard(Sv.Num.read.ok(V, Sv.Num.digs_eq(_, ds))) : Maybe<&2, Nat>}
      %LSemver.ps.digs_refl(ds) : {Rp.field.put(Bool.and(L, True{}), ds) == LMaybe.rk.guard(Sv.Num.read.ok(V, _)) : Maybe<&2, Nat>}
      %E : {Rp.field.put(Bool.and(L, True{}), ds) == LMaybe.rk.keepm(Nat.is_le(List.length(&2, Sv.Dig, _), 14n), V) : Maybe<&2, Nat>}
      rk.fp(L, ds)
    case False{}:
      +L = Nat.is_le(List.length(&2, Sv.Dig, ds), 14n)
      +V = Sv.Num.val(ds)
      +D = LBoolMisc.rk.not_true(Sv.Num.digs_eq(Sv.Num.dec(V), ds), t => LBoolMisc.semver.ps.absurdF(Empty, Equal.trans(Bool, False{}, Rp.canon(ds), True{}, Equal.sym(Bool, Rp.canon(ds), False{}, ec), rk.h2(ds, t))))
      %Equal.sym(Bool, Sv.Num.digs_eq(Sv.Num.dec(V), ds), False{}, D) : {Rp.field.put(Bool.and(L, False{}), ds) == LMaybe.rk.guard(Sv.Num.read.ok(V, _)) : Maybe<&2, Nat>}
      rk.fp0(L, ds)

def rk.field(+ds: List<&2, Sv.Dig>) -> {Rp.field(ds) == LMaybe.rk.guard(Sv.Num.read(ds)) : Maybe<&2, Nat>}:
  rk.field_at(ds, Rp.canon(ds), {==})

def rk.t1(p: Bool, -x: Nat, -gc: Maybe<&2, Nat>, -t: Nat) -> {Rp.rank.of3(LMaybe.rk.keepm(p, x), None{}, gc, t) == Nil{} : List<&2, Nat>}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.t2(p: Bool, q: Bool, -x: Nat, -y: Nat, -t: Nat) -> {Rp.rank.of3(LMaybe.rk.keepm(p, x), LMaybe.rk.keepm(q, y), None{}, t) == Nil{} : List<&2, Nat>}:
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rk.t3(p: Bool, q: Bool, r: Bool, -x: Nat, -y: Nat, -z: Nat, -t: Nat) -> {Rp.rank.of3(LMaybe.rk.keepm(p, x), LMaybe.rk.keepm(q, y), LMaybe.rk.keepm(r, z), t) == Replace.rank_spec.keep(Bool.and(p, Bool.and(q, r)), x, y, t, z) : List<&2, Nat>}:
  match p q r:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def rk.three(ra: Maybe<&2, Nat>, rb: Maybe<&2, Nat>, rc: Maybe<&2, Nat>, +t: Nat) -> {Rp.rank.of3(LMaybe.rk.guard(ra), LMaybe.rk.guard(rb), LMaybe.rk.guard(rc), t) == Replace.rank_spec.of(Sv.Ver.of3(ra, rb, rc), t) : List<&2, Nat>}:
  match ra rb rc:
    case None{} _ _:
      {==}
    case Some{+x} None{} _:
      rk.t1(LawsBase.rank_spec.short(x), x, LMaybe.rk.guard(rc), t)
    case Some{+x} Some{+y} None{}:
      rk.t2(LawsBase.rank_spec.short(x), LawsBase.rank_spec.short(y), x, y, t)
    case Some{+x} Some{+y} Some{+z}:
      rk.t3(LawsBase.rank_spec.short(x), LawsBase.rank_spec.short(y), LawsBase.rank_spec.short(z), x, y, z, t)

def rk.fields(m: Maybe<&2, List<&2, List<&2, Sv.Dig>>>, +t: Nat) -> {Rp.rank.fields(m, t) == Replace.rank_spec.of(Sv.Ver.of_fields(m), t) : List<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{fs}:
      match fs:
        case Nil{}:
          {==}
        case c <> Nil{}:
          {==}
        case c <> b <> Nil{}:
          {==}
        case +c <> +b <> +a <> Nil{}:
          %Equal.sym(Maybe<&2, Nat>, Rp.field(a), LMaybe.rk.guard(Sv.Num.read(a)), rk.field(a)) : {Rp.rank.of3(_, Rp.field(b), Rp.field(c), t) == Replace.rank_spec.of(Sv.Ver.of3(Sv.Num.read(a), Sv.Num.read(b), Sv.Num.read(c)), t) : List<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, Rp.field(b), LMaybe.rk.guard(Sv.Num.read(b)), rk.field(b)) : {Rp.rank.of3(LMaybe.rk.guard(Sv.Num.read(a)), _, Rp.field(c), t) == Replace.rank_spec.of(Sv.Ver.of3(Sv.Num.read(a), Sv.Num.read(b), Sv.Num.read(c)), t) : List<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, Rp.field(c), LMaybe.rk.guard(Sv.Num.read(c)), rk.field(c)) : {Rp.rank.of3(LMaybe.rk.guard(Sv.Num.read(a)), LMaybe.rk.guard(Sv.Num.read(b)), _, t) == Replace.rank_spec.of(Sv.Ver.of3(Sv.Num.read(a), Sv.Num.read(b), Sv.Num.read(c)), t) : List<&2, Nat>}
          rk.three(Sv.Num.read(a), Sv.Num.read(b), Sv.Num.read(c), t)
        case c <> b <> a <> d <> more:
          {==}

def rk.core_at(b: Bool, -c: Char, -rest: String) -> {Rp.core.at(b, c, rest) == Replace.rank_spec.core.at(b, c, rest) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.core_eq(s: String) -> {Rp.core(s) == Replace.rank_spec.core(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      %rk.core_eq(r) : {Rp.core.at(Char.is_eq(c, '-'), c, Rp.core(r)) == Replace.rank_spec.core.at(Char.is_eq(c, '-'), c, _) : String}
      rk.core_at(Char.is_eq(c, '-'), c, Rp.core(r))

def rk.tier_at(b: Bool, -rest: Nat) -> {Rp.tier.at(b, rest) == Replace.rank_spec.tier.at(b, rest) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rk.tier_eq(s: String) -> {Rp.tier(s) == Replace.rank_spec.tier(s) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      %rk.tier_eq(r) : {Rp.tier.at(Char.is_eq(c, '-'), Rp.tier(r)) == Replace.rank_spec.tier.at(Char.is_eq(c, '-'), _) : Nat}
      rk.tier_at(Char.is_eq(c, '-'), Rp.tier(r))

def rk.rank_read(+s: String) -> {Rp.rank.fields(Sv.Ver.fields(Sv.Sym.list(Rp.core(s)), Nil{}, Nil{}), Rp.tier(s)) == Replace.rank_spec.of(Sv.Ver.parse(Replace.rank_spec.core(s)), Replace.rank_spec.tier(s)) : List<&2, Nat>}:
  %rk.core_eq(s) : {Rp.rank.fields(Sv.Ver.fields(Sv.Sym.list(Rp.core(s)), Nil{}, Nil{}), Rp.tier(s)) == Replace.rank_spec.of(Sv.Ver.of_fields(Sv.Ver.fields(Sv.Sym.list(_), Nil{}, Nil{})), Replace.rank_spec.tier(s)) : List<&2, Nat>}
  %rk.tier_eq(s) : {Rp.rank.fields(Sv.Ver.fields(Sv.Sym.list(Rp.core(s)), Nil{}, Nil{}), Rp.tier(s)) == Replace.rank_spec.of(Sv.Ver.of_fields(Sv.Ver.fields(Sv.Sym.list(Rp.core(s)), Nil{}, Nil{})), _) : List<&2, Nat>}
  rk.fields(Sv.Ver.fields(Sv.Sym.list(Rp.core(s)), Nil{}, Nil{}), Rp.tier(s))

def rk.rank_cap(short: Bool, +s: String) -> {Rp.rank.cap(short, s) == Replace.rank_spec.cap(short, s) : List<&2, Nat>}:
  match short:
    case True{}:
      rk.rank_read(s)
    case False{}:
      {==}

def rk.rank(+s: String) -> {Rp.rank(s) == Replace.rank_spec(s) : List<&2, Nat>}:
  rk.rank_cap(Nat.is_le(String.length(s), 64n), s)
