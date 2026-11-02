# eukhe: the proof of LAW replace_ffi_exact
#
# PROOF: the entry's decoder takes, stage by stage, the same branches on
# the same wire primitives as the spec's reader (rpx.tag .. rpx.caller), so
# it reads every input as the spec does. On a request with nothing after it
# the entry's relation is the spec's: its ranks are rank_spec's
# (replace_rank_reads_semver), its order rank_below (LA.rk.lt_spec), its
# pick rel_spec.pick (LA.rk.rel_pick); its verdict verdict_spec
# (PV.rk.verdict_put); each spelled as the spec spells it. The two error
# texts are the spec's.

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../bend/replace.bend as Rp
import ../../bend/wire.bend as Wr
import ../../laws/replace.bend as Replace
import ./base.bend as LA
import ./replace_rank_reads_semver.bend as PReplaceRankReadsSemver
import ./replace_verdict_exact.bend as PV

def rpx.caller(+c: String, +d: String, +same: Bool, dn: Wr.Dec<Nat>) -> {FRp.get_verdict.k(c, d, same, FRp.get_caller.of(dn)) == Replace.rp_read.caller(c, d, same, dn) : Wr.Dec<FRp.Req>}:
  match dn:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n+p:
          {==}
    case Wr.Bad{}:
      {==}

def rpx.rel_same(+c: String, +d: String, db: Wr.Dec<Bool>) -> {FRp.get_relation.same(c, d, db) == Replace.rp_read.same(False{}, c, d, db) : Wr.Dec<FRp.Req>}:
  match db:
    case Wr.Got{same, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rpx.ver_same(+c: String, +d: String, db: Wr.Dec<Bool>) -> {FRp.get_verdict.same(c, d, db) == Replace.rp_read.same(True{}, c, d, db) : Wr.Dec<FRp.Req>}:
  match db:
    case Wr.Got{+same, +s}:
      rpx.caller(c, d, same, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rpx.rel_d(+c: String, ds: Wr.Dec<String>) -> {FRp.get_relation.d(c, ds) == Replace.rp_read.daemon(False{}, c, ds) : Wr.Dec<FRp.Req>}:
  match ds:
    case Wr.Got{+d, +s}:
      rpx.rel_same(c, d, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def rpx.ver_d(+c: String, ds: Wr.Dec<String>) -> {FRp.get_verdict.d(c, ds) == Replace.rp_read.daemon(True{}, c, ds) : Wr.Dec<FRp.Req>}:
  match ds:
    case Wr.Got{+d, +s}:
      rpx.ver_same(c, d, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def rpx.rel(cs: Wr.Dec<String>) -> {FRp.get_relation(cs) == Replace.rp_read.client(False{}, cs) : Wr.Dec<FRp.Req>}:
  match cs:
    case Wr.Got{+c, +s}:
      rpx.rel_d(c, Wr.get_str(s))
    case Wr.Bad{}:
      {==}

def rpx.ver(cs: Wr.Dec<String>) -> {FRp.get_verdict(cs) == Replace.rp_read.client(True{}, cs) : Wr.Dec<FRp.Req>}:
  match cs:
    case Wr.Got{+c, +s}:
      rpx.ver_d(c, Wr.get_str(s))
    case Wr.Bad{}:
      {==}

# the entry's decoder reads as the spec's reader
def rpx.tag(dn: Wr.Dec<Nat>) -> {FRp.get_req.of(dn) == Replace.rp_read.tag(dn) : Wr.Dec<FRp.Req>}:
  match dn:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          rpx.rel(Wr.get_str(s))
        case 1n:
          rpx.ver(Wr.get_str(s))
        case 2n+p:
          {==}
    case Wr.Bad{}:
      {==}

# the relation of two ranks equal to the spec's ranks is the spec's
def rpx.pick(same: Bool, +rc: List<&2, Nat>, +rd: List<&2, Nat>, -sc: List<&2, Nat>, -sd: List<&2, Nat>, ec: {rc == sc : List<&2, Nat>}, ed: {rd == sd : List<&2, Nat>}) -> {Rp.rel.put(same, Rp.lt(rd, rc), Rp.lt(rc, rd)) == Replace.rel_spec.pick(same, Replace.rank_below(sd, sc), Replace.rank_below(sc, sd)) : Rp.Rel}:
  %ec : {Rp.rel.put(same, Rp.lt(rd, rc), Rp.lt(rc, rd)) == Replace.rel_spec.pick(same, Replace.rank_below(sd, _), Replace.rank_below(_, sd)) : Rp.Rel}
  %ed : {Rp.rel.put(same, Rp.lt(rd, rc), Rp.lt(rc, rd)) == Replace.rel_spec.pick(same, Replace.rank_below(_, rc), Replace.rank_below(rc, _)) : Rp.Rel}
  %Equal.sym(Bool, Rp.lt(rd, rc), Replace.rank_below(rd, rc), LA.rk.lt_spec(rd, rc)) : {Rp.rel.put(same, _, Rp.lt(rc, rd)) == Replace.rel_spec.pick(same, Replace.rank_below(rd, rc), Replace.rank_below(rc, rd)) : Rp.Rel}
  %Equal.sym(Bool, Rp.lt(rc, rd), Replace.rank_below(rc, rd), LA.rk.lt_spec(rc, rd)) : {Rp.rel.put(same, Replace.rank_below(rd, rc), _) == Replace.rel_spec.pick(same, Replace.rank_below(rd, rc), Replace.rank_below(rc, rd)) : Rp.Rel}
  LA.rk.rel_pick(same, Replace.rank_below(rd, rc), Replace.rank_below(rc, rd))

# the entry's relation is the spec's
def rpx.relation(+c: String, +d: String, same: Bool) -> {FRp.relation(c, d, same) == Replace.rp_rel(c, d, same) : Rp.Rel}:
  rpx.pick(same, Rp.rank(c), Rp.rank(d), Replace.rank_spec(c), Replace.rank_spec(d), Replace.replace_rank_reads_semver(c), Replace.replace_rank_reads_semver(d))

def rpx.spell_rel(r: Rp.Rel) -> {FRp.put_rel(r, "") == Replace.rp_spell_rel(r, "") : String}:
  match r:
    case Rp.Same{}:
      {==}
    case Rp.Older{}:
      {==}
    case Rp.Newer{}:
      {==}
    case Rp.Other{}:
      {==}

def rpx.spell_verdict(v: Rp.Verdict) -> {FRp.put_verdict(v, "") == Replace.rp_spell_verdict(v, "") : String}:
  match v:
    case Rp.Replace{}:
      {==}
    case Rp.Keep{r}:
      match r:
        case Rp.Same{}:
          {==}
        case Rp.Older{}:
          {==}
        case Rp.Newer{}:
          {==}
        case Rp.Other{}:
          {==}

# the entry's reply to a whole request is the spec's
def rpx.reply(q: FRp.Req) -> {FRp.answer(q) == Replace.rp_reply(q) : String}:
  match q:
    case FRp.ReqRelation{+c, +d, +same}:
      %Equal.sym(Rp.Rel, FRp.relation(c, d, same), Replace.rp_rel(c, d, same), rpx.relation(c, d, same)) : {FRp.put_rel(_, "") == Replace.rp_spell_rel(Replace.rp_rel(c, d, same), "") : String}
      rpx.spell_rel(Replace.rp_rel(c, d, same))
    case FRp.ReqVerdict{+c, +d, +same, +k}:
      +r = Replace.rp_rel(c, d, same)
      %Equal.sym(Rp.Rel, FRp.relation(c, d, same), r, rpx.relation(c, d, same)) : {FRp.put_verdict(Rp.verdict.put(_, k), "") == Replace.rp_spell_verdict(Replace.verdict_spec(r, k), "") : String}
      %Equal.sym(Rp.Verdict, Rp.verdict.put(r, k), Replace.verdict_spec(r, k), PV.rk.verdict_put(r, k)) : {FRp.put_verdict(_, "") == Replace.rp_spell_verdict(Replace.verdict_spec(r, k), "") : String}
      rpx.spell_verdict(Replace.verdict_spec(r, k))

def rpx.end(q: FRp.Req, r: String) -> {FRp.ffi.whole(q, Wr.end(r)) == Replace.rp_entry.of(Wr.Got{q, r}) : String}:
  match r:
    case SNil{}:
      rpx.reply(q)
    case SCon{c, t}:
      {==}

def rpx.go(d: Wr.Dec<FRp.Req>) -> {FRp.ffi.of(d) == Replace.rp_entry.of(d) : String}:
  match d:
    case Wr.Got{q, r}:
      rpx.end(q, r)
    case Wr.Bad{}:
      {==}

def Replace.replace_ffi_exact(s):
  %rpx.tag(Wr.get_nat(s)) : {FRp.ffi(s) == Replace.rp_entry.of(_) : String}
  rpx.go(FRp.get_req(s))
