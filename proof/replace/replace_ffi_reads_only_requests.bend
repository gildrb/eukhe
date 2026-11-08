# eukhe: the proof of LAW replace_ffi_reads_only_requests
#
# PROOF of LAW replace_ffi_reads_only_requests: the decoder accepts only
# spellings: each stage (request tag, versions, flag, caller tag) is a
# wire value its exactness law inverts (wire_nat_exact, wire_str_exact,
# wire_bool_exact), threading the equation of the input so far; a decoded
# version fits (wire_str_decoded_fits). A tag past the last one is Bad.
# When the answer is not the error form, nothing is left after the
# request; that request is the witness, and the entry answers it with the
# spelled reply (rfe.answer).

import Base
import ../../bend/ffi_replace.bend as FRp
import ../../bend/replace.bend as Rp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/replace.bend as Replace
import ../../laws/wire.bend as Wire
import ../wire/base/spell.bend as LAWireSpell
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ./base.bend as LAReplace

# what a request decoder answer says about its input s: s spells it, and
# it fits
def rfo(s: String, d: Wr.Dec<FRp.Req>) -> Type:
  match d:
    case Wr.Got{+q, rest}:
      {s == Replace.rp_spell_req(q, rest) : String} & {Replace.rp_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# ---- a relation: 0, client, daemon, same ----

def rfo.rel_same(-s0: String, +c: String, +d: String, +s3: String,
  pre: {s0 == Wr.put_nat(0n, Wr.put_str(c, Wr.put_str(d, s3))) : String},
  fit: {Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d))) == True{} : Bool},
  r: Wr.Dec<Bool>, er: {Wr.get_bool(s3) == r : Wr.Dec<Bool>}) -> rfo(s0, FRp.get_relation.same(c, d, r)):
  match r:
    case Wr.Got{+same, +s4}:
      (Equal.trans(String, s0, Wr.put_nat(0n, Wr.put_str(c, Wr.put_str(d, s3))), Wr.put_nat(0n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, s4)))), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_str(c, Wr.put_str(d, z))), s3, Wr.put_bool(same, s4), Wire.wire_bool_exact(s3, same, s4, er))),
        fit)
    case Wr.Bad{}:
      Unit{}

def rfo.rel_d(-s0: String, +c: String, +s2: String,
  pre: {s0 == Wr.put_nat(0n, Wr.put_str(c, s2)) : String},
  hc: {LawsBase.wire_fits(String.length(c)) == True{} : Bool},
  r: Wr.Dec<String>, er: {Wr.get_str(s2) == r : Wr.Dec<String>}) -> rfo(s0, FRp.get_relation.d(c, r)):
  match r:
    case Wr.Got{+d, +s3}:
      +e2 = er
      rfo.rel_same(s0, c, d, s3,
        Equal.trans(String, s0, Wr.put_nat(0n, Wr.put_str(c, s2)), Wr.put_nat(0n, Wr.put_str(c, Wr.put_str(d, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_str(c, z)), s2, Wr.put_str(d, s3), Wire.wire_str_exact(s2, d, s3, e2))),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), hc, Wire.wire_str_decoded_fits(s2, d, s3, e2)),
        Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

# a relation request: its client version
def rfo.rel(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(0n, s1) : String}, r: Wr.Dec<String>, er: {Wr.get_str(s1) == r : Wr.Dec<String>}) -> rfo(s0, FRp.get_relation(r)):
  match r:
    case Wr.Got{+c, +s2}:
      +e2 = er
      rfo.rel_d(s0, c, s2,
        Equal.trans(String, s0, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_str(c, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_str(c, s2), Wire.wire_str_exact(s1, c, s2, e2))),
        Wire.wire_str_decoded_fits(s1, c, s2, e2), Wr.get_str(s2), {==})
    case Wr.Bad{}:
      Unit{}

# ---- a verdict: 1, client, daemon, same, caller ----

def rfo.ver_tag(-s0: String, +c: String, +d: String, +same: Bool, -s4: String, kt: Nat, +s5: String,
  pre: {s0 == Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, s4)))) : String},
  fit: {Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d))) == True{} : Bool},
  ex: {s4 == Wr.put_nat(kt, s5) : String}) -> rfo(s0, FRp.get_verdict.k(c, d, same, FRp.get_caller.tag(kt, s5))):
  match kt:
    case 0n:
      (Equal.trans(String, s0, Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, s4)))), Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Wr.put_nat(0n, s5))))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, z)))), s4, Wr.put_nat(0n, s5), ex)),
        fit)
    case 1n:
      (Equal.trans(String, s0, Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, s4)))), Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Wr.put_nat(1n, s5))))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, z)))), s4, Wr.put_nat(1n, s5), ex)),
        fit)
    case 2n+y:
      Unit{}

def rfo.ver_k(-s0: String, +c: String, +d: String, +same: Bool, +s4: String,
  pre: {s0 == Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, s4)))) : String},
  fit: {Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d))) == True{} : Bool},
  r: Wr.Dec<Nat>, er: {Wr.get_nat(s4) == r : Wr.Dec<Nat>}) -> rfo(s0, FRp.get_verdict.k(c, d, same, FRp.get_caller.of(r))):
  match r:
    case Wr.Got{+kt, +s5}:
      rfo.ver_tag(s0, c, d, same, s4, kt, s5, pre, fit, Wire.wire_nat_exact(s4, kt, s5, er))
    case Wr.Bad{}:
      Unit{}

def rfo.ver_same(-s0: String, +c: String, +d: String, +s3: String,
  pre: {s0 == Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, s3))) : String},
  fit: {Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d))) == True{} : Bool},
  r: Wr.Dec<Bool>, er: {Wr.get_bool(s3) == r : Wr.Dec<Bool>}) -> rfo(s0, FRp.get_verdict.same(c, d, r)):
  match r:
    case Wr.Got{+same, +s4}:
      rfo.ver_k(s0, c, d, same, s4,
        Equal.trans(String, s0, Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, s3))), Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, s4)))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, z))), s3, Wr.put_bool(same, s4), Wire.wire_bool_exact(s3, same, s4, er))),
        fit, Wr.get_nat(s4), {==})
    case Wr.Bad{}:
      Unit{}

def rfo.ver_d(-s0: String, +c: String, +s2: String,
  pre: {s0 == Wr.put_nat(1n, Wr.put_str(c, s2)) : String},
  hc: {LawsBase.wire_fits(String.length(c)) == True{} : Bool},
  r: Wr.Dec<String>, er: {Wr.get_str(s2) == r : Wr.Dec<String>}) -> rfo(s0, FRp.get_verdict.d(c, r)):
  match r:
    case Wr.Got{+d, +s3}:
      +e2 = er
      rfo.ver_same(s0, c, d, s3,
        Equal.trans(String, s0, Wr.put_nat(1n, Wr.put_str(c, s2)), Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_str(c, z)), s2, Wr.put_str(d, s3), Wire.wire_str_exact(s2, d, s3, e2))),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)), hc, Wire.wire_str_decoded_fits(s2, d, s3, e2)),
        Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

# a verdict request: its client version
def rfo.ver(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(1n, s1) : String}, r: Wr.Dec<String>, er: {Wr.get_str(s1) == r : Wr.Dec<String>}) -> rfo(s0, FRp.get_verdict(r)):
  match r:
    case Wr.Got{+c, +s2}:
      +e2 = er
      rfo.ver_d(s0, c, s2,
        Equal.trans(String, s0, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(c, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_str(c, s2), Wire.wire_str_exact(s1, c, s2, e2))),
        Wire.wire_str_decoded_fits(s1, c, s2, e2), Wr.get_str(s2), {==})
    case Wr.Bad{}:
      Unit{}

# ---- the request ----

def rfo.tag(+s0: String, t: Nat, +s1: String, ex: {s0 == Wr.put_nat(t, s1) : String}) -> rfo(s0, FRp.get_req.tag(t, s1)):
  match t:
    case 0n:
      rfo.rel(s0, s1, ex, Wr.get_str(s1), {==})
    case 1n:
      rfo.ver(s0, s1, ex, Wr.get_str(s1), {==})
    case 2n+y:
      Unit{}

def rfo.top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> rfo(s, FRp.get_req.of(r)):
  match r:
    case Wr.Got{+t, +s1}:
      rfo.tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, er))
    case Wr.Bad{}:
      Unit{}

# every request the decoder reads is spelled, and fits
def rfo.all(+s: String) -> rfo(s, FRp.get_req(s)):
  rfo.top(s, Wr.get_nat(s), {==})

# ---- the entry ----

# the claim: s spells a request that fits, and the entry answers it
def rfo.goal(+s: String) -> Type:
  &q: FRp.Req -> {(s, (Replace.rp_req_fits(q), FRp.ffi(s))) == (Replace.rp_spell_req(q, ""), (True{}, Replace.rp_spell_answer(q))) : String & (Bool & String)}

def rfo.eq(+s: String, +q: FRp.Req, ed: {FRp.get_req(s) == Wr.Got{q, ""} : Wr.Dec<FRp.Req>},
  e1: {s == Replace.rp_spell_req(q, "") : String}, e2: {Replace.rp_req_fits(q) == True{} : Bool}) -> {(s, (Replace.rp_req_fits(q), FRp.ffi(s))) == (Replace.rp_spell_req(q, ""), (True{}, Replace.rp_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(Wr.Dec<FRp.Req>, FRp.get_req(s), Wr.Got{q, ""}, ed) : {(s, (Replace.rp_req_fits(q), FRp.ffi.of(_))) == (Replace.rp_spell_req(q, ""), (True{}, Replace.rp_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, FRp.answer(q), Replace.rp_spell_answer(q), LAReplace.rfe.answer(q)) : {(s, (Replace.rp_req_fits(q), _)) == (Replace.rp_spell_req(q, ""), (True{}, Replace.rp_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, Replace.rp_req_fits(q), True{}, e2) : {(s, (_, Replace.rp_spell_answer(q))) == (Replace.rp_spell_req(q, ""), (True{}, Replace.rp_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, s, Replace.rp_spell_req(q, ""), e1) : {(_, (True{}, Replace.rp_spell_answer(q))) == (Replace.rp_spell_req(q, ""), (True{}, Replace.rp_spell_answer(q))) : String & (Bool & String)}
  {==}

def rfo.rest(+s: String, +q: FRp.Req, rest: String, ed: {FRp.get_req(s) == Wr.Got{q, rest} : Wr.Dec<FRp.Req>},
  e1: {s == Replace.rp_spell_req(q, rest) : String}, e2: {Replace.rp_req_fits(q) == True{} : Bool},
  ok: {LawsBase.wire_opens_err(FRp.ffi.whole(q, Wr.end(rest))) == False{} : Bool}) -> rfo.goal(s):
  match rest:
    case SNil{}:
      (q, rfo.eq(s, q, ed, e1, e2))
    case SCon{c, more}:
      LAWireSpell.ws_absurd(rfo.goal(s), ok)

def rfo.main(+s: String, d: Wr.Dec<FRp.Req>, ed: {FRp.get_req(s) == d : Wr.Dec<FRp.Req>}, inv: rfo(s, d),
  ok: {LawsBase.wire_opens_err(FRp.ffi.of(d)) == False{} : Bool}) -> rfo.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      rfo.rest(s, q, rest, ed, e1, e2, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(rfo.goal(s), ok)

def Replace.replace_ffi_reads_only_requests(s, ok):
  rfo.main(s, FRp.get_req(s), {==}, rfo.all(s), ok)
