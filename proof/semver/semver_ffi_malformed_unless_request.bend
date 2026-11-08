# eukhe: the proof of LAW semver_ffi_malformed_unless_request
#
# PROOF of LAW semver_ffi_malformed_unless_request: the decoder reads only
# spelled requests that fit, the rest after them untouched (sf.go of
# semver_ffi_exact_fits); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/wire.bend as Wr
import ../../laws/semver.bend as Semver
import ../wire/base/spell.bend as LAWireSpell
import ./semver_ffi_exact_fits.bend as PSemverFfiExactFits

def smu.goal(+s: String) -> Type:
  &q: FSv.Req -> &rest: String -> {(s, Semver.req_fits(q)) == (Semver.spell_req_then(q, rest), True{}) : String & Bool}

# the proof's speller is the law's
def smu.spell(q: FSv.Req, -rest: String) -> {PSemverFfiExactFits.sf.spell(q, rest) == Semver.spell_req_then(q, rest) : String}:
  match q:
    case FSv.QRelease{c, ts}:
      {==}
    case FSv.QSeries{w, r}:
      {==}

def smu.eq(+s: String, +q: FSv.Req, +rest: String, e1: {s == PSemverFfiExactFits.sf.spell(q, rest) : String}, e2: {Semver.req_fits(q) == True{} : Bool}) -> {(s, Semver.req_fits(q)) == (Semver.spell_req_then(q, rest), True{}) : String & Bool}:
  +e3 = Equal.trans(String, s, PSemverFfiExactFits.sf.spell(q, rest), Semver.spell_req_then(q, rest), e1, smu.spell(q, rest))
  %Equal.sym(String, s, Semver.spell_req_then(q, rest), e3) : {(_, Semver.req_fits(q)) == (Semver.spell_req_then(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Semver.req_fits(q), True{}, e2) : {(Semver.spell_req_then(q, rest), _) == (Semver.spell_req_then(q, rest), True{}) : String & Bool}
  {==}

def smu.main(+s: String, d: Wr.Dec<FSv.Req>, inv: PSemverFfiExactFits.sf.RP(s, d), other: {String.eq(FSv.ffi.got(d), Wr.err("semver: malformed request")) == False{} : Bool}) -> smu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, smu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(smu.goal(s), other)

def Semver.semver_ffi_malformed_unless_request(s, other):
  smu.main(s, FSv.get_req(s), PSemverFfiExactFits.sf.go(s, Wr.get_nat(s), PSemverFfiExactFits.sf.nat(s)), other)
