# eukhe: the proof of LAW orphan_ffi_unknown_work
#
# PROOF: the window and the absence read back (LA.oe.window, the Nat round
# trip); the work tag reads as itself or Bad (ws_nat_read), and a tag of 2
# or more is no work: Bad, the malformed error form.

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/orphan.bend as Or
import ../../bend/wire.bend as Wr
import ../../laws/orphan.bend as Orphan
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ../base/logic/bool.bend as LLogicBool
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LA

def ps.bad_work(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FO.get_work.of(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) : Wr.Dec<Or.Work>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a work tag of 2 or more reads Bad
def ps.work_bad(+n: Nat, +rest: String) -> {Wr.Bad{} == FO.get_work(Wr.put_nat(2n+n, rest)) : Wr.Dec<Or.Work>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {Wr.Bad{} == FO.get_work.of(_) : Wr.Dec<Or.Work>}
  ps.bad_work(LawsBase.wire_fits(2n+n), n, rest)

def ps.unknown_work(+m: Maybe<&2, Nat>, +a: Nat, fits: {Bool.and(LawsBase.wire_mfits(m), LawsBase.wire_fits(a)) == True{} : Bool}, +n: Nat, +rest: String) -> {FO.ffi(Orphan.orphan_spell_mwindow(m, Wr.put_nat(a, Wr.put_nat(2n+n, rest)))) == Wr.err("orphan: malformed request") : String}:
  +fs = fits
  %LA.oe.window(m, Wr.put_nat(a, Wr.put_nat(2n+n, rest)), LLogicBool.pq.and_l(LawsBase.wire_mfits(m), LawsBase.wire_fits(a), fs)) : {FO.ffi.go(FO.get_req.window(_)) == Wr.err("orphan: malformed request") : String}
  %LWire.ps.ffi_nat(a, Wr.put_nat(2n+n, rest), LLogicBool.pq.and_r(LawsBase.wire_mfits(m), LawsBase.wire_fits(a), fs)) : {FO.ffi.go(FO.get_req.absent(m, _)) == Wr.err("orphan: malformed request") : String}
  %ps.work_bad(n, rest) : {FO.ffi.go(FO.get_req.work(m, a, _)) == Wr.err("orphan: malformed request") : String}
  {==}

def Orphan.orphan_ffi_unknown_work(m, a, fits, n, rest):
  ps.unknown_work(m, a, fits, n, rest)
