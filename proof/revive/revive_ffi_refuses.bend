# eukhe: the proof of LAW revive_ffi_refuses
#
# PROOF: the entry answers either a veto, a tag spelled as a Nat (never
# 'E': wire_nat_not_err), or the one error form; so an answer that opens
# with 'E' is that error form.

import Base
import ../../bend/ffi_revive.bend as FR
import ../../bend/revive.bend as Rv
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/revive.bend as Revive
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def rvf.veto(v: Rv.Veto) -> {LawsBase.wire_opens_err(FR.put_veto(v)) == False{} : Bool}:
  match v:
    case Rv.Revive{}:
      {==}
    case Rv.GaveUp{}:
      {==}
    case Rv.Archived{}:
      {==}
    case Rv.Leased{p}:
      Wire.wire_nat_not_err(3n, Wr.put_nat(p, ""))
    case Rv.NoEvidence{}:
      {==}
    case Rv.Stale{}:
      {==}

def rvf.fin(b: Bool, +f: Rv.Facts, bad: {LawsBase.wire_opens_err(FR.ffi.fin(b, f)) == True{} : Bool}) -> {FR.ffi.fin(b, f) == Wr.err("revive: malformed request") : String}:
  match b:
    case True{}:
      LStg.stg.absurd({FR.put_veto(Rv.veto(f)) == Wr.err("revive: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FR.put_veto(Rv.veto(f))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FR.put_veto(Rv.veto(f))), True{}, bad), rvf.veto(Rv.veto(f))))
    case False{}:
      {==}

def rvf.go(d: Wr.Dec<Rv.Facts>, bad: {LawsBase.wire_opens_err(FR.ffi.go(d)) == True{} : Bool}) -> {FR.ffi.go(d) == Wr.err("revive: malformed request") : String}:
  match d:
    case Wr.Got{+f, +rest}:
      rvf.fin(Wr.end(rest), f, bad)
    case Wr.Bad{}:
      {==}

def Revive.revive_ffi_refuses(s, bad):
  rvf.go(FR.get_facts(s), bad)
