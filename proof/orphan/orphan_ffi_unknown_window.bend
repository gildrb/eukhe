# eukhe: the proof of LAW orphan_ffi_unknown_window
#
# PROOF: the window tag reads as itself or Bad (ws_nat_read), and a tag of
# 2 or more is no window: Bad, the malformed error form.

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/orphan.bend as Orphan
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def ps.bad_window(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FO.get_window.of(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ps.unknown_window(+n: Nat, +rest: String) -> {FO.ffi(Wr.put_nat(2n+n, rest)) == Wr.err("orphan: malformed request") : String}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FO.ffi.go(FO.get_req.window(FO.get_window.of(_))) == Wr.err("orphan: malformed request") : String}
  %ps.bad_window(LawsBase.wire_fits(2n+n), n, rest) : {FO.ffi.go(FO.get_req.window(_)) == Wr.err("orphan: malformed request") : String}
  {==}

def Orphan.orphan_ffi_unknown_window(n, rest):
  ps.unknown_window(n, rest)
