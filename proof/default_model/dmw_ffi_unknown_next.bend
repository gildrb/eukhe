# eukhe: the proof of LAW dmw_ffi_unknown_next
#
# PROOF: the spelled saved default is the entry's encoding (LS.dms.saved)
# and reads back (LA.pdw.saved), the three facts read back (LA.pdw.bool);
# the pick tag reads as itself or Bad (ws_nat_read), and a tag of 2 or
# more is no pick: Bad, the malformed error form.

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LA
import ./base/spell.bend as LS

def dun.bad(b: Bool, +sv: Dm.Saved, +cat: Bool, +key: Bool, +out: Bool, +n: Nat, rest: String) -> {FDm.ffi.go(FDm.get_in.next(sv, cat, key, out, FDm.get_next.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)))) == Wr.err("default_model: malformed request") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def DefaultModel.dmw_ffi_unknown_next(sv, fits, cat, key, out, n, rest):
  %LS.dms.saved(sv, Wr.put_bool(cat, Wr.put_bool(key, Wr.put_bool(out, Wr.put_nat(2n+n, rest))))) : {FDm.ffi(_) == Wr.err("default_model: malformed request") : String}
  %LA.pdw.saved(sv, Wr.put_bool(cat, Wr.put_bool(key, Wr.put_bool(out, Wr.put_nat(2n+n, rest)))), fits) : {FDm.ffi.go(FDm.get_in.go(_)) == Wr.err("default_model: malformed request") : String}
  %LA.pdw.bool(cat, Wr.put_bool(key, Wr.put_bool(out, Wr.put_nat(2n+n, rest)))) : {FDm.ffi.go(FDm.get_in.cat(sv, _)) == Wr.err("default_model: malformed request") : String}
  %LA.pdw.bool(key, Wr.put_bool(out, Wr.put_nat(2n+n, rest))) : {FDm.ffi.go(FDm.get_in.key(sv, cat, _)) == Wr.err("default_model: malformed request") : String}
  %LA.pdw.bool(out, Wr.put_nat(2n+n, rest)) : {FDm.ffi.go(FDm.get_in.out(sv, cat, key, _)) == Wr.err("default_model: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FDm.ffi.go(FDm.get_in.next(sv, cat, key, out, FDm.get_next.go(_))) == Wr.err("default_model: malformed request") : String}
  dun.bad(LawsBase.wire_fits(2n+n), sv, cat, key, out, n, rest)
