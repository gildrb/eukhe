# eukhe: the proof of LAW error_body_cut_over
#
# PROOF: the code's units are JS `length` (LA.ebu.units); the whole text
# has at least the units of kept then c (LA.ebu.snoc), past the cap, so it
# is cut; the code's prefix within the cap stops before c (LA.ebu.prefix:
# kept fits, kept then c does not), and the marker counts the units past
# the cap.

import Base
import ../../bend/error_body.bend as Eb
import ../../laws/error_body.bend as ErrorBody
import ../base/staging.bend as LStg
import ./base.bend as LA

def ErrorBody.error_body_cut_over(kept, c, rest, cap, hk, hc):
  +text = String.append(kept, SCon{c, rest})
  +one = String.append(kept, SCon{c, SNil{}})
  +hk2 = Equal.trans(Bool, Nat.is_le(Eb.units(kept), cap), Nat.is_le(ErrorBody.sp_units(kept), cap), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, cap), Eb.units(kept), ErrorBody.sp_units(kept), LA.ebu.units(kept)), hk)
  +hc2 = Equal.trans(Bool, Nat.is_lt(cap, Eb.units(one)), Nat.is_lt(cap, ErrorBody.sp_units(one)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(cap, z), Eb.units(one), ErrorBody.sp_units(one), LA.ebu.units(one)), hc)
  +ht = Equal.trans(Bool, Nat.is_lt(cap, Eb.units(text)), Nat.is_lt(cap, Nat.add(Eb.units(one), Eb.units(rest))), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(cap, z), Eb.units(text), Nat.add(Eb.units(one), Eb.units(rest)), LA.ebu.snoc(kept, c, rest)), LA.ebn.lt_le(cap, Eb.units(one), Nat.add(Eb.units(one), Eb.units(rest)), hc2, LA.ebn.le_add(Eb.units(one), Eb.units(rest))))
  %Equal.sym(Bool, Nat.is_le(Eb.units(text), cap), False{}, LA.ebn.lt_not_le(cap, Eb.units(text), ht)) : {Eb.truncate.at(text, cap, Eb.units(text), _) == String.concat([kept, "... [truncated ", Nat.show(Nat.sub(ErrorBody.sp_units(text), cap)), " chars]"]) : String}
  %Equal.sym(String, Eb.prefix(text, cap), kept, LA.ebu.prefix(kept, c, rest, cap, hk2, hc2)) : {String.concat([_, "... [truncated ", Nat.show(Nat.sub(Eb.units(text), cap)), " chars]"]) == String.concat([kept, "... [truncated ", Nat.show(Nat.sub(ErrorBody.sp_units(text), cap)), " chars]"]) : String}
  %Equal.sym(Nat, Eb.units(text), ErrorBody.sp_units(text), LA.ebu.units(text)) : {String.concat([kept, "... [truncated ", Nat.show(Nat.sub(_, cap)), " chars]"]) == String.concat([kept, "... [truncated ", Nat.show(Nat.sub(ErrorBody.sp_units(text), cap)), " chars]"]) : String}
  {==}
