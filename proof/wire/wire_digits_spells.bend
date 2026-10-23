# eukhe: the proof of LAW wire_digits_spells

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/list.bend as LList
import ../base/nat/add.bend as LNatAdd
import ../base/string.bend as LString
import ../base/wire.bend as LWire

# emit adds one char per digit to acc
def wn_len_emit(+ds: List<&2, Nat>, +acc: String)
  -> {String.length(LString.wn_emit(ds, acc)) == Nat.add(List.length(&2, Nat, ds), String.length(acc)) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %LNatAdd.wn_add_succ_r(List.length(&2, Nat, t), String.length(acc)) : {String.length(LString.wn_emit(t, SCon{Wr.dchar(d), acc})) == _ : Nat}
      wn_len_emit(t, SCon{Wr.dchar(d), acc})

def Wire.wire_digits_spells(n):
  +l = List.length(&2, Nat, LList.wn_full(n))
  %Equal.sym(Nat, LawsBase.wire_digits(n), l, LList.wn_wl(n)) : {String.length(Wr.put_nat(n, "")) == 1n+_ : Nat}
  %Equal.sym(String, Wr.put_nat(n, ""), LString.wn_emit(LList.wn_full(n), ","), LWire.wn_put_emit(n, "")) : {String.length(_) == 1n+l : Nat}
  %Equal.sym(Nat, String.length(LString.wn_emit(LList.wn_full(n), ",")), Nat.add(l, 1n), wn_len_emit(LList.wn_full(n), ",")) : {_ == 1n+l : Nat}
  %Equal.sym(Nat, Nat.add(l, 1n), 1n+Nat.add(l, 0n), LNatAdd.wn_add_succ_r(l, 0n)) : {_ == 1n+l : Nat}
  Equal.cong(Nat, Nat, k => 1n+k, Nat.add(l, 0n), l, LNatAdd.wn_add_zero_r(l))
