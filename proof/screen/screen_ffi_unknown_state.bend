# eukhe: the proof of LAW screen_ffi_unknown_state
#
# PROOF: the Run tag reads back; the block count, the first id and the
# state tag each read as themselves or Bad (ws_nat_read); a state tag of 3
# or more is no state, so the first block is Bad, the block list is Bad
# whatever its count (sus.go), and the entry answers the malformed error.

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/screen.bend as Sc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/screen/interface.bend as Screen
import ../base/wire.bend as LWire
import ../wire/base/spell.bend as LAWireSpell

def sus.st(b: Bool, +i: Nat, +n: Nat, rest: String) -> {Wr.Bad{} == FSc.get_blk.st(i, FSc.get_st.of(LAWireSpell.ws_nat_answer(b, 3n+n, rest))) : Wr.Dec<Sc.Blk>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sus.id(b: Bool, +i: Nat, +n: Nat, +rest: String) -> {Wr.Bad{} == FSc.get_blk.id(LAWireSpell.ws_nat_answer(b, i, Wr.put_nat(3n+n, rest))) : Wr.Dec<Sc.Blk>}:
  match b:
    case True{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(3n+n), 3n+n, rest), LAWireSpell.ws_nat_read(3n+n, rest)) : {Wr.Bad{} == FSc.get_blk.st(i, FSc.get_st.of(_)) : Wr.Dec<Sc.Blk>}
      sus.st(LawsBase.wire_fits(3n+n), i, n, rest)
    case False{}:
      {==}

# a block of an unknown state reads Bad
def sus.blk(+i: Nat, +n: Nat, +rest: String) -> {Wr.Bad{} == FSc.get_blk(Wr.put_nat(i, Wr.put_nat(3n+n, rest))) : Wr.Dec<Sc.Blk>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(i, Wr.put_nat(3n+n, rest))), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(i), i, Wr.put_nat(3n+n, rest)), LAWireSpell.ws_nat_read(i, Wr.put_nat(3n+n, rest))) : {Wr.Bad{} == FSc.get_blk.id(_) : Wr.Dec<Sc.Blk>}
  sus.id(LawsBase.wire_fits(i), i, n, rest)

# a bad first block makes the list Bad, whatever the count
def sus.go(m: Nat) -> {Wr.Bad{} == Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, m, Wr.Bad{}) : Wr.Dec<List<&2, Sc.Blk>>}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      {==}

def sus.cnt(b: Bool, +m: Nat, +i: Nat, +n: Nat, +rest: String) -> {FSc.ffi.of(FSc.get_run(FSc.get_tx.bs(Wr.get_list.start(~Sc.Blk, ~FSc.get_blk, LAWireSpell.ws_nat_answer(b, 1n+m, Wr.put_nat(i, Wr.put_nat(3n+n, rest))))))) == Wr.err("screen: malformed request") : String}:
  match b:
    case True{}:
      %sus.blk(i, n, rest) : {FSc.ffi.of(FSc.get_run(FSc.get_tx.bs(Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, m, _)))) == Wr.err("screen: malformed request") : String}
      %sus.go(m) : {FSc.ffi.of(FSc.get_run(FSc.get_tx.bs(_))) == Wr.err("screen: malformed request") : String}
      {==}
    case False{}:
      {==}

def Screen.screen_ffi_unknown_state(m, i, n, rest):
  +y = Wr.put_nat(i, Wr.put_nat(3n+n, rest))
  %LWire.pc.nat(0n, Wr.put_nat(1n+m, y), {==}) : {FSc.ffi.of(FSc.get_req.of(_)) == Wr.err("screen: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n+m, y)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(1n+m), 1n+m, y), LAWireSpell.ws_nat_read(1n+m, y)) : {FSc.ffi.of(FSc.get_run(FSc.get_tx.bs(Wr.get_list.start(~Sc.Blk, ~FSc.get_blk, _)))) == Wr.err("screen: malformed request") : String}
  sus.cnt(LawsBase.wire_fits(1n+m), m, i, n, rest)
