# eukhe: the proof of LAW screen_ffi_unknown_event
#
# PROOF: the Run tag and the spelled transcript read back (SP.scsp.tx, the
# transcript round trip); the event count and the event tag each read as
# themselves or Bad (ws_nat_read); a tag of 5 or more is no event, so the
# event list is Bad whatever its count (sue.go), and the entry answers the
# malformed error.

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/screen.bend as Sc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/screen.bend as Screen
import ../base/wire.bend as LWire
import ../wire/base/spell.bend as LAWireSpell
import ./screen_ffi_run.bend as PScreenFfiRun
import ./screen_ffi_answers_spelled/spell.bend as SP

def sue.at(b: Bool, +n: Nat, rest: String) -> {Wr.Bad{} == FSc.get_ev.of(LAWireSpell.ws_nat_answer(b, 5n+n, rest)) : Wr.Dec<Sc.Ev>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# an event of tag 5 or more reads Bad
def sue.ev(+n: Nat, +rest: String) -> {Wr.Bad{} == FSc.get_ev(Wr.put_nat(5n+n, rest)) : Wr.Dec<Sc.Ev>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(5n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(5n+n), 5n+n, rest), LAWireSpell.ws_nat_read(5n+n, rest)) : {Wr.Bad{} == FSc.get_ev.of(_) : Wr.Dec<Sc.Ev>}
  sue.at(LawsBase.wire_fits(5n+n), n, rest)

# a bad first event makes the list Bad, whatever the count
def sue.go(m: Nat) -> {Wr.Bad{} == Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, m, Wr.Bad{}) : Wr.Dec<List<&2, Sc.Ev>>}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      {==}

def sue.cnt(b: Bool, -t: Sc.Tx, +m: Nat, +n: Nat, +rest: String) -> {FSc.ffi.of(FSc.get_run.es(t, Wr.get_list.start(~Sc.Ev, ~FSc.get_ev, LAWireSpell.ws_nat_answer(b, 1n+m, Wr.put_nat(5n+n, rest))))) == Wr.err("screen: malformed request") : String}:
  match b:
    case True{}:
      %sue.ev(n, rest) : {FSc.ffi.of(FSc.get_run.es(t, Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, m, _))) == Wr.err("screen: malformed request") : String}
      %sue.go(m) : {FSc.ffi.of(FSc.get_run.es(t, _)) == Wr.err("screen: malformed request") : String}
      {==}
    case False{}:
      {==}

def Screen.screen_ffi_unknown_event(t, ft, m, n, rest):
  +v = Wr.put_nat(5n+n, rest)
  +w = Wr.put_nat(1n+m, v)
  %Equal.sym(String, Screen.screen_spell_tx(t, w), FSc.put_tx(t, w), SP.scsp.tx(t, w)) : {FSc.ffi(Wr.put_nat(0n, _)) == Wr.err("screen: malformed request") : String}
  %LWire.pc.nat(0n, FSc.put_tx(t, w), {==}) : {FSc.ffi.of(FSc.get_req.of(_)) == Wr.err("screen: malformed request") : String}
  %Equal.sym(Wr.Dec<Sc.Tx>, FSc.get_tx(FSc.put_tx(t, w)), Wr.Got{t, w}, PScreenFfiRun.fs.tx_rt(t, w, ft)) : {FSc.ffi.of(FSc.get_run(_)) == Wr.err("screen: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(w), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(1n+m), 1n+m, v), LAWireSpell.ws_nat_read(1n+m, v)) : {FSc.ffi.of(FSc.get_run.es(t, Wr.get_list.start(~Sc.Ev, ~FSc.get_ev, _))) == Wr.err("screen: malformed request") : String}
  sue.cnt(LawsBase.wire_fits(1n+m), t, m, n, rest)
