# eukhe: the proof of LAW timeouts_ffi_malformed_unless_request
#
# PROOF: each of the 19 base values the entry's decoder reads is exactly
# its spelling, then its rest (wire_nat_exact), and fits the wire
# (wire_nat_decoded_fits); the stages carry the input spelled up to their
# value (`pre`). So the base values the decoder reads are the input's
# spelled prefix; the entry answers anything but the malformed error only
# when nothing follows them (an empty rest), i.e. when the input is exactly
# their spelling.

import Base
import ../../bend/ffi_timeouts.bend as FT
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/timeouts.bend as Timeouts
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/base/spell.bend as LAWireSpell

# s spelled up to a value a is s spelled up to its spelling b
def tmu.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# the base values t spelled as Rust writes them, then rest
def tmu.spell_then(t: Su.Tm, rest: String) -> String:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, Wr.put_nat(slack, Wr.put_nat(k, Wr.put_nat(bmax, Wr.put_nat(loop, Wr.put_nat(qanswer, rest)))))))))))))))))))

def tmu.spell_nil(t: Su.Tm) -> {tmu.spell_then(t, "") == Timeouts.tw_spell(t) : String}:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      {==}

# base values the decoder reads: the input is their spelling, then the
# rest, and they fit
def tmu.Rd(s: String, d: Wr.Dec<Su.Tm>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == tmu.spell_then(t, r) : String} & {Timeouts.tw_fits(t) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tmu.qanswer(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +margin: Nat, +refresh: Nat, +boot: Nat, +relaunch: Nat, +startup: Nat, +check: Nat, +slack: Nat, +k: Nat, +bmax: Nat, +loop: Nat, +s18: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, Wr.put_nat(slack, Wr.put_nat(k, Wr.put_nat(bmax, Wr.put_nat(loop, s18)))))))))))))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, hmargin: {LawsBase.wire_fits(margin) == True{} : Bool}, hrefresh: {LawsBase.wire_fits(refresh) == True{} : Bool}, hboot: {LawsBase.wire_fits(boot) == True{} : Bool}, hrelaunch: {LawsBase.wire_fits(relaunch) == True{} : Bool}, hstartup: {LawsBase.wire_fits(startup) == True{} : Bool}, hcheck: {LawsBase.wire_fits(check) == True{} : Bool}, hslack: {LawsBase.wire_fits(slack) == True{} : Bool}, hk: {LawsBase.wire_fits(k) == True{} : Bool}, hbmax: {LawsBase.wire_fits(bmax) == True{} : Bool}, hloop: {LawsBase.wire_fits(loop) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s18) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.qanswer(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, d)):
  match d:
    case Wr.Got{+qanswer, +s19}:
      +ee = ed
      +hqanswer = Wire.wire_nat_decoded_fits(s18, qanswer, s19, ee)
      (tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, Wr.put_nat(slack, Wr.put_nat(k, Wr.put_nat(bmax, Wr.put_nat(loop, z)))))))))))))))))), s, s18, Wr.put_nat(qanswer, s19), pre, Wire.wire_nat_exact(s18, qanswer, s19, ee)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(snap), Bool.and(LawsBase.wire_fits(host), Bool.and(LawsBase.wire_fits(kstep), Bool.and(LawsBase.wire_fits(kterm), Bool.and(LawsBase.wire_fits(kverify), Bool.and(LawsBase.wire_fits(harness), Bool.and(LawsBase.wire_fits(wterm), Bool.and(LawsBase.wire_fits(wverify), Bool.and(LawsBase.wire_fits(margin), Bool.and(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer)))))))))))))))))), hsnap, LAWireSpell.ws_and_tt(LawsBase.wire_fits(host), Bool.and(LawsBase.wire_fits(kstep), Bool.and(LawsBase.wire_fits(kterm), Bool.and(LawsBase.wire_fits(kverify), Bool.and(LawsBase.wire_fits(harness), Bool.and(LawsBase.wire_fits(wterm), Bool.and(LawsBase.wire_fits(wverify), Bool.and(LawsBase.wire_fits(margin), Bool.and(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer))))))))))))))))), hhost, LAWireSpell.ws_and_tt(LawsBase.wire_fits(kstep), Bool.and(LawsBase.wire_fits(kterm), Bool.and(LawsBase.wire_fits(kverify), Bool.and(LawsBase.wire_fits(harness), Bool.and(LawsBase.wire_fits(wterm), Bool.and(LawsBase.wire_fits(wverify), Bool.and(LawsBase.wire_fits(margin), Bool.and(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer)))))))))))))))), hkstep, LAWireSpell.ws_and_tt(LawsBase.wire_fits(kterm), Bool.and(LawsBase.wire_fits(kverify), Bool.and(LawsBase.wire_fits(harness), Bool.and(LawsBase.wire_fits(wterm), Bool.and(LawsBase.wire_fits(wverify), Bool.and(LawsBase.wire_fits(margin), Bool.and(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer))))))))))))))), hkterm, LAWireSpell.ws_and_tt(LawsBase.wire_fits(kverify), Bool.and(LawsBase.wire_fits(harness), Bool.and(LawsBase.wire_fits(wterm), Bool.and(LawsBase.wire_fits(wverify), Bool.and(LawsBase.wire_fits(margin), Bool.and(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer)))))))))))))), hkverify, LAWireSpell.ws_and_tt(LawsBase.wire_fits(harness), Bool.and(LawsBase.wire_fits(wterm), Bool.and(LawsBase.wire_fits(wverify), Bool.and(LawsBase.wire_fits(margin), Bool.and(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer))))))))))))), hharness, LAWireSpell.ws_and_tt(LawsBase.wire_fits(wterm), Bool.and(LawsBase.wire_fits(wverify), Bool.and(LawsBase.wire_fits(margin), Bool.and(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer)))))))))))), hwterm, LAWireSpell.ws_and_tt(LawsBase.wire_fits(wverify), Bool.and(LawsBase.wire_fits(margin), Bool.and(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer))))))))))), hwverify, LAWireSpell.ws_and_tt(LawsBase.wire_fits(margin), Bool.and(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer)))))))))), hmargin, LAWireSpell.ws_and_tt(LawsBase.wire_fits(refresh), Bool.and(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer))))))))), hrefresh, LAWireSpell.ws_and_tt(LawsBase.wire_fits(boot), Bool.and(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer)))))))), hboot, LAWireSpell.ws_and_tt(LawsBase.wire_fits(relaunch), Bool.and(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer))))))), hrelaunch, LAWireSpell.ws_and_tt(LawsBase.wire_fits(startup), Bool.and(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer)))))), hstartup, LAWireSpell.ws_and_tt(LawsBase.wire_fits(check), Bool.and(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer))))), hcheck, LAWireSpell.ws_and_tt(LawsBase.wire_fits(slack), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer)))), hslack, LAWireSpell.ws_and_tt(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer))), hk, LAWireSpell.ws_and_tt(LawsBase.wire_fits(bmax), Bool.and(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer)), hbmax, LAWireSpell.ws_and_tt(LawsBase.wire_fits(loop), LawsBase.wire_fits(qanswer), hloop, hqanswer)))))))))))))))))))
    case Wr.Bad{}:
      Unit{}

def tmu.loop(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +margin: Nat, +refresh: Nat, +boot: Nat, +relaunch: Nat, +startup: Nat, +check: Nat, +slack: Nat, +k: Nat, +bmax: Nat, +s17: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, Wr.put_nat(slack, Wr.put_nat(k, Wr.put_nat(bmax, s17))))))))))))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, hmargin: {LawsBase.wire_fits(margin) == True{} : Bool}, hrefresh: {LawsBase.wire_fits(refresh) == True{} : Bool}, hboot: {LawsBase.wire_fits(boot) == True{} : Bool}, hrelaunch: {LawsBase.wire_fits(relaunch) == True{} : Bool}, hstartup: {LawsBase.wire_fits(startup) == True{} : Bool}, hcheck: {LawsBase.wire_fits(check) == True{} : Bool}, hslack: {LawsBase.wire_fits(slack) == True{} : Bool}, hk: {LawsBase.wire_fits(k) == True{} : Bool}, hbmax: {LawsBase.wire_fits(bmax) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s17) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.loop(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, d)):
  match d:
    case Wr.Got{+loop, +s18}:
      +ee = ed
      +hloop = Wire.wire_nat_decoded_fits(s17, loop, s18, ee)
      tmu.qanswer(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, s18, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, Wr.put_nat(slack, Wr.put_nat(k, Wr.put_nat(bmax, z))))))))))))))))), s, s17, Wr.put_nat(loop, s18), pre, Wire.wire_nat_exact(s17, loop, s18, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, hmargin, hrefresh, hboot, hrelaunch, hstartup, hcheck, hslack, hk, hbmax, hloop, Wr.get_nat(s18), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.bmax(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +margin: Nat, +refresh: Nat, +boot: Nat, +relaunch: Nat, +startup: Nat, +check: Nat, +slack: Nat, +k: Nat, +s16: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, Wr.put_nat(slack, Wr.put_nat(k, s16)))))))))))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, hmargin: {LawsBase.wire_fits(margin) == True{} : Bool}, hrefresh: {LawsBase.wire_fits(refresh) == True{} : Bool}, hboot: {LawsBase.wire_fits(boot) == True{} : Bool}, hrelaunch: {LawsBase.wire_fits(relaunch) == True{} : Bool}, hstartup: {LawsBase.wire_fits(startup) == True{} : Bool}, hcheck: {LawsBase.wire_fits(check) == True{} : Bool}, hslack: {LawsBase.wire_fits(slack) == True{} : Bool}, hk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s16) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.bmax(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, d)):
  match d:
    case Wr.Got{+bmax, +s17}:
      +ee = ed
      +hbmax = Wire.wire_nat_decoded_fits(s16, bmax, s17, ee)
      tmu.loop(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, s17, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, Wr.put_nat(slack, Wr.put_nat(k, z)))))))))))))))), s, s16, Wr.put_nat(bmax, s17), pre, Wire.wire_nat_exact(s16, bmax, s17, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, hmargin, hrefresh, hboot, hrelaunch, hstartup, hcheck, hslack, hk, hbmax, Wr.get_nat(s17), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.k(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +margin: Nat, +refresh: Nat, +boot: Nat, +relaunch: Nat, +startup: Nat, +check: Nat, +slack: Nat, +s15: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, Wr.put_nat(slack, s15))))))))))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, hmargin: {LawsBase.wire_fits(margin) == True{} : Bool}, hrefresh: {LawsBase.wire_fits(refresh) == True{} : Bool}, hboot: {LawsBase.wire_fits(boot) == True{} : Bool}, hrelaunch: {LawsBase.wire_fits(relaunch) == True{} : Bool}, hstartup: {LawsBase.wire_fits(startup) == True{} : Bool}, hcheck: {LawsBase.wire_fits(check) == True{} : Bool}, hslack: {LawsBase.wire_fits(slack) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s15) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.k(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, d)):
  match d:
    case Wr.Got{+k, +s16}:
      +ee = ed
      +hk = Wire.wire_nat_decoded_fits(s15, k, s16, ee)
      tmu.bmax(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, s16, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, Wr.put_nat(slack, z))))))))))))))), s, s15, Wr.put_nat(k, s16), pre, Wire.wire_nat_exact(s15, k, s16, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, hmargin, hrefresh, hboot, hrelaunch, hstartup, hcheck, hslack, hk, Wr.get_nat(s16), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.slack(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +margin: Nat, +refresh: Nat, +boot: Nat, +relaunch: Nat, +startup: Nat, +check: Nat, +s14: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, s14)))))))))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, hmargin: {LawsBase.wire_fits(margin) == True{} : Bool}, hrefresh: {LawsBase.wire_fits(refresh) == True{} : Bool}, hboot: {LawsBase.wire_fits(boot) == True{} : Bool}, hrelaunch: {LawsBase.wire_fits(relaunch) == True{} : Bool}, hstartup: {LawsBase.wire_fits(startup) == True{} : Bool}, hcheck: {LawsBase.wire_fits(check) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s14) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.slack(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, d)):
  match d:
    case Wr.Got{+slack, +s15}:
      +ee = ed
      +hslack = Wire.wire_nat_decoded_fits(s14, slack, s15, ee)
      tmu.k(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, s15, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, Wr.put_nat(check, z)))))))))))))), s, s14, Wr.put_nat(slack, s15), pre, Wire.wire_nat_exact(s14, slack, s15, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, hmargin, hrefresh, hboot, hrelaunch, hstartup, hcheck, hslack, Wr.get_nat(s15), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.check(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +margin: Nat, +refresh: Nat, +boot: Nat, +relaunch: Nat, +startup: Nat, +s13: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, s13))))))))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, hmargin: {LawsBase.wire_fits(margin) == True{} : Bool}, hrefresh: {LawsBase.wire_fits(refresh) == True{} : Bool}, hboot: {LawsBase.wire_fits(boot) == True{} : Bool}, hrelaunch: {LawsBase.wire_fits(relaunch) == True{} : Bool}, hstartup: {LawsBase.wire_fits(startup) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s13) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.check(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, d)):
  match d:
    case Wr.Got{+check, +s14}:
      +ee = ed
      +hcheck = Wire.wire_nat_decoded_fits(s13, check, s14, ee)
      tmu.slack(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, s14, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, Wr.put_nat(startup, z))))))))))))), s, s13, Wr.put_nat(check, s14), pre, Wire.wire_nat_exact(s13, check, s14, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, hmargin, hrefresh, hboot, hrelaunch, hstartup, hcheck, Wr.get_nat(s14), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.startup(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +margin: Nat, +refresh: Nat, +boot: Nat, +relaunch: Nat, +s12: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, s12)))))))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, hmargin: {LawsBase.wire_fits(margin) == True{} : Bool}, hrefresh: {LawsBase.wire_fits(refresh) == True{} : Bool}, hboot: {LawsBase.wire_fits(boot) == True{} : Bool}, hrelaunch: {LawsBase.wire_fits(relaunch) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s12) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.startup(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, d)):
  match d:
    case Wr.Got{+startup, +s13}:
      +ee = ed
      +hstartup = Wire.wire_nat_decoded_fits(s12, startup, s13, ee)
      tmu.check(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, s13, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, Wr.put_nat(relaunch, z)))))))))))), s, s12, Wr.put_nat(startup, s13), pre, Wire.wire_nat_exact(s12, startup, s13, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, hmargin, hrefresh, hboot, hrelaunch, hstartup, Wr.get_nat(s13), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.relaunch(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +margin: Nat, +refresh: Nat, +boot: Nat, +s11: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, s11))))))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, hmargin: {LawsBase.wire_fits(margin) == True{} : Bool}, hrefresh: {LawsBase.wire_fits(refresh) == True{} : Bool}, hboot: {LawsBase.wire_fits(boot) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s11) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.relaunch(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, d)):
  match d:
    case Wr.Got{+relaunch, +s12}:
      +ee = ed
      +hrelaunch = Wire.wire_nat_decoded_fits(s11, relaunch, s12, ee)
      tmu.startup(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, s12, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, Wr.put_nat(boot, z))))))))))), s, s11, Wr.put_nat(relaunch, s12), pre, Wire.wire_nat_exact(s11, relaunch, s12, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, hmargin, hrefresh, hboot, hrelaunch, Wr.get_nat(s12), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.boot(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +margin: Nat, +refresh: Nat, +s10: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, s10)))))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, hmargin: {LawsBase.wire_fits(margin) == True{} : Bool}, hrefresh: {LawsBase.wire_fits(refresh) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s10) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.boot(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, d)):
  match d:
    case Wr.Got{+boot, +s11}:
      +ee = ed
      +hboot = Wire.wire_nat_decoded_fits(s10, boot, s11, ee)
      tmu.relaunch(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, s11, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, Wr.put_nat(refresh, z)))))))))), s, s10, Wr.put_nat(boot, s11), pre, Wire.wire_nat_exact(s10, boot, s11, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, hmargin, hrefresh, hboot, Wr.get_nat(s11), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.refresh(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +margin: Nat, +s9: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, s9))))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, hmargin: {LawsBase.wire_fits(margin) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s9) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.refresh(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, d)):
  match d:
    case Wr.Got{+refresh, +s10}:
      +ee = ed
      +hrefresh = Wire.wire_nat_decoded_fits(s9, refresh, s10, ee)
      tmu.boot(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, s10, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, Wr.put_nat(margin, z))))))))), s, s9, Wr.put_nat(refresh, s10), pre, Wire.wire_nat_exact(s9, refresh, s10, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, hmargin, hrefresh, Wr.get_nat(s10), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.margin(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +wverify: Nat, +s8: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, s8)))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, hwverify: {LawsBase.wire_fits(wverify) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s8) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.margin(snap, host, kstep, kterm, kverify, harness, wterm, wverify, d)):
  match d:
    case Wr.Got{+margin, +s9}:
      +ee = ed
      +hmargin = Wire.wire_nat_decoded_fits(s8, margin, s9, ee)
      tmu.refresh(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, s9, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, Wr.put_nat(wverify, z)))))))), s, s8, Wr.put_nat(margin, s9), pre, Wire.wire_nat_exact(s8, margin, s9, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, hmargin, Wr.get_nat(s9), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.wverify(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +wterm: Nat, +s7: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, s7))))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, hwterm: {LawsBase.wire_fits(wterm) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s7) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.wverify(snap, host, kstep, kterm, kverify, harness, wterm, d)):
  match d:
    case Wr.Got{+wverify, +s8}:
      +ee = ed
      +hwverify = Wire.wire_nat_decoded_fits(s7, wverify, s8, ee)
      tmu.margin(s, snap, host, kstep, kterm, kverify, harness, wterm, wverify, s8, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, Wr.put_nat(wterm, z))))))), s, s7, Wr.put_nat(wverify, s8), pre, Wire.wire_nat_exact(s7, wverify, s8, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, hwverify, Wr.get_nat(s8), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.wterm(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +harness: Nat, +s6: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, s6)))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, hharness: {LawsBase.wire_fits(harness) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s6) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.wterm(snap, host, kstep, kterm, kverify, harness, d)):
  match d:
    case Wr.Got{+wterm, +s7}:
      +ee = ed
      +hwterm = Wire.wire_nat_decoded_fits(s6, wterm, s7, ee)
      tmu.wverify(s, snap, host, kstep, kterm, kverify, harness, wterm, s7, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, Wr.put_nat(harness, z)))))), s, s6, Wr.put_nat(wterm, s7), pre, Wire.wire_nat_exact(s6, wterm, s7, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, hwterm, Wr.get_nat(s7), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.harness(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +kverify: Nat, +s5: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, s5))))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, hkverify: {LawsBase.wire_fits(kverify) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s5) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.harness(snap, host, kstep, kterm, kverify, d)):
  match d:
    case Wr.Got{+harness, +s6}:
      +ee = ed
      +hharness = Wire.wire_nat_decoded_fits(s5, harness, s6, ee)
      tmu.wterm(s, snap, host, kstep, kterm, kverify, harness, s6, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, Wr.put_nat(kverify, z))))), s, s5, Wr.put_nat(harness, s6), pre, Wire.wire_nat_exact(s5, harness, s6, ee)), hsnap, hhost, hkstep, hkterm, hkverify, hharness, Wr.get_nat(s6), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.kverify(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +kterm: Nat, +s4: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, s4)))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, hkterm: {LawsBase.wire_fits(kterm) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s4) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.kverify(snap, host, kstep, kterm, d)):
  match d:
    case Wr.Got{+kverify, +s5}:
      +ee = ed
      +hkverify = Wire.wire_nat_decoded_fits(s4, kverify, s5, ee)
      tmu.harness(s, snap, host, kstep, kterm, kverify, s5, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, Wr.put_nat(kterm, z)))), s, s4, Wr.put_nat(kverify, s5), pre, Wire.wire_nat_exact(s4, kverify, s5, ee)), hsnap, hhost, hkstep, hkterm, hkverify, Wr.get_nat(s5), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.kterm(+s: String, +snap: Nat, +host: Nat, +kstep: Nat, +s3: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, s3))) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, hkstep: {LawsBase.wire_fits(kstep) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.kterm(snap, host, kstep, d)):
  match d:
    case Wr.Got{+kterm, +s4}:
      +ee = ed
      +hkterm = Wire.wire_nat_decoded_fits(s3, kterm, s4, ee)
      tmu.kverify(s, snap, host, kstep, kterm, s4, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, Wr.put_nat(kstep, z))), s, s3, Wr.put_nat(kterm, s4), pre, Wire.wire_nat_exact(s3, kterm, s4, ee)), hsnap, hhost, hkstep, hkterm, Wr.get_nat(s4), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.kstep(+s: String, +snap: Nat, +host: Nat, +s2: String, pre: {s == Wr.put_nat(snap, Wr.put_nat(host, s2)) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, hhost: {LawsBase.wire_fits(host) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.kstep(snap, host, d)):
  match d:
    case Wr.Got{+kstep, +s3}:
      +ee = ed
      +hkstep = Wire.wire_nat_decoded_fits(s2, kstep, s3, ee)
      tmu.kterm(s, snap, host, kstep, s3, tmu.step(z => Wr.put_nat(snap, Wr.put_nat(host, z)), s, s2, Wr.put_nat(kstep, s3), pre, Wire.wire_nat_exact(s2, kstep, s3, ee)), hsnap, hhost, hkstep, Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.host(+s: String, +snap: Nat, +s1: String, pre: {s == Wr.put_nat(snap, s1) : String}, hsnap: {LawsBase.wire_fits(snap) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.host(snap, d)):
  match d:
    case Wr.Got{+host, +s2}:
      +ee = ed
      +hhost = Wire.wire_nat_decoded_fits(s1, host, s2, ee)
      tmu.kstep(s, snap, host, s2, tmu.step(z => Wr.put_nat(snap, z), s, s1, Wr.put_nat(host, s2), pre, Wire.wire_nat_exact(s1, host, s2, ee)), hsnap, hhost, Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.snap(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tmu.Rd(s, FT.get_tm.snap(d)):
  match d:
    case Wr.Got{+snap, +s1}:
      +ee = ed
      +hsnap = Wire.wire_nat_decoded_fits(s, snap, s1, ee)
      tmu.host(s, snap, s1, Wire.wire_nat_exact(s, snap, s1, ee), hsnap, Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def tmu.goal(+s: String) -> Type:
  &t: Su.Tm -> {(s, Timeouts.tw_fits(t)) == (Timeouts.tw_spell(t), True{}) : String & Bool}

def tmu.eq(+s: String, +t: Su.Tm, e1: {s == Timeouts.tw_spell(t) : String}, e2: {Timeouts.tw_fits(t) == True{} : Bool}) -> {(s, Timeouts.tw_fits(t)) == (Timeouts.tw_spell(t), True{}) : String & Bool}:
  %Equal.sym(String, s, Timeouts.tw_spell(t), e1) : {(_, Timeouts.tw_fits(t)) == (Timeouts.tw_spell(t), True{}) : String & Bool}
  %Equal.sym(Bool, Timeouts.tw_fits(t), True{}, e2) : {(Timeouts.tw_spell(t), _) == (Timeouts.tw_spell(t), True{}) : String & Bool}
  {==}

# nothing after the base values: the input is their spelling; anything
# after them answers the malformed error, which the premise excludes
def tmu.fin(+s: String, +t: Su.Tm, r: String, pre: {s == tmu.spell_then(t, r) : String}, f: {Timeouts.tw_fits(t) == True{} : Bool}, other: {String.eq(FT.ffi.fin(Wr.end(r), t), Wr.err("timeouts: malformed request")) == False{} : Bool}) -> tmu.goal(s):
  match r:
    case SNil{}:
      (t, tmu.eq(s, t, Equal.trans(String, s, tmu.spell_then(t, ""), Timeouts.tw_spell(t), pre, tmu.spell_nil(t)), f))
    case SCon{c, rr}:
      LAWireSpell.ws_absurd(tmu.goal(s), other)

def tmu.main(+s: String, d: Wr.Dec<Su.Tm>, inv: tmu.Rd(s, d), other: {String.eq(FT.ffi.go(d), Wr.err("timeouts: malformed request")) == False{} : Bool}) -> tmu.goal(s):
  match d:
    case Wr.Got{+t, r}:
      (e, f) = inv
      tmu.fin(s, t, r, e, f, other)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(tmu.goal(s), other)

def Timeouts.timeouts_ffi_malformed_unless_request(s, other):
  tmu.main(s, FT.get_tm(s), tmu.snap(s, Wr.get_nat(s), {==}), other)
