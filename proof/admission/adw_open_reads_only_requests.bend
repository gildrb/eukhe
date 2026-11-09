# eukhe: the proof of LAW adw_open_reads_only_requests
#
# PROOF: whatever the decoder reads is a spelled open that fits, then its
# rest (asx.open); an answer that is no error comes from an open read
# whole, nothing left, and is its controller, spelled (asp.live).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell
import ../../laws/admission/wire.bend as AdmissionWire

def aoo.G(s: String, a: FAd.St & String) -> Type:
  &l: Ad.Lim -> &q: Nat -> {(s, (Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q)), a)) == (AdmissionWire.adw_spell_open(l, q, ""), (True{}, (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, AdmissionWire.adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")))) : String & (Bool & (FAd.St & String))}

def aoo.top(+s: String, +l: Ad.Lim, +q: Nat, -a: FAd.St & String, e: {s == AdmissionWire.adw_spell_open(l, q, "") : String}, f: {Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}, ea: {a == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, AdmissionWire.adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")) : FAd.St & String}) -> {(s, (Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q)), a)) == (AdmissionWire.adw_spell_open(l, q, ""), (True{}, (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, AdmissionWire.adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")))) : String & (Bool & (FAd.St & String))}:
  %Equal.sym(String, s, AdmissionWire.adw_spell_open(l, q, ""), e) : {(_, (Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q)), a)) == (AdmissionWire.adw_spell_open(l, q, ""), (True{}, (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, AdmissionWire.adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")))) : String & (Bool & (FAd.St & String))}
  %Equal.sym(Bool, Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q)), True{}, f) : {(AdmissionWire.adw_spell_open(l, q, ""), (_, a)) == (AdmissionWire.adw_spell_open(l, q, ""), (True{}, (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, AdmissionWire.adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")))) : String & (Bool & (FAd.St & String))}
  %Equal.sym(FAd.St & String, a, (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, AdmissionWire.adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")), ea) : {(AdmissionWire.adw_spell_open(l, q, ""), (True{}, _)) == (AdmissionWire.adw_spell_open(l, q, ""), (True{}, (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, AdmissionWire.adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")))) : String & (Bool & (FAd.St & String))}
  {==}

# a whole open answers its controller, spelled
def aoo.ans(+l: Ad.Lim, +q: Nat) -> {FAd.open.end(True{}, l, q) == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, AdmissionWire.adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")) : FAd.St & String}:
  %LASpell.asp.live(Ad.Live{l, q, Nil{}, 0n}, "") : {FAd.open.end(True{}, l, q) == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, _) : FAd.St & String}
  {==}

def aoo.fin(+s: String, +l: Ad.Lim, +q: Nat, r: String, pre: {s == AdmissionWire.adw_spell_open(l, q, r) : String}, f: {Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}, ok: {LawsBase.wire_opens_err(AdmissionWire.adw_reply(FAd.open.end(Wr.end(r), l, q))) == False{} : Bool}) -> aoo.G(s, FAd.open.end(Wr.end(r), l, q)):
  match r:
    case SNil{}:
      (l, (q, aoo.top(s, l, q, FAd.open.end(True{}, l, q), pre, f, aoo.ans(l, q))))
    case SCon{c, t}:
      LAWireSpell.ws_absurd(aoo.G(s, FAd.open.end(False{}, l, q)), ok)

def aoo.at(+s: String, lq: +Sigma<Ad.Lim, x => Nat>, +r: String, inv: LASpell.asx.Open.at(s, lq, r), ok: {LawsBase.wire_opens_err(AdmissionWire.adw_reply(FAd.open.req(lq, Wr.end(r)))) == False{} : Bool}) -> aoo.G(s, FAd.open.req(lq, Wr.end(r))):
  match lq:
    case (+l, +q):
      (e, f) = inv
      aoo.fin(s, l, q, r, e, f, ok)

def aoo.main(+s: String, d: Wr.Dec<+Sigma<Ad.Lim, x => Nat>>, inv: LASpell.asx.Open(s, d), ok: {LawsBase.wire_opens_err(AdmissionWire.adw_reply(FAd.open.go(d))) == False{} : Bool}) -> aoo.G(s, FAd.open.go(d)):
  match d:
    case Wr.Got{lq, +r}:
      aoo.at(s, lq, r, inv, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(aoo.G(s, (FAd.Shut{}, Wr.err("admission: malformed open"))), ok)

def AdmissionWire.adw_open_reads_only_requests(s, ok):
  aoo.main(s, FAd.get_open(s), LASpell.asx.open(s), ok)
