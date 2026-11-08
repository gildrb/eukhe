# eukhe: the proof of LAW adw_step_reads_only_ops
#
# PROOF: whatever the decoder reads is a spelled op that fits, then its
# rest (asx.op); an answer that is no error comes from an op read whole,
# nothing left, and is the model's next controller, spelled (asp.live).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell

def aro.G(x: Ad.Live, s: String, a: FAd.St & String) -> Type:
  &o: Ad.Op -> {(s, (Admission.adw_op_fits(o), a)) == (Admission.adw_spell_op(o, ""), (True{}, (FAd.Running{Ad.Live.step(x, o)}, Admission.adw_spell_live(Ad.Live.step(x, o), "")))) : String & (Bool & (FAd.St & String))}

def aro.top(+x: Ad.Live, +s: String, +o: Ad.Op, -a: FAd.St & String, e: {s == Admission.adw_spell_op(o, "") : String}, f: {Admission.adw_op_fits(o) == True{} : Bool}, ea: {a == (FAd.Running{Ad.Live.step(x, o)}, Admission.adw_spell_live(Ad.Live.step(x, o), "")) : FAd.St & String}) -> {(s, (Admission.adw_op_fits(o), a)) == (Admission.adw_spell_op(o, ""), (True{}, (FAd.Running{Ad.Live.step(x, o)}, Admission.adw_spell_live(Ad.Live.step(x, o), "")))) : String & (Bool & (FAd.St & String))}:
  %Equal.sym(String, s, Admission.adw_spell_op(o, ""), e) : {(_, (Admission.adw_op_fits(o), a)) == (Admission.adw_spell_op(o, ""), (True{}, (FAd.Running{Ad.Live.step(x, o)}, Admission.adw_spell_live(Ad.Live.step(x, o), "")))) : String & (Bool & (FAd.St & String))}
  %Equal.sym(Bool, Admission.adw_op_fits(o), True{}, f) : {(Admission.adw_spell_op(o, ""), (_, a)) == (Admission.adw_spell_op(o, ""), (True{}, (FAd.Running{Ad.Live.step(x, o)}, Admission.adw_spell_live(Ad.Live.step(x, o), "")))) : String & (Bool & (FAd.St & String))}
  %Equal.sym(FAd.St & String, a, (FAd.Running{Ad.Live.step(x, o)}, Admission.adw_spell_live(Ad.Live.step(x, o), "")), ea) : {(Admission.adw_spell_op(o, ""), (True{}, _)) == (Admission.adw_spell_op(o, ""), (True{}, (FAd.Running{Ad.Live.step(x, o)}, Admission.adw_spell_live(Ad.Live.step(x, o), "")))) : String & (Bool & (FAd.St & String))}
  {==}

# a whole op answers the model's next controller, spelled
def aro.ans(+x: Ad.Live, +o: Ad.Op) -> {FAd.step.end(True{}, x, o) == (FAd.Running{Ad.Live.step(x, o)}, Admission.adw_spell_live(Ad.Live.step(x, o), "")) : FAd.St & String}:
  %LASpell.asp.live(Ad.Live.step(x, o), "") : {FAd.step.end(True{}, x, o) == (FAd.Running{Ad.Live.step(x, o)}, _) : FAd.St & String}
  {==}

def aro.fin(+x: Ad.Live, +s: String, +o: Ad.Op, r: String, pre: {s == Admission.adw_spell_op(o, r) : String}, f: {Admission.adw_op_fits(o) == True{} : Bool}, ok: {LawsBase.wire_opens_err(Admission.adw_reply(FAd.step.end(Wr.end(r), x, o))) == False{} : Bool}) -> aro.G(x, s, FAd.step.end(Wr.end(r), x, o)):
  match r:
    case SNil{}:
      (o, aro.top(x, s, o, FAd.step.end(True{}, x, o), pre, f, aro.ans(x, o)))
    case SCon{c, t}:
      LAWireSpell.ws_absurd(aro.G(x, s, FAd.step.end(False{}, x, o)), ok)

def aro.main(+x: Ad.Live, +s: String, d: Wr.Dec<Ad.Op>, inv: LASpell.asx.Op(s, d), ok: {LawsBase.wire_opens_err(Admission.adw_reply(FAd.step.op(x, d))) == False{} : Bool}) -> aro.G(x, s, FAd.step.op(x, d)):
  match d:
    case Wr.Got{+o, +r}:
      (e, f) = inv
      aro.fin(x, s, o, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(aro.G(x, s, (FAd.Running{x}, Wr.err("admission: malformed op"))), ok)

def Admission.adw_step_reads_only_ops(x, s, ok):
  aro.main(x, s, FAd.get_op(s), LASpell.asx.op(s), ok)
