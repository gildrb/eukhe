# eukhe: the proof of LAW optchat_step_is_model
# Each spelled request answers and moves as the model does
# (LAF.oe.answers), by induction on the requests (sm.run).

import Base
import ../../bend/ffi_optchat.bend as FOc
import ../../bend/optchat/state.bend as OState
import ../../laws/optchat.bend as Optchat
import ./base/ffi_optchat.bend as LAF

def sm.run(qs: List<&2, FOc.Q>, +cfg: OState.Cfg, +s: OState.St, +fits: {Optchat.oc_all_fit(qs) == True{} : Bool}) -> {Optchat.oc_replies(qs, FOc.Live{cfg, s}) == Optchat.oc_spec(qs, cfg, s) : List<&2, String>}:
  match qs:
    case Nil{}:
      {==}
    case +q <> +rest:
      +fq = LAF.oe.and_l(Optchat.oc_fits(q), Optchat.oc_all_fit(rest), fits)
      +next = Optchat.oc_next(cfg, s, q)
      %Equal.sym(FOc.St & String, FOc.step(FOc.Live{cfg, s}, Optchat.oc_spell(q)), (FOc.Live{cfg, next}, Optchat.oc_reply(cfg, s, q)), LAF.oe.answers(cfg, s, q, fq)) : {Optchat.oc_reply_of(_) <> Optchat.oc_replies(rest, Optchat.oc_state(_)) == Optchat.oc_spec(q <> rest, cfg, s) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, x => Optchat.oc_reply(cfg, s, q) <> x, Optchat.oc_replies(rest, FOc.Live{cfg, next}), Optchat.oc_spec(rest, cfg, next), sm.run(rest, cfg, next, LAF.oe.and_r(Optchat.oc_fits(q), Optchat.oc_all_fit(rest), fits)))

def Optchat.optchat_step_is_model(cfg, s, qs, fits):
  sm.run(qs, cfg, s, fits)
