# eukhe: the proof of LAW optchat_step_is_model
# A spelled open opens the laws' open (LAO.oo.opened), which is live with
# the open's sizes (LAO.oo.live); from there each spelled request answers
# and moves as the model does (LAF.oe.answers), by induction on the
# requests (sm.run).

import Base
import ../../bend/ffi_optchat.bend as FOc
import ../../bend/optchat/state.bend as OState
import ../../laws/optchat.bend as Optchat
import ./base/ffi_optchat.bend as LAF
import ./base/open.bend as LAO

def sm.run(qs: List<&2, FOc.Q>, +cfg: OState.Cfg, +s: OState.St, +fits: {Optchat.oc_all_fit(qs) == True{} : Bool}) -> {Optchat.oc_replies(qs, FOc.Live{cfg, s}) == Optchat.oc_spec(qs, cfg, s) : List<&2, String>}:
  match qs:
    case Nil{}:
      {==}
    case +q <> +rest:
      +fq = LAF.oe.and_l(Optchat.oc_fits(q), Optchat.oc_all_fit(rest), fits)
      +next = Optchat.oc_next(cfg, s, q)
      %Equal.sym(FOc.St & String, FOc.step(FOc.Live{cfg, s}, Optchat.oc_spell(q)), (FOc.Live{cfg, next}, Optchat.oc_reply(cfg, s, q)), LAF.oe.answers(cfg, s, q, fq)) : {Optchat.oc_reply_of(_) <> Optchat.oc_replies(rest, Optchat.oc_state(_)) == Optchat.oc_spec(q <> rest, cfg, s) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, x => Optchat.oc_reply(cfg, s, q) <> x, Optchat.oc_replies(rest, FOc.Live{cfg, next}), Optchat.oc_spec(rest, cfg, next), sm.run(rest, cfg, next, LAF.oe.and_r(Optchat.oc_fits(q), Optchat.oc_all_fit(rest), fits)))

def sm.main(+o: FOc.Open, +qs: List<&2, FOc.Q>, +fits: {Bool.and(Optchat.oc_open_fits(o), Optchat.oc_all_fit(qs)) == True{} : Bool}) -> {Optchat.oc_replies(qs, Optchat.oc_state(FOc.open(Optchat.oc_spell_open(o)))) == Optchat.oc_spec(qs, Optchat.oc_cfg(o), Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_model(o)))) : List<&2, String>}:
  +fo = LAF.oe.and_l(Optchat.oc_open_fits(o), Optchat.oc_all_fit(qs), fits)
  %Equal.sym(FOc.St & String, FOc.open(Optchat.oc_spell_open(o)), Optchat.oc_open_model(o), LAO.oo.opened(o, fo)) : {Optchat.oc_replies(qs, Optchat.oc_state(_)) == Optchat.oc_spec(qs, Optchat.oc_cfg(o), Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_model(o)))) : List<&2, String>}
  %LAO.oo.live(o) : {Optchat.oc_replies(qs, _) == Optchat.oc_spec(qs, Optchat.oc_cfg(o), Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_model(o)))) : List<&2, String>}
  sm.run(qs, Optchat.oc_cfg(o), Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_model(o))), LAF.oe.and_r(Optchat.oc_open_fits(o), Optchat.oc_all_fit(qs), fits))

def Optchat.optchat_step_is_model(o, qs, fits):
  sm.main(o, qs, fits)
