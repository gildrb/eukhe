# eukhe: the proof of LAW wait_entry_once
# Every reply is the model's run cut at its poll (LA.ws.model). A reply to
# p that is not `0,` brought an end: the run over the signals before p
# reported none, and the run up to p reported one. Every later run
# extends that one (LA.ws.run_app), so it has ended before any later
# poll, which is answered `0,`.

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

# the run up to p ended: so did the run up to any later poll
def wo.more(+dl: Maybe<&2, Nat>, +pre: List<&2, Wt.Polled>, +p: Wt.Polled, +mid: List<&2, Wt.Polled>, -e: Wt.End, -t: List<&2, Wt.End>, h: {Wt.run(dl, List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p))) == e <> t : List<&2, Wt.End>}) -> {e <> List.append(&2, Wt.End, t, Wt.go(WaitLaws.ww_flat(mid), WaitLaws.ww_after(List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p)), Wt.start(dl)))) == Wt.run(dl, WaitLaws.ww_flat(List.append(&2, Wt.Polled, pre, p <> mid))) : List<&2, Wt.End>}:
  %LA.ws.flat_app(pre, p <> mid) : {e <> List.append(&2, Wt.End, t, Wt.go(WaitLaws.ww_flat(mid), WaitLaws.ww_after(List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p)), Wt.start(dl)))) == Wt.run(dl, _) : List<&2, Wt.End>}
  %LA.ws.app_assoc(Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p), WaitLaws.ww_flat(mid)) : {e <> List.append(&2, Wt.End, t, Wt.go(WaitLaws.ww_flat(mid), WaitLaws.ww_after(List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p)), Wt.start(dl)))) == Wt.run(dl, _) : List<&2, Wt.End>}
  %LA.ws.run_app(dl, List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p)), WaitLaws.ww_flat(mid)) : {e <> List.append(&2, Wt.End, t, Wt.go(WaitLaws.ww_flat(mid), WaitLaws.ww_after(List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p)), Wt.start(dl)))) == _ : List<&2, Wt.End>}
  %Equal.sym(List<&2, Wt.End>, Wt.run(dl, List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p))), e <> t, h) : {e <> List.append(&2, Wt.End, t, Wt.go(WaitLaws.ww_flat(mid), WaitLaws.ww_after(List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p)), Wt.start(dl)))) == List.append(&2, Wt.End, _, Wt.go(WaitLaws.ww_flat(mid), WaitLaws.ww_after(List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p)), Wt.start(dl)))) : List<&2, Wt.End>}
  {==}

# a run that has ended brings nothing new
def wo.quiet(r: List<&2, Wt.End>, x: List<&2, Wt.End>, -e: Wt.End, -t: List<&2, Wt.End>, h: {e <> t == r : List<&2, Wt.End>}) -> {WaitLaws.ww_spell_ends(WaitLaws.ww_new.go(r, x)) == "0," : String}:
  %h : {WaitLaws.ww_spell_ends(WaitLaws.ww_new.go(_, x)) == "0," : String}
  {==}

def wo.pick(+dl: Maybe<&2, Nat>, +pre: List<&2, Wt.Polled>, +p: Wt.Polled, +mid: List<&2, Wt.Polled>, +q: Wt.Polled, r: List<&2, Wt.End>, x: List<&2, Wt.End>, hx: {Wt.run(dl, List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p))) == x : List<&2, Wt.End>}, ended: {String.eq(WaitLaws.ww_spell_ends(WaitLaws.ww_new.go(r, x)), "0,") == False{} : Bool}) -> {WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, List.append(&2, Wt.Polled, pre, p <> mid), q)) == "0," : String}:
  match r:
    case Nil{}:
      match x:
        case Nil{}:
          LA.pw.absurd({WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, List.append(&2, Wt.Polled, pre, p <> mid), q)) == "0," : String}, ended)
        case e <> t:
          wo.quiet(Wt.run(dl, WaitLaws.ww_flat(List.append(&2, Wt.Polled, pre, p <> mid))), Wt.run(dl, List.append(&2, Wt.Sig, WaitLaws.ww_flat(List.append(&2, Wt.Polled, pre, p <> mid)), WaitLaws.ww_sigs(q))), e, List.append(&2, Wt.End, t, Wt.go(WaitLaws.ww_flat(mid), WaitLaws.ww_after(List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p)), Wt.start(dl)))), wo.more(dl, pre, p, mid, e, t, hx))
    case e <> t:
      LA.pw.absurd({WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, List.append(&2, Wt.Polled, pre, p <> mid), q)) == "0," : String}, ended)

def wo.go(+dl: Maybe<&2, Nat>, +pre: List<&2, Wt.Polled>, +p: Wt.Polled, +mid: List<&2, Wt.Polled>, +q: Wt.Polled, +fits: {LawsBase.wire_mfits(dl) == True{} : Bool}, ended: {String.eq(WaitLaws.ww_reply(FWt.step(WaitLaws.ww_feed(pre, WaitLaws.ww_opened(dl)), WaitLaws.ww_spell(p))), "0,") == False{} : Bool}) -> {WaitLaws.ww_reply(FWt.step(WaitLaws.ww_feed(List.append(&2, Wt.Polled, pre, p <> mid), WaitLaws.ww_opened(dl)), WaitLaws.ww_spell(q))) == "0," : String}:
  %Equal.sym(String, WaitLaws.ww_reply(FWt.step(WaitLaws.ww_feed(List.append(&2, Wt.Polled, pre, p <> mid), WaitLaws.ww_opened(dl)), WaitLaws.ww_spell(q))), WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, List.append(&2, Wt.Polled, pre, p <> mid), q)), LA.ws.model(dl, List.append(&2, Wt.Polled, pre, p <> mid), q, fits)) : {_ == "0," : String}
  wo.pick(dl, pre, p, mid, q, Wt.run(dl, WaitLaws.ww_flat(pre)), Wt.run(dl, List.append(&2, Wt.Sig, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p))), {==}, Equal.trans(Bool, String.eq(WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, pre, p)), "0,"), String.eq(WaitLaws.ww_reply(FWt.step(WaitLaws.ww_feed(pre, WaitLaws.ww_opened(dl)), WaitLaws.ww_spell(p))), "0,"), False{}, Equal.cong(String, Bool, s => String.eq(s, "0,"), WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, pre, p)), WaitLaws.ww_reply(FWt.step(WaitLaws.ww_feed(pre, WaitLaws.ww_opened(dl)), WaitLaws.ww_spell(p))), Equal.sym(String, WaitLaws.ww_reply(FWt.step(WaitLaws.ww_feed(pre, WaitLaws.ww_opened(dl)), WaitLaws.ww_spell(p))), WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, pre, p)), LA.ws.model(dl, pre, p, fits))), ended))

def WaitLaws.wait_entry_once(dl, pre, p, mid, q, fits, ended):
  wo.go(dl, pre, p, mid, q, fits, ended)
