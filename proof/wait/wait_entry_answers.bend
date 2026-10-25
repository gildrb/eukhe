# eukhe: the proof of LAW wait_entry_answers
import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

def WaitLaws.wait_entry_answers(w, r):
  Equal.sym(FWt.St & String, (FWt.Live{WaitLaws.ww_after(WaitLaws.ww_sigs(r), w)}, WaitLaws.ww_spell_ends(Wt.go(WaitLaws.ww_sigs(r), w))), FWt.step(FWt.Live{w}, WaitLaws.ww_spell(r)), LA.ws.step(w, r))
