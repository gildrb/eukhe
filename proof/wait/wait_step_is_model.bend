# eukhe: the proof of LAW wait_step_is_model
import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

def WaitLaws.wait_step_is_model(dl, pre, p, fits):
  LA.ws.model(dl, pre, p, fits)
