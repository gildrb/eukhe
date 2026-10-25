# eukhe: the proof of LAW wait_entry_open
import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

# The open of a spelled deadline is read whole (LA.ws.open_spelled); its
# reply is the model run before any signal.

def wo.first(dl: Maybe<&2, Nat>) -> {FWt.put_ends(Wt.first(dl)) == WaitLaws.ww_spell_ends(Wt.run(dl, Nil{})) : String}:
  match dl:
    case None{}:
      {==}
    case Some{d}:
      match d:
        case 0n:
          {==}
        case 1n+m:
          {==}

def WaitLaws.wait_entry_open(dl, fits):
  %LA.ws.open_spelled(dl, fits) : {WaitLaws.ww_reply(_) == WaitLaws.ww_spell_ends(Wt.run(dl, Nil{})) : String}
  wo.first(dl)
