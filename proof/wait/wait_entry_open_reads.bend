# eukhe: the proof of LAW wait_entry_open_reads
import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

# The entry reads every open as the laws reader does (LA.ww.read_dl); a
# whole deadline opens as the same deadline spelled (LA.ws.open_spelled).

import ../../laws/base.bend as LawsBase

def wor.got(d: Wr.Dec<Maybe<&2, Nat>>, +dl: Maybe<&2, Nat>, got: {WaitLaws.ww_read_dl.whole(d) == Some{dl} : Maybe<&2, Maybe<&2, Nat>>}, fits: {LawsBase.wire_mfits(dl) == True{} : Bool}) -> {FWt.open.dl(d) == FWt.open(WaitLaws.ww_spell_dl(dl)) : FWt.St & String}:
  match d:
    case Wr.Got{+x, rest}:
      match rest:
        case SNil{}:
          %Equal.sym(Maybe<&2, Nat>, x, dl, LA.ww.some_inj(Maybe<&2, Nat>, x, dl, got)) : {FWt.open.end(True{}, _) == FWt.open(WaitLaws.ww_spell_dl(dl)) : FWt.St & String}
          LA.ws.open_spelled(dl, fits)
        case SCon{c, t}:
          LA.ww.none_some(Maybe<&2, Nat>, {(FWt.Shut{}, SCon{'E', SCon{' ', "wait: malformed open"}}) == FWt.open(WaitLaws.ww_spell_dl(dl)) : FWt.St & String}, dl, got)
    case Wr.Bad{}:
      LA.ww.none_some(Maybe<&2, Nat>, {(FWt.Shut{}, SCon{'E', SCon{' ', "wait: malformed open"}}) == FWt.open(WaitLaws.ww_spell_dl(dl)) : FWt.St & String}, dl, got)

def WaitLaws.wait_entry_open_reads(i, dl, got, fits):
  %LA.ww.read_dl(Wr.get_nat(i)) : {FWt.open.dl(_) == FWt.open(WaitLaws.ww_spell_dl(dl)) : FWt.St & String}
  wor.got(WaitLaws.ww_read_dl.go(Wr.get_nat(i)), dl, got, fits)
