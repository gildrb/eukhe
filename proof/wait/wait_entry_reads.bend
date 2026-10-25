# eukhe: the proof of LAW wait_entry_reads
import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

# The entry reads every input as the laws reader does (LA.ww.read); a
# whole poll runs as the same poll spelled (LA.ws.spelled).

def wr.got(+w: Wt.W, d: Wr.Dec<Wt.Polled>, +r: Wt.Polled, got: {WaitLaws.ww_read.whole(d) == Some{r} : Maybe<&2, Wt.Polled>}) -> {FWt.step.poll(w, d) == FWt.step(FWt.Live{w}, WaitLaws.ww_spell(r)) : FWt.St & String}:
  match d:
    case Wr.Got{+x, rest}:
      match rest:
        case SNil{}:
          %LA.ww.some_inj(Wt.Polled, x, r, got) : {FWt.step.end(True{}, w, x) == FWt.step(FWt.Live{w}, WaitLaws.ww_spell(_)) : FWt.St & String}
          LA.ws.spelled(w, x)
        case SCon{c, t}:
          LA.ww.none_some(Wt.Polled, {(FWt.Live{w}, FWt.fail()) == FWt.step(FWt.Live{w}, WaitLaws.ww_spell(r)) : FWt.St & String}, r, got)
    case Wr.Bad{}:
      LA.ww.none_some(Wt.Polled, {(FWt.Live{w}, FWt.fail()) == FWt.step(FWt.Live{w}, WaitLaws.ww_spell(r)) : FWt.St & String}, r, got)

def WaitLaws.wait_entry_reads(w, i, r, got):
  %LA.ww.read(Wr.get_bool(i)) : {FWt.step.poll(w, _) == FWt.step(FWt.Live{w}, WaitLaws.ww_spell(r)) : FWt.St & String}
  wr.got(w, WaitLaws.ww_read.go(Wr.get_bool(i)), r, got)
