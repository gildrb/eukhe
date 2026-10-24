# eukhe: the proof of LAW wait_entry_reads
# The entry's decoder answers what the laws' reader answers (LA.ww.read);
# a whole poll gets the laws' end (LA.ww.ans).

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

def wr.got(d: Wr.Dec<Wt.Polled>, +r: Wt.Polled, got: {WaitLaws.ww_read.whole(d) == Some{r} : Maybe<&2, Wt.Polled>}) -> {FWt.run(d) == WaitLaws.ww_spell_end(WaitLaws.ww_end(r)) : String}:
  match d:
    case Wr.Got{+x, rest}:
      match rest:
        case SNil{}:
          %LA.ww.some_inj(x, r, got) : {FWt.run.end(True{}, x) == WaitLaws.ww_spell_end(WaitLaws.ww_end(_)) : String}
          LA.ww.ans(x)
        case SCon{c, t}:
          LA.ww.none_some({FWt.fail() == WaitLaws.ww_spell_end(WaitLaws.ww_end(r)) : String}, r, got)
    case Wr.Bad{}:
      LA.ww.none_some({FWt.fail() == WaitLaws.ww_spell_end(WaitLaws.ww_end(r)) : String}, r, got)

def WaitLaws.wait_entry_reads(i, r, got):
  %LA.ww.read(Wr.get_bool(i)) : {FWt.run(_) == WaitLaws.ww_spell_end(WaitLaws.ww_end(r)) : String}
  wr.got(WaitLaws.ww_read.go(Wr.get_bool(i)), r, got)
