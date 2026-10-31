# eukhe: the proof of LAW cron_file_take_exact
# By induction on the jobs: each job's claim pass is CronStore.take_spec
# (cron_take_exact), with the same claimed flag (a key named by a claim
# record, Nat.is_eq turned around).
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ../../laws/cron_file/view.bend as CronFileView
import ./base/logic.bend as LCfl
import ../cron_store/cron_take_exact.bend as PTake

def cfx.names(+k: Nat, m: Maybe<&2, Nat>) -> {CF.names(k, m) == CronFile.names_spec(k, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      LCfl.cfl.eq_comm(x, k)

def cfx.claimed(+k: Nat, cs: List<&2, Maybe<&2, Nat>>) -> {CF.claimed(k, cs) == CronFile.claimed_spec(k, cs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +m <> +t:
      %cfx.claimed(k, t) : {Bool.or(CF.names(k, m), CF.claimed(k, t)) == Bool.or(CronFile.names_spec(k, m), _) : Bool}
      %cfx.names(k, m) : {Bool.or(CF.names(k, m), CF.claimed(k, t)) == Bool.or(_, CF.claimed(k, t)) : Bool}
      {==}

def cfx.take(js: List<&2, CF.Slot>, +cs: List<&2, Maybe<&2, Nat>>, +d: Nat, +n: Nat) -> {CF.take(js, cs, d, n) == CronFile.take_all_spec(js, cs, d, n) : List<&2, CS.Took>}:
  match js:
    case Nil{}:
      {==}
    case j <> +t:
      match j:
        case CF.Slot{+key, +f}:
          %cfx.take(t, cs, d, n) : {CS.take(f, CF.claimed(key, cs), d, n) <> CF.take(t, cs, d, n) == CronStore.take_spec(f, CronFile.claimed_spec(key, cs), d, n) <> _ : List<&2, CS.Took>}
          %cfx.claimed(key, cs) : {CS.take(f, CF.claimed(key, cs), d, n) <> CF.take(t, cs, d, n) == CronStore.take_spec(f, _, d, n) <> CF.take(t, cs, d, n) : List<&2, CS.Took>}
          %CronStore.cron_take_exact(f, CF.claimed(key, cs), d, n) : {CS.take(f, CF.claimed(key, cs), d, n) <> CF.take(t, cs, d, n) == _ <> CF.take(t, cs, d, n) : List<&2, CS.Took>}
          {==}

def CronFile.cron_file_take_exact(js, cs, d, n):
  cfx.take(js, cs, d, n)
