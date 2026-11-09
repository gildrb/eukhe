# eukhe: the proof of LAW cron_file_take_spares_held
# By induction on the jobs: a held job's claim pass computes to Keep
# (CS.take matches the job's status first); an active job's answer is
# anything (the spec asks nothing of it).
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../laws/cron_file/pass.bend as CronFile

def cts.head(f: CS.Fact, -c: Bool, -d: Nat, -n: Nat, -rest: Bool, ih: {rest == True{} : Bool}) -> {Bool.and(CronFile.kept_took_spec(CronFile.live_spec(f), CS.take(f, c, d, n)), rest) == True{} : Bool}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          ih
        case Cr.Paused{}:
          ih
        case Cr.Finished{}:
          ih
        case Cr.Cancelled{}:
          ih

def cts.take(js: List<&2, CF.Slot>, +cs: List<&2, Maybe<&2, Nat>>, +d: Nat, +n: Nat) -> {CronFile.take_spares_spec(js, CF.take(js, cs, d, n)) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case j <> +t:
      match j:
        case CF.Slot{+key, +f}:
          cts.head(f, CF.claimed(key, cs), d, n, CronFile.take_spares_spec(t, CF.take(t, cs, d, n)), cts.take(t, cs, d, n))

def CronFile.cron_file_take_spares_held(js, cs, d, n):
  cts.take(js, cs, d, n)
