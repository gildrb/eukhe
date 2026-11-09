# eukhe: the proof of LAW cron_file_recover_spares_held
# By induction on the jobs: a held job's recovery computes to Kept whether
# or not a claim record of it was cleared (CS.recover keeps it uncleared,
# and CS.recover.go keeps every status but Active); an active job's answer
# is anything.
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../laws/cron_file/pass.bend as CronFile

def crs.head(f: CS.Fact, c: Bool, -rest: Bool, ih: {rest == True{} : Bool}) -> {Bool.and(CronFile.kept_back_spec(CronFile.live_spec(f), CS.recover(f, c)), rest) == True{} : Bool}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          ih
        case Cr.Paused{}:
          match c:
            case True{}:
              ih
            case False{}:
              ih
        case Cr.Finished{}:
          match c:
            case True{}:
              ih
            case False{}:
              ih
        case Cr.Cancelled{}:
          match c:
            case True{}:
              ih
            case False{}:
              ih

def crs.js(js: List<&2, CF.Slot>, +cs: List<&2, CF.Hold>) -> {CronFile.recover_spares_js_spec(js, CF.recover.js(js, cs)) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case j <> +t:
      match j:
        case CF.Slot{+key, +f}:
          crs.head(f, CF.cleared(key, cs), CronFile.recover_spares_js_spec(t, CF.recover.js(t, cs)), crs.js(t, cs))

def CronFile.cron_file_recover_spares_held(js, cs):
  crs.js(js, cs)
