# eukhe: the proof of LAW cron_file_finish_spares_held
# By induction on the jobs, for every key the dispatch may name: a job
# that does not take the finish step is Untouched, and a held job that
# takes it is Untouched too (CS.finish matches the job's status first); an
# active job's answer is anything.
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../laws/cron_file/pass.bend as CronFile

def cfs.head(go: Bool, f: CS.Fact, -u: Nat, -r: Bool, -b: Bool, -n: Nat, -rest: Bool, ih: {rest == True{} : Bool}) -> {Bool.and(CronFile.kept_fin_spec(CronFile.live_spec(f), CF.finish.one(go, f, u, r, b, n)), rest) == True{} : Bool}:
  match go:
    case True{}:
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
    case False{}:
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

def cfs.js(js: List<&2, CF.Slot>, +k: Maybe<&2, Nat>, +u: Nat, +r: Bool, +b: Bool, +n: Nat) -> {CronFile.finish_spares_js_spec(js, CF.finish.js(js, k, u, r, b, n)) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case j <> +t:
      match j:
        case CF.Slot{+key, +f}:
          cfs.head(CF.names(key, k), f, u, r, b, n, CronFile.finish_spares_js_spec(t, CF.finish.js(t, CF.finish.rest(CF.names(key, k), k), u, r, b, n)), cfs.js(t, CF.finish.rest(CF.names(key, k), k), u, r, b, n))

def CronFile.cron_file_finish_spares_held(u, js, cs, r, b, n):
  cfs.js(js, CF.hit(cs), u, r, b, n)
