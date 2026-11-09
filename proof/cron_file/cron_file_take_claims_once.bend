# eukhe: the proof of LAW cron_file_take_claims_once
# By induction on the jobs: the spec's claimed flag is the code's
# (cfx.claimed); with a claim on record a job's claim pass (CS.take) is
# Keep or Roll, whatever its status, next run and due time; with none the
# spec asks nothing.
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../laws/cron_file/pass.bend as CronFile
import ./cron_file_take_exact.bend as PTakeX

def cto.due(b: Bool, -p: CS.Plan, -n: Nat, -rest: Bool, ih: {rest == True{} : Bool}) -> {Bool.and(CronFile.once_took_spec(True{}, CS.take.due(b, True{}, p, n)), rest) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      ih

def cto.head(c: Bool, f: CS.Fact, d: Nat, -n: Nat, -rest: Bool, ih: {rest == True{} : Bool}) -> {Bool.and(CronFile.once_took_spec(c, CS.take(f, c, d, n)), rest) == True{} : Bool}:
  match c:
    case False{}:
      ih
    case True{}:
      match f:
        case CS.Fact{st, p, nx, k}:
          match st:
            case Cr.Active{}:
              match nx:
                case None{}:
                  ih
                case Some{x}:
                  cto.due(Nat.is_le(x, d), p, n, rest, ih)
            case Cr.Paused{}:
              ih
            case Cr.Finished{}:
              ih
            case Cr.Cancelled{}:
              ih

def cto.take(js: List<&2, CF.Slot>, +cs: List<&2, Maybe<&2, Nat>>, +d: Nat, +n: Nat) -> {CronFile.take_once_spec(js, cs, CF.take(js, cs, d, n)) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case j <> +t:
      match j:
        case CF.Slot{+key, +f}:
          %PTakeX.cfx.claimed(key, cs) : {Bool.and(CronFile.once_took_spec(_, CS.take(f, CF.claimed(key, cs), d, n)), CronFile.take_once_spec(t, cs, CF.take(t, cs, d, n))) == True{} : Bool}
          cto.head(CF.claimed(key, cs), f, d, n, CronFile.take_once_spec(t, cs, CF.take(t, cs, d, n)), cto.take(t, cs, d, n))

def CronFile.cron_file_take_claims_once(js, cs, d, n):
  cto.take(js, cs, d, n)
