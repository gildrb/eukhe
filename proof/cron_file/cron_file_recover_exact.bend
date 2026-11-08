# eukhe: the proof of LAW cron_file_recover_exact
# By induction on the claim records and the jobs: each verdict is
# CronStore.clear_spec (cron_clear_exact), each job's recovery
# CronStore.recover_spec (cron_recover_exact).
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ../../laws/cron_file/view.bend as CronFileView
import ./base/logic.bend as LCfl
import ../cron_store/cron_clear_exact.bend as PClear
import ../cron_store/cron_recover_exact.bend as PRecover

def cfr.names(+k: Nat, m: Maybe<&2, Nat>) -> {CF.names(k, m) == CronFile.names_spec(k, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      LCfl.cfl.eq_comm(x, k)

def cfr.keeps(cs: List<&2, CF.Hold>) -> {CF.keeps(cs) == CronFile.keeps_spec(cs) : List<&2, Bool>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case CF.Held{m, +w}:
          %cfr.keeps(t) : {Bool.not(CS.clear(w)) <> CF.keeps(t) == Bool.not(CronStore.clear_spec(w)) <> _ : List<&2, Bool>}
          %CronStore.cron_clear_exact(w) : {Bool.not(CS.clear(w)) <> CF.keeps(t) == Bool.not(_) <> CF.keeps(t) : List<&2, Bool>}
          {==}
        case CF.Unheld{}:
          %cfr.keeps(t) : {True{} <> CF.keeps(t) == True{} <> _ : List<&2, Bool>}
          {==}

def cfr.one(+k: Nat, c: CF.Hold) -> {CF.cleared.one(k, c) == CronFile.cleared_spec.one(k, c) : Bool}:
  match c:
    case CF.Held{+m, +w}:
      %cfr.names(k, m) : {Bool.and(CF.names(k, m), CS.clear(w)) == Bool.and(CronStore.clear_spec(w), _) : Bool}
      %CronStore.cron_clear_exact(w) : {Bool.and(CF.names(k, m), CS.clear(w)) == Bool.and(_, CF.names(k, m)) : Bool}
      LCfl.cfl.and_comm(CF.names(k, m), CS.clear(w))
    case CF.Unheld{}:
      {==}

def cfr.cleared(+k: Nat, cs: List<&2, CF.Hold>) -> {CF.cleared(k, cs) == CronFile.cleared_spec(k, cs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      %cfr.cleared(k, t) : {Bool.or(CF.cleared.one(k, c), CF.cleared(k, t)) == Bool.or(CronFile.cleared_spec.one(k, c), _) : Bool}
      %cfr.one(k, c) : {Bool.or(CF.cleared.one(k, c), CF.cleared(k, t)) == Bool.or(_, CF.cleared(k, t)) : Bool}
      {==}

def cfr.js(js: List<&2, CF.Slot>, +cs: List<&2, CF.Hold>) -> {CF.recover.js(js, cs) == CronFile.recover_js_spec(js, cs) : List<&2, CS.Back>}:
  match js:
    case Nil{}:
      {==}
    case j <> +t:
      match j:
        case CF.Slot{+key, +f}:
          %cfr.js(t, cs) : {CS.recover(f, CF.cleared(key, cs)) <> CF.recover.js(t, cs) == CronStore.recover_spec(f, CronFile.cleared_spec(key, cs)) <> _ : List<&2, CS.Back>}
          %cfr.cleared(key, cs) : {CS.recover(f, CF.cleared(key, cs)) <> CF.recover.js(t, cs) == CronStore.recover_spec(f, _) <> CF.recover.js(t, cs) : List<&2, CS.Back>}
          %CronStore.cron_recover_exact(f, CF.cleared(key, cs)) : {CS.recover(f, CF.cleared(key, cs)) <> CF.recover.js(t, cs) == _ <> CF.recover.js(t, cs) : List<&2, CS.Back>}
          {==}

def CronFile.cron_file_recover_exact(js, cs):
  %cfr.keeps(cs) : {CF.recover(js, cs) == CF.Swept{_, CronFile.recover_js_spec(js, cs)} : CF.Swept}
  %cfr.js(js, cs) : {CF.recover(js, cs) == CF.Swept{CF.keeps(cs), _} : CF.Swept}
  {==}
