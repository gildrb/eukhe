# eukhe: lemmas of the cron_file proofs: a claim pass and a recovery of
# the code that runs (bend/cron_file.bend) are the specs' passes
# (laws/cron_file/pass.bend). By induction on the jobs and the claim
# records: each job's claim pass is CronStore.take_spec, each verdict
# CronStore.clear_spec, each job's recovery CronStore.recover_spec
# (proof/cron_store/base.bend), with the same claimed and cleared flags (a
# key named by a claim record, Nat.is_eq turned around).

import Base
import ../../../bend/cron.bend as Cr
import ../../../bend/cron_store.bend as CS
import ../../../bend/cron_file.bend as CF
import ../../../laws/cron_store.bend as CronStore
import ../../../laws/cron_file/pass.bend as CronFile
import ../../cron_store/base.bend as LCs
import ./logic.bend as LCfl

# A claim pass
# ------------

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
          %LCs.cx.take(f, CF.claimed(key, cs), d, n) : {CS.take(f, CF.claimed(key, cs), d, n) <> CF.take(t, cs, d, n) == _ <> CF.take(t, cs, d, n) : List<&2, CS.Took>}
          {==}

# A recovery
# ----------

def cfr.keeps(cs: List<&2, CF.Hold>) -> {CF.keeps(cs) == CronFile.keeps_spec(cs) : List<&2, Bool>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case CF.Held{m, +w}:
          %cfr.keeps(t) : {Bool.not(CS.clear(w)) <> CF.keeps(t) == Bool.not(CronStore.clear_spec(w)) <> _ : List<&2, Bool>}
          %LCs.cx.clear(w) : {Bool.not(CS.clear(w)) <> CF.keeps(t) == Bool.not(_) <> CF.keeps(t) : List<&2, Bool>}
          {==}
        case CF.Unheld{}:
          %cfr.keeps(t) : {True{} <> CF.keeps(t) == True{} <> _ : List<&2, Bool>}
          {==}

def cfr.one(+k: Nat, c: CF.Hold) -> {CF.cleared.one(k, c) == CronFile.cleared_spec.one(k, c) : Bool}:
  match c:
    case CF.Held{+m, +w}:
      %cfx.names(k, m) : {Bool.and(CF.names(k, m), CS.clear(w)) == Bool.and(CronStore.clear_spec(w), _) : Bool}
      %LCs.cx.clear(w) : {Bool.and(CF.names(k, m), CS.clear(w)) == Bool.and(_, CF.names(k, m)) : Bool}
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
          %LCs.cx.recover(f, CF.cleared(key, cs)) : {CS.recover(f, CF.cleared(key, cs)) <> CF.recover.js(t, cs) == _ <> CF.recover.js(t, cs) : List<&2, CS.Back>}
          {==}

def cfr.recover(+js: List<&2, CF.Slot>, +cs: List<&2, CF.Hold>) -> {CF.recover(js, cs) == CronFile.recover_all_spec(js, cs) : CF.Swept}:
  %cfr.keeps(cs) : {CF.recover(js, cs) == CF.Swept{_, CronFile.recover_js_spec(js, cs)} : CF.Swept}
  %cfr.js(js, cs) : {CF.recover(js, cs) == CF.Swept{CF.keeps(cs), _} : CF.Swept}
  {==}
