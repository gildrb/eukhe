# eukhe: the proof of LAW once_entry_reads
#
# PROOF: a spelled event is read whole, so the stepper runs it on the
# life (LE.oe.spelled). A record moves the life by one step, the spec's
# for the journal with the record after it (once_life_step_is_spec); a
# question answers the restart's verdict, the spec's (LA.ob.recover_spec);
# both replies are spelled as Rust reads them (LE.oe.put_life,
# LE.oe.put_verdict).

import Base
import ../../bend/once.bend as O
import ../../bend/ffi_once.bend as FO
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base/entry.bend as LE
import ./once_life_step_is_spec.bend as POnceLifeStepIsSpec
import ./base.bend as LA

# a spelled record: the life the spec tells for j and r, answered
def oer.note(+j: List<&2, O.Rec>, +r: O.Rec) -> {FO.step(FO.Eff{S.life_spec(j)}, Once.on_spell(FO.Note{r})) == (FO.Eff{S.life_spec(List.append(&2, O.Rec, j, [r]))}, Once.on_spell_life(S.life_spec(List.append(&2, O.Rec, j, [r])))) : FO.St & String}:
  %LE.oe.put_life(S.life_spec(List.append(&2, O.Rec, j, [r]))) : {FO.step(FO.Eff{S.life_spec(j)}, Once.on_spell(FO.Note{r})) == (FO.Eff{S.life_spec(List.append(&2, O.Rec, j, [r]))}, _) : FO.St & String}
  %Once.once_life_step_is_spec(j, r) : {FO.step(FO.Eff{S.life_spec(j)}, Once.on_spell(FO.Note{r})) == FO.step.note(_) : FO.St & String}
  LE.oe.spelled(S.life_spec(j), FO.Note{r}, {==})

# a spelled question: the spec's verdict for j, the life kept
def oer.ask(+j: List<&2, O.Rec>, +m: O.Mode, +p: O.Policy, +s: O.Seen, fit: {Once.on_fit.policy(p) == True{} : Bool}) -> {FO.step(FO.Eff{S.life_spec(j)}, Once.on_spell(FO.Ask{m, p, s})) == (FO.Eff{S.life_spec(j)}, Once.on_spell_verdict(S.verdict_spec(S.life_spec(j), s, m, p))) : FO.St & String}:
  %LE.oe.put_verdict(S.verdict_spec(S.life_spec(j), s, m, p)) : {FO.step(FO.Eff{S.life_spec(j)}, Once.on_spell(FO.Ask{m, p, s})) == (FO.Eff{S.life_spec(j)}, _) : FO.St & String}
  %LA.ob.recover_spec(S.life_spec(j), s, m, p) : {FO.step(FO.Eff{S.life_spec(j)}, Once.on_spell(FO.Ask{m, p, s})) == (FO.Eff{S.life_spec(j)}, FO.put_verdict(_)) : FO.St & String}
  LE.oe.spelled(S.life_spec(j), FO.Ask{m, p, s}, fit)

def Once.once_entry_reads(j, r, m, p, s, fit):
  (oer.note(j, r), oer.ask(j, m, p, s, fit))
