# eukhe: the proof of LAW slash_args_auto_unknown
#
# PROOF: after an on word (not `status`: LA.sab.ne_on) the first option
# word's step comes first (LAA.saa.opts); its flag and name are R7's
# (LAA.saa.flag), which the flag table does not hold (LA.sab.index_none).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA
import ./base/auto.bend as LAA

def SlashArgs.slash_args_auto_unknown(s, w, x, t, ws, k, d, u):
  +r1 = Sa.options(t)
  +r2 = LA.sab.snd(Sa.reads(t))
  +raw = SlashArgs.sa_raw(x)
  +st = Equal.trans(Sa.Read, Sa.step(True{}, x, t, r1, r2), Sa.step.known(Sa.index(SlashArgs.sa_name(raw), Sa.flags(), 0n), x, raw, SlashArgs.sa_name(raw), t, r1, r2), Sa.RErr{Sa.auto_err("Unknown autonomous budget flag: ", raw)}, LAA.saa.flag(x, t, r1, r2), Equal.cong(Maybe<&2, Nat>, Sa.Read, z => Sa.step.known(z, x, raw, SlashArgs.sa_name(raw), t, r1, r2), Sa.index(SlashArgs.sa_name(raw), Sa.flags(), 0n), None{}, LA.sab.index_none(SlashArgs.sa_name(raw), u)))
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.on(Sa.step(True{}, x, t, r1, r2)), Sa.AErr{SlashArgs.sa_err("Unknown autonomous budget flag: ", raw)}, LAA.saa.opts(s, w, x, t, ws, k, True{}, d), Equal.cong(Sa.Read, Sa.Auto, z => Sa.auto.on(z), Sa.step(True{}, x, t, r1, r2), Sa.RErr{Sa.auto_err("Unknown autonomous budget flag: ", raw)}, st))
