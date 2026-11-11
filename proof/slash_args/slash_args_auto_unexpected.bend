# eukhe: the proof of LAW slash_args_auto_unexpected
#
# PROOF: after an on word (not `status`: LA.sab.ne_on) the options are
# read word by word; the first word's step comes first (LAA.saa.opts), and
# a word that does not start with `--` is unexpected.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA
import ./base/auto.bend as LAA

def SlashArgs.slash_args_auto_unexpected(s, w, x, t, ws, k, d):
  LAA.saa.opts(s, w, x, t, ws, k, False{}, d)
