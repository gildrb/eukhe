# eukhe: the proof of LAW slash_args_auto_none
#
# PROOF: `/autonomous` reads the words; none: the status.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def SlashArgs.slash_args_auto_none(s, ws):
  LA.sab.auto_ws(s, [], ws)
