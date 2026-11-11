# eukhe: the proof of LAW slash_args_auto_alone
#
# PROOF: `/autonomous` reads the words; one word w is judged by its
# lowercase, keyword by keyword (LA.sab.alone.at).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def SlashArgs.slash_args_auto_alone(s, w, ws):
  +l = String.to_lower(w)
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.words([w]), SlashArgs.sa_alone(l), LA.sab.auto_ws(s, [w], ws), LA.sab.alone.at(String.eq(l, "status"), SlashArgs.sa_on(l), SlashArgs.sa_off(l)))
