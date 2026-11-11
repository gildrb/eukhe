# eukhe: the proof of LAW slash_args_auto_more
#
# PROOF: `/autonomous` reads the words; a first word `status` or an off
# word (no on word: LA.sab.on_off) takes nothing after it, so the second
# word is unexpected.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def sam.at(st: Bool, +l: String, +v: String, +t: List<&2, String>, +k: {Bool.or(st, SlashArgs.sa_off(l)) == True{} : Bool}) -> {Sa.auto.kw(st, SlashArgs.sa_on(l), SlashArgs.sa_off(l), v <> t) == Sa.AErr{SlashArgs.sa_err("Unexpected autonomous argument: ", v)} : Sa.Auto}:
  match st:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, SlashArgs.sa_on(l), False{}, LA.sab.on_off(l, k)) : {Sa.auto.kw(False{}, _, SlashArgs.sa_off(l), v <> t) == Sa.AErr{SlashArgs.sa_err("Unexpected autonomous argument: ", v)} : Sa.Auto}
      %Equal.sym(Bool, SlashArgs.sa_off(l), True{}, k) : {Sa.auto.kw(False{}, False{}, _, v <> t) == Sa.AErr{SlashArgs.sa_err("Unexpected autonomous argument: ", v)} : Sa.Auto}
      {==}

def SlashArgs.slash_args_auto_more(s, w, v, t, ws, k):
  +l = String.to_lower(w)
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.words(w <> v <> t), Sa.AErr{SlashArgs.sa_err("Unexpected autonomous argument: ", v)}, LA.sab.auto_ws(s, w <> v <> t, ws), sam.at(String.eq(l, "status"), l, v, t, k))
