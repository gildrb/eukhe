# eukhe: the proof of LAW slash_args_auto_task
#
# PROOF: `/auto` reads the words; a first word that is none of the
# keywords answers the task, the args as given.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def sat.at(+st: Bool, +on: Bool, +off: Bool, +t: List<&2, String>, +a: String, +k: {Bool.or(st, Bool.or(on, off)) == False{} : Bool}) -> {Sa.auto.kw(st, on, off, t, a) == Sa.ATask{a} : Sa.Auto}:
  %Equal.sym(Bool, st, False{}, LA.sab.or_fl(st, Bool.or(on, off), k)) : {Sa.auto.kw(_, on, off, t, a) == Sa.ATask{a} : Sa.Auto}
  %Equal.sym(Bool, on, False{}, LA.sab.or_fl(on, off, LA.sab.or_fr(st, Bool.or(on, off), k))) : {Sa.auto.kw(False{}, _, off, t, a) == Sa.ATask{a} : Sa.Auto}
  %Equal.sym(Bool, off, False{}, LA.sab.or_fr(on, off, LA.sab.or_fr(st, Bool.or(on, off), k))) : {Sa.auto.kw(False{}, False{}, _, t, a) == Sa.ATask{a} : Sa.Auto}
  {==}

def SlashArgs.slash_args_auto_task(s, w, t, ws, k):
  +l = String.to_lower(w)
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.words(w <> t, s), Sa.ATask{s}, LA.sab.auto_ws(s, w <> t, ws), sat.at(String.eq(l, "status"), SlashArgs.sa_on(l), SlashArgs.sa_off(l), t, s, k))
