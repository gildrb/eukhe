# eukhe: the proof of LAW slash_args_auto_other
#
# PROOF: `/autonomous` reads the words; a first word that is none of the
# keywords answers the usage text.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def sao.at(+st: Bool, +on: Bool, +off: Bool, +t: List<&2, String>, +k: {Bool.or(st, Bool.or(on, off)) == False{} : Bool}) -> {Sa.auto.kw(st, on, off, t) == Sa.AErr{SlashArgs.sa_usage()} : Sa.Auto}:
  %Equal.sym(Bool, st, False{}, LA.sab.or_fl(st, Bool.or(on, off), k)) : {Sa.auto.kw(_, on, off, t) == Sa.AErr{SlashArgs.sa_usage()} : Sa.Auto}
  %Equal.sym(Bool, on, False{}, LA.sab.or_fl(on, off, LA.sab.or_fr(st, Bool.or(on, off), k))) : {Sa.auto.kw(False{}, _, off, t) == Sa.AErr{SlashArgs.sa_usage()} : Sa.Auto}
  %Equal.sym(Bool, off, False{}, LA.sab.or_fr(on, off, LA.sab.or_fr(st, Bool.or(on, off), k))) : {Sa.auto.kw(False{}, False{}, _, t) == Sa.AErr{SlashArgs.sa_usage()} : Sa.Auto}
  {==}

def SlashArgs.slash_args_auto_other(s, w, t, ws, k):
  +l = String.to_lower(w)
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.words(w <> t), Sa.AErr{SlashArgs.sa_usage()}, LA.sab.auto_ws(s, w <> t, ws), sao.at(String.eq(l, "status"), SlashArgs.sa_on(l), SlashArgs.sa_off(l), t, k))
