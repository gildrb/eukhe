# eukhe: the proof of LAW slash_args_auto_bad_value
#
# PROOF: after the on word the options of the words are read
# (LAA.saa.on); the option's words read its value first (LAO.sao.one),
# which R8 refuses: its error, whatever follows (LAO.sao.bad).

import Base
import ../../bend/slash_args.bend as Sa
import ../../laws/slash_args/model.bend as SlashArgs
import ./base.bend as LA
import ./base/auto.bend as LAA
import ./base/opts.bend as LAO

def SlashArgs.slash_args_auto_bad_value(s, w, o, r, ws, on, g, b):
  +x = List.append(&2, String, SlashArgs.sa_opt_words(o), r)
  +a1 = Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.words(w <> x, s), Sa.auto.on(Sa.options(x)), LA.sab.auto_ws(s, w <> x, ws), LAA.saa.on(String.to_lower(w), on, x, s))
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.on(Sa.options(x)), SlashArgs.sa_opt_read(o), a1, Equal.trans(Sa.Auto, Sa.auto.on(Sa.options(x)), Sa.auto.on(LAO.sao.at(o, Sa.options(r))), SlashArgs.sa_opt_read(o), Equal.cong(Sa.Read, Sa.Auto, z => Sa.auto.on(z), Sa.options(x), LAO.sao.at(o, Sa.options(r)), LAO.sao.one(o, r, g)), LAO.sao.bad(o, Sa.options(r), b)))
