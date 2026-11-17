# eukhe: the proof of LAW slash_args_auto_first_error
#
# PROOF: after the on word the options of the words are read
# (LAA.saa.on); the options read in turn come first (LAO.sao.words), each
# taken without an error, so the error of the words after them stays
# (LAO.sao.keep_err).

import Base
import ../../bend/slash_args.bend as Sa
import ../../laws/slash_args/model.bend as SlashArgs
import ./base.bend as LA
import ./base/auto.bend as LAA
import ./base/opts.bend as LAO

def SlashArgs.slash_args_auto_first_error(s, s2, w, os, r, ws, ws2, on, ok, er):
  +x = List.append(&2, String, SlashArgs.sa_opts_words(os), r)
  +a1 = Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.words(w <> x, s), Sa.auto.on(Sa.options(x)), LA.sab.auto_ws(s, w <> x, ws), LAA.saa.on(String.to_lower(w), on, x, s))
  +b1 = Equal.trans(Sa.Auto, Sa.auto(s2), Sa.auto.words(w <> r, s2), Sa.auto.on(Sa.options(r)), LA.sab.auto_ws(s2, w <> r, ws2), LAA.saa.on(String.to_lower(w), on, r, s2))
  +h = Equal.trans(Bool, SlashArgs.sa_is_err(Sa.auto.on(Sa.options(r))), SlashArgs.sa_is_err(Sa.auto(s2)), True{}, Equal.cong(Sa.Auto, Bool, z => SlashArgs.sa_is_err(z), Sa.auto.on(Sa.options(r)), Sa.auto(s2), Equal.sym(Sa.Auto, Sa.auto(s2), Sa.auto.on(Sa.options(r)), b1)), er)
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.on(Sa.options(x)), Sa.auto(s2), a1, Equal.trans(Sa.Auto, Sa.auto.on(Sa.options(x)), Sa.auto.on(LAO.sao.fold(os, Sa.options(r))), Sa.auto(s2), Equal.cong(Sa.Read, Sa.Auto, z => Sa.auto.on(z), Sa.options(x), LAO.sao.fold(os, Sa.options(r)), LAO.sao.words(os, r, ok)), Equal.trans(Sa.Auto, Sa.auto.on(LAO.sao.fold(os, Sa.options(r))), Sa.auto.on(Sa.options(r)), Sa.auto(s2), LAO.sao.keep_err(Sa.options(r), os, ok, h), Equal.sym(Sa.Auto, Sa.auto(s2), Sa.auto.on(Sa.options(r)), b1))))
