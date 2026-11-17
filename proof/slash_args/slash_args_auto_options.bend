# eukhe: the proof of LAW slash_args_auto_options
#
# PROOF: after the on word the options of the words are read
# (LAA.saa.on); the words of the options read in turn (LAO.sao.words)
# name each flag's last value and the gate commands in order
# (LAO.sao.fold_ok), which `/autonomous on` takes as R9 says
# (LAO.sao.conf).

import Base
import ../../bend/slash_args.bend as Sa
import ../../laws/slash_args/model.bend as SlashArgs
import ./base.bend as LA
import ./base/auto.bend as LAA
import ./base/opts.bend as LAO

def SlashArgs.slash_args_auto_options(s, w, os, ws, on, ok):
  +ow = SlashArgs.sa_opts_words(os)
  +sp = LAO.sao.spec(os)
  +a1 = Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.words(w <> ow, s), Sa.auto.on(Sa.options(ow)), LA.sab.auto_ws(s, w <> ow, ws), LAA.saa.on(String.to_lower(w), on, ow, s))
  +r1 = Equal.trans(Sa.Read, Sa.options(ow), Sa.options(List.append(&2, String, ow, Nil{})), Sa.ROk{sp}, Equal.cong(List<&2, String>, Sa.Read, z => Sa.options(z), ow, List.append(&2, String, ow, Nil{}), Equal.sym(List<&2, String>, List.append(&2, String, ow, Nil{}), ow, LAO.sao.app_nil(ow))), Equal.trans(Sa.Read, Sa.options(List.append(&2, String, ow, Nil{})), LAO.sao.fold(os, Sa.options(Nil{})), Sa.ROk{sp}, LAO.sao.words(os, Nil{}, ok), LAO.sao.fold_ok(os, ok)))
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.on(Sa.options(ow)), Sa.AOn{SlashArgs.sa_read_conf(os)}, a1, Equal.trans(Sa.Auto, Sa.auto.on(Sa.options(ow)), Sa.auto.on(Sa.ROk{sp}), Sa.AOn{SlashArgs.sa_read_conf(os)}, Equal.cong(Sa.Read, Sa.Auto, z => Sa.auto.on(z), Sa.options(ow), Sa.ROk{sp}, r1), Equal.cong(Sa.Conf, Sa.Auto, z => Sa.AOn{z}, Sa.conf(sp), SlashArgs.sa_read_conf(os), LAO.sao.conf(SlashArgs.sa_last(os, 0n), SlashArgs.sa_last(os, 1n), SlashArgs.sa_last(os, 2n), SlashArgs.sa_last(os, 3n), SlashArgs.sa_cmds(os), SlashArgs.sa_last(os, 5n), SlashArgs.sa_last(os, 6n), SlashArgs.sa_last(os, 7n)))))
