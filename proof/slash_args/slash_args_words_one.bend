# eukhe: the proof of LAW slash_args_words_one
#
# PROOF: with no White_Space outside a quote, the tokenizer only collects
# the chars that open or close no quote (LA.sab.one); the one word is
# pushed at the end: it has a char, or its first char opened a quote
# (LA.sab.one_ok, LA.sab.push_rev).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def SlashArgs.slash_args_words_one(c, t, ti):
  +s = {SCon{c, t} : String}
  +u = SlashArgs.sa_unquote(s, None{})
  +qq = LA.sab.orq(s, None{}, False{})
  +r = {Sa.Tok{SlashArgs.sa_end(s, None{}), String.reverse.go(u, SNil{}), qq, Nil{}} : Sa.Tok}
  Equal.trans(List<&2, String>, Sa.words(s), Sa.tok.fin(LA.sab.run(s, LA.sab.init())), [u], LA.sab.go_run(s, LA.sab.init()), Equal.trans(List<&2, String>, Sa.tok.fin(LA.sab.run(s, LA.sab.init())), Sa.tok.fin(r), [u], Equal.cong(Sa.Tok, List<&2, String>, z => Sa.tok.fin(z), LA.sab.run(s, LA.sab.init()), r, LA.sab.one(s, None{}, SNil{}, False{}, ti)), LA.sab.push_rev(u, qq, LA.sab.one_ok(c, t, SlashArgs.sa_qc(c), {==}))))
