# eukhe: the proof of LAW slash_args_words_split
#
# PROOF: the tokenizer reads s, then c and t (LA.sab.go_app); after s no
# quote is open (its quote is R2's: LA.sab.q.run), so the White_Space c
# ends the words so far (LA.sab.split.st), and the words before it do not
# change those read after (LA.sab.go_add).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def SlashArgs.slash_args_words_split(s, cl, c, cw, t):
  +st = LA.sab.run(s, LA.sab.init())
  +eq = Equal.trans(Maybe<&2, Char>, LA.sab.q(st), SlashArgs.sa_end(s, None{}), None{}, LA.sab.q.run(s, LA.sab.init()), LA.sab.none_of(SlashArgs.sa_end(s, None{}), cl))
  Equal.trans(List<&2, String>, Sa.words(String.append(s, SCon{c, t})), Sa.tok.go(SCon{c, t}, st), List.append(&2, String, Sa.words(s), Sa.words(t)), LA.sab.go_app(s, SCon{c, t}, LA.sab.init()), Equal.trans(List<&2, String>, Sa.tok.go(SCon{c, t}, st), List.append(&2, String, Sa.tok.fin(st), Sa.words(t)), List.append(&2, String, Sa.words(s), Sa.words(t)), LA.sab.split.st(st, eq, c, cw, t), Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, Sa.words(t)), Sa.tok.fin(st), Sa.words(s), Equal.sym(List<&2, String>, Sa.words(s), Sa.tok.fin(st), LA.sab.go_run(s, LA.sab.init())))))
