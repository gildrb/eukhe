# eukhe: the proof of LAW slash_args_words_spec
#
# PROOF: the tokenizer's step is the spec's for every char and state (sab.step), so its run over the text is (sab.go).

import Base
import ../../bend/slash_args.bend as Sa
import ../../laws/slash_args/model.bend as SlashArgs
import ./base/text.bend as LT

def SlashArgs.slash_args_words_spec(s):
  LT.sab.words(s)
