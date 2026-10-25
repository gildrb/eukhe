# eukhe: the proof of LAW slash_args_auto_spec
#
# PROOF: the words are the spec's (sab.words); then the keywords (saa.kw), each option (saa.value, saa.step), the reads of the words by induction (saa.reads) and the options as `/autonomous on` takes them (saa.conf) are.

import Base
import ../../bend/slash_args.bend as Sa
import ../../laws/slash_args/model.bend as SlashArgs
import ./base/auto.bend as LA

def SlashArgs.slash_args_auto_spec(s):
  LA.saa.auto(s)
