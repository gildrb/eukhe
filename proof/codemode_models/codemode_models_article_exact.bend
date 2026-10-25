# eukhe: the proof of LAW codemode_models_article_exact

import Base
import ../../bend/codemode_models.bend as Mod
import ../../laws/codemode_models/checks.bend as CodemodeModels
import ./base.bend as LACm

# PROOF of LAW codemode_models_article_exact: the vowel test is the spec's membership in a, e, i, o, u (cm.article).

def CodemodeModels.codemode_models_article_exact(w):
  LACm.cm.article(w)
