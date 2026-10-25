# eukhe: the proof of LAW theme_at_spec: the lookup lemma of
# theme_legible_spec

import Base
import ../../laws/theme_model.bend as ThemeModel
import ../theme/theme_legible_spec.bend as PLeg

def ThemeModel.theme_at_spec(xs, k):
  PLeg.lg.at(xs, k)
