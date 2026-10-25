# eukhe: the proof of LAW theme_concrete_of_spec: unset, or the value's
# color (LAW theme_concrete_spec)

import Base
import ../../laws/theme.bend as Theme
import ../../laws/theme_model.bend as ThemeModel
import ../theme/theme_concrete_spec.bend as PConcrete

def ThemeModel.theme_concrete_of_spec(m):
  match m:
    case None{}:
      {==}
    case Some{v}:
      Theme.theme_concrete_spec(v)
