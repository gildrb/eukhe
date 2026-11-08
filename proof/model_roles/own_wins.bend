# eukhe: the proof of LAW own_wins

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles
import ./base.bend as LA

def ModelRoles.own_wins(o, all, r, n, h):
  %LA.pmr.at_sym(o, all, r) : {_ == Some{Mr.Own{n}} : Maybe<&2, Mr.Src>}
  %Equal.sym(Mr.Choice, Mr.own(o, r), Mr.Sel{n}, h) : {Some{Mr.source(r, _, all)} == Some{Mr.Own{n}} : Maybe<&2, Mr.Src>}
  {==}
