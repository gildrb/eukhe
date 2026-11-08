# eukhe: the proof of LAW all_fills

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles
import ./base.bend as LA

def ModelRoles.all_fills(o, r, n, h, t):
  %LA.pmr.at_sym(o, Mr.Sel{n}, r) : {_ == Some{Mr.All{n}} : Maybe<&2, Mr.Src>}
  %Equal.sym(Mr.Choice, Mr.own(o, r), Mr.Unset{}, h) : {Some{Mr.source(r, _, Mr.Sel{n})} == Some{Mr.All{n}} : Maybe<&2, Mr.Src>}
  %Equal.sym(Bool, Mr.takes_chat(r), True{}, t) : {Some{Mr.fill(_, Mr.Sel{n})} == Some{Mr.All{n}} : Maybe<&2, Mr.Src>}
  {==}
