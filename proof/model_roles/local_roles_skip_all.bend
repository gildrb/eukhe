# eukhe: the proof of LAW local_roles_skip_all

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles
import ./base.bend as LA

def ModelRoles.local_roles_skip_all(o, all, r, h, t):
  %LA.pmr.at_sym(o, all, r) : {_ == Some{Mr.Default{}} : Maybe<&2, Mr.Src>}
  %Equal.sym(Mr.Choice, Mr.own(o, r), Mr.Unset{}, h) : {Some{Mr.source(r, _, all)} == Some{Mr.Default{}} : Maybe<&2, Mr.Src>}
  %Equal.sym(Bool, Mr.takes_chat(r), False{}, t) : {Some{Mr.fill(_, all)} == Some{Mr.Default{}} : Maybe<&2, Mr.Src>}
  {==}
