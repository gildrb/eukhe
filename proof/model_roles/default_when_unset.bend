# eukhe: the proof of LAW default_when_unset

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles
import ./base.bend as LA

# with the all-roles setting unset, a role without its own setting takes
# its default, whether or not it takes a chat model
def pmr.fill_unset(b: Bool) -> {Mr.fill(b, Mr.Unset{}) == Mr.Default{} : Mr.Src}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ModelRoles.default_when_unset(o, r, h):
  %LA.pmr.at_sym(o, Mr.Unset{}, r) : {_ == Some{Mr.Default{}} : Maybe<&2, Mr.Src>}
  %Equal.sym(Mr.Choice, Mr.own(o, r), Mr.Unset{}, h) : {Some{Mr.source(r, _, Mr.Unset{})} == Some{Mr.Default{}} : Maybe<&2, Mr.Src>}
  %Equal.sym(Mr.Src, Mr.fill(Mr.takes_chat(r), Mr.Unset{}), Mr.Default{}, pmr.fill_unset(Mr.takes_chat(r))) : {Some{_} == Some{Mr.Default{}} : Maybe<&2, Mr.Src>}
  {==}
