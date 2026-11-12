# eukhe: the proof of LAW own_others_ignored
#
# PROOF: the row of role r is the source of r's own setting
# (LA.pmr.at); setting role q's own setting keeps r's field when q is not
# r (ooi.kept: the field of r is mr_put(q, r, c, old), which the premise
# turns into old).

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles
import ./base.bend as LA

# role r's own setting is kept when another role's is set
def ooi.kept(o: Mr.Owns, -q: Mr.Role, r: Mr.Role, -c: Mr.Choice, h: {ModelRoles.mr_role_eq(q, r) == False{} : Bool}) -> {Mr.own(ModelRoles.mr_set_own(o, q, c), r) == Mr.own(o, r) : Mr.Choice}:
  match o:
    case Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
      match r:
        case Mr.Chat{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Chat{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, chat) == chat : Mr.Choice}
          {==}
        case Mr.Memory{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Memory{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, memory) == memory : Mr.Choice}
          {==}
        case Mr.Auxiliary{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Auxiliary{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, auxiliary) == auxiliary : Mr.Choice}
          {==}
        case Mr.Image{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Image{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, image) == image : Mr.Choice}
          {==}
        case Mr.Subagent{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Subagent{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, subagent) == subagent : Mr.Choice}
          {==}
        case Mr.Worker{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Worker{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, worker) == worker : Mr.Choice}
          {==}
        case Mr.Gateway{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Gateway{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, gateway) == gateway : Mr.Choice}
          {==}
        case Mr.Query{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Query{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, query) == query : Mr.Choice}
          {==}
        case Mr.Titles{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Titles{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, titles) == titles : Mr.Choice}
          {==}
        case Mr.Judge{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Judge{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, judge) == judge : Mr.Choice}
          {==}
        case Mr.Translate{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Translate{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, translate) == translate : Mr.Choice}
          {==}
        case Mr.Speech{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Speech{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, speech) == speech : Mr.Choice}
          {==}
        case Mr.Dictation{}:
          %Equal.sym(Bool, ModelRoles.mr_role_eq(q, Mr.Dictation{}), False{}, h) : {ModelRoles.mr_put.pick(_, c, dictation) == dictation : Mr.Choice}
          {==}

def ModelRoles.own_others_ignored(o, all, q, r, c, h):
  +rr = r
  %LA.pmr.at_sym(ModelRoles.mr_set_own(o, q, c), all, rr) : {_ == ModelRoles.mr_at(Mr.resolve(Mr.In{o, all}), rr) : Maybe<&2, Mr.Src>}
  %LA.pmr.at_sym(o, all, rr) : {Some{Mr.source(rr, Mr.own(ModelRoles.mr_set_own(o, q, c), rr), all)} == _ : Maybe<&2, Mr.Src>}
  Equal.cong(Mr.Choice, Maybe<&2, Mr.Src>, z => Some{Mr.source(rr, z, all)}, Mr.own(ModelRoles.mr_set_own(o, q, c), rr), Mr.own(o, rr), ooi.kept(o, q, rr, c, h))
