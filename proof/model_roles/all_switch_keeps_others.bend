# eukhe: the proof of LAW all_switch_keeps_others
#
# PROOF: split the settings into fields and the role: every role but
# speech and dictation is reached (the premise is True == False); speech
# and dictation keep their own setting through the switch and, taking no
# chat model, resolve the same under any all-roles setting (split on their
# own setting).

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles
import ../base/logic/logic.bend as LLogicLogic

# a role that takes no chat model resolves the same under any all-roles
# setting
def kos.local(+r: Mr.Role, c: Mr.Choice, -x: Mr.Choice, -y: Mr.Choice, +t: {Mr.takes_chat(r) == False{} : Bool}) -> {Some{Mr.source(r, c, x)} == Some{Mr.source(r, c, y)} : Maybe<&2, Mr.Src>}:
  match c:
    case Mr.Unset{}:
      %Equal.sym(Bool, Mr.takes_chat(r), False{}, t) : {Some{Mr.fill(_, x)} == Some{Mr.fill(Mr.takes_chat(r), y)} : Maybe<&2, Mr.Src>}
      %Equal.sym(Bool, Mr.takes_chat(r), False{}, t) : {Some{Mr.fill(False{}, x)} == Some{Mr.fill(_, y)} : Maybe<&2, Mr.Src>}
      {==}
    case Mr.Sel{k}:
      {==}

def ModelRoles.all_switch_keeps_others(o, a, n, r, h):
  match o:
    case Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
      match r:
        case Mr.Chat{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Chat{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Chat{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Memory{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Memory{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Memory{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Auxiliary{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Auxiliary{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Auxiliary{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Image{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Image{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Image{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Subagent{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Subagent{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Subagent{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Worker{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Worker{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Worker{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Gateway{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Gateway{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Gateway{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Query{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Query{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Query{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Titles{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Titles{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Titles{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Judge{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Judge{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Judge{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Translate{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Translate{}) == ModelRoles.mr_at(Mr.resolve(Mr.In{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, a}), Mr.Translate{}) : Maybe<&2, Mr.Src>}, Equal.sym(Bool, True{}, False{}, h))
        case Mr.Speech{}:
          kos.local(Mr.Speech{}, speech, Mr.Sel{n}, a, {==})
        case Mr.Dictation{}:
          kos.local(Mr.Dictation{}, dictation, Mr.Sel{n}, a, {==})
