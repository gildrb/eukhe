# eukhe: the proof of LAW all_switch_runs_n
#
# PROOF: split the settings into fields and the role: every reached role
# computes (its own setting cleared, or n for the chat; the table gives
# All{n} or Own{n}); speech and dictation are not reached (the premise is
# False == True).

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles
import ../base/logic/logic.bend as LLogicLogic

def ModelRoles.all_switch_runs_n(o, n, r, h):
  match o:
    case Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
      match r:
        case Mr.Chat{}:
          {==}
        case Mr.Memory{}:
          {==}
        case Mr.Auxiliary{}:
          {==}
        case Mr.Image{}:
          {==}
        case Mr.Subagent{}:
          {==}
        case Mr.Worker{}:
          {==}
        case Mr.Gateway{}:
          {==}
        case Mr.Query{}:
          {==}
        case Mr.Titles{}:
          {==}
        case Mr.Judge{}:
          {==}
        case Mr.Translate{}:
          {==}
        case Mr.Speech{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_runs(ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Speech{})) == Some{n} : Maybe<&2, Nat>}, h)
        case Mr.Dictation{}:
          LLogicLogic.wr_absurd({ModelRoles.mr_runs(ModelRoles.mr_at(Mr.resolve(Mr.In{ModelRoles.mr_switch(Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, n), Mr.Sel{n}}), Mr.Dictation{})) == Some{n} : Maybe<&2, Nat>}, h)
