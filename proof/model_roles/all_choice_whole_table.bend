# eukhe: the proof of LAW all_choice_whole_table

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles

# Every role but speech and dictation computes once the settings are
# split into fields; speech and dictation split on their own setting.

def ModelRoles.all_choice_whole_table(o, a, n):
  match o:
    case Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
      match speech:
        case Mr.Unset{}:
          match dictation:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{j}:
              {==}
        case Mr.Sel{k}:
          match dictation:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{j}:
              {==}
