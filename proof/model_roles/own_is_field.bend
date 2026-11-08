# eukhe: the proof of LAW own_is_field

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles

def ModelRoles.own_is_field(o, r):
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
          {==}
        case Mr.Dictation{}:
          {==}
