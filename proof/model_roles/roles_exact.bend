# eukhe: the proof of LAW roles_exact

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles

def ModelRoles.roles_exact(r):
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
