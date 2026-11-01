# eukhe: the proof of LAW table_roles

import Base
import ../../bend/model_roles.bend as Mr
import ../../laws/model_roles.bend as ModelRoles

def ModelRoles.table_roles(x):
  match x:
    case Mr.In{o, all}:
      {==}
