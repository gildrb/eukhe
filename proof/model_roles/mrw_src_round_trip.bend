# eukhe: the proof of LAW mrw_src_round_trip

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/model_roles.bend as ModelRoles
import ./base.bend as LA

def ModelRoles.mrw_src_round_trip(x, rest, h):
  match x:
    case Mr.Own{+n}:
      %LA.pmr.nat(n, rest, h) : {FMr.get_src.own(_) == Wr.Got{Mr.Own{n}, rest} : Wr.Dec<Mr.Src>}
      {==}
    case Mr.All{+n}:
      %LA.pmr.nat(n, rest, h) : {FMr.get_src.all(_) == Wr.Got{Mr.All{n}, rest} : Wr.Dec<Mr.Src>}
      {==}
    case Mr.Default{}:
      {==}
