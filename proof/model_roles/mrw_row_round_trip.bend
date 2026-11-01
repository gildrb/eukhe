# eukhe: the proof of LAW mrw_row_round_trip

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/model_roles.bend as ModelRoles
import ./mrw_role_round_trip.bend as PMrwRoleRoundTrip
import ./mrw_src_round_trip.bend as PMrwSrcRoundTrip

# a role reads back (turned around for rewriting)
def pmr.role(+r: Mr.Role, +rest: String) -> {Wr.Got{r, rest} == FMr.get_role(FMr.put_role(r, rest)) : Wr.Dec<Mr.Role>}:
  Equal.sym(Wr.Dec<Mr.Role>, FMr.get_role(FMr.put_role(r, rest)), Wr.Got{r, rest}, ModelRoles.mrw_role_round_trip(r, rest))

# a source reads back (turned around for rewriting)
def pmr.src(+x: Mr.Src, +rest: String, h: {ModelRoles.mrw_src_fits(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FMr.get_src(FMr.put_src(x, rest)) : Wr.Dec<Mr.Src>}:
  Equal.sym(Wr.Dec<Mr.Src>, FMr.get_src(FMr.put_src(x, rest)), Wr.Got{x, rest}, ModelRoles.mrw_src_round_trip(x, rest, h))

def ModelRoles.mrw_row_round_trip(x, rest, h):
  match x:
    case Mr.Row{+role, +src}:
      +z = rest
      %pmr.role(role, FMr.put_src(src, z)) : {FMr.get_row.go(_) == Wr.Got{Mr.Row{role, src}, z} : Wr.Dec<Mr.Row>}
      %pmr.src(src, z, h) : {FMr.get_row.src(role, _) == Wr.Got{Mr.Row{role, src}, z} : Wr.Dec<Mr.Row>}
      {==}
