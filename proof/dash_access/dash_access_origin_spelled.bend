# eukhe: the proof of LAW dash_access_origin_spelled
#
# PROOF: the scheme holds no ':' (it is http or https but for case:
# LA.dab.scheme_nocolon), so the origin cuts at the "://" after it
# (LA.dab.sep_text); the code's default port is the spec's (LA.dab.scheme);
# both authorities read as their host and port (LA.dab.split_spell); the
# code's host comparison is the spec's (LA.dab.same) and so is its port
# default (LA.dab.port_or).

import Base
import ../../bend/dash_access.bend as Ac
import ../../laws/dash_access.bend as DashAccess
import ./base.bend as LA

def DashAccess.dash_access_origin_spelled(sc, d, a, b, scheme, wa, wb):
  +sch = scheme
  +na = DashAccess.sp_name(a)
  +nb = DashAccess.sp_name(b)
  +pa = DashAccess.sp_port(a)
  +pb = DashAccess.sp_port(b)
  +ra = DashAccess.sp_spell(a)
  +rb = DashAccess.sp_spell(b)
  %Equal.sym(Maybe<&2, Ac.Cut>, Ac.sep(DashAccess.sp_origin_text(sc, a)), Some{Ac.Cut{sc, ra}}, LA.dab.sep_text(sc, ra, LA.dab.scheme_nocolon(sc, d, sch))) : {Ac.origin.sep(_, rb) == DashAccess.sp_same_site(d, a, b) : Bool}
  %Equal.sym(Maybe<&2, Nat>, Ac.scheme(sc), Some{d}, Equal.trans(Maybe<&2, Nat>, Ac.scheme(sc), DashAccess.sp_scheme(sc), Some{d}, LA.dab.scheme(sc), sch)) : {Ac.origin.port(_, ra, rb) == DashAccess.sp_same_site(d, a, b) : Bool}
  %Equal.sym(Ac.Authority, Ac.split(ra), Ac.HostPort{na, pa}, LA.dab.split_spell(a, wa)) : {Ac.origin.pair(d, _, Ac.split(rb)) == DashAccess.sp_same_site(d, a, b) : Bool}
  %Equal.sym(Ac.Authority, Ac.split(rb), Ac.HostPort{nb, pb}, LA.dab.split_spell(b, wb)) : {Ac.origin.pair(d, Ac.HostPort{na, pa}, _) == DashAccess.sp_same_site(d, a, b) : Bool}
  %LA.dab.same(na, nb) : {Bool.and(Ac.same(na, nb), Nat.is_eq(Ac.port_or(pa, d), Ac.port_or(pb, d))) == Bool.and(_, Nat.is_eq(DashAccess.sp_port_or(pa, d), DashAccess.sp_port_or(pb, d))) : Bool}
  %LA.dab.port_or(pa, d) : {Bool.and(Ac.same(na, nb), Nat.is_eq(Ac.port_or(pa, d), Ac.port_or(pb, d))) == Bool.and(Ac.same(na, nb), Nat.is_eq(_, DashAccess.sp_port_or(pb, d))) : Bool}
  %LA.dab.port_or(pb, d) : {Bool.and(Ac.same(na, nb), Nat.is_eq(Ac.port_or(pa, d), Ac.port_or(pb, d))) == Bool.and(Ac.same(na, nb), Nat.is_eq(Ac.port_or(pa, d), _)) : Bool}
  {==}
