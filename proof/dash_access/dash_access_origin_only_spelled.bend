# eukhe: the proof of LAW dash_access_origin_only_spelled
#
# PROOF: a matching origin cuts at a "://" (LA.dab.sep_inv: it is scheme
# "://" rest), its scheme has a default port (the code's is the spec's:
# LA.dab.scheme), and both its rest and the `Host` read as authorities, so
# each is the writing of a well-formed one (LA.dab.split_inv).

import Base
import ../../bend/dash_access.bend as Ac
import ../../laws/dash_access.bend as DashAccess
import ./base.bend as LA
import ../../laws/base.bend as LawsBase

# both authorities are writings of well-formed ones: build the origin
def dgo.mk(-o: String, +sc: String, -au: String, -h: String, -d: Nat, eo: {o == String.append(sc, SCon{':', SCon{'/', SCon{'/', au}}}) : String}, esm: {Ac.scheme(sc) == Some{d} : Maybe<&2, Nat>}, spa: Sigma<&1, &1, DashAccess.SpAuth, w => {au == DashAccess.sp_spell(w) : String} & {DashAccess.sp_well(w) == True{} : Bool}>, spb: Sigma<&1, &1, DashAccess.SpAuth, w => {h == DashAccess.sp_spell(w) : String} & {DashAccess.sp_well(w) == True{} : Bool}>) -> Sigma<&1, &1, DashAccess.SpOrigin, w => {o == DashAccess.sp_o_origin(w) : String} & {h == DashAccess.sp_o_host(w) : String} & {DashAccess.sp_o_ok(w) == True{} : Bool}>:
  (+wa, (ea, la)) = spa
  (+wb, (eb, lb)) = spb
  +eo2 = Equal.trans(String, o, String.append(sc, SCon{':', SCon{'/', SCon{'/', au}}}), DashAccess.sp_origin_text(sc, wa), eo, Equal.cong(String, String, z => String.append(sc, SCon{':', SCon{'/', SCon{'/', z}}}), au, DashAccess.sp_spell(wa), ea))
  +es = Equal.trans(Bool, Maybe.is_some(&2, Nat, DashAccess.sp_scheme(sc)), Maybe.is_some(&2, Nat, Some{d}), True{}, Equal.cong(Maybe<&2, Nat>, Bool, z => Maybe.is_some(&2, Nat, z), DashAccess.sp_scheme(sc), Some{d}, Equal.trans(Maybe<&2, Nat>, DashAccess.sp_scheme(sc), Ac.scheme(sc), Some{d}, Equal.sym(Maybe<&2, Nat>, Ac.scheme(sc), DashAccess.sp_scheme(sc), LA.dab.scheme(sc)), esm)), {==})
  (DashAccess.SpOrigin{sc, wa, wb}, (eo2, (eb, LA.dab.and_tt(Maybe.is_some(&2, Nat, DashAccess.sp_scheme(sc)), Bool.and(DashAccess.sp_well(wa), DashAccess.sp_well(wb)), es, LA.dab.and_tt(DashAccess.sp_well(wa), DashAccess.sp_well(wb), la, lb)))))

# the page's authority read as one; now the `Host`'s
def dgo.pair2(-o: String, +sc: String, -au: String, -h: String, -d: Nat, -n1: String, -p1: Maybe<&2, Nat>, eo: {o == String.append(sc, SCon{':', SCon{'/', SCon{'/', au}}}) : String}, esm: {Ac.scheme(sc) == Some{d} : Maybe<&2, Nat>}, mb: Ac.Authority, spb: LA.dab.SP(h, mb), spa: Sigma<&1, &1, DashAccess.SpAuth, w => {au == DashAccess.sp_spell(w) : String} & {DashAccess.sp_well(w) == True{} : Bool}>, yes: {Ac.origin.pair(d, Ac.HostPort{n1, p1}, mb) == True{} : Bool}) -> Sigma<&1, &1, DashAccess.SpOrigin, w => {o == DashAccess.sp_o_origin(w) : String} & {h == DashAccess.sp_o_host(w) : String} & {DashAccess.sp_o_ok(w) == True{} : Bool}>:
  match mb:
    case Ac.HostPort{n2, p2}:
      dgo.mk(o, sc, au, h, d, eo, esm, spa, spb)
    case Ac.NoAuthority{}:
      LA.dab.absurdF(Sigma<&1, &1, DashAccess.SpOrigin, w => {o == DashAccess.sp_o_origin(w) : String} & {h == DashAccess.sp_o_host(w) : String} & {DashAccess.sp_o_ok(w) == True{} : Bool}>, yes)

def dgo.pair(-o: String, +sc: String, -au: String, -h: String, -d: Nat, eo: {o == String.append(sc, SCon{':', SCon{'/', SCon{'/', au}}}) : String}, esm: {Ac.scheme(sc) == Some{d} : Maybe<&2, Nat>}, ma: Ac.Authority, spa: LA.dab.SP(au, ma), mb: Ac.Authority, spb: LA.dab.SP(h, mb), yes: {Ac.origin.pair(d, ma, mb) == True{} : Bool}) -> Sigma<&1, &1, DashAccess.SpOrigin, w => {o == DashAccess.sp_o_origin(w) : String} & {h == DashAccess.sp_o_host(w) : String} & {DashAccess.sp_o_ok(w) == True{} : Bool}>:
  match ma:
    case Ac.HostPort{n1, p1}:
      dgo.pair2(o, sc, au, h, d, n1, p1, eo, esm, mb, spb, spa, yes)
    case Ac.NoAuthority{}:
      match mb:
        case Ac.HostPort{n2, p2}:
          LA.dab.absurdF(Sigma<&1, &1, DashAccess.SpOrigin, w => {o == DashAccess.sp_o_origin(w) : String} & {h == DashAccess.sp_o_host(w) : String} & {DashAccess.sp_o_ok(w) == True{} : Bool}>, yes)
        case Ac.NoAuthority{}:
          LA.dab.absurdF(Sigma<&1, &1, DashAccess.SpOrigin, w => {o == DashAccess.sp_o_origin(w) : String} & {h == DashAccess.sp_o_host(w) : String} & {DashAccess.sp_o_ok(w) == True{} : Bool}>, yes)

def dgo.port(-o: String, +sc: String, +au: String, +h: String, eo: {o == String.append(sc, SCon{':', SCon{'/', SCon{'/', au}}}) : String}, sm: Maybe<&2, Nat>, esm: {Ac.scheme(sc) == sm : Maybe<&2, Nat>}, yes: {Ac.origin.port(sm, au, h) == True{} : Bool}) -> Sigma<&1, &1, DashAccess.SpOrigin, w => {o == DashAccess.sp_o_origin(w) : String} & {h == DashAccess.sp_o_host(w) : String} & {DashAccess.sp_o_ok(w) == True{} : Bool}>:
  match sm:
    case None{}:
      LA.dab.absurdF(Sigma<&1, &1, DashAccess.SpOrigin, w => {o == DashAccess.sp_o_origin(w) : String} & {h == DashAccess.sp_o_host(w) : String} & {DashAccess.sp_o_ok(w) == True{} : Bool}>, yes)
    case Some{+d}:
      dgo.pair(o, sc, au, h, d, eo, esm, Ac.split(au), LA.dab.split_inv(au), Ac.split(h), LA.dab.split_inv(h), yes)

def dgo.sep(-o: String, m: Maybe<&2, Ac.Cut>, sp: LA.dab.SepP(o, m), +h: String, yes: {Ac.origin.sep(m, h) == True{} : Bool}) -> Sigma<&1, &1, DashAccess.SpOrigin, w => {o == DashAccess.sp_o_origin(w) : String} & {h == DashAccess.sp_o_host(w) : String} & {DashAccess.sp_o_ok(w) == True{} : Bool}>:
  match m:
    case None{}:
      LA.dab.absurdF(Sigma<&1, &1, DashAccess.SpOrigin, w => {o == DashAccess.sp_o_origin(w) : String} & {h == DashAccess.sp_o_host(w) : String} & {DashAccess.sp_o_ok(w) == True{} : Bool}>, yes)
    case Some{p}:
      match p:
        case Ac.Cut{+sc, +au}:
          dgo.port(o, sc, au, h, sp, Ac.scheme(sc), {==}, yes)

def DashAccess.dash_access_origin_only_spelled(o, h, yes):
  dgo.sep(o, Ac.sep(o), LA.dab.sep_inv(o), h, yes)
