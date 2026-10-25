# eukhe: lemmas the proofs of area cvar_layers share: the entry's reader
# answers what the laws' reader answers on every input (one lemma per
# stage, each a case split on the stage's input), the entry reads back
# what the laws' spellers write, and its reply writers write what the
# laws' spellers write.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar_layers.bend as FCL
import ../../bend/wire.bend as Wr
import ../../laws/cvar_layers.bend as Cl
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../cvar/base.bend as LA

# Logic
# -----

def cl.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# a claim that Some is None proves anything
def cl.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : cl.if_none(A, _, G)
  Unit{}

# The reader, stage by stage
# --------------------------

def cl.v_nat(r: Wr.Dec<Nat>) -> {Cl.read_val.nat(r) == FCL.get_val.nat(r) : Wr.Dec<Cv.Val>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.v_bool(r: Wr.Dec<Bool>) -> {Cl.read_val.bool(r) == FCL.get_val.bool(r) : Wr.Dec<Cv.Val>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.v_tag(t: Nat, +s: String) -> {Cl.read_val.tag(t, s) == FCL.get_val.tag(t, s) : Wr.Dec<Cv.Val>}:
  match t:
    case 0n:
      cl.v_nat(Wr.get_nat(s))
    case 1n:
      cl.v_bool(Wr.get_bool(s))
    case 2n+p:
      {==}

def cl.v(r: Wr.Dec<Nat>) -> {Cl.read_val(r) == FCL.get_val.go(r) : Wr.Dec<Cv.Val>}:
  match r:
    case Wr.Got{t, s}:
      cl.v_tag(t, s)
    case Wr.Bad{}:
      {==}

def cl.ty_tag(t: Nat, +s: String) -> {Cl.read_ty.tag(t, s) == FCL.get_ty.tag(t, s) : Wr.Dec<Cv.Ty>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def cl.ty(r: Wr.Dec<Nat>) -> {Cl.read_ty(r) == FCL.get_ty.go(r) : Wr.Dec<Cv.Ty>}:
  match r:
    case Wr.Got{t, s}:
      cl.ty_tag(t, s)
    case Wr.Bad{}:
      {==}

def cl.scope_tag(t: Nat, +s: String) -> {Cl.read_scope.tag(t, s) == FCL.get_scope.tag(t, s) : Wr.Dec<Cv.Scope>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def cl.scope(r: Wr.Dec<Nat>) -> {Cl.read_scope(r) == FCL.get_scope.go(r) : Wr.Dec<Cv.Scope>}:
  match r:
    case Wr.Got{t, s}:
      cl.scope_tag(t, s)
    case Wr.Bad{}:
      {==}

def cl.layer_tag(t: Nat, +s: String) -> {Cl.read_layer.tag(t, s) == FCL.get_layer.tag(t, s) : Wr.Dec<Cv.Layer>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def cl.layer(r: Wr.Dec<Nat>) -> {Cl.read_layer(r) == FCL.get_layer.go(r) : Wr.Dec<Cv.Layer>}:
  match r:
    case Wr.Got{t, s}:
      cl.layer_tag(t, s)
    case Wr.Bad{}:
      {==}

def cl.flag_tag(t: Nat, +s: String) -> {Cl.read_flag.tag(t, s) == FCL.get_flag.tag(t, s) : Wr.Dec<Cv.Flag>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def cl.flag(r: Wr.Dec<Nat>) -> {Cl.read_flag(r) == FCL.get_flag.go(r) : Wr.Dec<Cv.Flag>}:
  match r:
    case Wr.Got{t, s}:
      cl.flag_tag(t, s)
    case Wr.Bad{}:
      {==}

def cl.d_init(i: Nat, t: Cv.Ty, c: Cv.Scope, p: Bool, q: Bool, r: Wr.Dec<Cv.Val>) -> {Cl.read_decl.init(i, t, c, p, q, r) == FCL.get_decl.init(i, t, c, p, q, r) : Wr.Dec<Cv.Decl>}:
  match r:
    case Wr.Got{v, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.d_rep(+i: Nat, +t: Cv.Ty, +c: Cv.Scope, +p: Bool, r: Wr.Dec<Bool>) -> {Cl.read_decl.rep(i, t, c, p, r) == FCL.get_decl.rep(i, t, c, p, r) : Wr.Dec<Cv.Decl>}:
  match r:
    case Wr.Got{+q, +s}:
      %cl.v(Wr.get_nat(s)) : {Cl.read_decl.init(i, t, c, p, q, Cl.read_val(Wr.get_nat(s))) == FCL.get_decl.init(i, t, c, p, q, _) : Wr.Dec<Cv.Decl>}
      %cl.d_init(i, t, c, p, q, Cl.read_val(Wr.get_nat(s))) : {Cl.read_decl.init(i, t, c, p, q, Cl.read_val(Wr.get_nat(s))) == _ : Wr.Dec<Cv.Decl>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.d_per(+i: Nat, +t: Cv.Ty, +c: Cv.Scope, r: Wr.Dec<Bool>) -> {Cl.read_decl.per(i, t, c, r) == FCL.get_decl.per(i, t, c, r) : Wr.Dec<Cv.Decl>}:
  match r:
    case Wr.Got{p, s}:
      cl.d_rep(i, t, c, p, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def cl.d_scope(+i: Nat, +t: Cv.Ty, r: Wr.Dec<Cv.Scope>) -> {Cl.read_decl.scope(i, t, r) == FCL.get_decl.scope(i, t, r) : Wr.Dec<Cv.Decl>}:
  match r:
    case Wr.Got{c, s}:
      cl.d_per(i, t, c, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def cl.d_ty(+i: Nat, r: Wr.Dec<Cv.Ty>) -> {Cl.read_decl.ty(i, r) == FCL.get_decl.ty(i, r) : Wr.Dec<Cv.Decl>}:
  match r:
    case Wr.Got{+t, +s}:
      %cl.scope(Wr.get_nat(s)) : {Cl.read_decl.scope(i, t, Cl.read_scope(Wr.get_nat(s))) == FCL.get_decl.scope(i, t, _) : Wr.Dec<Cv.Decl>}
      %cl.d_scope(i, t, Cl.read_scope(Wr.get_nat(s))) : {Cl.read_decl.scope(i, t, Cl.read_scope(Wr.get_nat(s))) == _ : Wr.Dec<Cv.Decl>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.d_id(r: Wr.Dec<Nat>) -> {Cl.read_decl.id(r) == FCL.get_decl.id(r) : Wr.Dec<Cv.Decl>}:
  match r:
    case Wr.Got{+i, +s}:
      %cl.ty(Wr.get_nat(s)) : {Cl.read_decl.ty(i, Cl.read_ty(Wr.get_nat(s))) == FCL.get_decl.ty(i, _) : Wr.Dec<Cv.Decl>}
      %cl.d_ty(i, Cl.read_ty(Wr.get_nat(s))) : {Cl.read_decl.ty(i, Cl.read_ty(Wr.get_nat(s))) == _ : Wr.Dec<Cv.Decl>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.d(+s: String) -> {Cl.read_decl(s) == FCL.get_decl(s) : Wr.Dec<Cv.Decl>}:
  cl.d_id(Wr.get_nat(s))

def cl.ds_cons(x: Cv.Decl, r: Wr.Dec<List<&2, Cv.Decl>>) -> {Cl.read_decls.cons(x, r) == FCL.get_decls.cons(x, r) : Wr.Dec<List<&2, Cv.Decl>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.ds_go(n: Nat, cur: Wr.Dec<Cv.Decl>) -> {Cl.read_decls.go(n, cur) == FCL.get_decls.go(n, cur) : Wr.Dec<List<&2, Cv.Decl>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+x, +s}:
          %cl.d(s) : {Cl.read_decls.cons(x, Cl.read_decls.go(m, Cl.read_decl(s))) == FCL.get_decls.cons(x, FCL.get_decls.go(m, _)) : Wr.Dec<List<&2, Cv.Decl>>}
          %cl.ds_go(m, Cl.read_decl(s)) : {Cl.read_decls.cons(x, Cl.read_decls.go(m, Cl.read_decl(s))) == FCL.get_decls.cons(x, _) : Wr.Dec<List<&2, Cv.Decl>>}
          %cl.ds_cons(x, Cl.read_decls.go(m, Cl.read_decl(s))) : {Cl.read_decls.cons(x, Cl.read_decls.go(m, Cl.read_decl(s))) == _ : Wr.Dec<List<&2, Cv.Decl>>}
          {==}
        case Wr.Bad{}:
          {==}

def cl.ds(r: Wr.Dec<Nat>) -> {Cl.read_decls(r) == FCL.get_decls(r) : Wr.Dec<List<&2, Cv.Decl>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %cl.d(s) : {Cl.read_decls.go(m, Cl.read_decl(s)) == FCL.get_decls.go(m, _) : Wr.Dec<List<&2, Cv.Decl>>}
          cl.ds_go(m, Cl.read_decl(s))
    case Wr.Bad{}:
      {==}

def cl.b_val(i: Nat, r: Wr.Dec<Cv.Val>) -> {Cl.read_bind.val(i, r) == FCL.get_bind.val(i, r) : Wr.Dec<Cv.Bind>}:
  match r:
    case Wr.Got{v, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.b_id(r: Wr.Dec<Nat>) -> {Cl.read_bind.id(r) == FCL.get_bind.id(r) : Wr.Dec<Cv.Bind>}:
  match r:
    case Wr.Got{+i, +s}:
      %cl.v(Wr.get_nat(s)) : {Cl.read_bind.val(i, Cl.read_val(Wr.get_nat(s))) == FCL.get_bind.val(i, _) : Wr.Dec<Cv.Bind>}
      %cl.b_val(i, Cl.read_val(Wr.get_nat(s))) : {Cl.read_bind.val(i, Cl.read_val(Wr.get_nat(s))) == _ : Wr.Dec<Cv.Bind>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.b(+s: String) -> {Cl.read_bind(s) == FCL.get_bind(s) : Wr.Dec<Cv.Bind>}:
  cl.b_id(Wr.get_nat(s))

def cl.bs_cons(x: Cv.Bind, r: Wr.Dec<List<&2, Cv.Bind>>) -> {Cl.read_binds.cons(x, r) == FCL.get_binds.cons(x, r) : Wr.Dec<List<&2, Cv.Bind>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.bs_go(n: Nat, cur: Wr.Dec<Cv.Bind>) -> {Cl.read_binds.go(n, cur) == FCL.get_binds.go(n, cur) : Wr.Dec<List<&2, Cv.Bind>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+x, +s}:
          %cl.b(s) : {Cl.read_binds.cons(x, Cl.read_binds.go(m, Cl.read_bind(s))) == FCL.get_binds.cons(x, FCL.get_binds.go(m, _)) : Wr.Dec<List<&2, Cv.Bind>>}
          %cl.bs_go(m, Cl.read_bind(s)) : {Cl.read_binds.cons(x, Cl.read_binds.go(m, Cl.read_bind(s))) == FCL.get_binds.cons(x, _) : Wr.Dec<List<&2, Cv.Bind>>}
          %cl.bs_cons(x, Cl.read_binds.go(m, Cl.read_bind(s))) : {Cl.read_binds.cons(x, Cl.read_binds.go(m, Cl.read_bind(s))) == _ : Wr.Dec<List<&2, Cv.Bind>>}
          {==}
        case Wr.Bad{}:
          {==}

def cl.bs(r: Wr.Dec<Nat>) -> {Cl.read_binds(r) == FCL.get_binds(r) : Wr.Dec<List<&2, Cv.Bind>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %cl.b(s) : {Cl.read_binds.go(m, Cl.read_bind(s)) == FCL.get_binds.go(m, _) : Wr.Dec<List<&2, Cv.Bind>>}
          cl.bs_go(m, Cl.read_bind(s))
    case Wr.Bad{}:
      {==}

def cl.a_sets(p: List<&2, Cv.Bind>, r: Wr.Dec<List<&2, Cv.Bind>>) -> {Cl.read_ag.sets(p, r) == FCL.get_ag.sets(p, r) : Wr.Dec<Cv.Ag>}:
  match r:
    case Wr.Got{ss, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.a_profile(r: Wr.Dec<List<&2, Cv.Bind>>) -> {Cl.read_ag.profile(r) == FCL.get_ag.profile(r) : Wr.Dec<Cv.Ag>}:
  match r:
    case Wr.Got{+p, +s}:
      %cl.bs(Wr.get_nat(s)) : {Cl.read_ag.sets(p, Cl.read_binds(Wr.get_nat(s))) == FCL.get_ag.sets(p, _) : Wr.Dec<Cv.Ag>}
      %cl.a_sets(p, Cl.read_binds(Wr.get_nat(s))) : {Cl.read_ag.sets(p, Cl.read_binds(Wr.get_nat(s))) == _ : Wr.Dec<Cv.Ag>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.a(+s: String) -> {Cl.read_ag(s) == FCL.get_ag(s) : Wr.Dec<Cv.Ag>}:
  %cl.bs(Wr.get_nat(s)) : {Cl.read_ag.profile(Cl.read_binds(Wr.get_nat(s))) == FCL.get_ag.profile(_) : Wr.Dec<Cv.Ag>}
  %cl.a_profile(Cl.read_binds(Wr.get_nat(s))) : {Cl.read_ag.profile(Cl.read_binds(Wr.get_nat(s))) == _ : Wr.Dec<Cv.Ag>}
  {==}

def cl.as_cons(x: Cv.Ag, r: Wr.Dec<List<&2, Cv.Ag>>) -> {Cl.read_ags.cons(x, r) == FCL.get_ags.cons(x, r) : Wr.Dec<List<&2, Cv.Ag>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.as_go(n: Nat, cur: Wr.Dec<Cv.Ag>) -> {Cl.read_ags.go(n, cur) == FCL.get_ags.go(n, cur) : Wr.Dec<List<&2, Cv.Ag>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+x, +s}:
          %cl.a(s) : {Cl.read_ags.cons(x, Cl.read_ags.go(m, Cl.read_ag(s))) == FCL.get_ags.cons(x, FCL.get_ags.go(m, _)) : Wr.Dec<List<&2, Cv.Ag>>}
          %cl.as_go(m, Cl.read_ag(s)) : {Cl.read_ags.cons(x, Cl.read_ags.go(m, Cl.read_ag(s))) == FCL.get_ags.cons(x, _) : Wr.Dec<List<&2, Cv.Ag>>}
          %cl.as_cons(x, Cl.read_ags.go(m, Cl.read_ag(s))) : {Cl.read_ags.cons(x, Cl.read_ags.go(m, Cl.read_ag(s))) == _ : Wr.Dec<List<&2, Cv.Ag>>}
          {==}
        case Wr.Bad{}:
          {==}

def cl.as(r: Wr.Dec<Nat>) -> {Cl.read_ags(r) == FCL.get_ags(r) : Wr.Dec<List<&2, Cv.Ag>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %cl.a(s) : {Cl.read_ags.go(m, Cl.read_ag(s)) == FCL.get_ags.go(m, _) : Wr.Dec<List<&2, Cv.Ag>>}
          cl.as_go(m, Cl.read_ag(s))
    case Wr.Bad{}:
      {==}

def cl.reg(r: Wr.Dec<List<&2, Cv.Decl>>) -> {Cl.read_reg(r) == FCL.get_reg(r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{ds, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.vals_fam(ds: List<&2, Cv.Decl>, c: List<&2, Cv.Bind>, r: Wr.Dec<List<&2, Cv.Ag>>) -> {Cl.read_vals.fam(ds, c, r) == FCL.get_vals.fam(ds, c, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.vals_cfg(+ds: List<&2, Cv.Decl>, r: Wr.Dec<List<&2, Cv.Bind>>) -> {Cl.read_vals.cfg(ds, r) == FCL.get_vals.cfg(ds, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+c, +s}:
      %cl.as(Wr.get_nat(s)) : {Cl.read_vals.fam(ds, c, Cl.read_ags(Wr.get_nat(s))) == FCL.get_vals.fam(ds, c, _) : Wr.Dec<FCL.Ask>}
      %cl.vals_fam(ds, c, Cl.read_ags(Wr.get_nat(s))) : {Cl.read_vals.fam(ds, c, Cl.read_ags(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.vals(r: Wr.Dec<List<&2, Cv.Decl>>) -> {Cl.read_vals(r) == FCL.get_vals(r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+ds, +s}:
      %cl.bs(Wr.get_nat(s)) : {Cl.read_vals.cfg(ds, Cl.read_binds(Wr.get_nat(s))) == FCL.get_vals.cfg(ds, _) : Wr.Dec<FCL.Ask>}
      %cl.vals_cfg(ds, Cl.read_binds(Wr.get_nat(s))) : {Cl.read_vals.cfg(ds, Cl.read_binds(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.tog_id(ds: List<&2, Cv.Decl>, c: List<&2, Cv.Bind>, f: List<&2, Cv.Ag>, l: Cv.Layer, r: Wr.Dec<Nat>) -> {Cl.read_tog.id(ds, c, f, l, r) == FCL.get_tog.id(ds, c, f, l, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.tog_layer(+ds: List<&2, Cv.Decl>, +c: List<&2, Cv.Bind>, +f: List<&2, Cv.Ag>, r: Wr.Dec<Cv.Layer>) -> {Cl.read_tog.layer(ds, c, f, r) == FCL.get_tog.layer(ds, c, f, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{l, s}:
      cl.tog_id(ds, c, f, l, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cl.tog_fam(+ds: List<&2, Cv.Decl>, +c: List<&2, Cv.Bind>, r: Wr.Dec<List<&2, Cv.Ag>>) -> {Cl.read_tog.fam(ds, c, r) == FCL.get_tog.fam(ds, c, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+f, +s}:
      %cl.layer(Wr.get_nat(s)) : {Cl.read_tog.layer(ds, c, f, Cl.read_layer(Wr.get_nat(s))) == FCL.get_tog.layer(ds, c, f, _) : Wr.Dec<FCL.Ask>}
      %cl.tog_layer(ds, c, f, Cl.read_layer(Wr.get_nat(s))) : {Cl.read_tog.layer(ds, c, f, Cl.read_layer(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.tog_cfg(+ds: List<&2, Cv.Decl>, r: Wr.Dec<List<&2, Cv.Bind>>) -> {Cl.read_tog.cfg(ds, r) == FCL.get_tog.cfg(ds, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+c, +s}:
      %cl.as(Wr.get_nat(s)) : {Cl.read_tog.fam(ds, c, Cl.read_ags(Wr.get_nat(s))) == FCL.get_tog.fam(ds, c, _) : Wr.Dec<FCL.Ask>}
      %cl.tog_fam(ds, c, Cl.read_ags(Wr.get_nat(s))) : {Cl.read_tog.fam(ds, c, Cl.read_ags(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.tog(r: Wr.Dec<List<&2, Cv.Decl>>) -> {Cl.read_tog(r) == FCL.get_tog(r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+ds, +s}:
      %cl.bs(Wr.get_nat(s)) : {Cl.read_tog.cfg(ds, Cl.read_binds(Wr.get_nat(s))) == FCL.get_tog.cfg(ds, _) : Wr.Dec<FCL.Ask>}
      %cl.tog_cfg(ds, Cl.read_binds(Wr.get_nat(s))) : {Cl.read_tog.cfg(ds, Cl.read_binds(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.chk_set(ds: List<&2, Cv.Decl>, l: Cv.Layer, r: Wr.Dec<Cv.Bind>) -> {Cl.read_chk.set(ds, l, r) == FCL.get_chk.set(ds, l, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.chk_layer(+ds: List<&2, Cv.Decl>, r: Wr.Dec<Cv.Layer>) -> {Cl.read_chk.layer(ds, r) == FCL.get_chk.layer(ds, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+l, +s}:
      %cl.b(s) : {Cl.read_chk.set(ds, l, Cl.read_bind(s)) == FCL.get_chk.set(ds, l, _) : Wr.Dec<FCL.Ask>}
      %cl.chk_set(ds, l, Cl.read_bind(s)) : {Cl.read_chk.set(ds, l, Cl.read_bind(s)) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.chk(r: Wr.Dec<List<&2, Cv.Decl>>) -> {Cl.read_chk(r) == FCL.get_chk(r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+ds, +s}:
      %cl.layer(Wr.get_nat(s)) : {Cl.read_chk.layer(ds, Cl.read_layer(Wr.get_nat(s))) == FCL.get_chk.layer(ds, _) : Wr.Dec<FCL.Ask>}
      %cl.chk_layer(ds, Cl.read_layer(Wr.get_nat(s))) : {Cl.read_chk.layer(ds, Cl.read_layer(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.wr_flag(ds: List<&2, Cv.Decl>, ss: List<&2, Cv.Bind>, r: Wr.Dec<Cv.Flag>) -> {Cl.read_wr.flag(ds, ss, r) == FCL.get_wr.flag(ds, ss, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{g, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.wr_sets(+ds: List<&2, Cv.Decl>, r: Wr.Dec<List<&2, Cv.Bind>>) -> {Cl.read_wr.sets(ds, r) == FCL.get_wr.sets(ds, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+ss, +s}:
      %cl.flag(Wr.get_nat(s)) : {Cl.read_wr.flag(ds, ss, Cl.read_flag(Wr.get_nat(s))) == FCL.get_wr.flag(ds, ss, _) : Wr.Dec<FCL.Ask>}
      %cl.wr_flag(ds, ss, Cl.read_flag(Wr.get_nat(s))) : {Cl.read_wr.flag(ds, ss, Cl.read_flag(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.wr(r: Wr.Dec<List<&2, Cv.Decl>>) -> {Cl.read_wr(r) == FCL.get_wr(r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+ds, +s}:
      %cl.bs(Wr.get_nat(s)) : {Cl.read_wr.sets(ds, Cl.read_binds(Wr.get_nat(s))) == FCL.get_wr.sets(ds, _) : Wr.Dec<FCL.Ask>}
      %cl.wr_sets(ds, Cl.read_binds(Wr.get_nat(s))) : {Cl.read_wr.sets(ds, Cl.read_binds(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.doc_global(ds: List<&2, Cv.Decl>, m: List<&2, Cv.Bind>, r: Wr.Dec<List<&2, Cv.Bind>>) -> {Cl.read_doc.global(ds, m, r) == FCL.get_doc.global(ds, m, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{g, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cl.doc_merged(+ds: List<&2, Cv.Decl>, r: Wr.Dec<List<&2, Cv.Bind>>) -> {Cl.read_doc.merged(ds, r) == FCL.get_doc.merged(ds, r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+m, +s}:
      %cl.bs(Wr.get_nat(s)) : {Cl.read_doc.global(ds, m, Cl.read_binds(Wr.get_nat(s))) == FCL.get_doc.global(ds, m, _) : Wr.Dec<FCL.Ask>}
      %cl.doc_global(ds, m, Cl.read_binds(Wr.get_nat(s))) : {Cl.read_doc.global(ds, m, Cl.read_binds(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.doc(r: Wr.Dec<List<&2, Cv.Decl>>) -> {Cl.read_doc(r) == FCL.get_doc(r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{+ds, +s}:
      %cl.bs(Wr.get_nat(s)) : {Cl.read_doc.merged(ds, Cl.read_binds(Wr.get_nat(s))) == FCL.get_doc.merged(ds, _) : Wr.Dec<FCL.Ask>}
      %cl.doc_merged(ds, Cl.read_binds(Wr.get_nat(s))) : {Cl.read_doc.merged(ds, Cl.read_binds(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def cl.ask_tag(t: Nat, +s: String) -> {Cl.read_ask.tag(t, s) == FCL.get_ask.tag(t, s) : Wr.Dec<FCL.Ask>}:
  match t:
    case 0n:
      %cl.ds(Wr.get_nat(s)) : {Cl.read_reg(Cl.read_decls(Wr.get_nat(s))) == FCL.get_reg(_) : Wr.Dec<FCL.Ask>}
      %cl.reg(Cl.read_decls(Wr.get_nat(s))) : {Cl.read_reg(Cl.read_decls(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case 1n:
      %cl.ds(Wr.get_nat(s)) : {Cl.read_vals(Cl.read_decls(Wr.get_nat(s))) == FCL.get_vals(_) : Wr.Dec<FCL.Ask>}
      %cl.vals(Cl.read_decls(Wr.get_nat(s))) : {Cl.read_vals(Cl.read_decls(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case 2n:
      %cl.ds(Wr.get_nat(s)) : {Cl.read_tog(Cl.read_decls(Wr.get_nat(s))) == FCL.get_tog(_) : Wr.Dec<FCL.Ask>}
      %cl.tog(Cl.read_decls(Wr.get_nat(s))) : {Cl.read_tog(Cl.read_decls(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case 3n:
      %cl.ds(Wr.get_nat(s)) : {Cl.read_chk(Cl.read_decls(Wr.get_nat(s))) == FCL.get_chk(_) : Wr.Dec<FCL.Ask>}
      %cl.chk(Cl.read_decls(Wr.get_nat(s))) : {Cl.read_chk(Cl.read_decls(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case 4n:
      %cl.ds(Wr.get_nat(s)) : {Cl.read_wr(Cl.read_decls(Wr.get_nat(s))) == FCL.get_wr(_) : Wr.Dec<FCL.Ask>}
      %cl.wr(Cl.read_decls(Wr.get_nat(s))) : {Cl.read_wr(Cl.read_decls(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case 5n:
      %cl.ds(Wr.get_nat(s)) : {Cl.read_doc(Cl.read_decls(Wr.get_nat(s))) == FCL.get_doc(_) : Wr.Dec<FCL.Ask>}
      %cl.doc(Cl.read_decls(Wr.get_nat(s))) : {Cl.read_doc(Cl.read_decls(Wr.get_nat(s))) == _ : Wr.Dec<FCL.Ask>}
      {==}
    case 6n+p:
      {==}

# the entry reads every input as the laws' reader does
def cl.ask(r: Wr.Dec<Nat>) -> {Cl.read_ask.go(r) == FCL.get_ask.go(r) : Wr.Dec<FCL.Ask>}:
  match r:
    case Wr.Got{t, s}:
      cl.ask_tag(t, s)
    case Wr.Bad{}:
      {==}


# Round trips
# -----------

def cl.and_l(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  LA.cvar.pv.and_l(a, b, h)

def cl.and_r(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  LA.cvar.pv.and_r(a, b, h)

# a Bool reads back, whatever follows it
def cl.bool_rt(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

def cl.val_rt(v: Cv.Val, +rest: String, h: {Cl.val_fits(v) == True{} : Bool}) -> {Wr.Got{v, rest} == FCL.get_val(Cl.spell_val(v, rest)) : Wr.Dec<Cv.Val>}:
  match v:
    case Cv.VNat{+n}:
      %LWire.pw6.nat(0n, Wr.put_nat(n, rest), {==}) : {Wr.Got{Cv.VNat{n}, rest} == FCL.get_val.go(_) : Wr.Dec<Cv.Val>}
      %LWire.pw6.nat(n, rest, h) : {Wr.Got{Cv.VNat{n}, rest} == FCL.get_val.nat(_) : Wr.Dec<Cv.Val>}
      {==}
    case Cv.VBool{+b}:
      %LWire.pw6.nat(1n, Wr.put_bool(b, rest), {==}) : {Wr.Got{Cv.VBool{b}, rest} == FCL.get_val.go(_) : Wr.Dec<Cv.Val>}
      %cl.bool_rt(b, rest) : {Wr.Got{Cv.VBool{b}, rest} == FCL.get_val.bool(_) : Wr.Dec<Cv.Val>}
      {==}

def cl.ty_rt(t: Cv.Ty, rest: String) -> {Wr.Got{t, rest} == FCL.get_ty.go(Wr.get_nat(Cl.spell_ty(t, rest))) : Wr.Dec<Cv.Ty>}:
  match t:
    case Cv.TNat{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Cv.TNat{}, rest} == FCL.get_ty.go(_) : Wr.Dec<Cv.Ty>}
      {==}
    case Cv.TBool{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Cv.TBool{}, rest} == FCL.get_ty.go(_) : Wr.Dec<Cv.Ty>}
      {==}

def cl.scope_rt(c: Cv.Scope, rest: String) -> {Wr.Got{c, rest} == FCL.get_scope.go(Wr.get_nat(Cl.spell_scope(c, rest))) : Wr.Dec<Cv.Scope>}:
  match c:
    case Cv.Global{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Cv.Global{}, rest} == FCL.get_scope.go(_) : Wr.Dec<Cv.Scope>}
      {==}
    case Cv.Local{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Cv.Local{}, rest} == FCL.get_scope.go(_) : Wr.Dec<Cv.Scope>}
      {==}

def cl.layer_rt(l: Cv.Layer, rest: String) -> {Wr.Got{l, rest} == FCL.get_layer.go(Wr.get_nat(Cl.spell_layer(l, rest))) : Wr.Dec<Cv.Layer>}:
  match l:
    case Cv.Config{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Cv.Config{}, rest} == FCL.get_layer.go(_) : Wr.Dec<Cv.Layer>}
      {==}
    case Cv.Agent{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Cv.Agent{}, rest} == FCL.get_layer.go(_) : Wr.Dec<Cv.Layer>}
      {==}

def cl.flag_rt(f: Cv.Flag, rest: String) -> {Wr.Got{f, rest} == FCL.get_flag.go(Wr.get_nat(Cl.spell_flag(f, rest))) : Wr.Dec<Cv.Flag>}:
  match f:
    case Cv.Persist{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Cv.Persist{}, rest} == FCL.get_flag.go(_) : Wr.Dec<Cv.Flag>}
      {==}
    case Cv.Replicate{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Cv.Replicate{}, rest} == FCL.get_flag.go(_) : Wr.Dec<Cv.Flag>}
      {==}

# a declaration the laws spell reads back, whatever follows it
def cl.decl_rt(d: Cv.Decl, +rest: String, +h: {Cl.decl_fits(d) == True{} : Bool}) -> {Wr.Got{d, rest} == FCL.get_decl(Cl.spell_decl(d, rest)) : Wr.Dec<Cv.Decl>}:
  match d:
    case Cv.Decl{+i, +t, +c, +p, +r, +v}:
      +z4 = Cl.spell_val(v, rest)
      +z3 = Wr.put_bool(r, z4)
      +z2 = Wr.put_bool(p, z3)
      +z1 = Cl.spell_scope(c, z2)
      +z0 = Cl.spell_ty(t, z1)
      +g = {Wr.Got{Cv.Decl{i, t, c, p, r, v}, rest} : Wr.Dec<Cv.Decl>}
      %LWire.pw6.nat(i, z0, cl.and_l(LawsBase.wire_fits(i), Cl.val_fits(v), h)) : {g == FCL.get_decl.id(_) : Wr.Dec<Cv.Decl>}
      %cl.ty_rt(t, z1) : {g == FCL.get_decl.ty(i, _) : Wr.Dec<Cv.Decl>}
      %cl.scope_rt(c, z2) : {g == FCL.get_decl.scope(i, t, _) : Wr.Dec<Cv.Decl>}
      %cl.bool_rt(p, z3) : {g == FCL.get_decl.per(i, t, c, _) : Wr.Dec<Cv.Decl>}
      %cl.bool_rt(r, z4) : {g == FCL.get_decl.rep(i, t, c, p, _) : Wr.Dec<Cv.Decl>}
      %cl.val_rt(v, rest, cl.and_r(LawsBase.wire_fits(i), Cl.val_fits(v), h)) : {g == FCL.get_decl.init(i, t, c, p, r, _) : Wr.Dec<Cv.Decl>}
      {==}

# a set the laws spell reads back, whatever follows it
def cl.bind_rt(b: Cv.Bind, +rest: String, +h: {Cl.bind_fits(b) == True{} : Bool}) -> {Wr.Got{b, rest} == FCL.get_bind(Cl.spell_bind(b, rest)) : Wr.Dec<Cv.Bind>}:
  match b:
    case Cv.Bind{+i, +v}:
      +g = {Wr.Got{Cv.Bind{i, v}, rest} : Wr.Dec<Cv.Bind>}
      %LWire.pw6.nat(i, Cl.spell_val(v, rest), cl.and_l(LawsBase.wire_fits(i), Cl.val_fits(v), h)) : {g == FCL.get_bind.id(_) : Wr.Dec<Cv.Bind>}
      %cl.val_rt(v, rest, cl.and_r(LawsBase.wire_fits(i), Cl.val_fits(v), h)) : {g == FCL.get_bind.val(i, _) : Wr.Dec<Cv.Bind>}
      {==}

# the items after the first read back, the first one being x
def cl.decls_rt(t: List<&2, Cv.Decl>, +x: Cv.Decl, +rest: String, +h: {Cl.decls_all(x <> t) == True{} : Bool}) -> {Wr.Got{x <> t, rest} == FCL.get_decls.go(List.length(&2, Cv.Decl, t), FCL.get_decl(Cl.spell_decl(x, Cl.spell_decls.items(t, rest)))) : Wr.Dec<List<&2, Cv.Decl>>}:
  match t:
    case Nil{}:
      %cl.decl_rt(x, rest, cl.and_l(Cl.decl_fits(x), True{}, h)) : {Wr.Got{[x], rest} == FCL.get_decls.go(0n, _) : Wr.Dec<List<&2, Cv.Decl>>}
      {==}
    case +y <> +u:
      %cl.decl_rt(x, Cl.spell_decl(y, Cl.spell_decls.items(u, rest)), cl.and_l(Cl.decl_fits(x), Cl.decls_all(y <> u), h)) : {Wr.Got{x <> y <> u, rest} == FCL.get_decls.go(1n+List.length(&2, Cv.Decl, u), _) : Wr.Dec<List<&2, Cv.Decl>>}
      %cl.decls_rt(u, y, rest, cl.and_r(Cl.decl_fits(x), Cl.decls_all(y <> u), h)) : {Wr.Got{x <> y <> u, rest} == FCL.get_decls.cons(x, _) : Wr.Dec<List<&2, Cv.Decl>>}
      {==}

# a list the laws spell reads back, whatever follows it
def cl.decls_full(xs: List<&2, Cv.Decl>, +rest: String, +h: {Cl.decls_fit(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == FCL.get_decls(Wr.get_nat(Cl.spell_decls(xs, rest))) : Wr.Dec<List<&2, Cv.Decl>>}:
  match xs:
    case Nil{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Nil{}, rest} == FCL.get_decls(_) : Wr.Dec<List<&2, Cv.Decl>>}
      {==}
    case +x <> +t:
      +n = List.length(&2, Cv.Decl, x <> t)
      %LWire.pw6.nat(n, Cl.spell_decls.items(x <> t, rest), cl.and_l(LawsBase.wire_fits(n), Cl.decls_all(x <> t), h)) : {Wr.Got{x <> t, rest} == FCL.get_decls(_) : Wr.Dec<List<&2, Cv.Decl>>}
      cl.decls_rt(t, x, rest, cl.and_r(LawsBase.wire_fits(n), Cl.decls_all(x <> t), h))

# the items after the first read back, the first one being x
def cl.binds_rt(t: List<&2, Cv.Bind>, +x: Cv.Bind, +rest: String, +h: {Cl.binds_all(x <> t) == True{} : Bool}) -> {Wr.Got{x <> t, rest} == FCL.get_binds.go(List.length(&2, Cv.Bind, t), FCL.get_bind(Cl.spell_bind(x, Cl.spell_binds.items(t, rest)))) : Wr.Dec<List<&2, Cv.Bind>>}:
  match t:
    case Nil{}:
      %cl.bind_rt(x, rest, cl.and_l(Cl.bind_fits(x), True{}, h)) : {Wr.Got{[x], rest} == FCL.get_binds.go(0n, _) : Wr.Dec<List<&2, Cv.Bind>>}
      {==}
    case +y <> +u:
      %cl.bind_rt(x, Cl.spell_bind(y, Cl.spell_binds.items(u, rest)), cl.and_l(Cl.bind_fits(x), Cl.binds_all(y <> u), h)) : {Wr.Got{x <> y <> u, rest} == FCL.get_binds.go(1n+List.length(&2, Cv.Bind, u), _) : Wr.Dec<List<&2, Cv.Bind>>}
      %cl.binds_rt(u, y, rest, cl.and_r(Cl.bind_fits(x), Cl.binds_all(y <> u), h)) : {Wr.Got{x <> y <> u, rest} == FCL.get_binds.cons(x, _) : Wr.Dec<List<&2, Cv.Bind>>}
      {==}

# a list the laws spell reads back, whatever follows it
def cl.binds_full(xs: List<&2, Cv.Bind>, +rest: String, +h: {Cl.binds_fit(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == FCL.get_binds(Wr.get_nat(Cl.spell_binds(xs, rest))) : Wr.Dec<List<&2, Cv.Bind>>}:
  match xs:
    case Nil{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Nil{}, rest} == FCL.get_binds(_) : Wr.Dec<List<&2, Cv.Bind>>}
      {==}
    case +x <> +t:
      +n = List.length(&2, Cv.Bind, x <> t)
      %LWire.pw6.nat(n, Cl.spell_binds.items(x <> t, rest), cl.and_l(LawsBase.wire_fits(n), Cl.binds_all(x <> t), h)) : {Wr.Got{x <> t, rest} == FCL.get_binds(_) : Wr.Dec<List<&2, Cv.Bind>>}
      cl.binds_rt(t, x, rest, cl.and_r(LawsBase.wire_fits(n), Cl.binds_all(x <> t), h))

# an agent the laws spell reads back, whatever follows it
def cl.ag_rt(a: Cv.Ag, +rest: String, +h: {Cl.ag_fits(a) == True{} : Bool}) -> {Wr.Got{a, rest} == FCL.get_ag(Cl.spell_ag(a, rest)) : Wr.Dec<Cv.Ag>}:
  match a:
    case Cv.Ag{+p, +s}:
      +g = {Wr.Got{Cv.Ag{p, s}, rest} : Wr.Dec<Cv.Ag>}
      %cl.binds_full(p, Cl.spell_binds(s, rest), cl.and_l(Cl.binds_fit(p), Cl.binds_fit(s), h)) : {g == FCL.get_ag.profile(_) : Wr.Dec<Cv.Ag>}
      %cl.binds_full(s, rest, cl.and_r(Cl.binds_fit(p), Cl.binds_fit(s), h)) : {g == FCL.get_ag.sets(p, _) : Wr.Dec<Cv.Ag>}
      {==}

# the items after the first read back, the first one being x
def cl.ags_rt(t: List<&2, Cv.Ag>, +x: Cv.Ag, +rest: String, +h: {Cl.ags_all(x <> t) == True{} : Bool}) -> {Wr.Got{x <> t, rest} == FCL.get_ags.go(List.length(&2, Cv.Ag, t), FCL.get_ag(Cl.spell_ag(x, Cl.spell_ags.items(t, rest)))) : Wr.Dec<List<&2, Cv.Ag>>}:
  match t:
    case Nil{}:
      %cl.ag_rt(x, rest, cl.and_l(Cl.ag_fits(x), True{}, h)) : {Wr.Got{[x], rest} == FCL.get_ags.go(0n, _) : Wr.Dec<List<&2, Cv.Ag>>}
      {==}
    case +y <> +u:
      %cl.ag_rt(x, Cl.spell_ag(y, Cl.spell_ags.items(u, rest)), cl.and_l(Cl.ag_fits(x), Cl.ags_all(y <> u), h)) : {Wr.Got{x <> y <> u, rest} == FCL.get_ags.go(1n+List.length(&2, Cv.Ag, u), _) : Wr.Dec<List<&2, Cv.Ag>>}
      %cl.ags_rt(u, y, rest, cl.and_r(Cl.ag_fits(x), Cl.ags_all(y <> u), h)) : {Wr.Got{x <> y <> u, rest} == FCL.get_ags.cons(x, _) : Wr.Dec<List<&2, Cv.Ag>>}
      {==}

# a list the laws spell reads back, whatever follows it
def cl.ags_full(xs: List<&2, Cv.Ag>, +rest: String, +h: {Cl.ags_fit(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == FCL.get_ags(Wr.get_nat(Cl.spell_ags(xs, rest))) : Wr.Dec<List<&2, Cv.Ag>>}:
  match xs:
    case Nil{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Nil{}, rest} == FCL.get_ags(_) : Wr.Dec<List<&2, Cv.Ag>>}
      {==}
    case +x <> +t:
      +n = List.length(&2, Cv.Ag, x <> t)
      %LWire.pw6.nat(n, Cl.spell_ags.items(x <> t, rest), cl.and_l(LawsBase.wire_fits(n), Cl.ags_all(x <> t), h)) : {Wr.Got{x <> t, rest} == FCL.get_ags(_) : Wr.Dec<List<&2, Cv.Ag>>}
      cl.ags_rt(t, x, rest, cl.and_r(LawsBase.wire_fits(n), Cl.ags_all(x <> t), h))

# Writers
# -------

def cl.val_put(v: Cv.Val, rest: String) -> {FCL.put_val(v, rest) == Cl.spell_val(v, rest) : String}:
  match v:
    case Cv.VNat{n}:
      {==}
    case Cv.VBool{b}:
      {==}

def cl.mval_put(m: Maybe<&2, Cv.Val>, rest: String) -> {FCL.put_mval(m, rest) == Cl.spell_mval(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case Cv.VNat{n}:
          {==}
        case Cv.VBool{b}:
          {==}

def cl.bind_put(b: Cv.Bind, rest: String) -> {FCL.put_bind(b, rest) == Cl.spell_bind(b, rest) : String}:
  match b:
    case Cv.Bind{i, v}:
      match v:
        case Cv.VNat{n}:
          {==}
        case Cv.VBool{c}:
          {==}

def cl.binds_items(bs: List<&2, Cv.Bind>, +rest: String) -> {FCL.put_binds.items(bs, rest) == Cl.spell_binds.items(bs, rest) : String}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +t:
      %cl.binds_items(t, rest) : {FCL.put_bind(b, FCL.put_binds.items(t, rest)) == Cl.spell_bind(b, _) : String}
      cl.bind_put(b, FCL.put_binds.items(t, rest))

def cl.binds_put(+bs: List<&2, Cv.Bind>, +rest: String) -> {FCL.put_binds(bs, rest) == Cl.spell_binds(bs, rest) : String}:
  %cl.binds_items(bs, rest) : {Wr.put_nat(List.length(&2, Cv.Bind, bs), FCL.put_binds.items(bs, rest)) == Wr.put_nat(List.length(&2, Cv.Bind, bs), _) : String}
  {==}

def cl.refusal_put(f: Cv.Refusal, rest: String) -> {FCL.put_refusal(f, rest) == Cl.spell_refusal(f, rest) : String}:
  match f:
    case Cv.Accept{}:
      {==}
    case Cv.Twice{i}:
      {==}
    case Cv.BadInit{i}:
      {==}

def cl.check_put(c: Cv.Check, rest: String) -> {FCL.put_check(c, rest) == Cl.spell_check(c, rest) : String}:
  match c:
    case Cv.CkUndeclared{}:
      {==}
    case Cv.CkGlobal{}:
      {==}
    case Cv.CkType{}:
      {==}
    case Cv.CkFine{}:
      {==}

def cl.tog_put(t: Cv.Tog, rest: String) -> {FCL.put_tog(t, rest) == Cl.spell_tog(t, rest) : String}:
  match t:
    case Cv.TgUndeclared{}:
      {==}
    case Cv.TgGlobal{}:
      {==}
    case Cv.TgNotBool{}:
      {==}
    case Cv.TgFlip{b}:
      match b:
        case Cv.Bind{i, v}:
          match v:
            case Cv.VNat{n}:
              {==}
            case Cv.VBool{c}:
              {==}

# per declaration, the value and the layered value, as the laws spell them
def cl.values_items(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, +rest: String) -> {FCL.put_values.items(xs, ds, cfg, fam, rest) == Cl.spell_values.items(xs, ds, cfg, fam, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Cv.Decl{+i, t, c, p, r, v} <> +u:
      +vv = Cv.value(ds, cfg, fam, i)
      +lv = Cv.layered(ds, cfg, fam, i)
      +pu = FCL.put_values.items(u, ds, cfg, fam, rest)
      %cl.values_items(u, ds, cfg, fam, rest) : {FCL.put_mval(vv, FCL.put_mval(lv, pu)) == Cl.spell_mval(vv, Cl.spell_mval(lv, _)) : String}
      %cl.mval_put(lv, pu) : {FCL.put_mval(vv, FCL.put_mval(lv, pu)) == Cl.spell_mval(vv, _) : String}
      cl.mval_put(vv, FCL.put_mval(lv, pu))
