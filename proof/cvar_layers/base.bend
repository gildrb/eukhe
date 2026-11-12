# eukhe: lemmas the proofs of area cvar_layers share: the entry reads
# back what the laws' spellers write, and its reply writers write what
# the laws' spellers write.

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

# the entry's writers answer every request as the laws spell the decision
def cl.answer(a: FCL.Ask) -> {FCL.answer(a) == Cl.spell_answer(a) : String}:
  match a:
    case FCL.AskRegistry{ds}:
      cl.refusal_put(Cv.refusal(ds), "")
    case FCL.AskValues{+ds, c, f}:
      %cl.values_items(ds, ds, c, f, "") : {Wr.put_nat(List.length(&2, Cv.Decl, ds), FCL.put_values.items(ds, ds, c, f, "")) == Wr.put_nat(List.length(&2, Cv.Decl, ds), _) : String}
      {==}
    case FCL.AskToggle{ds, c, f, l, x}:
      cl.tog_put(Cv.tog(ds, c, f, l, x), "")
    case FCL.AskCheck{ds, l, b}:
      cl.check_put(Cv.check(ds, l, b), "")
    case FCL.AskWritten{ds, ss, g}:
      cl.binds_put(Cv.written(ss, ds, g), "")
    case FCL.AskDocument{ds, m, g}:
      cl.binds_put(Cv.document(ds, m, g), "")
