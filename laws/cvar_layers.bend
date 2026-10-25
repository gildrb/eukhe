# eukhe: the laws of area cvar_layers

import Base
import ../bend/cvar.bend as Cv
import ../bend/ffi_cvar_layers.bend as FCL
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- cvar_layers ----

# LAWS (S4, the compiled core): the entry bend/ffi_cvar_layers.bend (id
# 64) answers the Rust code's cvar resolution: the registry's refusal, the
# value of each cvar and the value a layer sets, the verdict on a set and
# on a toggle, the sets an agent writes, the config sets of a settings
# document. Each law is a claim about FCL.ffi, bytes in and bytes out; the
# model's decisions are pinned whole by laws/cvar.bend (cvar resolution).
# Every input is free: any request, any text.
#
# R1: a request Rust writes (the grammar below, every Nat within the wire)
#     gets the encoding of the model's decision on that request: no field
#     lost, swapped or misread on the way in, none on the way out.
# R2: any other input (malformed, an unknown tag, input left over) gets
#     exactly the error form 'E cvar_layers: malformed request', never a
#     default decision.

# Spellings
# ---------
# The request and the reply as Rust writes and reads them, from the wire
# primitives of bend/wire.bend (crates/eukhe-bend/WIRE.md):
#   Val   = 0 VNat (Nat) | 1 VBool (Bool)
#   Ty    = 0 TNat | 1 TBool;  Scope = 0 Global | 1 Local
#   Decl  = id, Ty, Scope, persist, replicate, init
#   Bind  = id, Val;  Ag = profile (List<Bind>), sets (List<Bind>)
#   Layer = 0 Config | 1 Agent;  Flag = 0 Persist | 1 Replicate
# A list is its count, then its items.

def spell_val(v: Cv.Val, rest: String) -> String:
  match v:
    case Cv.VNat{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case Cv.VBool{b}:
      Wr.put_nat(1n, Wr.put_bool(b, rest))

def spell_mval(m: Maybe<&2, Cv.Val>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{v}:
      Wr.put_nat(1n, spell_val(v, rest))

def spell_ty(t: Cv.Ty, rest: String) -> String:
  match t:
    case Cv.TNat{}:
      Wr.put_nat(0n, rest)
    case Cv.TBool{}:
      Wr.put_nat(1n, rest)

def spell_scope(c: Cv.Scope, rest: String) -> String:
  match c:
    case Cv.Global{}:
      Wr.put_nat(0n, rest)
    case Cv.Local{}:
      Wr.put_nat(1n, rest)

def spell_decl(d: Cv.Decl, rest: String) -> String:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      Wr.put_nat(i, spell_ty(t, spell_scope(c, Wr.put_bool(p, Wr.put_bool(r, spell_val(v, rest))))))

def spell_decls.items(ds: List<&2, Cv.Decl>, rest: String) -> String:
  match ds:
    case Nil{}:
      rest
    case d <> t:
      spell_decl(d, spell_decls.items(t, rest))

def spell_decls(+ds: List<&2, Cv.Decl>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cv.Decl, ds), spell_decls.items(ds, rest))

def spell_bind(b: Cv.Bind, rest: String) -> String:
  match b:
    case Cv.Bind{i, v}:
      Wr.put_nat(i, spell_val(v, rest))

def spell_binds.items(bs: List<&2, Cv.Bind>, rest: String) -> String:
  match bs:
    case Nil{}:
      rest
    case b <> t:
      spell_bind(b, spell_binds.items(t, rest))

def spell_binds(+bs: List<&2, Cv.Bind>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cv.Bind, bs), spell_binds.items(bs, rest))

def spell_ag(a: Cv.Ag, rest: String) -> String:
  match a:
    case Cv.Ag{p, s}:
      spell_binds(p, spell_binds(s, rest))

def spell_ags.items(fs: List<&2, Cv.Ag>, rest: String) -> String:
  match fs:
    case Nil{}:
      rest
    case a <> t:
      spell_ag(a, spell_ags.items(t, rest))

def spell_ags(+fs: List<&2, Cv.Ag>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cv.Ag, fs), spell_ags.items(fs, rest))

def spell_layer(l: Cv.Layer, rest: String) -> String:
  match l:
    case Cv.Config{}:
      Wr.put_nat(0n, rest)
    case Cv.Agent{}:
      Wr.put_nat(1n, rest)

def spell_flag(f: Cv.Flag, rest: String) -> String:
  match f:
    case Cv.Persist{}:
      Wr.put_nat(0n, rest)
    case Cv.Replicate{}:
      Wr.put_nat(1n, rest)

# the request Rust writes for a
def spell_ask(a: FCL.Ask) -> String:
  match a:
    case FCL.AskRegistry{ds}:
      Wr.put_nat(0n, spell_decls(ds, ""))
    case FCL.AskValues{ds, c, f}:
      Wr.put_nat(1n, spell_decls(ds, spell_binds(c, spell_ags(f, ""))))
    case FCL.AskToggle{ds, c, f, l, x}:
      Wr.put_nat(2n, spell_decls(ds, spell_binds(c, spell_ags(f, spell_layer(l, Wr.put_nat(x, ""))))))
    case FCL.AskCheck{ds, l, b}:
      Wr.put_nat(3n, spell_decls(ds, spell_layer(l, spell_bind(b, ""))))
    case FCL.AskWritten{ds, ss, g}:
      Wr.put_nat(4n, spell_decls(ds, spell_binds(ss, spell_flag(g, ""))))
    case FCL.AskDocument{ds, m, g}:
      Wr.put_nat(5n, spell_decls(ds, spell_binds(m, spell_binds(g, ""))))

def spell_refusal(f: Cv.Refusal, rest: String) -> String:
  match f:
    case Cv.Accept{}:
      Wr.put_nat(0n, rest)
    case Cv.Twice{i}:
      Wr.put_nat(1n, Wr.put_nat(i, rest))
    case Cv.BadInit{i}:
      Wr.put_nat(2n, Wr.put_nat(i, rest))

def spell_tog(t: Cv.Tog, rest: String) -> String:
  match t:
    case Cv.TgUndeclared{}:
      Wr.put_nat(0n, rest)
    case Cv.TgGlobal{}:
      Wr.put_nat(1n, rest)
    case Cv.TgNotBool{}:
      Wr.put_nat(2n, rest)
    case Cv.TgFlip{b}:
      Wr.put_nat(3n, spell_bind(b, rest))

def spell_check(c: Cv.Check, rest: String) -> String:
  match c:
    case Cv.CkUndeclared{}:
      Wr.put_nat(0n, rest)
    case Cv.CkGlobal{}:
      Wr.put_nat(1n, rest)
    case Cv.CkType{}:
      Wr.put_nat(2n, rest)
    case Cv.CkFine{}:
      Wr.put_nat(3n, rest)

# per declaration of xs: the value of its cvar, then the value a layer sets
def spell_values.items(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Cv.Decl{+i, t, c, p, r, v} <> u:
      spell_mval(Cv.value(ds, cfg, fam, i), spell_mval(Cv.layered(ds, cfg, fam, i), spell_values.items(u, ds, cfg, fam, rest)))

# the reply to a: the model's decision on it
def spell_answer(a: FCL.Ask) -> String:
  match a:
    case FCL.AskRegistry{ds}:
      spell_refusal(Cv.refusal(ds), "")
    case FCL.AskValues{+ds, c, f}:
      Wr.put_nat(List.length(&2, Cv.Decl, ds), spell_values.items(ds, ds, c, f, ""))
    case FCL.AskToggle{ds, c, f, l, x}:
      spell_tog(Cv.tog(ds, c, f, l, x), "")
    case FCL.AskCheck{ds, l, b}:
      spell_check(Cv.check(ds, l, b), "")
    case FCL.AskWritten{ds, ss, g}:
      spell_binds(Cv.written(ss, ds, g), "")
    case FCL.AskDocument{ds, m, g}:
      spell_binds(Cv.document(ds, m, g), "")

# What fits the wire
# ------------------

def val_fits(v: Cv.Val) -> Bool:
  match v:
    case Cv.VNat{n}:
      LawsBase.wire_fits(n)
    case Cv.VBool{b}:
      True{}

def decl_fits(d: Cv.Decl) -> Bool:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      Bool.and(LawsBase.wire_fits(i), val_fits(v))

def decls_all(ds: List<&2, Cv.Decl>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case d <> t:
      Bool.and(decl_fits(d), decls_all(t))

def decls_fit(+ds: List<&2, Cv.Decl>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cv.Decl, ds)), decls_all(ds))

def bind_fits(b: Cv.Bind) -> Bool:
  match b:
    case Cv.Bind{i, v}:
      Bool.and(LawsBase.wire_fits(i), val_fits(v))

def binds_all(bs: List<&2, Cv.Bind>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case b <> t:
      Bool.and(bind_fits(b), binds_all(t))

def binds_fit(+bs: List<&2, Cv.Bind>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cv.Bind, bs)), binds_all(bs))

def ag_fits(a: Cv.Ag) -> Bool:
  match a:
    case Cv.Ag{p, s}:
      Bool.and(binds_fit(p), binds_fit(s))

def ags_all(fs: List<&2, Cv.Ag>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case a <> t:
      Bool.and(ag_fits(a), ags_all(t))

def ags_fit(+fs: List<&2, Cv.Ag>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cv.Ag, fs)), ags_all(fs))

# every number of the request a fits the wire
def ask_fits(a: FCL.Ask) -> Bool:
  match a:
    case FCL.AskRegistry{ds}:
      decls_fit(ds)
    case FCL.AskValues{ds, c, f}:
      Bool.and(decls_fit(ds), Bool.and(binds_fit(c), ags_fit(f)))
    case FCL.AskToggle{ds, c, f, l, x}:
      Bool.and(decls_fit(ds), Bool.and(binds_fit(c), Bool.and(ags_fit(f), LawsBase.wire_fits(x))))
    case FCL.AskCheck{ds, l, b}:
      Bool.and(decls_fit(ds), bind_fits(b))
    case FCL.AskWritten{ds, ss, g}:
      Bool.and(decls_fit(ds), binds_fit(ss))
    case FCL.AskDocument{ds, m, g}:
      Bool.and(decls_fit(ds), Bool.and(binds_fit(m), binds_fit(g)))

# Reading
# -------
# The request at the start of a text, read field by field with the wire's
# decoders: what a request is, independent of the entry's own reader.

def read_val.nat(r: Wr.Dec<Nat>) -> Wr.Dec<Cv.Val>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Cv.VNat{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_val.bool(r: Wr.Dec<Bool>) -> Wr.Dec<Cv.Val>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{Cv.VBool{b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_val.tag(t: Nat, s: String) -> Wr.Dec<Cv.Val>:
  match t:
    case 0n:
      read_val.nat(Wr.get_nat(s))
    case 1n:
      read_val.bool(Wr.get_bool(s))
    case 2n+p:
      Wr.Bad{}

def read_val(r: Wr.Dec<Nat>) -> Wr.Dec<Cv.Val>:
  match r:
    case Wr.Got{t, s}:
      read_val.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ty.tag(t: Nat, s: String) -> Wr.Dec<Cv.Ty>:
  match t:
    case 0n:
      Wr.Got{Cv.TNat{}, s}
    case 1n:
      Wr.Got{Cv.TBool{}, s}
    case 2n+p:
      Wr.Bad{}

def read_ty(r: Wr.Dec<Nat>) -> Wr.Dec<Cv.Ty>:
  match r:
    case Wr.Got{t, s}:
      read_ty.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_scope.tag(t: Nat, s: String) -> Wr.Dec<Cv.Scope>:
  match t:
    case 0n:
      Wr.Got{Cv.Global{}, s}
    case 1n:
      Wr.Got{Cv.Local{}, s}
    case 2n+p:
      Wr.Bad{}

def read_scope(r: Wr.Dec<Nat>) -> Wr.Dec<Cv.Scope>:
  match r:
    case Wr.Got{t, s}:
      read_scope.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_layer.tag(t: Nat, s: String) -> Wr.Dec<Cv.Layer>:
  match t:
    case 0n:
      Wr.Got{Cv.Config{}, s}
    case 1n:
      Wr.Got{Cv.Agent{}, s}
    case 2n+p:
      Wr.Bad{}

def read_layer(r: Wr.Dec<Nat>) -> Wr.Dec<Cv.Layer>:
  match r:
    case Wr.Got{t, s}:
      read_layer.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_flag.tag(t: Nat, s: String) -> Wr.Dec<Cv.Flag>:
  match t:
    case 0n:
      Wr.Got{Cv.Persist{}, s}
    case 1n:
      Wr.Got{Cv.Replicate{}, s}
    case 2n+p:
      Wr.Bad{}

def read_flag(r: Wr.Dec<Nat>) -> Wr.Dec<Cv.Flag>:
  match r:
    case Wr.Got{t, s}:
      read_flag.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_decl.init(i: Nat, t: Cv.Ty, c: Cv.Scope, p: Bool, q: Bool, r: Wr.Dec<Cv.Val>) -> Wr.Dec<Cv.Decl>:
  match r:
    case Wr.Got{v, s}:
      Wr.Got{Cv.Decl{i, t, c, p, q, v}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_decl.rep(i: Nat, t: Cv.Ty, c: Cv.Scope, p: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<Cv.Decl>:
  match r:
    case Wr.Got{q, s}:
      read_decl.init(i, t, c, p, q, read_val(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_decl.per(i: Nat, t: Cv.Ty, c: Cv.Scope, r: Wr.Dec<Bool>) -> Wr.Dec<Cv.Decl>:
  match r:
    case Wr.Got{p, s}:
      read_decl.rep(i, t, c, p, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_decl.scope(i: Nat, t: Cv.Ty, r: Wr.Dec<Cv.Scope>) -> Wr.Dec<Cv.Decl>:
  match r:
    case Wr.Got{c, s}:
      read_decl.per(i, t, c, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_decl.ty(i: Nat, r: Wr.Dec<Cv.Ty>) -> Wr.Dec<Cv.Decl>:
  match r:
    case Wr.Got{t, s}:
      read_decl.scope(i, t, read_scope(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_decl.id(r: Wr.Dec<Nat>) -> Wr.Dec<Cv.Decl>:
  match r:
    case Wr.Got{i, s}:
      read_decl.ty(i, read_ty(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_decl(s: String) -> Wr.Dec<Cv.Decl>:
  read_decl.id(Wr.get_nat(s))

def read_decls.cons(d: Cv.Decl, r: Wr.Dec<List<&2, Cv.Decl>>) -> Wr.Dec<List<&2, Cv.Decl>>:
  match r:
    case Wr.Got{ds, s}:
      Wr.Got{d <> ds, s}
    case Wr.Bad{}:
      Wr.Bad{}

# n more declarations after the one cur answers
def read_decls.go(n: Nat, cur: Wr.Dec<Cv.Decl>) -> Wr.Dec<List<&2, Cv.Decl>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{d, s}:
          Wr.Got{[d], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+m:
      match cur:
        case Wr.Got{d, s}:
          read_decls.cons(d, read_decls.go(m, read_decl(s)))
        case Wr.Bad{}:
          Wr.Bad{}

def read_decls(r: Wr.Dec<Nat>) -> Wr.Dec<List<&2, Cv.Decl>>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          Wr.Got{Nil{}, s}
        case 1n+m:
          read_decls.go(m, read_decl(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_bind.val(i: Nat, r: Wr.Dec<Cv.Val>) -> Wr.Dec<Cv.Bind>:
  match r:
    case Wr.Got{v, s}:
      Wr.Got{Cv.Bind{i, v}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_bind.id(r: Wr.Dec<Nat>) -> Wr.Dec<Cv.Bind>:
  match r:
    case Wr.Got{i, s}:
      read_bind.val(i, read_val(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_bind(s: String) -> Wr.Dec<Cv.Bind>:
  read_bind.id(Wr.get_nat(s))

def read_binds.cons(b: Cv.Bind, r: Wr.Dec<List<&2, Cv.Bind>>) -> Wr.Dec<List<&2, Cv.Bind>>:
  match r:
    case Wr.Got{bs, s}:
      Wr.Got{b <> bs, s}
    case Wr.Bad{}:
      Wr.Bad{}

# n more sets after the one cur answers
def read_binds.go(n: Nat, cur: Wr.Dec<Cv.Bind>) -> Wr.Dec<List<&2, Cv.Bind>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{b, s}:
          Wr.Got{[b], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+m:
      match cur:
        case Wr.Got{b, s}:
          read_binds.cons(b, read_binds.go(m, read_bind(s)))
        case Wr.Bad{}:
          Wr.Bad{}

def read_binds(r: Wr.Dec<Nat>) -> Wr.Dec<List<&2, Cv.Bind>>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          Wr.Got{Nil{}, s}
        case 1n+m:
          read_binds.go(m, read_bind(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ag.sets(p: List<&2, Cv.Bind>, r: Wr.Dec<List<&2, Cv.Bind>>) -> Wr.Dec<Cv.Ag>:
  match r:
    case Wr.Got{ss, s}:
      Wr.Got{Cv.Ag{p, ss}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_ag.profile(r: Wr.Dec<List<&2, Cv.Bind>>) -> Wr.Dec<Cv.Ag>:
  match r:
    case Wr.Got{p, s}:
      read_ag.sets(p, read_binds(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ag(s: String) -> Wr.Dec<Cv.Ag>:
  read_ag.profile(read_binds(Wr.get_nat(s)))

def read_ags.cons(a: Cv.Ag, r: Wr.Dec<List<&2, Cv.Ag>>) -> Wr.Dec<List<&2, Cv.Ag>>:
  match r:
    case Wr.Got{fs, s}:
      Wr.Got{a <> fs, s}
    case Wr.Bad{}:
      Wr.Bad{}

# n more agents after the one cur answers
def read_ags.go(n: Nat, cur: Wr.Dec<Cv.Ag>) -> Wr.Dec<List<&2, Cv.Ag>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{a, s}:
          Wr.Got{[a], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+m:
      match cur:
        case Wr.Got{a, s}:
          read_ags.cons(a, read_ags.go(m, read_ag(s)))
        case Wr.Bad{}:
          Wr.Bad{}

def read_ags(r: Wr.Dec<Nat>) -> Wr.Dec<List<&2, Cv.Ag>>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          Wr.Got{Nil{}, s}
        case 1n+m:
          read_ags.go(m, read_ag(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_reg(r: Wr.Dec<List<&2, Cv.Decl>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{ds, s}:
      Wr.Got{FCL.AskRegistry{ds}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_vals.fam(ds: List<&2, Cv.Decl>, c: List<&2, Cv.Bind>, r: Wr.Dec<List<&2, Cv.Ag>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{FCL.AskValues{ds, c, f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_vals.cfg(ds: List<&2, Cv.Decl>, r: Wr.Dec<List<&2, Cv.Bind>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{c, s}:
      read_vals.fam(ds, c, read_ags(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_vals(r: Wr.Dec<List<&2, Cv.Decl>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{ds, s}:
      read_vals.cfg(ds, read_binds(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_tog.id(ds: List<&2, Cv.Decl>, c: List<&2, Cv.Bind>, f: List<&2, Cv.Ag>, l: Cv.Layer, r: Wr.Dec<Nat>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{FCL.AskToggle{ds, c, f, l, x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_tog.layer(ds: List<&2, Cv.Decl>, c: List<&2, Cv.Bind>, f: List<&2, Cv.Ag>, r: Wr.Dec<Cv.Layer>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{l, s}:
      read_tog.id(ds, c, f, l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_tog.fam(ds: List<&2, Cv.Decl>, c: List<&2, Cv.Bind>, r: Wr.Dec<List<&2, Cv.Ag>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{f, s}:
      read_tog.layer(ds, c, f, read_layer(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_tog.cfg(ds: List<&2, Cv.Decl>, r: Wr.Dec<List<&2, Cv.Bind>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{c, s}:
      read_tog.fam(ds, c, read_ags(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_tog(r: Wr.Dec<List<&2, Cv.Decl>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{ds, s}:
      read_tog.cfg(ds, read_binds(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_chk.set(ds: List<&2, Cv.Decl>, l: Cv.Layer, r: Wr.Dec<Cv.Bind>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{FCL.AskCheck{ds, l, b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_chk.layer(ds: List<&2, Cv.Decl>, r: Wr.Dec<Cv.Layer>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{l, s}:
      read_chk.set(ds, l, read_bind(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_chk(r: Wr.Dec<List<&2, Cv.Decl>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{ds, s}:
      read_chk.layer(ds, read_layer(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_wr.flag(ds: List<&2, Cv.Decl>, ss: List<&2, Cv.Bind>, r: Wr.Dec<Cv.Flag>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{g, s}:
      Wr.Got{FCL.AskWritten{ds, ss, g}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_wr.sets(ds: List<&2, Cv.Decl>, r: Wr.Dec<List<&2, Cv.Bind>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{ss, s}:
      read_wr.flag(ds, ss, read_flag(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_wr(r: Wr.Dec<List<&2, Cv.Decl>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{ds, s}:
      read_wr.sets(ds, read_binds(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_doc.global(ds: List<&2, Cv.Decl>, m: List<&2, Cv.Bind>, r: Wr.Dec<List<&2, Cv.Bind>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{g, s}:
      Wr.Got{FCL.AskDocument{ds, m, g}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_doc.merged(ds: List<&2, Cv.Decl>, r: Wr.Dec<List<&2, Cv.Bind>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{m, s}:
      read_doc.global(ds, m, read_binds(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_doc(r: Wr.Dec<List<&2, Cv.Decl>>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{ds, s}:
      read_doc.merged(ds, read_binds(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tag(t: Nat, s: String) -> Wr.Dec<FCL.Ask>:
  match t:
    case 0n:
      read_reg(read_decls(Wr.get_nat(s)))
    case 1n:
      read_vals(read_decls(Wr.get_nat(s)))
    case 2n:
      read_tog(read_decls(Wr.get_nat(s)))
    case 3n:
      read_chk(read_decls(Wr.get_nat(s)))
    case 4n:
      read_wr(read_decls(Wr.get_nat(s)))
    case 5n:
      read_doc(read_decls(Wr.get_nat(s)))
    case 6n+p:
      Wr.Bad{}

def read_ask.go(r: Wr.Dec<Nat>) -> Wr.Dec<FCL.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: FCL.Ask) -> Maybe<&2, FCL.Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(r: Wr.Dec<FCL.Ask>) -> Maybe<&2, FCL.Ask>:
  match r:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, FCL.Ask>:
  read_ask.whole(read_ask.go(Wr.get_nat(s)))

# Laws
# ----

# LAW cvar_layers_ffi_answers: on every request Rust writes whose numbers fit the wire, the entry answers the model's decision: the registry's first refusal, each declaration's value and the value a layer sets (in order), the verdict on the toggle, the verdict on the set, the sets written, the document's config sets
# EXCLUDES: a field lost, swapped or misread on the way in or out, a
#   decision by any other rule, a default answer
law cvar_layers_ffi_answers:
  for +a: FCL.Ask
  for fits: {ask_fits(a) == True{} : Bool}
  {FCL.ffi(spell_ask(a)) == spell_answer(a) : String}

# LAW cvar_layers_ffi_malformed_exact: every input that is not exactly one request (malformed, an unknown tag, input left over) gets exactly the error form 'E ', then "cvar_layers: malformed request"
# EXCLUDES: a default decision (a value, an accepted registry, a valid
#   set) for bad input
law cvar_layers_ffi_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, FCL.Ask>}
  {FCL.ffi(s) == SCon{'E', SCon{' ', "cvar_layers: malformed request"}} : String}

# LAW cvar_layers_ffi_example: anchor: the strings Rust sends: a registry that declares cvar 0 twice is refused naming 0; the value of a Bool cvar (default F) set to T by the agent; a toggle of it flips T to F; a set of 7 to that Bool cvar has the wrong type; a request with input left over is refused
law cvar_layers_ffi_example:
  {FCL.ffi("0,2,0,1,1,TF1,F0,0,1,FF0,0,") == "1,0," : String} &
  {FCL.ffi("1,1,0,1,1,TF1,F0,1,0,1,0,1,T") == "1,1,1,T1,1,T" : String} &
  {FCL.ffi("2,1,0,1,1,TF1,F0,1,0,1,0,1,T1,0,") == "3,0,1,F" : String} &
  {FCL.ffi("3,1,0,1,1,TF1,F1,0,0,7,") == "2," : String} &
  {FCL.ffi("0,0,0,") == SCon{'E', SCon{' ', "cvar_layers: malformed request"}} : String}

# LAW cvar_layers_fits_example: witness: a request of each kind fits the wire
law cvar_layers_fits_example:
  {ask_fits(FCL.AskRegistry{[Cv.Decl{0n, Cv.TBool{}, Cv.Local{}, True{}, False{}, Cv.VBool{False{}}}]}) == True{} : Bool} &
  {ask_fits(FCL.AskValues{[Cv.Decl{0n, Cv.TNat{}, Cv.Global{}, False{}, True{}, Cv.VNat{0n}}], [Cv.Bind{0n, Cv.VNat{1n}}], [Cv.Ag{[Cv.Bind{0n, Cv.VNat{2n}}], Nil{}}]}) == True{} : Bool} &
  {ask_fits(FCL.AskToggle{Nil{}, Nil{}, Nil{}, Cv.Agent{}, 3n}) == True{} : Bool} &
  {ask_fits(FCL.AskCheck{Nil{}, Cv.Config{}, Cv.Bind{1n, Cv.VBool{True{}}}}) == True{} : Bool} &
  {ask_fits(FCL.AskWritten{Nil{}, [Cv.Bind{1n, Cv.VNat{4n}}], Cv.Persist{}}) == True{} : Bool} &
  {ask_fits(FCL.AskDocument{Nil{}, [Cv.Bind{1n, Cv.VNat{4n}}], [Cv.Bind{2n, Cv.VBool{False{}}}]}) == True{} : Bool}
