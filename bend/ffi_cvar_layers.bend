import Base
import ./wire.bend as W
import ./cvar.bend as Cv

# ffi_cvar_layers: the resolution of the cvars (bend/cvar.bend `refusal`,
# `value`, `layered`, `tog`, `check`, `written`, `document`) as an entry
# of the compiled Bend core. Entry 6 (bend/ffi_cvar.bend) keeps the
# expansion and the presses: its laws pin its answer to every input.
#
# Wire (crates/eukhe-bend/WIRE.md):
#   Val   = 0 VNat (Nat) | 1 VBool (Bool)
#   Ty    = 0 TNat | 1 TBool
#   Scope = 0 Global | 1 Local
#   Decl  = a record (id: Nat, ty: Ty, scope: Scope, persist: Bool,
#           replicate: Bool, init: Val)
#   Bind  = a record (id: Nat, val: Val)
#   Ag    = a record (profile: List<Bind>, sets: List<Bind>)
#   Layer = 0 Config | 1 Agent
#   Flag  = 0 Persist | 1 Replicate
# Request: a tag, then
#   0  registry: the declarations (List<Decl>)
#   1  values: the declarations, config.cfg (List<Bind>), the family
#      chain, root first (List<Ag>)
#   2  toggle: the declarations, config.cfg, the family, the Layer, the id
#   3  check: the declarations, the Layer, the set (Bind)
#   4  written: the declarations, the agent's sets (List<Bind>), the Flag
#   5  document: the declarations, the merged document's sets, the global
#      document's sets (List<Bind> each)
# Reply:
#   0  0 accept | 1 then an id declared twice | 2 then the id of a default
#      of the wrong type (the first declaration the registry drops)
#   1  a count, then per declaration in order its value and the value a
#      layer sets (Maybe<Val> each)
#   2  0 undeclared | 1 Global | 2 not a Bool | 3 then the Bind that flips
#   3  0 undeclared | 1 Global | 2 a value of the wrong type | 3 valid
#   4  the sets written (List<Bind>)
#   5  the config sets of the document (List<Bind>)
# Any other input, or input left over: the error form.

type Ask is Data:
  AskRegistry{decls: List<&2, Cv.Decl>}
  AskValues{decls: List<&2, Cv.Decl>, cfg: List<&2, Cv.Bind>, fam: List<&2, Cv.Ag>}
  AskToggle{decls: List<&2, Cv.Decl>, cfg: List<&2, Cv.Bind>, fam: List<&2, Cv.Ag>, layer: Cv.Layer, id: Nat}
  AskCheck{decls: List<&2, Cv.Decl>, layer: Cv.Layer, set: Cv.Bind}
  AskWritten{decls: List<&2, Cv.Decl>, sets: List<&2, Cv.Bind>, flag: Cv.Flag}
  AskDocument{decls: List<&2, Cv.Decl>, merged: List<&2, Cv.Bind>, global: List<&2, Cv.Bind>}

# Decoding
# --------

def get_val.nat(r: W.Dec<Nat>) -> W.Dec<Cv.Val>:
  match r:
    case W.Got{n, s}:
      W.Got{Cv.VNat{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_val.bool(r: W.Dec<Bool>) -> W.Dec<Cv.Val>:
  match r:
    case W.Got{b, s}:
      W.Got{Cv.VBool{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_val.tag(t: Nat, s: String) -> W.Dec<Cv.Val>:
  match t:
    case 0n:
      get_val.nat(W.get_nat(s))
    case 1n:
      get_val.bool(W.get_bool(s))
    case 2n+p:
      W.Bad{}

def get_val.go(r: W.Dec<Nat>) -> W.Dec<Cv.Val>:
  match r:
    case W.Got{t, s}:
      get_val.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_val(s: String) -> W.Dec<Cv.Val>:
  get_val.go(W.get_nat(s))

def get_ty.tag(t: Nat, s: String) -> W.Dec<Cv.Ty>:
  match t:
    case 0n:
      W.Got{Cv.TNat{}, s}
    case 1n:
      W.Got{Cv.TBool{}, s}
    case 2n+p:
      W.Bad{}

def get_ty.go(r: W.Dec<Nat>) -> W.Dec<Cv.Ty>:
  match r:
    case W.Got{t, s}:
      get_ty.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_scope.tag(t: Nat, s: String) -> W.Dec<Cv.Scope>:
  match t:
    case 0n:
      W.Got{Cv.Global{}, s}
    case 1n:
      W.Got{Cv.Local{}, s}
    case 2n+p:
      W.Bad{}

def get_scope.go(r: W.Dec<Nat>) -> W.Dec<Cv.Scope>:
  match r:
    case W.Got{t, s}:
      get_scope.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_layer.tag(t: Nat, s: String) -> W.Dec<Cv.Layer>:
  match t:
    case 0n:
      W.Got{Cv.Config{}, s}
    case 1n:
      W.Got{Cv.Agent{}, s}
    case 2n+p:
      W.Bad{}

def get_layer.go(r: W.Dec<Nat>) -> W.Dec<Cv.Layer>:
  match r:
    case W.Got{t, s}:
      get_layer.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_flag.tag(t: Nat, s: String) -> W.Dec<Cv.Flag>:
  match t:
    case 0n:
      W.Got{Cv.Persist{}, s}
    case 1n:
      W.Got{Cv.Replicate{}, s}
    case 2n+p:
      W.Bad{}

def get_flag.go(r: W.Dec<Nat>) -> W.Dec<Cv.Flag>:
  match r:
    case W.Got{t, s}:
      get_flag.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a declaration, field by field
def get_decl.init(i: Nat, t: Cv.Ty, c: Cv.Scope, p: Bool, q: Bool, r: W.Dec<Cv.Val>) -> W.Dec<Cv.Decl>:
  match r:
    case W.Got{v, s}:
      W.Got{Cv.Decl{i, t, c, p, q, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_decl.rep(i: Nat, t: Cv.Ty, c: Cv.Scope, p: Bool, r: W.Dec<Bool>) -> W.Dec<Cv.Decl>:
  match r:
    case W.Got{q, s}:
      get_decl.init(i, t, c, p, q, get_val(s))
    case W.Bad{}:
      W.Bad{}

def get_decl.per(i: Nat, t: Cv.Ty, c: Cv.Scope, r: W.Dec<Bool>) -> W.Dec<Cv.Decl>:
  match r:
    case W.Got{p, s}:
      get_decl.rep(i, t, c, p, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_decl.scope(i: Nat, t: Cv.Ty, r: W.Dec<Cv.Scope>) -> W.Dec<Cv.Decl>:
  match r:
    case W.Got{c, s}:
      get_decl.per(i, t, c, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_decl.ty(i: Nat, r: W.Dec<Cv.Ty>) -> W.Dec<Cv.Decl>:
  match r:
    case W.Got{t, s}:
      get_decl.scope(i, t, get_scope.go(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_decl.id(r: W.Dec<Nat>) -> W.Dec<Cv.Decl>:
  match r:
    case W.Got{i, s}:
      get_decl.ty(i, get_ty.go(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_decl(s: String) -> W.Dec<Cv.Decl>:
  get_decl.id(W.get_nat(s))

def get_decls.cons(d: Cv.Decl, r: W.Dec<List<&2, Cv.Decl>>) -> W.Dec<List<&2, Cv.Decl>>:
  match r:
    case W.Got{ds, s}:
      W.Got{d <> ds, s}
    case W.Bad{}:
      W.Bad{}

# n more declarations after the one cur answers
def get_decls.go(n: Nat, cur: W.Dec<Cv.Decl>) -> W.Dec<List<&2, Cv.Decl>>:
  match n:
    case 0n:
      match cur:
        case W.Got{d, s}:
          W.Got{[d], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{d, s}:
          get_decls.cons(d, get_decls.go(m, get_decl(s)))
        case W.Bad{}:
          W.Bad{}

# a list of declarations, its count read
def get_decls(r: W.Dec<Nat>) -> W.Dec<List<&2, Cv.Decl>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_decls.go(m, get_decl(s))
    case W.Bad{}:
      W.Bad{}

# a set
def get_bind.val(i: Nat, r: W.Dec<Cv.Val>) -> W.Dec<Cv.Bind>:
  match r:
    case W.Got{v, s}:
      W.Got{Cv.Bind{i, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_bind.id(r: W.Dec<Nat>) -> W.Dec<Cv.Bind>:
  match r:
    case W.Got{i, s}:
      get_bind.val(i, get_val(s))
    case W.Bad{}:
      W.Bad{}

def get_bind(s: String) -> W.Dec<Cv.Bind>:
  get_bind.id(W.get_nat(s))

def get_binds.cons(b: Cv.Bind, r: W.Dec<List<&2, Cv.Bind>>) -> W.Dec<List<&2, Cv.Bind>>:
  match r:
    case W.Got{bs, s}:
      W.Got{b <> bs, s}
    case W.Bad{}:
      W.Bad{}

# n more sets after the one cur answers
def get_binds.go(n: Nat, cur: W.Dec<Cv.Bind>) -> W.Dec<List<&2, Cv.Bind>>:
  match n:
    case 0n:
      match cur:
        case W.Got{b, s}:
          W.Got{[b], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{b, s}:
          get_binds.cons(b, get_binds.go(m, get_bind(s)))
        case W.Bad{}:
          W.Bad{}

# a list of sets, its count read
def get_binds(r: W.Dec<Nat>) -> W.Dec<List<&2, Cv.Bind>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_binds.go(m, get_bind(s))
    case W.Bad{}:
      W.Bad{}

# an agent: its profile, then its own sets
def get_ag.sets(p: List<&2, Cv.Bind>, r: W.Dec<List<&2, Cv.Bind>>) -> W.Dec<Cv.Ag>:
  match r:
    case W.Got{ss, s}:
      W.Got{Cv.Ag{p, ss}, s}
    case W.Bad{}:
      W.Bad{}

def get_ag.profile(r: W.Dec<List<&2, Cv.Bind>>) -> W.Dec<Cv.Ag>:
  match r:
    case W.Got{p, s}:
      get_ag.sets(p, get_binds(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_ag(s: String) -> W.Dec<Cv.Ag>:
  get_ag.profile(get_binds(W.get_nat(s)))

def get_ags.cons(a: Cv.Ag, r: W.Dec<List<&2, Cv.Ag>>) -> W.Dec<List<&2, Cv.Ag>>:
  match r:
    case W.Got{as, s}:
      W.Got{a <> as, s}
    case W.Bad{}:
      W.Bad{}

# n more agents after the one cur answers
def get_ags.go(n: Nat, cur: W.Dec<Cv.Ag>) -> W.Dec<List<&2, Cv.Ag>>:
  match n:
    case 0n:
      match cur:
        case W.Got{a, s}:
          W.Got{[a], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{a, s}:
          get_ags.cons(a, get_ags.go(m, get_ag(s)))
        case W.Bad{}:
          W.Bad{}

# a family chain, its count read
def get_ags(r: W.Dec<Nat>) -> W.Dec<List<&2, Cv.Ag>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_ags.go(m, get_ag(s))
    case W.Bad{}:
      W.Bad{}

# The requests
# ------------

def get_reg(r: W.Dec<List<&2, Cv.Decl>>) -> W.Dec<Ask>:
  match r:
    case W.Got{ds, s}:
      W.Got{AskRegistry{ds}, s}
    case W.Bad{}:
      W.Bad{}

def get_vals.fam(ds: List<&2, Cv.Decl>, c: List<&2, Cv.Bind>, r: W.Dec<List<&2, Cv.Ag>>) -> W.Dec<Ask>:
  match r:
    case W.Got{f, s}:
      W.Got{AskValues{ds, c, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_vals.cfg(ds: List<&2, Cv.Decl>, r: W.Dec<List<&2, Cv.Bind>>) -> W.Dec<Ask>:
  match r:
    case W.Got{c, s}:
      get_vals.fam(ds, c, get_ags(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_vals(r: W.Dec<List<&2, Cv.Decl>>) -> W.Dec<Ask>:
  match r:
    case W.Got{ds, s}:
      get_vals.cfg(ds, get_binds(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_tog.id(ds: List<&2, Cv.Decl>, c: List<&2, Cv.Bind>, f: List<&2, Cv.Ag>, l: Cv.Layer, r: W.Dec<Nat>) -> W.Dec<Ask>:
  match r:
    case W.Got{x, s}:
      W.Got{AskToggle{ds, c, f, l, x}, s}
    case W.Bad{}:
      W.Bad{}

def get_tog.layer(ds: List<&2, Cv.Decl>, c: List<&2, Cv.Bind>, f: List<&2, Cv.Ag>, r: W.Dec<Cv.Layer>) -> W.Dec<Ask>:
  match r:
    case W.Got{l, s}:
      get_tog.id(ds, c, f, l, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_tog.fam(ds: List<&2, Cv.Decl>, c: List<&2, Cv.Bind>, r: W.Dec<List<&2, Cv.Ag>>) -> W.Dec<Ask>:
  match r:
    case W.Got{f, s}:
      get_tog.layer(ds, c, f, get_layer.go(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_tog.cfg(ds: List<&2, Cv.Decl>, r: W.Dec<List<&2, Cv.Bind>>) -> W.Dec<Ask>:
  match r:
    case W.Got{c, s}:
      get_tog.fam(ds, c, get_ags(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_tog(r: W.Dec<List<&2, Cv.Decl>>) -> W.Dec<Ask>:
  match r:
    case W.Got{ds, s}:
      get_tog.cfg(ds, get_binds(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_chk.set(ds: List<&2, Cv.Decl>, l: Cv.Layer, r: W.Dec<Cv.Bind>) -> W.Dec<Ask>:
  match r:
    case W.Got{b, s}:
      W.Got{AskCheck{ds, l, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_chk.layer(ds: List<&2, Cv.Decl>, r: W.Dec<Cv.Layer>) -> W.Dec<Ask>:
  match r:
    case W.Got{l, s}:
      get_chk.set(ds, l, get_bind(s))
    case W.Bad{}:
      W.Bad{}

def get_chk(r: W.Dec<List<&2, Cv.Decl>>) -> W.Dec<Ask>:
  match r:
    case W.Got{ds, s}:
      get_chk.layer(ds, get_layer.go(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_wr.flag(ds: List<&2, Cv.Decl>, ss: List<&2, Cv.Bind>, r: W.Dec<Cv.Flag>) -> W.Dec<Ask>:
  match r:
    case W.Got{g, s}:
      W.Got{AskWritten{ds, ss, g}, s}
    case W.Bad{}:
      W.Bad{}

def get_wr.sets(ds: List<&2, Cv.Decl>, r: W.Dec<List<&2, Cv.Bind>>) -> W.Dec<Ask>:
  match r:
    case W.Got{ss, s}:
      get_wr.flag(ds, ss, get_flag.go(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_wr(r: W.Dec<List<&2, Cv.Decl>>) -> W.Dec<Ask>:
  match r:
    case W.Got{ds, s}:
      get_wr.sets(ds, get_binds(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_doc.global(ds: List<&2, Cv.Decl>, m: List<&2, Cv.Bind>, r: W.Dec<List<&2, Cv.Bind>>) -> W.Dec<Ask>:
  match r:
    case W.Got{g, s}:
      W.Got{AskDocument{ds, m, g}, s}
    case W.Bad{}:
      W.Bad{}

def get_doc.merged(ds: List<&2, Cv.Decl>, r: W.Dec<List<&2, Cv.Bind>>) -> W.Dec<Ask>:
  match r:
    case W.Got{m, s}:
      get_doc.global(ds, m, get_binds(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_doc(r: W.Dec<List<&2, Cv.Decl>>) -> W.Dec<Ask>:
  match r:
    case W.Got{ds, s}:
      get_doc.merged(ds, get_binds(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(t: Nat, s: String) -> W.Dec<Ask>:
  match t:
    case 0n:
      get_reg(get_decls(W.get_nat(s)))
    case 1n:
      get_vals(get_decls(W.get_nat(s)))
    case 2n:
      get_tog(get_decls(W.get_nat(s)))
    case 3n:
      get_chk(get_decls(W.get_nat(s)))
    case 4n:
      get_wr(get_decls(W.get_nat(s)))
    case 5n:
      get_doc(get_decls(W.get_nat(s)))
    case 6n+p:
      W.Bad{}

def get_ask.go(r: W.Dec<Nat>) -> W.Dec<Ask>:
  match r:
    case W.Got{t, s}:
      get_ask.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_ask(s: String) -> W.Dec<Ask>:
  get_ask.go(W.get_nat(s))

# Encoding
# --------

def put_val(v: Cv.Val, rest: String) -> String:
  match v:
    case Cv.VNat{n}:
      W.put_nat(0n, W.put_nat(n, rest))
    case Cv.VBool{b}:
      W.put_nat(1n, W.put_bool(b, rest))

def put_mval(m: Maybe<&2, Cv.Val>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{v}:
      W.put_nat(1n, put_val(v, rest))

def put_bind(b: Cv.Bind, rest: String) -> String:
  match b:
    case Cv.Bind{i, v}:
      W.put_nat(i, put_val(v, rest))

def put_binds.items(bs: List<&2, Cv.Bind>, rest: String) -> String:
  match bs:
    case Nil{}:
      rest
    case b <> t:
      put_bind(b, put_binds.items(t, rest))

def put_binds(+bs: List<&2, Cv.Bind>, rest: String) -> String:
  W.put_nat(List.length(&2, Cv.Bind, bs), put_binds.items(bs, rest))

def put_refusal(f: Cv.Refusal, rest: String) -> String:
  match f:
    case Cv.Accept{}:
      W.put_nat(0n, rest)
    case Cv.Twice{i}:
      W.put_nat(1n, W.put_nat(i, rest))
    case Cv.BadInit{i}:
      W.put_nat(2n, W.put_nat(i, rest))

def put_tog(t: Cv.Tog, rest: String) -> String:
  match t:
    case Cv.TgUndeclared{}:
      W.put_nat(0n, rest)
    case Cv.TgGlobal{}:
      W.put_nat(1n, rest)
    case Cv.TgNotBool{}:
      W.put_nat(2n, rest)
    case Cv.TgFlip{b}:
      W.put_nat(3n, put_bind(b, rest))

def put_check(c: Cv.Check, rest: String) -> String:
  match c:
    case Cv.CkUndeclared{}:
      W.put_nat(0n, rest)
    case Cv.CkGlobal{}:
      W.put_nat(1n, rest)
    case Cv.CkType{}:
      W.put_nat(2n, rest)
    case Cv.CkFine{}:
      W.put_nat(3n, rest)

# per declaration of xs: the value of its cvar, then the value a layer sets
def put_values.items(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +cfg: List<&2, Cv.Bind>, +fam: List<&2, Cv.Ag>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case d <> t:
      +x = Cv.Decl.id(d)
      put_mval(Cv.value(ds, cfg, fam, x), put_mval(Cv.layered(ds, cfg, fam, x), put_values.items(t, ds, cfg, fam, rest)))

# The entry
# ---------

# the answer to a request
def answer(a: Ask) -> String:
  match a:
    case AskRegistry{ds}:
      put_refusal(Cv.refusal(ds), "")
    case AskValues{+ds, c, f}:
      W.put_nat(List.length(&2, Cv.Decl, ds), put_values.items(ds, ds, c, f, ""))
    case AskToggle{ds, c, f, l, x}:
      put_tog(Cv.tog(ds, c, f, l, x), "")
    case AskCheck{ds, l, b}:
      put_check(Cv.check(ds, l, b), "")
    case AskWritten{ds, ss, g}:
      put_binds(Cv.written(ss, ds, g), "")
    case AskDocument{ds, m, g}:
      put_binds(Cv.document(ds, m, g), "")

def fail() -> String:
  W.err("cvar_layers: malformed request")

def run.end(whole: Bool, a: Ask) -> String:
  match whole:
    case True{}:
      answer(a)
    case False{}:
      fail()

def run(r: W.Dec<Ask>) -> String:
  match r:
    case W.Got{a, s}:
      run.end(W.end(s), a)
    case W.Bad{}:
      fail()

# a request in, its answer out
def ffi(input: String) -> String:
  run(get_ask(input))
