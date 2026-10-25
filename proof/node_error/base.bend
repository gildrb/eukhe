# eukhe: lemmas of the proofs of area node_error

import Base
import ../../bend/node_error.bend as Ne
import ../../bend/ffi_node_error.bend as FNe
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../../laws/node_error.bend as NodeError

# ---- logic ----

def ne.BD(b: Bool, T: Type, F: Type) -> Type:
  match b:
    case True{}:
      T
    case False{}:
      F

def ne.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : ne.BD(_, G, Unit)
  Unit{}

def ne.absurd_t(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : ne.BD(_, Unit, G)
  Unit{}

def ne.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ne.absurd({False{} == True{} : Bool}, e)

def ne.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      ne.absurd({b == True{} : Bool}, e)

def ne.and2(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def ne.under(-s: String, -s1: String, -y: String, -f: String -> String, e: {s == f(s1) : String}, p: {s1 == y : String}) -> {s == f(y) : String}:
  %p : {s == f(_) : String}
  e

# ---- the reply ----

# the file error code's writer is the spec's speller
def ne.put_file(k: Ne.FileCode, rest: String) -> {FNe.put_file(k, rest) == NodeError.spell_file(k, rest) : String}:
  match k:
    case Ne.NotFound{}:
      {==}
    case Ne.Denied{}:
      {==}
    case Ne.NotDir{}:
      {==}
    case Ne.IsDir{}:
      {==}
    case Ne.Invalid{}:
      {==}
    case Ne.Other{}:
      {==}

# an answer opens with the file error code's tag, never with 'E'
def ne.file_not_err(k: Ne.FileCode, rest: String) -> {LawsBase.wire_opens_err(FNe.put_file(k, rest)) == False{} : Bool}:
  match k:
    case Ne.NotFound{}:
      Wire.wire_nat_not_err(0n, rest)
    case Ne.Denied{}:
      Wire.wire_nat_not_err(1n, rest)
    case Ne.NotDir{}:
      Wire.wire_nat_not_err(2n, rest)
    case Ne.IsDir{}:
      Wire.wire_nat_not_err(3n, rest)
    case Ne.Invalid{}:
      Wire.wire_nat_not_err(4n, rest)
    case Ne.Other{}:
      Wire.wire_nat_not_err(5n, rest)

# an answer is never the error form
def ne.answer_not_err(q: FNe.Req) -> {LawsBase.wire_opens_err(FNe.ffi.done(q, True{})) == False{} : Bool}:
  match q:
    case FNe.Req{+c, f}:
      ne.file_not_err(Ne.file(c), Wr.put_str(Ne.message(c, f), ""))

# ---- round trips ----

def ne.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def ne.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

# every code's tag fits the wire
def ne.tag_fits(c: Ne.Code) -> {LawsBase.wire_fits(NodeError.tag_spec(c)) == True{} : Bool}:
  match c:
    case Ne.E2big{}:
      {==}
    case Ne.Eacces{}:
      {==}
    case Ne.Eagain{}:
      {==}
    case Ne.Ebadf{}:
      {==}
    case Ne.Ebusy{}:
      {==}
    case Ne.Ecanceled{}:
      {==}
    case Ne.Eexist{}:
      {==}
    case Ne.Efault{}:
      {==}
    case Ne.Efbig{}:
      {==}
    case Ne.Eintr{}:
      {==}
    case Ne.Einval{}:
      {==}
    case Ne.Eio{}:
      {==}
    case Ne.Eisdir{}:
      {==}
    case Ne.Eloop{}:
      {==}
    case Ne.Emfile{}:
      {==}
    case Ne.Emlink{}:
      {==}
    case Ne.Enametoolong{}:
      {==}
    case Ne.Enfile{}:
      {==}
    case Ne.Enodev{}:
      {==}
    case Ne.Enoent{}:
      {==}
    case Ne.Enoexec{}:
      {==}
    case Ne.Enomem{}:
      {==}
    case Ne.Enospc{}:
      {==}
    case Ne.Enosys{}:
      {==}
    case Ne.Enotdir{}:
      {==}
    case Ne.Enotempty{}:
      {==}
    case Ne.Enotsup{}:
      {==}
    case Ne.Enxio{}:
      {==}
    case Ne.Eoverflow{}:
      {==}
    case Ne.Eperm{}:
      {==}
    case Ne.Epipe{}:
      {==}
    case Ne.Erofs{}:
      {==}
    case Ne.Espipe{}:
      {==}
    case Ne.Esrch{}:
      {==}
    case Ne.Etimedout{}:
      {==}
    case Ne.Etxtbsy{}:
      {==}
    case Ne.Exdev{}:
      {==}
    case Ne.Unknown{}:
      {==}

# the code of a code's tag is the code
def ne.code_of_tag(c: Ne.Code, rest: String) -> {Wr.Got{c, rest} == FNe.get_code.of(FNe.code_of(NodeError.tag_spec(c)), rest) : Wr.Dec<Ne.Code>}:
  match c:
    case Ne.E2big{}:
      {==}
    case Ne.Eacces{}:
      {==}
    case Ne.Eagain{}:
      {==}
    case Ne.Ebadf{}:
      {==}
    case Ne.Ebusy{}:
      {==}
    case Ne.Ecanceled{}:
      {==}
    case Ne.Eexist{}:
      {==}
    case Ne.Efault{}:
      {==}
    case Ne.Efbig{}:
      {==}
    case Ne.Eintr{}:
      {==}
    case Ne.Einval{}:
      {==}
    case Ne.Eio{}:
      {==}
    case Ne.Eisdir{}:
      {==}
    case Ne.Eloop{}:
      {==}
    case Ne.Emfile{}:
      {==}
    case Ne.Emlink{}:
      {==}
    case Ne.Enametoolong{}:
      {==}
    case Ne.Enfile{}:
      {==}
    case Ne.Enodev{}:
      {==}
    case Ne.Enoent{}:
      {==}
    case Ne.Enoexec{}:
      {==}
    case Ne.Enomem{}:
      {==}
    case Ne.Enospc{}:
      {==}
    case Ne.Enosys{}:
      {==}
    case Ne.Enotdir{}:
      {==}
    case Ne.Enotempty{}:
      {==}
    case Ne.Enotsup{}:
      {==}
    case Ne.Enxio{}:
      {==}
    case Ne.Eoverflow{}:
      {==}
    case Ne.Eperm{}:
      {==}
    case Ne.Epipe{}:
      {==}
    case Ne.Erofs{}:
      {==}
    case Ne.Espipe{}:
      {==}
    case Ne.Esrch{}:
      {==}
    case Ne.Etimedout{}:
      {==}
    case Ne.Etxtbsy{}:
      {==}
    case Ne.Exdev{}:
      {==}
    case Ne.Unknown{}:
      {==}

# a spelled code reads back
def ne.code_rt(+c: Ne.Code, +rest: String) -> {Wr.Got{c, rest} == FNe.get_code(Wr.get_nat(NodeError.spell_code(c, rest))) : Wr.Dec<Ne.Code>}:
  %ne.nat(NodeError.tag_spec(c), rest, ne.tag_fits(c)) : {Wr.Got{c, rest} == FNe.get_code(_) : Wr.Dec<Ne.Code>}
  ne.code_of_tag(c, rest)

# a form whose texts fit reads back
def ne.form_rt(+f: Ne.Form, +rest: String, +h: {NodeError.form_fits(f) == True{} : Bool}) -> {Wr.Got{f, rest} == FNe.get_form(Wr.get_nat(NodeError.spell_form(f, rest))) : Wr.Dec<Ne.Form>}:
  match f:
    case Ne.Fd{+s}:
      %ne.nat(0n, Wr.put_str(s, rest), {==}) : {Wr.Got{Ne.Fd{s}, rest} == FNe.get_form(_) : Wr.Dec<Ne.Form>}
      %ne.str(s, rest, h) : {Wr.Got{Ne.Fd{s}, rest} == FNe.get_fd(_) : Wr.Dec<Ne.Form>}
      {==}
    case Ne.Path{+s, +p}:
      %ne.nat(1n, Wr.put_str(s, Wr.put_str(p, rest)), {==}) : {Wr.Got{Ne.Path{s, p}, rest} == FNe.get_form(_) : Wr.Dec<Ne.Form>}
      %ne.str(s, Wr.put_str(p, rest), ne.and_l(LawsBase.wire_fits(String.length(s)), LawsBase.wire_fits(String.length(p)), h)) : {Wr.Got{Ne.Path{s, p}, rest} == FNe.get_path(_) : Wr.Dec<Ne.Form>}
      %ne.str(p, rest, ne.and_r(LawsBase.wire_fits(String.length(s)), LawsBase.wire_fits(String.length(p)), h)) : {Wr.Got{Ne.Path{s, p}, rest} == FNe.get_path.path(s, _) : Wr.Dec<Ne.Form>}
      {==}
    case Ne.Dest{+s, +p, +t}:
      +hpt = ne.and_r(LawsBase.wire_fits(String.length(s)), Bool.and(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(t))), h)
      %ne.nat(2n, Wr.put_str(s, Wr.put_str(p, Wr.put_str(t, rest))), {==}) : {Wr.Got{Ne.Dest{s, p, t}, rest} == FNe.get_form(_) : Wr.Dec<Ne.Form>}
      %ne.str(s, Wr.put_str(p, Wr.put_str(t, rest)), ne.and_l(LawsBase.wire_fits(String.length(s)), Bool.and(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(t))), h)) : {Wr.Got{Ne.Dest{s, p, t}, rest} == FNe.get_dest(_) : Wr.Dec<Ne.Form>}
      %ne.str(p, Wr.put_str(t, rest), ne.and_l(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(t)), hpt)) : {Wr.Got{Ne.Dest{s, p, t}, rest} == FNe.get_dest.path(s, _) : Wr.Dec<Ne.Form>}
      %ne.str(t, rest, ne.and_r(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(t)), hpt)) : {Wr.Got{Ne.Dest{s, p, t}, rest} == FNe.get_dest.dest(s, p, _) : Wr.Dec<Ne.Form>}
      {==}
    case Ne.Spawn{+prog}:
      %ne.nat(3n, Wr.put_str(prog, rest), {==}) : {Wr.Got{Ne.Spawn{prog}, rest} == FNe.get_form(_) : Wr.Dec<Ne.Form>}
      %ne.str(prog, rest, h) : {Wr.Got{Ne.Spawn{prog}, rest} == FNe.get_spawn(_) : Wr.Dec<Ne.Form>}
      {==}

# a request that fits reads back: the entry is at its last step
def ne.reads(+q: FNe.Req, +rest: String, +h: {NodeError.req_fits(q) == True{} : Bool}) -> {FNe.ffi(NodeError.spell_req(q, rest)) == FNe.ffi.done(q, Wr.end(rest)) : String}:
  match q:
    case FNe.Req{+c, +f}:
      %ne.code_rt(c, NodeError.spell_form(f, rest)) : {FNe.ffi.got(FNe.get_req(_)) == FNe.ffi.done(FNe.Req{c, f}, Wr.end(rest)) : String}
      %ne.form_rt(f, rest, h) : {FNe.ffi.got(FNe.get_req.form(c, _)) == FNe.ffi.done(FNe.Req{c, f}, Wr.end(rest)) : String}
      {==}

# ---- exactness: what the decoder reads is spelled and fits ----

def ne.PN(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String}
    case Wr.Bad{}:
      Unit

def ne.pn_go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ne.PN(s, d):
  match d:
    case Wr.Got{+n, +r}:
      Wire.wire_nat_exact(s, n, r, ed)
    case Wr.Bad{}:
      Unit{}

def ne.pn(+s: String) -> ne.PN(s, Wr.get_nat(s)):
  ne.pn_go(s, Wr.get_nat(s), {==})

def ne.PS(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{+a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ne.ps_go(+s: String, d: Wr.Dec<String>, +ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> ne.PS(s, d):
  match d:
    case Wr.Got{+a, +r}:
      (Wire.wire_str_exact(s, a, r, ed), Wire.wire_str_decoded_fits(s, a, r, ed))
    case Wr.Bad{}:
      Unit{}

def ne.ps(+s: String) -> ne.PS(s, Wr.get_str(s)):
  ne.ps_go(s, Wr.get_str(s), {==})

# what the code decoder's answer says about its input s
def ne.PK(s: String, d: Wr.Dec<Ne.Code>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == NodeError.spell_code(c, r) : String}
    case Wr.Bad{}:
      Unit

def ne.pk_of(t: Nat, -s: String, -r: String, e: {s == Wr.put_nat(t, r) : String}) -> ne.PK(s, FNe.get_code.of(FNe.code_of(t), r)):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n:
      e
    case 4n:
      e
    case 5n:
      e
    case 6n:
      e
    case 7n:
      e
    case 8n:
      e
    case 9n:
      e
    case 10n:
      e
    case 11n:
      e
    case 12n:
      e
    case 13n:
      e
    case 14n:
      e
    case 15n:
      e
    case 16n:
      e
    case 17n:
      e
    case 18n:
      e
    case 19n:
      e
    case 20n:
      e
    case 21n:
      e
    case 22n:
      e
    case 23n:
      e
    case 24n:
      e
    case 25n:
      e
    case 26n:
      e
    case 27n:
      e
    case 28n:
      e
    case 29n:
      e
    case 30n:
      e
    case 31n:
      e
    case 32n:
      e
    case 33n:
      e
    case 34n:
      e
    case 35n:
      e
    case 36n:
      e
    case 37n:
      e
    case 38n+u:
      Unit{}

def ne.pk_top(-s: String, d: Wr.Dec<Nat>, pn: ne.PN(s, d)) -> ne.PK(s, FNe.get_code(d)):
  match d:
    case Wr.Got{t, r}:
      ne.pk_of(t, s, r, pn)
    case Wr.Bad{}:
      Unit{}

def ne.pk(+s: String) -> ne.PK(s, FNe.get_code(Wr.get_nat(s))):
  ne.pk_top(s, Wr.get_nat(s), ne.pn(s))

# what the form decoder's answer says about its input s
def ne.PF(s: String, d: Wr.Dec<Ne.Form>) -> Type:
  match d:
    case Wr.Got{+f, r}:
      {s == NodeError.spell_form(f, r) : String} & {NodeError.form_fits(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ne.pf_fd(-s: String, -s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, ps: ne.PS(s1, d)) -> ne.PF(s, FNe.get_fd(d)):
  match d:
    case Wr.Got{+y, +r}:
      (e1, f1) = ps
      (ne.under(s, s1, Wr.put_str(y, r), z => Wr.put_nat(0n, z), e0, e1), f1)
    case Wr.Bad{}:
      Unit{}

def ne.pf_path2(-s: String, +y: String, -s2: String, e: {s == Wr.put_nat(1n, Wr.put_str(y, s2)) : String}, fy: {LawsBase.wire_fits(String.length(y)) == True{} : Bool}, d: Wr.Dec<String>, ps: ne.PS(s2, d)) -> ne.PF(s, FNe.get_path.path(y, d)):
  match d:
    case Wr.Got{+p, +r}:
      (e1, f1) = ps
      (ne.under(s, s2, Wr.put_str(p, r), z => Wr.put_nat(1n, Wr.put_str(y, z)), e, e1), ne.and2(LawsBase.wire_fits(String.length(y)), LawsBase.wire_fits(String.length(p)), fy, f1))
    case Wr.Bad{}:
      Unit{}

def ne.pf_path(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, ps: ne.PS(s1, d)) -> ne.PF(s, FNe.get_path(d)):
  match d:
    case Wr.Got{+y, +s2}:
      (e1, f1) = ps
      ne.pf_path2(s, y, s2, ne.under(s, s1, Wr.put_str(y, s2), z => Wr.put_nat(1n, z), e0, e1), f1, Wr.get_str(s2), ne.ps(s2))
    case Wr.Bad{}:
      Unit{}

def ne.pf_dest3(-s: String, +y: String, +p: String, -s3: String, e: {s == Wr.put_nat(2n, Wr.put_str(y, Wr.put_str(p, s3))) : String}, fy: {LawsBase.wire_fits(String.length(y)) == True{} : Bool}, fp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}, d: Wr.Dec<String>, ps: ne.PS(s3, d)) -> ne.PF(s, FNe.get_dest.dest(y, p, d)):
  match d:
    case Wr.Got{+t, +r}:
      (e1, f1) = ps
      (ne.under(s, s3, Wr.put_str(t, r), z => Wr.put_nat(2n, Wr.put_str(y, Wr.put_str(p, z))), e, e1), ne.and2(LawsBase.wire_fits(String.length(y)), Bool.and(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(t))), fy, ne.and2(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(t)), fp, f1)))
    case Wr.Bad{}:
      Unit{}

def ne.pf_dest2(-s: String, +y: String, -s2: String, e: {s == Wr.put_nat(2n, Wr.put_str(y, s2)) : String}, fy: {LawsBase.wire_fits(String.length(y)) == True{} : Bool}, d: Wr.Dec<String>, ps: ne.PS(s2, d)) -> ne.PF(s, FNe.get_dest.path(y, d)):
  match d:
    case Wr.Got{+p, +s3}:
      (e1, f1) = ps
      ne.pf_dest3(s, y, p, s3, ne.under(s, s2, Wr.put_str(p, s3), z => Wr.put_nat(2n, Wr.put_str(y, z)), e, e1), fy, f1, Wr.get_str(s3), ne.ps(s3))
    case Wr.Bad{}:
      Unit{}

def ne.pf_dest(-s: String, -s1: String, e0: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, ps: ne.PS(s1, d)) -> ne.PF(s, FNe.get_dest(d)):
  match d:
    case Wr.Got{+y, +s2}:
      (e1, f1) = ps
      ne.pf_dest2(s, y, s2, ne.under(s, s1, Wr.put_str(y, s2), z => Wr.put_nat(2n, z), e0, e1), f1, Wr.get_str(s2), ne.ps(s2))
    case Wr.Bad{}:
      Unit{}

def ne.pf_spawn(-s: String, -s1: String, e0: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<String>, ps: ne.PS(s1, d)) -> ne.PF(s, FNe.get_spawn(d)):
  match d:
    case Wr.Got{+y, +r}:
      (e1, f1) = ps
      (ne.under(s, s1, Wr.put_str(y, r), z => Wr.put_nat(3n, z), e0, e1), f1)
    case Wr.Bad{}:
      Unit{}

def ne.pf_top(-s: String, d: Wr.Dec<Nat>, pn: ne.PN(s, d)) -> ne.PF(s, FNe.get_form(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          ne.pf_fd(s, s1, pn, Wr.get_str(s1), ne.ps(s1))
        case 1n:
          ne.pf_path(s, s1, pn, Wr.get_str(s1), ne.ps(s1))
        case 2n:
          ne.pf_dest(s, s1, pn, Wr.get_str(s1), ne.ps(s1))
        case 3n:
          ne.pf_spawn(s, s1, pn, Wr.get_str(s1), ne.ps(s1))
        case 4n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ne.pf(+s: String) -> ne.PF(s, FNe.get_form(Wr.get_nat(s))):
  ne.pf_top(s, Wr.get_nat(s), ne.pn(s))

# what the request decoder's answer says about its input s
def ne.PR(s: String, d: Wr.Dec<FNe.Req>) -> Type:
  match d:
    case Wr.Got{+q, r}:
      {s == NodeError.spell_req(q, r) : String} & {NodeError.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ne.pr_form(-s: String, -c: Ne.Code, -s1: String, e: {s == NodeError.spell_code(c, s1) : String}, d: Wr.Dec<Ne.Form>, pf: ne.PF(s1, d)) -> ne.PR(s, FNe.get_req.form(c, d)):
  match d:
    case Wr.Got{+f, +r}:
      (e1, f1) = pf
      (ne.under(s, s1, NodeError.spell_form(f, r), z => NodeError.spell_code(c, z), e, e1), f1)
    case Wr.Bad{}:
      Unit{}

def ne.pr_code(-s: String, d: Wr.Dec<Ne.Code>, pk: ne.PK(s, d)) -> ne.PR(s, FNe.get_req(d)):
  match d:
    case Wr.Got{+c, +s1}:
      ne.pr_form(s, c, s1, pk, FNe.get_form(Wr.get_nat(s1)), ne.pf(s1))
    case Wr.Bad{}:
      Unit{}

# every request the decoder reads is spelled, fits, and so is the input
# after it
def ne.pr(+s: String) -> ne.PR(s, FNe.get_req(FNe.get_code(Wr.get_nat(s)))):
  ne.pr_code(s, FNe.get_code(Wr.get_nat(s)), ne.pk(s))
