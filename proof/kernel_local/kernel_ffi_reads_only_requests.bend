# eukhe: the proof of LAW kernel_ffi_reads_only_requests
#
# Each decoder layer that answers Got gives the prefix of its input as the
# laws spell it (the wire's exactness laws wire_nat_exact,
# wire_bool_exact) and every Nat it read fits the wire
# (wire_nat_decoded_fits); a predicate per layer (kr.NatOk .. kr.AskOk)
# carries that, and each layer is proven from the one below it. The files
# of a sweep: induction on the count. At the end, input left over, a Bad
# layer or an unknown tag answers the error form, which the premise
# refutes.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/kernel_local.bend as KL
import ../../bend/ffi_kernel_local.bend as FKL
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/kernel_local.bend as KernelLocal
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ./base.bend as LKL

# The wire's primitives
# ---------------------

def kr.NatOk(s: String, r: Wr.Dec<Nat>) -> Type:
  match r:
    case Wr.Got{n, rest}:
      {s == Wr.put_nat(n, rest) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def kr.nat_go(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> kr.NatOk(s, r):
  match r:
    case Wr.Got{+n, +rest}:
      +er2 = er
      (Wire.wire_nat_exact(s, n, rest, er2), Wire.wire_nat_decoded_fits(s, n, rest, er2))
    case Wr.Bad{}:
      Unit{}

def kr.nat(+s: String) -> kr.NatOk(s, Wr.get_nat(s)):
  kr.nat_go(s, Wr.get_nat(s), {==})

def kr.BoolOk(s: String, r: Wr.Dec<Bool>) -> Type:
  match r:
    case Wr.Got{b, rest}:
      {s == Wr.put_bool(b, rest) : String}
    case Wr.Bad{}:
      Unit

def kr.bool_go(+s: String, r: Wr.Dec<Bool>, er: {Wr.get_bool(s) == r : Wr.Dec<Bool>}) -> kr.BoolOk(s, r):
  match r:
    case Wr.Got{+b, +rest}:
      Wire.wire_bool_exact(s, b, rest, er)
    case Wr.Bad{}:
      Unit{}

def kr.bool(+s: String) -> kr.BoolOk(s, Wr.get_bool(s)):
  kr.bool_go(s, Wr.get_bool(s), {==})

# The request
# -----------

# the request a with rest after it
def kr.sp(a: KL.Ask, rest: String) -> String:
  match a:
    case KL.AskPlan{f, s}:
      Wr.put_nat(0n, KernelLocal.spell_found(f, KernelLocal.spell_setup(s, rest)))
    case KL.AskSweep{+ls}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, KL.Left, ls), KernelLocal.spell_lefts(ls, rest)))
    case KL.AskLock{x}:
      Wr.put_nat(2n, KernelLocal.spell_seen(x, rest))

def kr.sp_ask(a: KL.Ask) -> {kr.sp(a, "") == KernelLocal.spell_ask(a) : String}:
  match a:
    case KL.AskPlan{f, s}:
      {==}
    case KL.AskSweep{ls}:
      {==}
    case KL.AskLock{x}:
      {==}

def kr.AskOk(s: String, r: Wr.Dec<KL.Ask>) -> Type:
  match r:
    case Wr.Got{a, rest}:
      {s == kr.sp(a, rest) : String} & {KernelLocal.ask_fits(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# The plan: the venv found, the setup

def kr.FoundOk(s: String, r: Wr.Dec<KL.Found>) -> Type:
  match r:
    case Wr.Got{f, rest}:
      {s == KernelLocal.spell_found(f, rest) : String}
    case Wr.Bad{}:
      Unit

def kr.found(-s: String, r: Wr.Dec<Nat>, h: kr.NatOk(s, r)) -> kr.FoundOk(s, FKL.get_found.go(r)):
  match r:
    case Wr.Got{t, s1}:
      match t:
        case 0n:
          (e, fit) = h
          e
        case 1n:
          (e, fit) = h
          e
        case 2n:
          (e, fit) = h
          e
        case 3n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def kr.SetupOk(s: String, r: Wr.Dec<KL.Setup>) -> Type:
  match r:
    case Wr.Got{x, rest}:
      {s == KernelLocal.spell_setup(x, rest) : String}
    case Wr.Bad{}:
      Unit

def kr.setup(-s: String, r: Wr.Dec<Nat>, h: kr.NatOk(s, r)) -> kr.SetupOk(s, FKL.get_setup.go(r)):
  match r:
    case Wr.Got{t, s1}:
      match t:
        case 0n:
          (e, fit) = h
          e
        case 1n:
          (e, fit) = h
          e
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def kr.plan_setup(-s: String, -s1: String, -f: KL.Found, -s2: String, e0: {s == Wr.put_nat(0n, s1) : String}, e1: {s1 == KernelLocal.spell_found(f, s2) : String}, r: Wr.Dec<KL.Setup>, h: kr.SetupOk(s2, r)) -> kr.AskOk(s, FKL.get_plan.setup(f, r)):
  match r:
    case Wr.Got{x, s3}:
      ((%h : {s == Wr.put_nat(0n, KernelLocal.spell_found(f, _)) : String}; %e1 : {s == Wr.put_nat(0n, _) : String}; e0), {==})
    case Wr.Bad{}:
      Unit{}

def kr.plan(-s: String, -s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, r: Wr.Dec<KL.Found>, h: kr.FoundOk(s1, r)) -> kr.AskOk(s, FKL.get_plan.found(r)):
  match r:
    case Wr.Got{f, +s2}:
      kr.plan_setup(s, s1, f, s2, e0, h, FKL.get_setup.go(Wr.get_nat(s2)), kr.setup(s2, Wr.get_nat(s2), kr.nat(s2)))
    case Wr.Bad{}:
      Unit{}

# The sweep: the files, by count

def kr.KindOk(s: String, r: Wr.Dec<KL.FileKind>) -> Type:
  match r:
    case Wr.Got{k, rest}:
      {s == KernelLocal.spell_left.kind(k, rest) : String}
    case Wr.Bad{}:
      Unit

def kr.kind(-s: String, r: Wr.Dec<Nat>, h: kr.NatOk(s, r)) -> kr.KindOk(s, FKL.get_kind.go(r)):
  match r:
    case Wr.Got{t, s1}:
      match t:
        case 0n:
          (e, fit) = h
          e
        case 1n:
          (e, fit) = h
          e
        case 2n:
          (e, fit) = h
          e
        case 3n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def kr.LeftOk(s: String, r: Wr.Dec<KL.Left>) -> Type:
  match r:
    case Wr.Got{l, rest}:
      {s == KernelLocal.spell_left(l, rest) : String}
    case Wr.Bad{}:
      Unit

def kr.left_owner(-s: String, -k: KL.FileKind, -s1: String, e: {s == KernelLocal.spell_left.kind(k, s1) : String}, r: Wr.Dec<Bool>, h: kr.BoolOk(s1, r)) -> kr.LeftOk(s, FKL.get_left.owner(k, r)):
  match r:
    case Wr.Got{b, s2}:
      match b:
        case True{}:
          %h : {s == KernelLocal.spell_left.kind(k, _) : String}
          e
        case False{}:
          %h : {s == KernelLocal.spell_left.kind(k, _) : String}
          e
    case Wr.Bad{}:
      Unit{}

def kr.left_go(-s: String, r: Wr.Dec<KL.FileKind>, h: kr.KindOk(s, r)) -> kr.LeftOk(s, FKL.get_left.go(r)):
  match r:
    case Wr.Got{k, +s1}:
      kr.left_owner(s, k, s1, h, Wr.get_bool(s1), kr.bool(s1))
    case Wr.Bad{}:
      Unit{}

def kr.left(+s: String) -> kr.LeftOk(s, FKL.get_left(s)):
  kr.left_go(s, FKL.get_kind.go(Wr.get_nat(s)), kr.kind(s, Wr.get_nat(s), kr.nat(s)))

def kr.LeftsOk(s: String, m: Nat, r: Wr.Dec<List<&2, KL.Left>>) -> Type:
  match r:
    case Wr.Got{ls, rest}:
      {s == KernelLocal.spell_lefts(ls, rest) : String} & {List.length(&2, KL.Left, ls) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def kr.lefts_cons(-s: String, -l: KL.Left, -s1: String, -p: Nat, e: {s == KernelLocal.spell_left(l, s1) : String}, r: Wr.Dec<List<&2, KL.Left>>, h: kr.LeftsOk(s1, p, r)) -> kr.LeftsOk(s, 1n+p, FKL.get_lefts.cons(l, r)):
  match r:
    case Wr.Got{ls, s2}:
      (e2, len) = h
      ((%e2 : {s == KernelLocal.spell_left(l, _) : String}; e), Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, KL.Left, ls), 1n+p, len))
    case Wr.Bad{}:
      Unit{}

def kr.lefts(m: Nat, -s: String, r: Wr.Dec<KL.Left>, h: kr.LeftOk(s, r)) -> kr.LeftsOk(s, m, FKL.get_lefts.go(m, r)):
  match m:
    case 0n:
      match r:
        case Wr.Got{l, s1}:
          (h, {==})
        case Wr.Bad{}:
          Unit{}
    case 1n++p:
      match r:
        case Wr.Got{l, +s1}:
          kr.lefts_cons(s, l, s1, p, h, FKL.get_lefts.go(p, FKL.get_left(s1)), kr.lefts(p, s1, FKL.get_left(s1), kr.left(s1)))
        case Wr.Bad{}:
          Unit{}

def kr.sweep_files(-s: String, -s0: String, -s1: String, -m: Nat, e0: {s == Wr.put_nat(1n, s0) : String}, e1: {s0 == Wr.put_nat(1n+m, s1) : String}, f1: {LawsBase.wire_fits(1n+m) == True{} : Bool}, r: Wr.Dec<List<&2, KL.Left>>, h: kr.LeftsOk(s1, m, r)) -> kr.AskOk(s, FKL.get_sweep.files(r)):
  match r:
    case Wr.Got{ls, s2}:
      (e2, +len) = h
      ((%Equal.sym(Nat, List.length(&2, KL.Left, ls), 1n+m, len) : {s == Wr.put_nat(1n, Wr.put_nat(_, KernelLocal.spell_lefts(ls, s2))) : String}; %e2 : {s == Wr.put_nat(1n, Wr.put_nat(1n+m, _)) : String}; %e1 : {s == Wr.put_nat(1n, _) : String}; e0), (%Equal.sym(Nat, List.length(&2, KL.Left, ls), 1n+m, len) : {LawsBase.wire_fits(_) == True{} : Bool}; f1))
    case Wr.Bad{}:
      Unit{}

def kr.sweep(-s: String, -s0: String, e0: {s == Wr.put_nat(1n, s0) : String}, r: Wr.Dec<Nat>, h: kr.NatOk(s0, r)) -> kr.AskOk(s, FKL.get_sweep(r)):
  match r:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          (e1, f1) = h
          ((%e1 : {s == Wr.put_nat(1n, _) : String}; e0), f1)
        case 1n++m:
          (e1, f1) = h
          kr.sweep_files(s, s0, s1, m, e0, e1, f1, FKL.get_lefts.go(m, FKL.get_left(s1)), kr.lefts(m, s1, FKL.get_left(s1), kr.left(s1)))
    case Wr.Bad{}:
      Unit{}

# The lock: what the attempt saw

def kr.SeenOk(s: String, r: Wr.Dec<KL.Seen>) -> Type:
  match r:
    case Wr.Got{x, rest}:
      {s == KernelLocal.spell_seen(x, rest) : String} & {KernelLocal.ask_fits(KL.AskLock{x}) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def kr.owner(-s: String, -s1: String, e: {s == Wr.put_nat(2n, s1) : String}, r: Wr.Dec<Bool>, h: kr.BoolOk(s1, r)) -> kr.SeenOk(s, FKL.get_owner(r)):
  match r:
    case Wr.Got{b, s2}:
      ((%h : {s == Wr.put_nat(2n, _) : String}; e), {==})
    case Wr.Bad{}:
      Unit{}

def kr.age_some(-s: String, -s1: String, -s2: String, e: {s == Wr.put_nat(3n, s1) : String}, e1: {s1 == Wr.put_nat(1n, s2) : String}, r: Wr.Dec<Nat>, h: kr.NatOk(s2, r)) -> kr.SeenOk(s, FKL.get_age.some(r)):
  match r:
    case Wr.Got{a, s3}:
      (e2, f2) = h
      ((%e2 : {s == Wr.put_nat(3n, Wr.put_nat(1n, _)) : String}; %e1 : {s == Wr.put_nat(3n, _) : String}; e), f2)
    case Wr.Bad{}:
      Unit{}

def kr.age(-s: String, -s1: String, e: {s == Wr.put_nat(3n, s1) : String}, r: Wr.Dec<Nat>, h: kr.NatOk(s1, r)) -> kr.SeenOk(s, FKL.get_age.go(r)):
  match r:
    case Wr.Got{t, +s2}:
      match t:
        case 0n:
          (e1, f1) = h
          ((%e1 : {s == Wr.put_nat(3n, _) : String}; e), {==})
        case 1n:
          (e1, f1) = h
          kr.age_some(s, s1, s2, e, e1, Wr.get_nat(s2), kr.nat(s2))
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def kr.seen(-s: String, r: Wr.Dec<Nat>, h: kr.NatOk(s, r)) -> kr.SeenOk(s, FKL.get_seen.go(r)):
  match r:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e, fit) = h
          (e, {==})
        case 1n:
          (e, fit) = h
          (e, {==})
        case 2n:
          (e, fit) = h
          kr.owner(s, s1, e, Wr.get_bool(s1), kr.bool(s1))
        case 3n:
          (e, fit) = h
          kr.age(s, s1, e, Wr.get_nat(s1), kr.nat(s1))
        case 4n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def kr.lock(-s: String, -s1: String, e0: {s == Wr.put_nat(2n, s1) : String}, r: Wr.Dec<KL.Seen>, h: kr.SeenOk(s1, r)) -> kr.AskOk(s, FKL.get_lock(r)):
  match r:
    case Wr.Got{x, s2}:
      (e, f) = h
      ((%e : {s == Wr.put_nat(2n, _) : String}; e0), f)
    case Wr.Bad{}:
      Unit{}

# The request, whole
# ------------------

def kr.ask(-s: String, r: Wr.Dec<Nat>, h: kr.NatOk(s, r)) -> kr.AskOk(s, FKL.get_ask.go(r)):
  match r:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = h
          kr.plan(s, s1, e0, FKL.get_found.go(Wr.get_nat(s1)), kr.found(s1, Wr.get_nat(s1), kr.nat(s1)))
        case 1n:
          (e0, f0) = h
          kr.sweep(s, s1, e0, Wr.get_nat(s1), kr.nat(s1))
        case 2n:
          (e0, f0) = h
          kr.lock(s, s1, e0, FKL.get_seen.go(Wr.get_nat(s1)), kr.seen(s1, Wr.get_nat(s1), kr.nat(s1)))
        case 3n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def kr.G(s: String) -> Type:
  &a: KL.Ask -> ({s == KernelLocal.spell_ask(a) : String} & {KernelLocal.ask_fits(a) == True{} : Bool})

# nothing left after the request: s is its spelling; anything else is the
# error form, which ok refutes
def kr.fin(-s: String, r: Wr.Dec<KL.Ask>, h: kr.AskOk(s, r), ok: {LawsBase.wire_opens_err(FKL.run(r)) == False{} : Bool}) -> kr.G(s):
  match r:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          (e, f) = h
          (a, (Equal.trans(String, s, kr.sp(a, ""), KernelLocal.spell_ask(a), e, kr.sp_ask(a)), f))
        case SCon{c, t}:
          LKL.kl.absurd(kr.G(s), Equal.sym(Bool, True{}, False{}, ok))
    case Wr.Bad{}:
      LKL.kl.absurd(kr.G(s), Equal.sym(Bool, True{}, False{}, ok))

def KernelLocal.kernel_ffi_reads_only_requests(s, ok):
  kr.fin(s, FKL.get_ask(s), kr.ask(s, Wr.get_nat(s), kr.nat(s)), ok)
