# eukhe: the proof of LAW launcher_ffi_reads_only_requests
#
# Each decoder layer that answers Got gives the prefix of its input as the
# laws spell it (the wire's exactness laws wire_nat_exact,
# wire_bool_exact) and every Nat it read fits the wire
# (wire_nat_decoded_fits); a predicate per layer (lr.NatOk .. lr.AskOk)
# carries that, and each layer is proven from the one below it. The
# answers of a commit: induction on the count. At the end, input left
# over, a Bad layer or an unknown tag answers the error form, which the
# premise refutes.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/launcher.bend as La
import ../../bend/ffi_launcher.bend as FLa
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/launcher.bend as Launcher
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ./base.bend as LLa

# The wire's primitives
# ---------------------

def lr.NatOk(s: String, r: Wr.Dec<Nat>) -> Type:
  match r:
    case Wr.Got{n, rest}:
      {s == Wr.put_nat(n, rest) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def lr.nat_go(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> lr.NatOk(s, r):
  match r:
    case Wr.Got{+n, +rest}:
      +er2 = er
      (Wire.wire_nat_exact(s, n, rest, er2), Wire.wire_nat_decoded_fits(s, n, rest, er2))
    case Wr.Bad{}:
      Unit{}

def lr.nat(+s: String) -> lr.NatOk(s, Wr.get_nat(s)):
  lr.nat_go(s, Wr.get_nat(s), {==})

def lr.BoolOk(s: String, r: Wr.Dec<Bool>) -> Type:
  match r:
    case Wr.Got{b, rest}:
      {s == Wr.put_bool(b, rest) : String}
    case Wr.Bad{}:
      Unit

def lr.bool_go(+s: String, r: Wr.Dec<Bool>, er: {Wr.get_bool(s) == r : Wr.Dec<Bool>}) -> lr.BoolOk(s, r):
  match r:
    case Wr.Got{+b, +rest}:
      Wire.wire_bool_exact(s, b, rest, er)
    case Wr.Bad{}:
      Unit{}

def lr.bool(+s: String) -> lr.BoolOk(s, Wr.get_bool(s)):
  lr.bool_go(s, Wr.get_bool(s), {==})

# The request
# -----------

# the request a with rest after it
def lr.sp(a: La.Ask, rest: String) -> String:
  match a:
    case La.AskPrompt{c}:
      Wr.put_nat(0n, Wr.put_bool(c, rest))
    case La.AskQuiesce{b, c}:
      Wr.put_nat(1n, Wr.put_bool(b, Wr.put_bool(c, rest)))
    case La.AskCommit{+xs}:
      Wr.put_nat(2n, Wr.put_nat(List.length(&2, Bool, xs), Launcher.spell_bools(xs, rest)))
    case La.AskAdopt{w}:
      match w:
        case None{}:
          Wr.put_nat(3n, Wr.put_nat(0n, rest))
        case Some{n}:
          Wr.put_nat(3n, Wr.put_nat(1n, Wr.put_nat(n, rest)))

def lr.sp_ask(a: La.Ask) -> {lr.sp(a, "") == Launcher.spell_ask(a) : String}:
  match a:
    case La.AskPrompt{c}:
      {==}
    case La.AskQuiesce{b, c}:
      {==}
    case La.AskCommit{xs}:
      {==}
    case La.AskAdopt{w}:
      match w:
        case None{}:
          {==}
        case Some{n}:
          {==}

def lr.AskOk(s: String, r: Wr.Dec<La.Ask>) -> Type:
  match r:
    case Wr.Got{a, rest}:
      {s == lr.sp(a, rest) : String} & {Launcher.ask_fits(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# A run start, a quiesce

def lr.prompt(-s: String, -s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, r: Wr.Dec<Bool>, h: lr.BoolOk(s1, r)) -> lr.AskOk(s, FLa.get_prompt(r)):
  match r:
    case Wr.Got{c, s2}:
      ((%h : {s == Wr.put_nat(0n, _) : String}; e0), {==})
    case Wr.Bad{}:
      Unit{}

def lr.quiesce_closed(-s: String, -s1: String, -b: Bool, -s2: String, e0: {s == Wr.put_nat(1n, s1) : String}, e1: {s1 == Wr.put_bool(b, s2) : String}, r: Wr.Dec<Bool>, h: lr.BoolOk(s2, r)) -> lr.AskOk(s, FLa.get_quiesce.closed(b, r)):
  match r:
    case Wr.Got{c, s3}:
      ((%h : {s == Wr.put_nat(1n, Wr.put_bool(b, _)) : String}; %e1 : {s == Wr.put_nat(1n, _) : String}; e0), {==})
    case Wr.Bad{}:
      Unit{}

def lr.quiesce(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, r: Wr.Dec<Bool>, h: lr.BoolOk(s1, r)) -> lr.AskOk(s, FLa.get_quiesce(r)):
  match r:
    case Wr.Got{b, +s2}:
      lr.quiesce_closed(s, s1, b, s2, e0, h, Wr.get_bool(s2), lr.bool(s2))
    case Wr.Bad{}:
      Unit{}

# The commit: the answers, by count

def lr.AnsOk(s: String, m: Nat, r: Wr.Dec<List<&2, Bool>>) -> Type:
  match r:
    case Wr.Got{xs, rest}:
      {s == Launcher.spell_bools(xs, rest) : String} & {List.length(&2, Bool, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def lr.ans_cons(-s: String, -x: Bool, -s1: String, -p: Nat, e: {s == Wr.put_bool(x, s1) : String}, r: Wr.Dec<List<&2, Bool>>, h: lr.AnsOk(s1, p, r)) -> lr.AnsOk(s, 1n+p, FLa.get_answers.cons(x, r)):
  match r:
    case Wr.Got{xs, s2}:
      (e2, len) = h
      ((%e2 : {s == Wr.put_bool(x, _) : String}; e), Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Bool, xs), 1n+p, len))
    case Wr.Bad{}:
      Unit{}

def lr.answers(m: Nat, -s: String, r: Wr.Dec<Bool>, h: lr.BoolOk(s, r)) -> lr.AnsOk(s, m, FLa.get_answers.go(m, r)):
  match m:
    case 0n:
      match r:
        case Wr.Got{x, s1}:
          (h, {==})
        case Wr.Bad{}:
          Unit{}
    case 1n++p:
      match r:
        case Wr.Got{x, +s1}:
          lr.ans_cons(s, x, s1, p, h, FLa.get_answers.go(p, Wr.get_bool(s1)), lr.answers(p, s1, Wr.get_bool(s1), lr.bool(s1)))
        case Wr.Bad{}:
          Unit{}

def lr.commit_answers(-s: String, -s0: String, -s1: String, -m: Nat, e0: {s == Wr.put_nat(2n, s0) : String}, e1: {s0 == Wr.put_nat(1n+m, s1) : String}, f1: {LawsBase.wire_fits(1n+m) == True{} : Bool}, r: Wr.Dec<List<&2, Bool>>, h: lr.AnsOk(s1, m, r)) -> lr.AskOk(s, FLa.get_commit.answers(r)):
  match r:
    case Wr.Got{xs, s2}:
      (e2, +len) = h
      ((%Equal.sym(Nat, List.length(&2, Bool, xs), 1n+m, len) : {s == Wr.put_nat(2n, Wr.put_nat(_, Launcher.spell_bools(xs, s2))) : String}; %e2 : {s == Wr.put_nat(2n, Wr.put_nat(1n+m, _)) : String}; %e1 : {s == Wr.put_nat(2n, _) : String}; e0), (%Equal.sym(Nat, List.length(&2, Bool, xs), 1n+m, len) : {LawsBase.wire_fits(_) == True{} : Bool}; f1))
    case Wr.Bad{}:
      Unit{}

def lr.commit(-s: String, -s0: String, e0: {s == Wr.put_nat(2n, s0) : String}, r: Wr.Dec<Nat>, h: lr.NatOk(s0, r)) -> lr.AskOk(s, FLa.get_commit(r)):
  match r:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          (e1, f1) = h
          ((%e1 : {s == Wr.put_nat(2n, _) : String}; e0), f1)
        case 1n++m:
          (e1, f1) = h
          lr.commit_answers(s, s0, s1, m, e0, e1, f1, FLa.get_answers.go(m, Wr.get_bool(s1)), lr.answers(m, s1, Wr.get_bool(s1), lr.bool(s1)))
    case Wr.Bad{}:
      Unit{}

# An adoption: the worker's build

def lr.adopt_some(-s: String, -s1: String, -s2: String, e0: {s == Wr.put_nat(3n, s1) : String}, e1: {s1 == Wr.put_nat(1n, s2) : String}, r: Wr.Dec<Nat>, h: lr.NatOk(s2, r)) -> lr.AskOk(s, FLa.get_adopt.some(r)):
  match r:
    case Wr.Got{n, s3}:
      (e2, f2) = h
      ((%e2 : {s == Wr.put_nat(3n, Wr.put_nat(1n, _)) : String}; %e1 : {s == Wr.put_nat(3n, _) : String}; e0), f2)
    case Wr.Bad{}:
      Unit{}

def lr.adopt(-s: String, -s1: String, e0: {s == Wr.put_nat(3n, s1) : String}, r: Wr.Dec<Nat>, h: lr.NatOk(s1, r)) -> lr.AskOk(s, FLa.get_adopt(r)):
  match r:
    case Wr.Got{t, +s2}:
      match t:
        case 0n:
          (e1, f1) = h
          ((%e1 : {s == Wr.put_nat(3n, _) : String}; e0), {==})
        case 1n:
          (e1, f1) = h
          lr.adopt_some(s, s1, s2, e0, e1, Wr.get_nat(s2), lr.nat(s2))
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# The request, whole
# ------------------

def lr.ask(-s: String, r: Wr.Dec<Nat>, h: lr.NatOk(s, r)) -> lr.AskOk(s, FLa.get_ask.go(r)):
  match r:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = h
          lr.prompt(s, s1, e0, Wr.get_bool(s1), lr.bool(s1))
        case 1n:
          (e0, f0) = h
          lr.quiesce(s, s1, e0, Wr.get_bool(s1), lr.bool(s1))
        case 2n:
          (e0, f0) = h
          lr.commit(s, s1, e0, Wr.get_nat(s1), lr.nat(s1))
        case 3n:
          (e0, f0) = h
          lr.adopt(s, s1, e0, Wr.get_nat(s1), lr.nat(s1))
        case 4n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def lr.G(s: String) -> Type:
  &a: La.Ask -> ({s == Launcher.spell_ask(a) : String} & {Launcher.ask_fits(a) == True{} : Bool})

# nothing left after the request: s is its spelling; anything else is the
# error form, which ok refutes
def lr.fin(-s: String, r: Wr.Dec<La.Ask>, h: lr.AskOk(s, r), ok: {LawsBase.wire_opens_err(FLa.run(r)) == False{} : Bool}) -> lr.G(s):
  match r:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          (e, f) = h
          (a, (Equal.trans(String, s, lr.sp(a, ""), Launcher.spell_ask(a), e, lr.sp_ask(a)), f))
        case SCon{c, t}:
          LLa.la.absurd(lr.G(s), Equal.sym(Bool, True{}, False{}, ok))
    case Wr.Bad{}:
      LLa.la.absurd(lr.G(s), Equal.sym(Bool, True{}, False{}, ok))

def Launcher.launcher_ffi_reads_only_requests(s, ok):
  lr.fin(s, FLa.get_ask(s), lr.ask(s, Wr.get_nat(s), lr.nat(s)), ok)
