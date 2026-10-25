# eukhe: lemmas of the entry proofs of area context_order: only spelled
# requests decode
#
# Each decoder of bend/ffi_context_order.bend answers Got only for the
# spec's spelling (laws/context_order.bend spell_*) of a value whose
# numbers fit: a predicate per decoder (coe.<X>: what its answer says
# about its input), proven stage by stage from the wire's exactness laws
# (wire_nat_exact, wire_nat_decoded_fits, wire_bool_exact); one loop per
# list type (coe.<l>.loop).

import Base
import ../../../bend/context_order.bend as Co
import ../../../bend/ffi_context_order.bend as FCo
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/context_order.bend as ContextOrder
import ../base.bend as LACo

# what the Nat decoder's answer says about its input s
def coe.PNF(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.pnf_go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> coe.PNF(s, d):
  match d:
    case Wr.Got{+n, +r}:
      (Wire.wire_nat_exact(s, n, r, ed), Wire.wire_nat_decoded_fits(s, n, r, ed))
    case Wr.Bad{}:
      Unit{}

def coe.pnf(+s: String) -> coe.PNF(s, Wr.get_nat(s)):
  coe.pnf_go(s, Wr.get_nat(s), {==})

# what the Bool decoder's answer says about its input s
def coe.PB(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def coe.pb_go(+s: String, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> coe.PB(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def coe.pb(+s: String) -> coe.PB(s, Wr.get_bool(s)):
  coe.pb_go(s, Wr.get_bool(s), {==})

# ---- stop reasons, roles ----

def coe.ST(s: String, d: Wr.Dec<Co.Stop>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == ContextOrder.spell_stop(x, r) : String}
    case Wr.Bad{}:
      Unit

def coe.st.top(-s: String, d: Wr.Dec<Nat>, p: coe.PNF(s, d)) -> coe.ST(s, FCo.get_stop.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          e0
        case 1n:
          (e0, f0) = p
          e0
        case 2n:
          (e0, f0) = p
          e0
        case 3n:
          (e0, f0) = p
          e0
        case 4n:
          (e0, f0) = p
          e0
        case 5n:
          (e0, f0) = p
          e0
        case 6n:
          (e0, f0) = p
          e0
        case 7n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def coe.stop(+s: String) -> coe.ST(s, FCo.get_stop(s)):
  coe.st.top(s, Wr.get_nat(s), coe.pnf(s))

def coe.RO(s: String, d: Wr.Dec<Co.Role>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == ContextOrder.spell_role(x, r) : String}
    case Wr.Bad{}:
      Unit

def coe.ro.top(-s: String, d: Wr.Dec<Nat>, p: coe.PNF(s, d)) -> coe.RO(s, FCo.get_role.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          e0
        case 1n:
          (e0, f0) = p
          e0
        case 2n:
          (e0, f0) = p
          e0
        case 3n:
          (e0, f0) = p
          e0
        case 4n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def coe.role(+s: String) -> coe.RO(s, FCo.get_role(s)):
  coe.ro.top(s, Wr.get_nat(s), coe.pnf(s))

# what the item loop over roles answers says about its input s (m + 1 items)
def coe.rl.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Co.Role>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ContextOrder.spell_roles.items(xs, r) : String} & {List.length(&2, Co.Role, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def coe.rl.step(-s: String, +x: Co.Role, +s3: String, -k: Nat, ex: {s == ContextOrder.spell_role(x, s3) : String}, d: Wr.Dec<List<&2, Co.Role>>, ih: coe.rl.PL(s3, k, d)) -> coe.rl.PL(s, 1n+k, Wr.get_list.cons(Co.Role, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, ContextOrder.spell_role(x, s3), ContextOrder.spell_role(x, ContextOrder.spell_roles.items(ys, r)), ex, Equal.cong(String, String, z => ContextOrder.spell_role(x, z), s3, ContextOrder.spell_roles.items(ys, r), e1)), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Co.Role, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

def coe.rl.loop(m: Nat, cur: Wr.Dec<Co.Role>, +s: String, pc: coe.RO(s, cur)) -> coe.rl.PL(s, m, Wr.get_list.go(~Co.Role, ~FCo.get_role, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (pc, {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      coe.rl.step(s, x, s3, k, pc, Wr.get_list.go(~Co.Role, ~FCo.get_role, k, FCo.get_role(s3)), coe.rl.loop(k, FCo.get_role(s3), s3, coe.role(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def coe.rl.LS(s: String, d: Wr.Dec<List<&2, Co.Role>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Co.Role, xs), ContextOrder.spell_roles.items(xs, r)) : String} & {LawsBase.wire_fits(List.length(&2, Co.Role, xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.rl.conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Co.Role>>, pl: coe.rl.PL(s2, m, d)) -> coe.rl.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, +e2) = pl
      +e2s = Equal.sym(Nat, List.length(&2, Co.Role, xs), 1n+m, e2)
      %e2s : {s == Wr.put_nat(_, ContextOrder.spell_roles.items(xs, r)) : String} & {LawsBase.wire_fits(_) == True{} : Bool}
      %e1 : {s == Wr.put_nat(1n+m, _) : String} & {LawsBase.wire_fits(1n+m) == True{} : Bool}
      (en, fn)
    case Wr.Bad{}:
      Unit{}

def coe.rl.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> coe.rl.LS(s, Wr.get_list.start(~Co.Role, ~FCo.get_role, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      coe.rl.conv(s, s2, m, en, fn, Wr.get_list.go(~Co.Role, ~FCo.get_role, m, FCo.get_role(s2)), coe.rl.loop(m, FCo.get_role(s2), s2, coe.role(s2)))

def coe.rl.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> coe.rl.LS(s, Wr.get_list.start(~Co.Role, ~FCo.get_role, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      coe.rl.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of roles decoded is spelled, and its count fits
def coe.rl.list(+s: String) -> coe.rl.LS(s, Wr.get_list(~Co.Role, ~FCo.get_role, s)):
  coe.rl.top(s, Wr.get_nat(s), {==})

# ---- call ids ----

def coe.NI(s: String, d: Wr.Dec<Nat>) -> Type:
  coe.PNF(s, d)

# what the item loop over Nat answers says about its input s (m + 1 items)
def coe.nl.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == LawsBase.wire_spell_nats.items(xs, r) : String} & ({List.length(&2, Nat, xs) == 1n+m : Nat} & {LawsBase.wire_nats_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def coe.nl.step(-s: String, +x: Nat, +s3: String, -k: Nat, ex: {s == Wr.put_nat(x, s3) : String}, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ih: coe.nl.PL(s3, k, d)) -> coe.nl.PL(s, 1n+k, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, rest) = ih
      (e2, e3) = rest
      (Equal.trans(String, s, Wr.put_nat(x, s3), Wr.put_nat(x, LawsBase.wire_spell_nats.items(ys, r)), ex, Equal.cong(String, String, z => Wr.put_nat(x, z), s3, LawsBase.wire_spell_nats.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Nat, ys), 1n+k, e2), LACo.co.and_tt(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items whose numbers fit
def coe.nl.loop(m: Nat, cur: Wr.Dec<Nat>, +s: String, pc: coe.PNF(s, cur)) -> coe.nl.PL(s, m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LACo.co.and_tt(LawsBase.wire_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      coe.nl.step(s, x, s3, k, e, f, Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(s3)), coe.nl.loop(k, Wr.get_nat(s3), s3, coe.pnf(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def coe.nl.LS(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Nat, xs), LawsBase.wire_spell_nats.items(xs, r)) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.nl.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Nat>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == LawsBase.wire_spell_nats.items(xs, r) : String}, e2: {List.length(&2, Nat, xs) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, Nat, xs), LawsBase.wire_spell_nats.items(xs, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e2) : {s == Wr.put_nat(_, LawsBase.wire_spell_nats.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def coe.nl.conv_f(+m: Nat, +xs: List<&2, Nat>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Nat, xs) == 1n+m : Nat}, e3: {LawsBase.wire_nats_fit(xs) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
  LACo.co.and_tt(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(xs), fn, e3)

def coe.nl.conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, pl: coe.nl.PL(s2, m, d)) -> coe.nl.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, rest) = pl
      (+e2, e3) = rest
      (coe.nl.conv_s(s, s2, m, xs, r, en, e1, e2), coe.nl.conv_f(m, xs, fn, e2, e3))
    case Wr.Bad{}:
      Unit{}

def coe.nl.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> coe.nl.LS(s, Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      coe.nl.conv(s, s2, m, en, fn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s2)), coe.nl.loop(m, Wr.get_nat(s2), s2, coe.pnf(s2)))

def coe.nl.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> coe.nl.LS(s, Wr.get_list.start(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      coe.nl.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of Nat decoded is spelled, and its count and items fit
def coe.nl.list(+s: String) -> coe.nl.LS(s, Wr.get_list(~Nat, ~Wr.get_nat, s)):
  coe.nl.top(s, Wr.get_nat(s), {==})

# ---- messages ----

def coe.MS(s: String, d: Wr.Dec<Co.Msg>) -> Type:
  match d:
    case Wr.Got{+m, r}:
      {s == ContextOrder.spell_msg(m, r) : String} & {ContextOrder.msg_fits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.ms.calls(-s: String, -s2: String, +st: Co.Stop, e0: {s == Wr.put_nat(2n, ContextOrder.spell_stop(st, s2)) : String}, d: Wr.Dec<List<&2, Nat>>, p: coe.nl.LS(s2, d)) -> coe.MS(s, FCo.get_msg.calls(st, d)):
  match d:
    case Wr.Got{+cs, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(2n, ContextOrder.spell_stop(st, s2)), Wr.put_nat(2n, ContextOrder.spell_stop(st, LawsBase.wire_spell_nats(cs, r))), e0, Equal.cong(String, String, z => Wr.put_nat(2n, ContextOrder.spell_stop(st, z)), s2, LawsBase.wire_spell_nats(cs, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def coe.ms.stop(-s: String, -s1: String, e0: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Co.Stop>, p: coe.ST(s1, d)) -> coe.MS(s, FCo.get_msg.stop(d)):
  match d:
    case Wr.Got{+st, +s2}:
      coe.ms.calls(s, s2, st, Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, ContextOrder.spell_stop(st, s2)), e0, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, ContextOrder.spell_stop(st, s2), p)), Wr.get_list(~Nat, ~Wr.get_nat, s2), coe.nl.list(s2))
    case Wr.Bad{}:
      Unit{}

def coe.ms.res(-s: String, -s1: String, e0: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Nat>, p: coe.PNF(s1, d)) -> coe.MS(s, FCo.get_msg.res(d)):
  match d:
    case Wr.Got{+c, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(3n, s1), Wr.put_nat(3n, Wr.put_nat(c, r)), e0, Equal.cong(String, String, z => Wr.put_nat(3n, z), s1, Wr.put_nat(c, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def coe.ms.top(-s: String, d: Wr.Dec<Nat>, p: coe.PNF(s, d)) -> coe.MS(s, FCo.get_msg.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          (e0, {==})
        case 1n:
          (e0, f0) = p
          (e0, {==})
        case 2n:
          (e0, f0) = p
          coe.ms.stop(s, s1, e0, FCo.get_stop(s1), coe.stop(s1))
        case 3n:
          (e0, f0) = p
          coe.ms.res(s, s1, e0, Wr.get_nat(s1), coe.pnf(s1))
        case 4n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a message decoded is spelled, and its numbers fit
def coe.msg(+s: String) -> coe.MS(s, FCo.get_msg(s)):
  coe.ms.top(s, Wr.get_nat(s), coe.pnf(s))

# what the item loop over Co.Msg answers says about its input s (m + 1 items)
def coe.ml.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Co.Msg>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ContextOrder.spell_msgs.items(xs, r) : String} & ({List.length(&2, Co.Msg, xs) == 1n+m : Nat} & {ContextOrder.msgs_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def coe.ml.step(-s: String, +x: Co.Msg, +s3: String, -k: Nat, ex: {s == ContextOrder.spell_msg(x, s3) : String}, fx: {ContextOrder.msg_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Co.Msg>>, ih: coe.ml.PL(s3, k, d)) -> coe.ml.PL(s, 1n+k, Wr.get_list.cons(Co.Msg, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, rest) = ih
      (e2, e3) = rest
      (Equal.trans(String, s, ContextOrder.spell_msg(x, s3), ContextOrder.spell_msg(x, ContextOrder.spell_msgs.items(ys, r)), ex, Equal.cong(String, String, z => ContextOrder.spell_msg(x, z), s3, ContextOrder.spell_msgs.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Co.Msg, ys), 1n+k, e2), LACo.co.and_tt(ContextOrder.msg_fits(x), ContextOrder.msgs_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items whose numbers fit
def coe.ml.loop(m: Nat, cur: Wr.Dec<Co.Msg>, +s: String, pc: coe.MS(s, cur)) -> coe.ml.PL(s, m, Wr.get_list.go(~Co.Msg, ~FCo.get_msg, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LACo.co.and_tt(ContextOrder.msg_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      coe.ml.step(s, x, s3, k, e, f, Wr.get_list.go(~Co.Msg, ~FCo.get_msg, k, FCo.get_msg(s3)), coe.ml.loop(k, FCo.get_msg(s3), s3, coe.msg(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def coe.ml.LS(s: String, d: Wr.Dec<List<&2, Co.Msg>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Co.Msg, xs), ContextOrder.spell_msgs.items(xs, r)) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Co.Msg, xs)), ContextOrder.msgs_all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.ml.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Co.Msg>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == ContextOrder.spell_msgs.items(xs, r) : String}, e2: {List.length(&2, Co.Msg, xs) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, Co.Msg, xs), ContextOrder.spell_msgs.items(xs, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Co.Msg, xs), 1n+m, e2) : {s == Wr.put_nat(_, ContextOrder.spell_msgs.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def coe.ml.conv_f(+m: Nat, +xs: List<&2, Co.Msg>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Co.Msg, xs) == 1n+m : Nat}, e3: {ContextOrder.msgs_all(xs) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Co.Msg, xs)), ContextOrder.msgs_all(xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Co.Msg, xs), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), ContextOrder.msgs_all(xs)) == True{} : Bool}
  LACo.co.and_tt(LawsBase.wire_fits(1n+m), ContextOrder.msgs_all(xs), fn, e3)

def coe.ml.conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Co.Msg>>, pl: coe.ml.PL(s2, m, d)) -> coe.ml.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, rest) = pl
      (+e2, e3) = rest
      (coe.ml.conv_s(s, s2, m, xs, r, en, e1, e2), coe.ml.conv_f(m, xs, fn, e2, e3))
    case Wr.Bad{}:
      Unit{}

def coe.ml.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> coe.ml.LS(s, Wr.get_list.start(~Co.Msg, ~FCo.get_msg, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      coe.ml.conv(s, s2, m, en, fn, Wr.get_list.go(~Co.Msg, ~FCo.get_msg, m, FCo.get_msg(s2)), coe.ml.loop(m, FCo.get_msg(s2), s2, coe.msg(s2)))

def coe.ml.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> coe.ml.LS(s, Wr.get_list.start(~Co.Msg, ~FCo.get_msg, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      coe.ml.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of Co.Msg decoded is spelled, and its count and items fit
def coe.ml.list(+s: String) -> coe.ml.LS(s, Wr.get_list(~Co.Msg, ~FCo.get_msg, s)):
  coe.ml.top(s, Wr.get_nat(s), {==})

# ---- edits, entries, added entries ----

def coe.ED(s: String, d: Wr.Dec<Co.Edit>) -> Type:
  match d:
    case Wr.Got{+e, r}:
      {s == ContextOrder.spell_edit(e, r) : String} & {ContextOrder.edit_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.ed.ms(-s: String, -s1: String, e0: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<List<&2, Co.Msg>>, p: coe.ml.LS(s1, d)) -> coe.ED(s, FCo.get_edit.ms(d)):
  match d:
    case Wr.Got{+ms, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, ContextOrder.spell_msgs(ms, r)), e0, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, ContextOrder.spell_msgs(ms, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def coe.ed.top(-s: String, d: Wr.Dec<Nat>, p: coe.PNF(s, d)) -> coe.ED(s, FCo.get_edit.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          (e0, {==})
        case 1n:
          (e0, f0) = p
          (e0, {==})
        case 2n:
          (e0, f0) = p
          coe.ed.ms(s, s1, e0, FCo.get_msgs(s1), coe.ml.list(s1))
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def coe.edit(+s: String) -> coe.ED(s, FCo.get_edit(s)):
  coe.ed.top(s, Wr.get_nat(s), coe.pnf(s))

def coe.EN(s: String, d: Wr.Dec<Co.Ent>) -> Type:
  match d:
    case Wr.Got{+e, r}:
      {s == ContextOrder.spell_ent(e, r) : String} & {ContextOrder.ent_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.en.own(-s: String, -s2: String, +h: Bool, +ed: Co.Edit, e0: {s == Wr.put_bool(h, ContextOrder.spell_edit(ed, s2)) : String}, fe: {ContextOrder.edit_fits(ed) == True{} : Bool}, d: Wr.Dec<List<&2, Co.Msg>>, p: coe.ml.LS(s2, d)) -> coe.EN(s, FCo.get_ent.own(h, ed, d)):
  match d:
    case Wr.Got{+ms, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_bool(h, ContextOrder.spell_edit(ed, s2)), Wr.put_bool(h, ContextOrder.spell_edit(ed, ContextOrder.spell_msgs(ms, r))), e0, Equal.cong(String, String, z => Wr.put_bool(h, ContextOrder.spell_edit(ed, z)), s2, ContextOrder.spell_msgs(ms, r), e1)), LACo.co.and_tt(ContextOrder.edit_fits(ed), ContextOrder.msgs_fit(ms), fe, f1))
    case Wr.Bad{}:
      Unit{}

def coe.en.edit(-s: String, -s1: String, +h: Bool, e0: {s == Wr.put_bool(h, s1) : String}, d: Wr.Dec<Co.Edit>, p: coe.ED(s1, d)) -> coe.EN(s, FCo.get_ent.edit(h, d)):
  match d:
    case Wr.Got{+ed, +s2}:
      (e1, f1) = p
      coe.en.own(s, s2, h, ed, Equal.trans(String, s, Wr.put_bool(h, s1), Wr.put_bool(h, ContextOrder.spell_edit(ed, s2)), e0, Equal.cong(String, String, z => Wr.put_bool(h, z), s1, ContextOrder.spell_edit(ed, s2), e1)), f1, FCo.get_msgs(s2), coe.ml.list(s2))
    case Wr.Bad{}:
      Unit{}

def coe.en.head(-s: String, d: Wr.Dec<Bool>, p: coe.PB(s, d)) -> coe.EN(s, FCo.get_ent.head(d)):
  match d:
    case Wr.Got{+h, +s1}:
      coe.en.edit(s, s1, h, p, FCo.get_edit(s1), coe.edit(s1))
    case Wr.Bad{}:
      Unit{}

# an entry decoded is spelled, and its numbers fit
def coe.ent(+s: String) -> coe.EN(s, FCo.get_ent(s)):
  coe.en.head(s, Wr.get_bool(s), coe.pb(s))

def coe.AD(s: String, d: Wr.Dec<Co.Add>) -> Type:
  match d:
    case Wr.Got{+a, r}:
      {s == ContextOrder.spell_add(a, r) : String} & {ContextOrder.add_fits(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.ad.own(-s: String, -s3: String, +x: Bool, +h: Bool, +dd: Bool, e0: {s == Wr.put_bool(x, Wr.put_bool(h, Wr.put_bool(dd, s3))) : String}, d: Wr.Dec<List<&2, Co.Msg>>, p: coe.ml.LS(s3, d)) -> coe.AD(s, FCo.get_add.own(x, h, dd, d)):
  match d:
    case Wr.Got{+ms, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_bool(x, Wr.put_bool(h, Wr.put_bool(dd, s3))), Wr.put_bool(x, Wr.put_bool(h, Wr.put_bool(dd, ContextOrder.spell_msgs(ms, r)))), e0, Equal.cong(String, String, z => Wr.put_bool(x, Wr.put_bool(h, Wr.put_bool(dd, z))), s3, ContextOrder.spell_msgs(ms, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def coe.ad.edited(-s: String, -s2: String, +x: Bool, +h: Bool, e0: {s == Wr.put_bool(x, Wr.put_bool(h, s2)) : String}, d: Wr.Dec<Bool>, p: coe.PB(s2, d)) -> coe.AD(s, FCo.get_add.edited(x, h, d)):
  match d:
    case Wr.Got{+dd, +s3}:
      coe.ad.own(s, s3, x, h, dd, Equal.trans(String, s, Wr.put_bool(x, Wr.put_bool(h, s2)), Wr.put_bool(x, Wr.put_bool(h, Wr.put_bool(dd, s3))), e0, Equal.cong(String, String, z => Wr.put_bool(x, Wr.put_bool(h, z)), s2, Wr.put_bool(dd, s3), p)), FCo.get_msgs(s3), coe.ml.list(s3))
    case Wr.Bad{}:
      Unit{}

def coe.ad.head(-s: String, -s1: String, +x: Bool, e0: {s == Wr.put_bool(x, s1) : String}, d: Wr.Dec<Bool>, p: coe.PB(s1, d)) -> coe.AD(s, FCo.get_add.head(x, d)):
  match d:
    case Wr.Got{+h, +s2}:
      coe.ad.edited(s, s2, x, h, Equal.trans(String, s, Wr.put_bool(x, s1), Wr.put_bool(x, Wr.put_bool(h, s2)), e0, Equal.cong(String, String, z => Wr.put_bool(x, z), s1, Wr.put_bool(h, s2), p)), Wr.get_bool(s2), coe.pb(s2))
    case Wr.Bad{}:
      Unit{}

def coe.ad.edits(-s: String, d: Wr.Dec<Bool>, p: coe.PB(s, d)) -> coe.AD(s, FCo.get_add.edits(d)):
  match d:
    case Wr.Got{+x, +s1}:
      coe.ad.head(s, s1, x, p, Wr.get_bool(s1), coe.pb(s1))
    case Wr.Bad{}:
      Unit{}

# an added entry decoded is spelled, and its numbers fit
def coe.add(+s: String) -> coe.AD(s, FCo.get_add(s)):
  coe.ad.edits(s, Wr.get_bool(s), coe.pb(s))

# what the item loop over Co.Ent answers says about its input s (m + 1 items)
def coe.el.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Co.Ent>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ContextOrder.spell_ents.items(xs, r) : String} & ({List.length(&2, Co.Ent, xs) == 1n+m : Nat} & {ContextOrder.ents_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def coe.el.step(-s: String, +x: Co.Ent, +s3: String, -k: Nat, ex: {s == ContextOrder.spell_ent(x, s3) : String}, fx: {ContextOrder.ent_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Co.Ent>>, ih: coe.el.PL(s3, k, d)) -> coe.el.PL(s, 1n+k, Wr.get_list.cons(Co.Ent, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, rest) = ih
      (e2, e3) = rest
      (Equal.trans(String, s, ContextOrder.spell_ent(x, s3), ContextOrder.spell_ent(x, ContextOrder.spell_ents.items(ys, r)), ex, Equal.cong(String, String, z => ContextOrder.spell_ent(x, z), s3, ContextOrder.spell_ents.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Co.Ent, ys), 1n+k, e2), LACo.co.and_tt(ContextOrder.ent_fits(x), ContextOrder.ents_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items whose numbers fit
def coe.el.loop(m: Nat, cur: Wr.Dec<Co.Ent>, +s: String, pc: coe.EN(s, cur)) -> coe.el.PL(s, m, Wr.get_list.go(~Co.Ent, ~FCo.get_ent, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LACo.co.and_tt(ContextOrder.ent_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      coe.el.step(s, x, s3, k, e, f, Wr.get_list.go(~Co.Ent, ~FCo.get_ent, k, FCo.get_ent(s3)), coe.el.loop(k, FCo.get_ent(s3), s3, coe.ent(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def coe.el.LS(s: String, d: Wr.Dec<List<&2, Co.Ent>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Co.Ent, xs), ContextOrder.spell_ents.items(xs, r)) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Co.Ent, xs)), ContextOrder.ents_all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.el.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Co.Ent>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == ContextOrder.spell_ents.items(xs, r) : String}, e2: {List.length(&2, Co.Ent, xs) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, Co.Ent, xs), ContextOrder.spell_ents.items(xs, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Co.Ent, xs), 1n+m, e2) : {s == Wr.put_nat(_, ContextOrder.spell_ents.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def coe.el.conv_f(+m: Nat, +xs: List<&2, Co.Ent>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Co.Ent, xs) == 1n+m : Nat}, e3: {ContextOrder.ents_all(xs) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Co.Ent, xs)), ContextOrder.ents_all(xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Co.Ent, xs), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), ContextOrder.ents_all(xs)) == True{} : Bool}
  LACo.co.and_tt(LawsBase.wire_fits(1n+m), ContextOrder.ents_all(xs), fn, e3)

def coe.el.conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Co.Ent>>, pl: coe.el.PL(s2, m, d)) -> coe.el.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, rest) = pl
      (+e2, e3) = rest
      (coe.el.conv_s(s, s2, m, xs, r, en, e1, e2), coe.el.conv_f(m, xs, fn, e2, e3))
    case Wr.Bad{}:
      Unit{}

def coe.el.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> coe.el.LS(s, Wr.get_list.start(~Co.Ent, ~FCo.get_ent, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      coe.el.conv(s, s2, m, en, fn, Wr.get_list.go(~Co.Ent, ~FCo.get_ent, m, FCo.get_ent(s2)), coe.el.loop(m, FCo.get_ent(s2), s2, coe.ent(s2)))

def coe.el.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> coe.el.LS(s, Wr.get_list.start(~Co.Ent, ~FCo.get_ent, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      coe.el.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of Co.Ent decoded is spelled, and its count and items fit
def coe.el.list(+s: String) -> coe.el.LS(s, Wr.get_list(~Co.Ent, ~FCo.get_ent, s)):
  coe.el.top(s, Wr.get_nat(s), {==})

# what the item loop over Co.Add answers says about its input s (m + 1 items)
def coe.al.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Co.Add>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ContextOrder.spell_adds.items(xs, r) : String} & ({List.length(&2, Co.Add, xs) == 1n+m : Nat} & {ContextOrder.adds_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def coe.al.step(-s: String, +x: Co.Add, +s3: String, -k: Nat, ex: {s == ContextOrder.spell_add(x, s3) : String}, fx: {ContextOrder.add_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Co.Add>>, ih: coe.al.PL(s3, k, d)) -> coe.al.PL(s, 1n+k, Wr.get_list.cons(Co.Add, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, rest) = ih
      (e2, e3) = rest
      (Equal.trans(String, s, ContextOrder.spell_add(x, s3), ContextOrder.spell_add(x, ContextOrder.spell_adds.items(ys, r)), ex, Equal.cong(String, String, z => ContextOrder.spell_add(x, z), s3, ContextOrder.spell_adds.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Co.Add, ys), 1n+k, e2), LACo.co.and_tt(ContextOrder.add_fits(x), ContextOrder.adds_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items whose numbers fit
def coe.al.loop(m: Nat, cur: Wr.Dec<Co.Add>, +s: String, pc: coe.AD(s, cur)) -> coe.al.PL(s, m, Wr.get_list.go(~Co.Add, ~FCo.get_add, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LACo.co.and_tt(ContextOrder.add_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      coe.al.step(s, x, s3, k, e, f, Wr.get_list.go(~Co.Add, ~FCo.get_add, k, FCo.get_add(s3)), coe.al.loop(k, FCo.get_add(s3), s3, coe.add(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def coe.al.LS(s: String, d: Wr.Dec<List<&2, Co.Add>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Co.Add, xs), ContextOrder.spell_adds.items(xs, r)) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Co.Add, xs)), ContextOrder.adds_all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.al.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Co.Add>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == ContextOrder.spell_adds.items(xs, r) : String}, e2: {List.length(&2, Co.Add, xs) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, Co.Add, xs), ContextOrder.spell_adds.items(xs, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Co.Add, xs), 1n+m, e2) : {s == Wr.put_nat(_, ContextOrder.spell_adds.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def coe.al.conv_f(+m: Nat, +xs: List<&2, Co.Add>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Co.Add, xs) == 1n+m : Nat}, e3: {ContextOrder.adds_all(xs) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Co.Add, xs)), ContextOrder.adds_all(xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Co.Add, xs), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), ContextOrder.adds_all(xs)) == True{} : Bool}
  LACo.co.and_tt(LawsBase.wire_fits(1n+m), ContextOrder.adds_all(xs), fn, e3)

def coe.al.conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Co.Add>>, pl: coe.al.PL(s2, m, d)) -> coe.al.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, rest) = pl
      (+e2, e3) = rest
      (coe.al.conv_s(s, s2, m, xs, r, en, e1, e2), coe.al.conv_f(m, xs, fn, e2, e3))
    case Wr.Bad{}:
      Unit{}

def coe.al.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> coe.al.LS(s, Wr.get_list.start(~Co.Add, ~FCo.get_add, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      coe.al.conv(s, s2, m, en, fn, Wr.get_list.go(~Co.Add, ~FCo.get_add, m, FCo.get_add(s2)), coe.al.loop(m, FCo.get_add(s2), s2, coe.add(s2)))

def coe.al.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> coe.al.LS(s, Wr.get_list.start(~Co.Add, ~FCo.get_add, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      coe.al.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of Co.Add decoded is spelled, and its count and items fit
def coe.al.list(+s: String) -> coe.al.LS(s, Wr.get_list(~Co.Add, ~FCo.get_add, s)):
  coe.al.top(s, Wr.get_nat(s), {==})

# ---- requests ----

# what the request decoder's answer says about its input s
def coe.RQ(s: String, d: Wr.Dec<FCo.Req>) -> Type:
  match d:
    case Wr.Got{+q, r}:
      {s == ContextOrder.spell_req(q, r) : String} & {ContextOrder.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def coe.rq.order(-s: String, -s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<List<&2, Co.Msg>>, p: coe.ml.LS(s1, d)) -> coe.RQ(s, FCo.get_order(d)):
  match d:
    case Wr.Got{+ms, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, ContextOrder.spell_msgs(ms, r)), e0, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, ContextOrder.spell_msgs(ms, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def coe.rq.es(-s: String, -s2: String, +mk: Bool, e0: {s == Wr.put_nat(1n, Wr.put_bool(mk, s2)) : String}, d: Wr.Dec<List<&2, Co.Ent>>, p: coe.el.LS(s2, d)) -> coe.RQ(s, FCo.get_derive.es(mk, d)):
  match d:
    case Wr.Got{+es, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_bool(mk, s2)), Wr.put_nat(1n, Wr.put_bool(mk, Wr.put_nat(List.length(&2, Co.Ent, es), ContextOrder.spell_ents.items(es, r)))), e0, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_bool(mk, z)), s2, Wr.put_nat(List.length(&2, Co.Ent, es), ContextOrder.spell_ents.items(es, r)), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def coe.rq.derive(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, p: coe.PB(s1, d)) -> coe.RQ(s, FCo.get_derive(d)):
  match d:
    case Wr.Got{+mk, +s2}:
      coe.rq.es(s, s2, mk, Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_bool(mk, s2)), e0, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_bool(mk, s2), p)), Wr.get_list(~Co.Ent, ~FCo.get_ent, s2), coe.el.list(s2))
    case Wr.Bad{}:
      Unit{}

def coe.rq.open(-s: String, -s2: String, +ads: List<&2, Co.Add>, e0: {s == Wr.put_nat(2n, Wr.put_nat(List.length(&2, Co.Add, ads), ContextOrder.spell_adds.items(ads, s2))) : String}, fa: {Bool.and(LawsBase.wire_fits(List.length(&2, Co.Add, ads)), ContextOrder.adds_all(ads)) == True{} : Bool}, d: Wr.Dec<List<&2, Co.Msg>>, p: coe.ml.LS(s2, d)) -> coe.RQ(s, FCo.get_extend.open(ads, d)):
  match d:
    case Wr.Got{+ms, +r}:
      (e1, f1) = p
      +fa2 = fa
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(List.length(&2, Co.Add, ads), ContextOrder.spell_adds.items(ads, s2))), Wr.put_nat(2n, Wr.put_nat(List.length(&2, Co.Add, ads), ContextOrder.spell_adds.items(ads, ContextOrder.spell_msgs(ms, r)))), e0, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(List.length(&2, Co.Add, ads), ContextOrder.spell_adds.items(ads, z))), s2, ContextOrder.spell_msgs(ms, r), e1)), LACo.co.and_tt(LawsBase.wire_fits(List.length(&2, Co.Add, ads)), Bool.and(ContextOrder.adds_all(ads), ContextOrder.msgs_fit(ms)), LACo.co.and_l(LawsBase.wire_fits(List.length(&2, Co.Add, ads)), ContextOrder.adds_all(ads), fa2), LACo.co.and_tt(ContextOrder.adds_all(ads), ContextOrder.msgs_fit(ms), LACo.co.and_r(LawsBase.wire_fits(List.length(&2, Co.Add, ads)), ContextOrder.adds_all(ads), fa2), f1)))
    case Wr.Bad{}:
      Unit{}

def coe.rq.extend(-s: String, -s1: String, e0: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<List<&2, Co.Add>>, p: coe.al.LS(s1, d)) -> coe.RQ(s, FCo.get_extend(d)):
  match d:
    case Wr.Got{+ads, +s2}:
      (e1, f1) = p
      coe.rq.open(s, s2, ads, Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_nat(List.length(&2, Co.Add, ads), ContextOrder.spell_adds.items(ads, s2))), e0, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_nat(List.length(&2, Co.Add, ads), ContextOrder.spell_adds.items(ads, s2)), e1)), f1, FCo.get_msgs(s2), coe.ml.list(s2))
    case Wr.Bad{}:
      Unit{}

def coe.rq.lead(-s: String, -s1: String, e0: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<List<&2, Co.Role>>, p: coe.rl.LS(s1, d)) -> coe.RQ(s, FCo.get_lead(d)):
  match d:
    case Wr.Got{+rs, +r}:
      (e1, f1) = p
      (Equal.trans(String, s, Wr.put_nat(3n, s1), Wr.put_nat(3n, Wr.put_nat(List.length(&2, Co.Role, rs), ContextOrder.spell_roles.items(rs, r))), e0, Equal.cong(String, String, z => Wr.put_nat(3n, z), s1, Wr.put_nat(List.length(&2, Co.Role, rs), ContextOrder.spell_roles.items(rs, r)), e1)), f1)
    case Wr.Bad{}:
      Unit{}

def coe.rq.top(-s: String, d: Wr.Dec<Nat>, p: coe.PNF(s, d)) -> coe.RQ(s, FCo.get_req.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          coe.rq.order(s, s1, e0, FCo.get_msgs(s1), coe.ml.list(s1))
        case 1n:
          (e0, f0) = p
          coe.rq.derive(s, s1, e0, Wr.get_bool(s1), coe.pb(s1))
        case 2n:
          (e0, f0) = p
          coe.rq.extend(s, s1, e0, Wr.get_list(~Co.Add, ~FCo.get_add, s1), coe.al.list(s1))
        case 3n:
          (e0, f0) = p
          coe.rq.lead(s, s1, e0, Wr.get_list(~Co.Role, ~FCo.get_role, s1), coe.rl.list(s1))
        case 4n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and its numbers fit
def coe.req(+s: String) -> coe.RQ(s, FCo.get_req(s)):
  coe.rq.top(s, Wr.get_nat(s), coe.pnf(s))
