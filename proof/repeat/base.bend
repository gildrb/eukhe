# eukhe: lemmas of the proofs of area repeat

import Base
import ../../bend/repeat.bend as Rp
import ../../bend/ffi_repeat.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../../laws/repeat.bend as Repeat

# ---- logic ----

def rp.BD(b: Bool, T: Type, F: Type) -> Type:
  match b:
    case True{}:
      T
    case False{}:
      F

def rp.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : rp.BD(_, G, Unit)
  Unit{}

def rp.absurd_t(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : rp.BD(_, Unit, G)
  Unit{}

def rp.under(-s: String, -s1: String, -y: String, -f: String -> String, e: {s == f(s1) : String}, p: {s1 == y : String}) -> {s == f(y) : String}:
  %p : {s == f(_) : String}
  e

# ---- Nat ----

def rp.add_zero(k: Nat) -> {Nat.add(k, 0n) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(j, 0n), j, rp.add_zero(j))

def rp.add_succ(k: Nat, +x: Nat) -> {Nat.add(k, 1n+x) == 1n+Nat.add(k, x) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.add(j, 1n+x), 1n+Nat.add(j, x), rp.add_succ(j, x))

def rp.eq_refl(s: Nat) -> {Nat.is_eq(s, s) == True{} : Bool}:
  match s:
    case 0n:
      {==}
    case 1n+j:
      rp.eq_refl(j)

def rp.le_refl(c: Nat) -> {Nat.is_le(c, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+j:
      rp.le_refl(j)

def rp.le0(k: Nat) -> {Nat.is_le(0n, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

# c not below n: n is at most c
def rp.nlt_le(c: Nat, n: Nat, e: {Nat.is_lt(c, n) == False{} : Bool}) -> {Nat.is_le(n, c) == True{} : Bool}:
  match c n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      rp.absurd_t({Nat.is_le(1n+q, 0n) == True{} : Bool}, e)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rp.nlt_le(p, q, e)

# ---- the count ----

def rp.cp_succ(b: Bool, +k: Nat, +c: Nat) -> {Rp.count.pick(b, 1n+k, 1n+c) == 1n+Rp.count.pick(b, k, c) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rp.kp_succ(b: Bool, +n: Nat, +c: Nat) -> {Repeat.clip.pick(b, 1n+n, 1n+c) == 1n+Repeat.clip.pick(b, n, c) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# 1 and k saturated at c, as the code counts and as the spec clips
def rp.cnt(k: Nat, c: Nat) -> {Rp.count.pick(Nat.is_lt(k, c), k, c) == Repeat.clip.pick(Nat.is_lt(c, 1n+k), 1n+k, c) : Nat}:
  match k c:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      match q:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      +a = Rp.count.pick(Nat.is_lt(p, q), p, q)
      +b = Repeat.clip.pick(Nat.is_lt(q, 1n+p), 1n+p, q)
      Equal.trans(Nat, Rp.count.pick(Nat.is_lt(p, q), 1n+p, 1n+q), 1n+a, Repeat.clip.pick(Nat.is_lt(q, 1n+p), 2n+p, 1n+q), rp.cp_succ(Nat.is_lt(p, q), p, q), Equal.trans(Nat, 1n+a, 1n+b, Repeat.clip.pick(Nat.is_lt(q, 1n+p), 2n+p, 1n+q), Equal.cong(Nat, Nat, x => 1n+x, a, b, rp.cnt(p, q)), Equal.sym(Nat, Repeat.clip.pick(Nat.is_lt(q, 1n+p), 2n+p, 1n+q), 1n+b, rp.kp_succ(Nat.is_lt(q, 1n+p), 1n+p, q))))

# the code's count is the spec's: 1 and k, saturated at 2^32 - 1
def rp.count(+k: Nat) -> {Rp.count(k) == Repeat.clip(1n+k) : Nat}:
  rp.cnt(k, Rp.cap())

# the count with no round added
def rp.halt0(+k: Nat) -> {Rp.count(k) == Repeat.clip(1n+Nat.add(k, 0n)) : Nat}:
  %Equal.sym(Nat, Nat.add(k, 0n), k, rp.add_zero(k)) : {Rp.count(k) == Repeat.clip(1n+_) : Nat}
  rp.count(k)

# a clipped count is 1 to c
def rp.cb(h: Bool, +k: Nat, +c: Nat, eh: {Nat.is_lt(c, 1n+k) == h : Bool}, one: {Nat.is_le(1n, c) == True{} : Bool}) -> {Bool.and(Nat.is_le(1n, Repeat.clip.pick(h, 1n+k, c)), Nat.is_le(Repeat.clip.pick(h, 1n+k, c), c)) == True{} : Bool}:
  match h:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(1n, c), True{}, one) : {Bool.and(_, Nat.is_le(c, c)) == True{} : Bool}
      rp.le_refl(c)
    case False{}:
      %Equal.sym(Bool, Nat.is_le(0n, k), True{}, rp.le0(k)) : {Bool.and(_, Nat.is_le(1n+k, c)) == True{} : Bool}
      rp.nlt_le(c, 1n+k, eh)

# ---- lists ----

# the code's comparison of results is the spec's
def rp.same(a: List<&2, Nat>, b: List<&2, Nat>) -> {Rp.same(a, b) == Repeat.ids_eq(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> u:
      {==}
    case x <> t Nil{}:
      {==}
    case +x <> t +y <> u:
      Equal.cong(Bool, Bool, z => Bool.and(Nat.is_eq(x, y), z), Rp.same(t, u), Repeat.ids_eq(t, u), rp.same(t, u))

# ---- the walk against the pieces ----

# the rounds that repeat at the head of ps, for a walk whose first round
# is first
def rp.from(+want: Nat, first: Maybe<&2, Rp.Round>, ps: List<&2, Repeat.Piece>) -> Nat:
  match first:
    case None{}:
      Repeat.row(want, ps)
    case Some{r}:
      match r:
        case Rp.Round{+s0, +rs0}:
          Repeat.again(s0, rs0, ps)

# a stopped walk answers its count, whatever follows
def rp.halt(t: List<&2, Rp.Ev>, +k: Nat) -> {Repeat.drive(t, Rp.Stops{Rp.count(k)}) == Repeat.clip(1n+Nat.add(k, 0n)) : Nat}:
  match t:
    case Nil{}:
      rp.halt0(k)
    case e <> u:
      rp.halt0(k)

# one more round that repeats
def rp.more(+t: List<&2, Rp.Ev>, +g: Rp.Walk, +k: Nat, +x: Nat, ih: {Repeat.drive(t, Rp.Goes{g}) == Repeat.clip(1n+Nat.add(1n+k, x)) : Nat}) -> {Repeat.drive(t, Rp.Goes{g}) == Repeat.clip(1n+Nat.add(k, 1n+x)) : Nat}:
  %Equal.sym(Nat, Nat.add(k, 1n+x), 1n+Nat.add(k, x), rp.add_succ(k, x)) : {Repeat.drive(t, Rp.Goes{g}) == Repeat.clip(1n+_) : Nat}
  ih

# a reply with calls s on a walk with no round yet
def rp.c_none(h: Bool, +want: Nat, +k: Nat, +s: Nat, +pend: List<&2, Nat>, +t: List<&2, Rp.Ev>, ih: {Repeat.drive(t, Rp.Goes{Rp.Walk{want, 1n+k, Some{Rp.Round{s, pend}}, Nil{}}}) == Repeat.clip(1n+Nat.add(1n+k, Repeat.again(s, pend, Repeat.pieces(t, Nil{})))) : Nat}) -> {Repeat.drive(t, Rp.called.pick(h, want, k, None{}, s, pend)) == Repeat.clip(1n+Nat.add(k, Repeat.again.pick(h, Repeat.again(s, pend, Repeat.pieces(t, Nil{}))))) : Nat}:
  match h:
    case True{}:
      rp.more(t, Rp.Walk{want, 1n+k, Some{Rp.Round{s, pend}}, Nil{}}, k, Repeat.again(s, pend, Repeat.pieces(t, Nil{})), ih)
    case False{}:
      rp.halt(t, k)

# a reply with calls s on a walk whose first round is s0, rs0
def rp.c_some(h: Bool, +want: Nat, +k: Nat, +s0: Nat, +rs0: List<&2, Nat>, +s: Nat, +pend: List<&2, Nat>, +t: List<&2, Rp.Ev>, ih: {Repeat.drive(t, Rp.Goes{Rp.Walk{want, 1n+k, Some{Rp.Round{s0, rs0}}, Nil{}}}) == Repeat.clip(1n+Nat.add(1n+k, Repeat.again(s0, rs0, Repeat.pieces(t, Nil{})))) : Nat}) -> {Repeat.drive(t, Rp.called.pick(h, want, k, Some{Rp.Round{s0, rs0}}, s, pend)) == Repeat.clip(1n+Nat.add(k, Repeat.again.pick(h, Repeat.again(s0, rs0, Repeat.pieces(t, Nil{}))))) : Nat}:
  match h:
    case True{}:
      rp.more(t, Rp.Walk{want, 1n+k, Some{Rp.Round{s0, rs0}}, Nil{}}, k, Repeat.again(s0, rs0, Repeat.pieces(t, Nil{})), ih)
    case False{}:
      rp.halt(t, k)

# a message that ends the row: the count so far
def rp.stop(first: Maybe<&2, Rp.Round>, +want: Nat, t: List<&2, Rp.Ev>, +k: Nat) -> {Repeat.drive(t, Rp.Stops{Rp.count(k)}) == Repeat.clip(1n+Nat.add(k, rp.from(want, first, [Repeat.RowEnd{}]))) : Nat}:
  match first:
    case None{}:
      rp.halt(t, k)
    case Some{r}:
      match r:
        case Rp.Round{s0, rs0}:
          rp.halt(t, k)

# the walk, driven over es from any state, answers the count of the spec's
# pieces: 1, the k rounds so far, and the rounds of es that repeat
def rp.walk(es: List<&2, Rp.Ev>, +want: Nat, +k: Nat, +first: Maybe<&2, Rp.Round>, +pend: List<&2, Nat>) -> {Repeat.drive(es, Rp.Goes{Rp.Walk{want, k, first, pend}}) == Repeat.clip(1n+Nat.add(k, rp.from(want, first, Repeat.pieces(es, pend)))) : Nat}:
  match es:
    case Nil{}:
      match first:
        case None{}:
          rp.halt0(k)
        case Some{r}:
          match r:
            case Rp.Round{s0, rs0}:
              rp.halt0(k)
    case e <> +t:
      match e:
        case Rp.System{}:
          rp.walk(t, want, k, first, pend)
        case Rp.User{}:
          rp.stop(first, want, t, k)
        case Rp.Result{+r}:
          rp.walk(t, want, k, first, r <> pend)
        case Rp.Called{+s}:
          match first:
            case None{}:
              rp.c_none(Nat.is_eq(s, want), want, k, s, pend, t, rp.walk(t, want, 1n+k, Some{Rp.Round{s, pend}}, Nil{}))
            case Some{r}:
              match r:
                case Rp.Round{+s0, +rs0}:
                  %Equal.sym(Bool, Rp.same(pend, rs0), Repeat.ids_eq(pend, rs0), rp.same(pend, rs0)) : {Repeat.drive(t, Rp.called.pick(Bool.and(Nat.is_eq(s, s0), _), want, k, Some{Rp.Round{s0, rs0}}, s, pend)) == Repeat.clip(1n+Nat.add(k, Repeat.again.pick(Bool.and(Nat.is_eq(s, s0), Repeat.ids_eq(pend, rs0)), Repeat.again(s0, rs0, Repeat.pieces(t, Nil{}))))) : Nat}
                  rp.c_some(Bool.and(Nat.is_eq(s, s0), Repeat.ids_eq(pend, rs0)), want, k, s0, rs0, s, pend, t, rp.walk(t, want, 1n+k, Some{Rp.Round{s0, rs0}}, Nil{}))
        case Rp.Said{}:
          rp.stop(first, want, t, k)
        case Rp.End{}:
          rp.stop(first, want, t, k)

# ---- one step ----

# a stop with the code's count is a stop with the spec's
def rp.stop_eq(+k: Nat) -> {Rp.Stops{Rp.count(k)} == Rp.Stops{Repeat.clip(1n+k)} : Rp.Next}:
  Equal.cong(Nat, Rp.Next, c => Rp.Stops{c}, Rp.count(k), Repeat.clip(1n+k), rp.count(k))

def rp.sx_pick(h: Bool, +want: Nat, +k: Nat, first: Maybe<&2, Rp.Round>, +s: Nat, +pend: List<&2, Nat>, +g: Rp.Walk, eg: {Rp.Walk{want, 1n+k, Rp.keep(first, s, pend), Nil{}} == g : Rp.Walk}) -> {Rp.called.pick(h, want, k, first, s, pend) == Repeat.step_spec.hit(h, g, k) : Rp.Next}:
  match h:
    case True{}:
      Equal.cong(Rp.Walk, Rp.Next, x => Rp.Goes{x}, Rp.Walk{want, 1n+k, Rp.keep(first, s, pend), Nil{}}, g, eg)
    case False{}:
      rp.stop_eq(k)

# a reply with calls, as the code and the spec take it
def rp.sx_called(first: Maybe<&2, Rp.Round>, +want: Nat, +k: Nat, +s: Nat, +pend: List<&2, Nat>) -> {Rp.called.pick(Rp.repeats(want, first, s, pend), want, k, first, s, pend) == Repeat.step_spec.called(first, want, k, s, pend) : Rp.Next}:
  match first:
    case None{}:
      rp.sx_pick(Nat.is_eq(s, want), want, k, None{}, s, pend, Rp.Walk{want, 1n+k, Some{Rp.Round{s, pend}}, Nil{}}, {==})
    case Some{r}:
      match r:
        case Rp.Round{+s0, +rs0}:
          %Equal.sym(Bool, Rp.same(pend, rs0), Repeat.ids_eq(pend, rs0), rp.same(pend, rs0)) : {Rp.called.pick(Bool.and(Nat.is_eq(s, s0), _), want, k, Some{Rp.Round{s0, rs0}}, s, pend) == Repeat.step_spec.hit(Bool.and(Nat.is_eq(s, s0), Repeat.ids_eq(pend, rs0)), Rp.Walk{want, 1n+k, Some{Rp.Round{s0, rs0}}, Nil{}}, k) : Rp.Next}
          rp.sx_pick(Bool.and(Nat.is_eq(s, s0), Repeat.ids_eq(pend, rs0)), want, k, Some{Rp.Round{s0, rs0}}, s, pend, Rp.Walk{want, 1n+k, Some{Rp.Round{s0, rs0}}, Nil{}}, {==})

# a stop answers a count of 1 to 2^32 - 1
def rp.bnd(+k: Nat) -> {Repeat.bounded(Rp.Stops{Rp.count(k)}) == True{} : Bool}:
  %Equal.sym(Nat, Rp.count(k), Repeat.clip(1n+k), rp.count(k)) : {Bool.and(Nat.is_le(1n, _), Nat.is_le(_, Repeat.cap_spec())) == True{} : Bool}
  rp.cb(Nat.is_lt(Repeat.cap_spec(), 1n+k), k, Repeat.cap_spec(), {==}, {==})

def rp.bnd_pick(h: Bool, +want: Nat, +k: Nat, first: Maybe<&2, Rp.Round>, +s: Nat, +pend: List<&2, Nat>) -> {Repeat.bounded(Rp.called.pick(h, want, k, first, s, pend)) == True{} : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      rp.bnd(k)

# a stopped drive answers its count, whatever follows
def rp.halted(ys: List<&2, Rp.Ev>, c: Nat) -> {Repeat.drive(ys, Rp.Stops{c}) == c : Nat}:
  match ys:
    case Nil{}:
      {==}
    case e <> t:
      {==}

# ---- the entry ----

def rp.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

# a spelled message whose id fits reads back
def rp.ev_rt(+e: Rp.Ev, +rest: String, +h: {Repeat.ev_fits(e) == True{} : Bool}) -> {Wr.Got{e, rest} == FRp.get_ev(Wr.get_nat(Repeat.spell_ev(e, rest))) : Wr.Dec<Rp.Ev>}:
  match e:
    case Rp.System{}:
      %rp.nat(0n, rest, {==}) : {Wr.Got{Rp.System{}, rest} == FRp.get_ev(_) : Wr.Dec<Rp.Ev>}
      {==}
    case Rp.User{}:
      %rp.nat(1n, rest, {==}) : {Wr.Got{Rp.User{}, rest} == FRp.get_ev(_) : Wr.Dec<Rp.Ev>}
      {==}
    case Rp.Result{+r}:
      %rp.nat(2n, Wr.put_nat(r, rest), {==}) : {Wr.Got{Rp.Result{r}, rest} == FRp.get_ev(_) : Wr.Dec<Rp.Ev>}
      %rp.nat(r, rest, h) : {Wr.Got{Rp.Result{r}, rest} == FRp.get_result(_) : Wr.Dec<Rp.Ev>}
      {==}
    case Rp.Called{+x}:
      %rp.nat(3n, Wr.put_nat(x, rest), {==}) : {Wr.Got{Rp.Called{x}, rest} == FRp.get_ev(_) : Wr.Dec<Rp.Ev>}
      %rp.nat(x, rest, h) : {Wr.Got{Rp.Called{x}, rest} == FRp.get_called(_) : Wr.Dec<Rp.Ev>}
      {==}
    case Rp.Said{}:
      %rp.nat(4n, rest, {==}) : {Wr.Got{Rp.Said{}, rest} == FRp.get_ev(_) : Wr.Dec<Rp.Ev>}
      {==}
    case Rp.End{}:
      %rp.nat(5n, rest, {==}) : {Wr.Got{Rp.End{}, rest} == FRp.get_ev(_) : Wr.Dec<Rp.Ev>}
      {==}

# the stepper's reply writer is the spec's speller
def rp.of(n: Rp.Next) -> {FRp.step.of(n) == Repeat.spell_next(n) : FRp.St & String}:
  match n:
    case Rp.Goes{w}:
      {==}
    case Rp.Stops{c}:
      {==}

# a step's answer is never the error form
def rp.of_not_err(n: Rp.Next) -> {LawsBase.wire_opens_err(Repeat.reply(FRp.step.of(n))) == False{} : Bool}:
  match n:
    case Rp.Goes{w}:
      Wire.wire_nat_not_err(0n, "")
    case Rp.Stops{+c}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(c, ""))

def rp.PNF(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rp.pnf_go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rp.PNF(s, d):
  match d:
    case Wr.Got{+n, +r}:
      (Wire.wire_nat_exact(s, n, r, ed), Wire.wire_nat_decoded_fits(s, n, r, ed))
    case Wr.Bad{}:
      Unit{}

def rp.pnf(+s: String) -> rp.PNF(s, Wr.get_nat(s)):
  rp.pnf_go(s, Wr.get_nat(s), {==})

# what the message decoder's answer says about its input s
def rp.PE(s: String, d: Wr.Dec<Rp.Ev>) -> Type:
  match d:
    case Wr.Got{+e, r}:
      {s == Repeat.spell_ev(e, r) : String} & {Repeat.ev_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rp.pe_res(-s: String, -s1: String, e0: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, p: rp.PNF(s1, d)) -> rp.PE(s, FRp.get_result(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e1, f1) = p
      (rp.under(s, s1, Wr.put_nat(x, r), z => Wr.put_nat(2n, z), e0, e1), f1)
    case Wr.Bad{}:
      Unit{}

def rp.pe_call(-s: String, -s1: String, e0: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Nat>, p: rp.PNF(s1, d)) -> rp.PE(s, FRp.get_called(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e1, f1) = p
      (rp.under(s, s1, Wr.put_nat(x, r), z => Wr.put_nat(3n, z), e0, e1), f1)
    case Wr.Bad{}:
      Unit{}

def rp.pe_top(-s: String, d: Wr.Dec<Nat>, p: rp.PNF(s, d)) -> rp.PE(s, FRp.get_ev(d)):
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
          rp.pe_res(s, s1, e0, Wr.get_nat(s1), rp.pnf(s1))
        case 3n:
          (e0, f0) = p
          rp.pe_call(s, s1, e0, Wr.get_nat(s1), rp.pnf(s1))
        case 4n:
          (e0, f0) = p
          (e0, {==})
        case 5n:
          (e0, f0) = p
          (e0, {==})
        case 6n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every message the decoder reads is spelled, and its id fits
def rp.pe(+s: String) -> rp.PE(s, FRp.get_ev(Wr.get_nat(s))):
  rp.pe_top(s, Wr.get_nat(s), rp.pnf(s))
