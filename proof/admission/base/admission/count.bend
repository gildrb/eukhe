# eukhe: lemmas the proofs of area admission share: admission/count. The
# laws' counts, tests and preemption table (laws/admission.bend, Terms)
# are the model's.

import Base
import ../../../../bend/admission.bend as Ad
import ../../../../laws/admission.bend as Admission

# Logic
# -----

def pac.IfS(m: Maybe<&2, Ad.Cls>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{c}:
      Unit

# a claim that Some is None proves anything
def pac.some_none(-G: Type, -c: Ad.Cls, e: {Some{c} == None{} : Maybe<&2, Ad.Cls>}) -> G:
  %e : pac.IfS(_, G)
  Unit{}

def pac.IfZ(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      G
    case 1n+p:
      Unit

# a claim that a successor is 0 proves anything
def pac.succ_zero(-G: Type, -x: Nat, e: {1n+x == 0n : Nat}) -> G:
  %e : pac.IfZ(_, G)
  Unit{}

def pac.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a claim that True is False proves anything
def pac.true_false(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : pac.IfT(_, G)
  Unit{}

def pac.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a claim that False is True proves anything
def pac.false_true(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : pac.IfF(_, G)
  Unit{}

# Counts and tests
# ----------------

def pac.same(a: Ad.Cls, b: Ad.Cls) -> {Admission.ads_same(a, b) == Ad.Cls.eq(a, b) : Bool}:
  match a b:
    case Ad.Ia{} Ad.Ia{}:
      {==}
    case Ad.Ia{} Ad.Bg{}:
      {==}
    case Ad.Bg{} Ad.Ia{}:
      {==}
    case Ad.Bg{} Ad.Bg{}:
      {==}

def pac.holding(s: Ad.Sts) -> {Admission.ads_holding(s) == Ad.Mode.of(Ad.Holding{}, s) : Bool}:
  match s:
    case Ad.Queued{}:
      {==}
    case Ad.Granted{}:
      {==}
    case Ad.Held{}:
      {==}
    case Ad.Preempted{}:
      {==}
    case Ad.Ended{}:
      {==}

def pac.waiting(s: Ad.Sts) -> {Admission.ads_waiting(s) == Ad.Mode.of(Ad.Waiting{}, s) : Bool}:
  match s:
    case Ad.Queued{}:
      {==}
    case Ad.Granted{}:
      {==}
    case Ad.Held{}:
      {==}
    case Ad.Preempted{}:
      {==}
    case Ad.Ended{}:
      {==}

def pac.holds(+c: Ad.Cls, t: Ad.Tk) -> {Admission.ads_holds(c, t) == Ad.hit(Ad.Holding{}, c, t) : Bool}:
  match t:
    case Ad.Tk{+tc, +s}:
      %pac.holding(s) : {Bool.and(Admission.ads_holding(s), Admission.ads_same(c, tc)) == Bool.and(_, Ad.Cls.eq(c, tc)) : Bool}
      %pac.same(c, tc) : {Bool.and(Admission.ads_holding(s), Admission.ads_same(c, tc)) == Bool.and(Admission.ads_holding(s), _) : Bool}
      {==}

def pac.waits(+c: Ad.Cls, t: Ad.Tk) -> {Admission.ads_waits(c, t) == Ad.hit(Ad.Waiting{}, c, t) : Bool}:
  match t:
    case Ad.Tk{+tc, +s}:
      %pac.waiting(s) : {Bool.and(Admission.ads_waiting(s), Admission.ads_same(c, tc)) == Bool.and(_, Ad.Cls.eq(c, tc)) : Bool}
      %pac.same(c, tc) : {Bool.and(Admission.ads_waiting(s), Admission.ads_same(c, tc)) == Bool.and(Admission.ads_waiting(s), _) : Bool}
      {==}

def pac.one(b: Bool, n: Nat) -> {Admission.ads_one(b, n) == Ad.bit(b, n) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pac.held(+c: Ad.Cls, ts: List<&2, Ad.Tk>) -> {Admission.ads_held(c, ts) == Ad.cnt(Ad.Holding{}, c, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case +h <> +r:
      %pac.held(c, r) : {Admission.ads_one(Admission.ads_holds(c, h), Admission.ads_held(c, r)) == Ad.bit(Ad.hit(Ad.Holding{}, c, h), _) : Nat}
      %pac.holds(c, h) : {Admission.ads_one(Admission.ads_holds(c, h), Admission.ads_held(c, r)) == Ad.bit(_, Admission.ads_held(c, r)) : Nat}
      pac.one(Admission.ads_holds(c, h), Admission.ads_held(c, r))

def pac.queued(+c: Ad.Cls, ts: List<&2, Ad.Tk>) -> {Admission.ads_queued(c, ts) == Ad.cnt(Ad.Waiting{}, c, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case +h <> +r:
      %pac.queued(c, r) : {Admission.ads_one(Admission.ads_waits(c, h), Admission.ads_queued(c, r)) == Ad.bit(Ad.hit(Ad.Waiting{}, c, h), _) : Nat}
      %pac.waits(c, h) : {Admission.ads_one(Admission.ads_waits(c, h), Admission.ads_queued(c, r)) == Ad.bit(_, Admission.ads_queued(c, r)) : Nat}
      pac.one(Admission.ads_waits(c, h), Admission.ads_queued(c, r))

def pac.busy(+ts: List<&2, Ad.Tk>) -> {Admission.ads_busy(ts) == Ad.held(ts) : Nat}:
  %pac.held(Ad.Ia{}, ts) : {Nat.add(Admission.ads_held(Ad.Ia{}, ts), Admission.ads_held(Ad.Bg{}, ts)) == Nat.add(_, Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)) : Nat}
  %pac.held(Ad.Bg{}, ts) : {Nat.add(Admission.ads_held(Ad.Ia{}, ts), Admission.ads_held(Ad.Bg{}, ts)) == Nat.add(Admission.ads_held(Ad.Ia{}, ts), _) : Nat}
  {==}

def pac.le(a: Nat, b: Nat) -> {Ad.le(a, b) == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      pac.le(x, y)

def pac.isz(n: Nat) -> {Ad.isz(n) == Nat.is_eq(n, 0n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pac.room(l: Ad.Lim, n: Nat) -> {Ad.room(l, n) == Admission.ads_room(l, n) : Bool}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      pac.le(n, p)

def pac.pre1(t: Ad.Tk) -> {Ad.Tk.preempt(t) == Admission.adm_taken_back(t) : Ad.Tk}:
  match t:
    case Ad.Tk{c, s}:
      match c:
        case Ad.Ia{}:
          {==}
        case Ad.Bg{}:
          match s:
            case Ad.Queued{}:
              {==}
            case Ad.Granted{}:
              {==}
            case Ad.Held{}:
              {==}
            case Ad.Preempted{}:
              {==}
            case Ad.Ended{}:
              {==}

def pac.pre(ts: List<&2, Ad.Tk>) -> {Ad.preempt(ts) == Admission.adm_taken_back.all(ts) : List<&2, Ad.Tk>}:
  match ts:
    case Nil{}:
      {==}
    case +h <> +r:
      %pac.pre(r) : {Ad.Tk.preempt(h) <> Ad.preempt(r) == Admission.adm_taken_back(h) <> _ : List<&2, Ad.Tk>}
      %pac.pre1(h) : {Ad.Tk.preempt(h) <> Ad.preempt(r) == _ <> Ad.preempt(r) : List<&2, Ad.Tk>}
      {==}

def pac.pre_on(l: Ad.Lim, ts: List<&2, Ad.Tk>) -> {Ad.preempt.on(l, ts) == Admission.adm_yield(Ad.Ia{}, l, ts) : List<&2, Ad.Tk>}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      pac.pre(ts)

