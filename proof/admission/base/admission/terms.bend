# eukhe: lemmas the proofs of area admission share: admission/terms
#
# The predicates the proofs reason with, stated over the model's own
# counts (Ad.cnt, Ad.hit, Ad.bit). The laws state their predicates over
# their own counts (laws/admission.bend, Terms); each fill rewrites the
# law's predicate into the one here (the bridges of ./bridge.bend), then
# proves it.

import Base
import ../../../../bend/admission.bend as Ad
import ../../../../laws/admission.bend as Admission

def St.new(l: Ad.Lim, q: Nat) -> Ad.St:
  Ad.St{l, q, Nil{}}

# n slots held are within the limit
def within(l: Ad.Lim, n: Nat) -> Bool:
  match l:
    case Ad.Unl{}:
      True{}
    case Ad.Cap{p}:
      Ad.le(n, 1n+p)

# no lost wake-up: some waiter may take a free slot
def grantable(+s: Ad.St) -> Bool:
  match s:
    case Ad.St{+l, q, +ts}:
      Maybe.is_some(&2, Ad.Cls, Ad.pick(l, ts))

# a background slot is held only while no interactive request waits
def calm.n(wi: Nat, hb: Nat) -> Bool:
  Bool.or(Ad.isz(hb), Ad.isz(wi))

def calm(+ts: List<&2, Ad.Tk>) -> Bool:
  calm.n(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts))

# the slots an op frees itself, before any grant
def freed.at(m: Maybe<&2, Ad.Tk>, rel: Bool) -> Nat:
  match m rel:
    case Some{Ad.Tk{c, Ad.Held{}}} True{}:
      1n
    case Some{Ad.Tk{c, Ad.Granted{}}} False{}:
      1n
    case _ _:
      0n

def freed.ia(l: Ad.Lim, n: Nat) -> Nat:
  match l:
    case Ad.Unl{}:
      0n
    case Ad.Cap{p}:
      n

def freed(+s: Ad.St, o: Ad.Op) -> Nat:
  match o:
    case Ad.Admit{Ad.Ia{}}:
      freed.ia(Admission.adm_lim(s), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Admission.adm_ts(s)))
    case Ad.Admit{Ad.Bg{}}:
      0n
    case Ad.Collect{k}:
      0n
    case Ad.Release{k}:
      freed.at(Ad.get(Admission.adm_ts(s), k), True{})
    case Ad.Depart{k}:
      freed.at(Ad.get(Admission.adm_ts(s), k), False{})
    case Ad.Limit{l, q}:
      0n

# fifo(c, ts, seen): no ticket of class c holds a slot after one of its
# class that waits (seen: one waited before ts)
def fifo(+c: Ad.Cls, ts: List<&2, Ad.Tk>, +seen: Bool) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +h <> r:
      Bool.and(Bool.not(Bool.and(seen, Ad.hit(Ad.Holding{}, c, h))), fifo(c, r, Bool.or(seen, Ad.hit(Ad.Waiting{}, c, h))))

def fifo.both(+ts: List<&2, Ad.Tk>) -> Bool:
  Bool.and(fifo(Ad.Ia{}, ts, False{}), fifo(Ad.Bg{}, ts, False{}))

# what interactive ticket w waits for: the interactive slots held and the
# interactive waiters ahead of it
def pot(ts: List<&2, Ad.Tk>, w: Nat) -> Nat:
  match ts:
    case Nil{}:
      0n
    case +h <> +r:
      match w:
        case 0n:
          Ad.cnt(Ad.Holding{}, Ad.Ia{}, h <> r)
        case 1n+p:
          Ad.bit(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, h), Ad.hit(Ad.Waiting{}, Ad.Ia{}, h)), pot(r, p))

def ahead(+s: Ad.St, w: Nat) -> Nat:
  pot(Admission.adm_ts(s), w)
