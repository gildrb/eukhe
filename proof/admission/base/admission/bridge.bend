# eukhe: lemmas the proofs of area admission share: admission/bridge
#
# Each predicate of the laws (laws/admission.bend, Terms), stated over
# the laws' own counts, is the predicate the proofs reason with
# (./terms.bend), stated over the model's counts. Every lemma reads
# {proofs' term == laws' term}, the form a rewrite of a law's goal takes.

import Base
import ../../../../bend/admission.bend as Ad
import ../../../../laws/admission.bend as Admission
import ./count.bend as PC
import ./terms.bend as AT

def br.held(+c: Ad.Cls, +ts: List<&2, Ad.Tk>) -> {Ad.cnt(Ad.Holding{}, c, ts) == Admission.ads_held(c, ts) : Nat}:
  Equal.sym(Nat, Admission.ads_held(c, ts), Ad.cnt(Ad.Holding{}, c, ts), PC.pac.held(c, ts))

def br.queued(+c: Ad.Cls, +ts: List<&2, Ad.Tk>) -> {Ad.cnt(Ad.Waiting{}, c, ts) == Admission.ads_queued(c, ts) : Nat}:
  Equal.sym(Nat, Admission.ads_queued(c, ts), Ad.cnt(Ad.Waiting{}, c, ts), PC.pac.queued(c, ts))

def br.busy(+ts: List<&2, Ad.Tk>) -> {Ad.held(ts) == Admission.ads_busy(ts) : Nat}:
  Equal.sym(Nat, Admission.ads_busy(ts), Ad.held(ts), PC.pac.busy(ts))

def br.holds(+c: Ad.Cls, +t: Ad.Tk) -> {Ad.hit(Ad.Holding{}, c, t) == Admission.ads_holds(c, t) : Bool}:
  Equal.sym(Bool, Admission.ads_holds(c, t), Ad.hit(Ad.Holding{}, c, t), PC.pac.holds(c, t))

def br.waits(+c: Ad.Cls, +t: Ad.Tk) -> {Ad.hit(Ad.Waiting{}, c, t) == Admission.ads_waits(c, t) : Bool}:
  Equal.sym(Bool, Admission.ads_waits(c, t), Ad.hit(Ad.Waiting{}, c, t), PC.pac.waits(c, t))

def br.one(+b: Bool, +n: Nat) -> {Ad.bit(b, n) == Admission.ads_one(b, n) : Nat}:
  Equal.sym(Nat, Admission.ads_one(b, n), Ad.bit(b, n), PC.pac.one(b, n))

def br.within(l: Ad.Lim, +n: Nat) -> {AT.within(l, n) == Admission.adm_within(l, n) : Bool}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      PC.pac.le(n, 1n+p)

# who may take a free slot, as the laws state it
def br.pick(r: Bool, wi: Nat, hi: Nat, wb: Nat) -> {Maybe.is_some(&2, Ad.Cls, Ad.pick.go(r, wi, hi, wb)) == Bool.and(r, Bool.or(Bool.not(Ad.isz(wi)), Bool.and(Bool.not(Ad.isz(wb)), Ad.isz(hi)))) : Bool}:
  match r wi hi wb:
    case False{} _ _ _:
      {==}
    case True{} 1n+a _ _:
      {==}
    case True{} 0n 1n+b 0n:
      {==}
    case True{} 0n 1n+b 1n+d:
      {==}
    case True{} 0n 0n 0n:
      {==}
    case True{} 0n 0n 1n+d:
      {==}

def br.grantable(s: Ad.St) -> {AT.grantable(s) == Admission.adm_grantable(s) : Bool}:
  match s:
    case Ad.St{+l, q, +ts}:
      +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
      +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
      +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
      %br.busy(ts) : {AT.grantable(Ad.St{l, q, ts}) == Bool.and(Admission.ads_room(l, _), Bool.or(Bool.not(Nat.is_eq(Admission.ads_queued(Ad.Ia{}, ts), 0n)), Bool.and(Bool.not(Nat.is_eq(Admission.ads_queued(Ad.Bg{}, ts), 0n)), Nat.is_eq(Admission.ads_held(Ad.Ia{}, ts), 0n)))) : Bool}
      %PC.pac.room(l, Ad.held(ts)) : {AT.grantable(Ad.St{l, q, ts}) == Bool.and(_, Bool.or(Bool.not(Nat.is_eq(Admission.ads_queued(Ad.Ia{}, ts), 0n)), Bool.and(Bool.not(Nat.is_eq(Admission.ads_queued(Ad.Bg{}, ts), 0n)), Nat.is_eq(Admission.ads_held(Ad.Ia{}, ts), 0n)))) : Bool}
      %br.queued(Ad.Ia{}, ts) : {AT.grantable(Ad.St{l, q, ts}) == Bool.and(Ad.room(l, Ad.held(ts)), Bool.or(Bool.not(Nat.is_eq(_, 0n)), Bool.and(Bool.not(Nat.is_eq(Admission.ads_queued(Ad.Bg{}, ts), 0n)), Nat.is_eq(Admission.ads_held(Ad.Ia{}, ts), 0n)))) : Bool}
      %br.queued(Ad.Bg{}, ts) : {AT.grantable(Ad.St{l, q, ts}) == Bool.and(Ad.room(l, Ad.held(ts)), Bool.or(Bool.not(Nat.is_eq(wi, 0n)), Bool.and(Bool.not(Nat.is_eq(_, 0n)), Nat.is_eq(Admission.ads_held(Ad.Ia{}, ts), 0n)))) : Bool}
      %br.held(Ad.Ia{}, ts) : {AT.grantable(Ad.St{l, q, ts}) == Bool.and(Ad.room(l, Ad.held(ts)), Bool.or(Bool.not(Nat.is_eq(wi, 0n)), Bool.and(Bool.not(Nat.is_eq(wb, 0n)), Nat.is_eq(_, 0n)))) : Bool}
      %PC.pac.isz(wi) : {AT.grantable(Ad.St{l, q, ts}) == Bool.and(Ad.room(l, Ad.held(ts)), Bool.or(Bool.not(_), Bool.and(Bool.not(Nat.is_eq(wb, 0n)), Nat.is_eq(hi, 0n)))) : Bool}
      %PC.pac.isz(wb) : {AT.grantable(Ad.St{l, q, ts}) == Bool.and(Ad.room(l, Ad.held(ts)), Bool.or(Bool.not(Ad.isz(wi)), Bool.and(Bool.not(_), Nat.is_eq(hi, 0n)))) : Bool}
      %PC.pac.isz(hi) : {AT.grantable(Ad.St{l, q, ts}) == Bool.and(Ad.room(l, Ad.held(ts)), Bool.or(Bool.not(Ad.isz(wi)), Bool.and(Bool.not(Ad.isz(wb)), _))) : Bool}
      br.pick(Ad.room(l, Ad.held(ts)), wi, hi, wb)

def br.calm(+ts: List<&2, Ad.Tk>) -> {AT.calm(ts) == Admission.adm_calm(ts) : Bool}:
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hb = Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts)
  %br.held(Ad.Bg{}, ts) : {AT.calm(ts) == Bool.or(Nat.is_eq(_, 0n), Nat.is_eq(Admission.ads_queued(Ad.Ia{}, ts), 0n)) : Bool}
  %br.queued(Ad.Ia{}, ts) : {AT.calm(ts) == Bool.or(Nat.is_eq(hb, 0n), Nat.is_eq(_, 0n)) : Bool}
  %PC.pac.isz(hb) : {AT.calm(ts) == Bool.or(_, Nat.is_eq(wi, 0n)) : Bool}
  %PC.pac.isz(wi) : {AT.calm(ts) == Bool.or(Ad.isz(hb), _) : Bool}
  {==}

def br.fifo(+c: Ad.Cls, ts: List<&2, Ad.Tk>, +seen: Bool) -> {AT.fifo(c, ts, seen) == Admission.adm_fifo(c, ts, seen) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +h <> +r:
      %br.fifo(c, r, Bool.or(seen, Admission.ads_waits(c, h))) : {AT.fifo(c, h <> r, seen) == Bool.and(Bool.not(Bool.and(seen, Admission.ads_holds(c, h))), _) : Bool}
      %br.waits(c, h) : {AT.fifo(c, h <> r, seen) == Bool.and(Bool.not(Bool.and(seen, Admission.ads_holds(c, h))), AT.fifo(c, r, Bool.or(seen, _))) : Bool}
      %br.holds(c, h) : {AT.fifo(c, h <> r, seen) == Bool.and(Bool.not(Bool.and(seen, _)), AT.fifo(c, r, Bool.or(seen, Ad.hit(Ad.Waiting{}, c, h)))) : Bool}
      {==}

def br.fifo_both(+ts: List<&2, Ad.Tk>) -> {AT.fifo.both(ts) == Admission.adm_fifo_both(ts) : Bool}:
  %br.fifo(Ad.Ia{}, ts, False{}) : {AT.fifo.both(ts) == Bool.and(_, Admission.adm_fifo(Ad.Bg{}, ts, False{})) : Bool}
  %br.fifo(Ad.Bg{}, ts, False{}) : {AT.fifo.both(ts) == Bool.and(AT.fifo(Ad.Ia{}, ts, False{}), _) : Bool}
  {==}

def br.pot(ts: List<&2, Ad.Tk>, w: Nat) -> {AT.pot(ts, w) == Admission.adm_pot(ts, w) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case +h <> +r:
      match w:
        case 0n:
          br.held(Ad.Ia{}, h <> r)
        case 1n++p:
          +b = Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, h), Ad.hit(Ad.Waiting{}, Ad.Ia{}, h))
          %br.pot(r, p) : {AT.pot(h <> r, 1n+p) == Admission.ads_one(Bool.or(Admission.ads_holds(Ad.Ia{}, h), Admission.ads_waits(Ad.Ia{}, h)), _) : Nat}
          %br.holds(Ad.Ia{}, h) : {AT.pot(h <> r, 1n+p) == Admission.ads_one(Bool.or(_, Admission.ads_waits(Ad.Ia{}, h)), AT.pot(r, p)) : Nat}
          %br.waits(Ad.Ia{}, h) : {AT.pot(h <> r, 1n+p) == Admission.ads_one(Bool.or(Ad.hit(Ad.Holding{}, Ad.Ia{}, h), _), AT.pot(r, p)) : Nat}
          br.one(b, AT.pot(r, p))

def br.ahead(+s: Ad.St, w: Nat) -> {AT.ahead(s, w) == Admission.adm_ahead(s, w) : Nat}:
  br.pot(Admission.adm_ts(s), w)

def br.freed_ia(l: Ad.Lim, n: Nat) -> {AT.freed.ia(l, n) == Admission.adm_freed.ia(l, n) : Nat}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      {==}

def br.freed_at(m: Maybe<&2, Ad.Tk>, rel: Bool) -> {AT.freed.at(m, rel) == Admission.adm_freed.at(m, rel) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      match t:
        case Ad.Tk{c, s}:
          match s rel:
            case Ad.Queued{} True{}:
              {==}
            case Ad.Queued{} False{}:
              {==}
            case Ad.Granted{} True{}:
              {==}
            case Ad.Granted{} False{}:
              {==}
            case Ad.Held{} True{}:
              {==}
            case Ad.Held{} False{}:
              {==}
            case Ad.Preempted{} True{}:
              {==}
            case Ad.Preempted{} False{}:
              {==}
            case Ad.Ended{} True{}:
              {==}
            case Ad.Ended{} False{}:
              {==}

def br.freed(+s: Ad.St, o: Ad.Op) -> {AT.freed(s, o) == Admission.adm_freed(s, o) : Nat}:
  match o:
    case Ad.Admit{c}:
      match c:
        case Ad.Ia{}:
          %br.held(Ad.Bg{}, Admission.adm_ts(s)) : {AT.freed(s, Ad.Admit{Ad.Ia{}}) == Admission.adm_freed.ia(Admission.adm_lim(s), _) : Nat}
          br.freed_ia(Admission.adm_lim(s), Ad.cnt(Ad.Holding{}, Ad.Bg{}, Admission.adm_ts(s)))
        case Ad.Bg{}:
          {==}
    case Ad.Collect{k}:
      {==}
    case Ad.Release{k}:
      br.freed_at(List.get(&2, Ad.Tk, Admission.adm_ts(s), k), True{})
    case Ad.Leave{k}:
      br.freed_at(List.get(&2, Ad.Tk, Admission.adm_ts(s), k), False{})
    case Ad.Limit{l, q}:
      {==}
