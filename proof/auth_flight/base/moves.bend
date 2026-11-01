# eukhe: lemmas the proofs of the desk's safety laws share: what each
# kind of move of the desk (an arrival, a caller that leaves, a caller
# that moves on, a land, an unwind) keeps, one lemma per move and
# property. The proofs split each event into these moves.

import Base
import ../../../bend/auth_flight.bend as F
import ../../../laws/auth_flight/entry.bend as S
import ../../../laws/auth_flight/safety.bend as SS
import ./entry.bend as LAE
import ./logic.bend as AL
import ./callers.bend as AC
import ./flights.bend as AF

# Properties of a desk
# --------------------

def mv.m_of(d: F.Desk) -> Nat:
  match d:
    case F.Desk{cs, m}:
      m

# every number held once and below the next one's
def mv.ids(d: F.Desk) -> Bool:
  match d:
    case F.Desk{+cs, m}:
      Bool.and(AC.ad.below(m, cs), AC.ad.desc(cs))

# at most one leader per provider
def mv.Lead(d: F.Desk) -> Type:
  @q: String -> {Nat.is_le(SS.af_leaders(q, S.af_cs(d)), 1n) == True{} : Bool}

# every waiting caller led
def mv.led(d: F.Desk) -> Bool:
  match d:
    case F.Desk{+cs, m}:
      SS.af_led_all(cs, cs)

# x <= 1 from y <= 1 and x == y
def mv.le1_eq(+x: Nat, +y: Nat, e: {x == y : Nat}, h: {Nat.is_le(y, 1n) == True{} : Bool}) -> {Nat.is_le(x, 1n) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(x, 1n), Nat.is_le(y, 1n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, 1n), x, y, e), h)

# Numbers
# -------

def mv.ids_arrive(+n: Nat, +p: String, +cs: List<&2, F.Cl>, h: {mv.ids(F.Desk{cs, n}) == True{} : Bool}) -> {mv.ids(F.Desk{F.Cl{n, p, F.Loads{}} <> cs, 1n+n}) == True{} : Bool}:
  +h2 = h
  +hb = AL.ad.and_l(AC.ad.below(n, cs), AC.ad.desc(cs), h2)
  AL.ad.and_tt(Bool.and(Nat.is_lt(n, 1n+n), AC.ad.below(1n+n, cs)), Bool.and(AC.ad.below(n, cs), AC.ad.desc(cs)), AL.ad.and_tt(Nat.is_lt(n, 1n+n), AC.ad.below(1n+n, cs), AL.ad.lt_self(n), AC.ad.below_succ(n, cs, hb)), h2)

def mv.ids_cut(+k: Nat, +cs: List<&2, F.Cl>, +n: Nat, h: {mv.ids(F.Desk{cs, n}) == True{} : Bool}) -> {mv.ids(F.Desk{S.af_cut(k, cs), n}) == True{} : Bool}:
  +h2 = h
  AL.ad.and_tt(AC.ad.below(n, S.af_cut(k, cs)), AC.ad.desc(S.af_cut(k, cs)), AC.ad.below_cut(n, k, cs, AL.ad.and_l(AC.ad.below(n, cs), AC.ad.desc(cs), h2)), AC.ad.desc_cut(k, cs, AL.ad.and_r(AC.ad.below(n, cs), AC.ad.desc(cs), h2)))

def mv.ids_set(+k: Nat, +a2: F.At, +cs: List<&2, F.Cl>, +n: Nat, h: {mv.ids(F.Desk{cs, n}) == True{} : Bool}) -> {mv.ids(F.Desk{S.af_set(k, a2, cs), n}) == True{} : Bool}:
  %Equal.sym(Bool, AC.ad.below(n, S.af_set(k, a2, cs)), AC.ad.below(n, cs), AC.ad.below_set(n, k, a2, cs)) : {Bool.and(_, AC.ad.desc(S.af_set(k, a2, cs))) == True{} : Bool}
  %Equal.sym(Bool, AC.ad.desc(S.af_set(k, a2, cs)), AC.ad.desc(cs), AC.ad.desc_set(k, a2, cs)) : {Bool.and(AC.ad.below(n, cs), _) == True{} : Bool}
  h

def mv.ids_land(+k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, h: {mv.ids(F.Desk{cs, n}) == True{} : Bool}) -> {mv.ids(F.Desk{S.af_unwait(p, S.af_cut(k, cs)), n}) == True{} : Bool}:
  +h2 = h
  AL.ad.and_tt(AC.ad.below(n, S.af_unwait(p, S.af_cut(k, cs))), AC.ad.desc(S.af_unwait(p, S.af_cut(k, cs))), AC.ad.below_unwait(n, p, S.af_cut(k, cs), AC.ad.below_cut(n, k, cs, AL.ad.and_l(AC.ad.below(n, cs), AC.ad.desc(cs), h2))), AC.ad.desc_unwait(p, S.af_cut(k, cs), AC.ad.desc_cut(k, cs, AL.ad.and_r(AC.ad.below(n, cs), AC.ad.desc(cs), h2))))

# Leaders
# -------

def mv.gain_w(w: Bool, +q: String, +p: String, +cs: List<&2, F.Cl>, +ew: {String.eq(p, q) == w : Bool}, +nf: {S.af_inflight(p, cs) == False{} : Bool}, h: {Nat.is_le(SS.af_leaders(q, cs), 1n) == True{} : Bool}) -> {Nat.is_le(Nat.add(S.af_bit(w), SS.af_leaders(q, cs)), 1n) == True{} : Bool}:
  match w:
    case True{}:
      +ep = AL.ad.str_sound(p, q, ew)
      +nq = Equal.trans(Bool, S.af_inflight(q, cs), S.af_inflight(p, cs), False{}, Equal.cong(String, Bool, s => S.af_inflight(s, cs), q, p, Equal.sym(String, p, q, ep)), nf)
      %Equal.sym(Nat, SS.af_leaders(q, cs), 0n, AF.ad.lead_none(q, cs, nq)) : {Nat.is_le(Nat.add(1n, _), 1n) == True{} : Bool}
      {==}
    case False{}:
      h

# a loading caller of p leads p's new flight, p having none: one leader
def mv.lead_gain(+q: String, +k: Nat, +cs: List<&2, F.Cl>, -j: Nat, +p: String, at: {S.af_find(k, cs) == Some{F.Cl{j, p, F.Loads{}}} : Maybe<&2, F.Cl>}, +nf: {S.af_inflight(p, cs) == False{} : Bool}, h: {Nat.is_le(SS.af_leaders(q, cs), 1n) == True{} : Bool}) -> {Nat.is_le(SS.af_leaders(q, S.af_set(k, F.Checks{}, cs)), 1n) == True{} : Bool}:
  %Equal.sym(Nat, SS.af_leaders(q, S.af_set(k, F.Checks{}, cs)), Nat.add(S.af_bit(String.eq(p, q)), SS.af_leaders(q, cs)), AF.ad.lead_set_gain(q, k, cs, j, p, at)) : {Nat.is_le(_, 1n) == True{} : Bool}
  mv.gain_w(String.eq(p, q), q, p, cs, {==}, nf, h)

# Who stays live
# --------------

def mv.kept_live(+i: Nat, +cs: List<&2, F.Cl>, o: F.DOut, h: {SS.af_live(i, cs) == True{} : Bool}) -> {Bool.or(SS.af_live(i, cs), SS.af_ends(i, o)) == True{} : Bool}:
  AL.ad.or_l(SS.af_live(i, cs), SS.af_ends(i, o), h)

def mv.kept_set(+i: Nat, +k: Nat, +a2: F.At, +cs: List<&2, F.Cl>, o: F.DOut, h: {SS.af_live(i, cs) == True{} : Bool}) -> {Bool.or(SS.af_live(i, S.af_set(k, a2, cs)), SS.af_ends(i, o)) == True{} : Bool}:
  %Equal.sym(Bool, SS.af_live(i, S.af_set(k, a2, cs)), SS.af_live(i, cs), AC.ad.live_set(i, k, a2, cs)) : {Bool.or(_, SS.af_ends(i, o)) == True{} : Bool}
  AL.ad.or_l(SS.af_live(i, cs), SS.af_ends(i, o), h)

def mv.kept_done_v(v: Bool, +i: Nat, +k: Nat, +cs: List<&2, F.Cl>, +ev: {Nat.is_eq(k, i) == v : Bool}, h: {SS.af_live(i, cs) == True{} : Bool}) -> {Bool.or(SS.af_live(i, S.af_cut(k, cs)), SS.af_ends(i, F.Acts{[F.To{k, F.DoDone{}}]})) == True{} : Bool}:
  match v:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(k, i), True{}, ev) : {Bool.or(SS.af_live(i, S.af_cut(k, cs)), Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(_, True{})), 0n))) == True{} : Bool}
      AL.ad.or_r(SS.af_live(i, S.af_cut(k, cs)), True{}, {==})
    case False{}:
      %Equal.sym(Bool, SS.af_live(i, S.af_cut(k, cs)), SS.af_live(i, cs), AC.ad.live_cut_ne(i, k, cs, ev)) : {Bool.or(_, SS.af_ends(i, F.Acts{[F.To{k, F.DoDone{}}]})) == True{} : Bool}
      AL.ad.or_l(SS.af_live(i, cs), SS.af_ends(i, F.Acts{[F.To{k, F.DoDone{}}]}), h)

# a caller that is done leaves; every other caller stays
def mv.kept_done(+i: Nat, +k: Nat, +cs: List<&2, F.Cl>, h: {SS.af_live(i, cs) == True{} : Bool}) -> {Bool.or(SS.af_live(i, S.af_cut(k, cs)), SS.af_ends(i, F.Acts{[F.To{k, F.DoDone{}}]})) == True{} : Bool}:
  mv.kept_done_v(Nat.is_eq(k, i), i, k, cs, {==}, h)

def mv.kept_land_v(v: Bool, +i: Nat, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +ev: {Nat.is_eq(k, i) == v : Bool}, h: {SS.af_live(i, cs) == True{} : Bool}) -> {Bool.or(SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))), SS.af_ends(i, F.Acts{F.To{k, F.DoDone{}} <> S.af_wake(p, F.DoDone{}, S.af_cut(k, cs))})) == True{} : Bool}:
  match v:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(k, i), True{}, ev) : {Bool.or(SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))), Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(_, True{})), SS.af_ends_in(i, S.af_wake(p, F.DoDone{}, S.af_cut(k, cs)))))) == True{} : Bool}
      AL.ad.or_r(SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))), True{}, {==})
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, ev) : {Bool.or(SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))), Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(_, True{})), SS.af_ends_in(i, S.af_wake(p, F.DoDone{}, S.af_cut(k, cs)))))) == True{} : Bool}
      +hc = Equal.trans(Bool, SS.af_live(i, S.af_cut(k, cs)), SS.af_live(i, cs), True{}, AC.ad.live_cut_ne(i, k, cs, ev), h)
      AC.ad.live_or_ends(i, p, F.DoDone{}, S.af_cut(k, cs), {==}, hc)

# a land: the leader and the flight's callers are done; every other
# caller stays
def mv.kept_land(+i: Nat, +k: Nat, +p: String, +cs: List<&2, F.Cl>, h: {SS.af_live(i, cs) == True{} : Bool}) -> {Bool.or(SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))), SS.af_ends(i, F.Acts{F.To{k, F.DoDone{}} <> S.af_wake(p, F.DoDone{}, S.af_cut(k, cs))})) == True{} : Bool}:
  mv.kept_land_v(Nat.is_eq(k, i), i, k, p, cs, {==}, h)

# an unwind of a caller that does not lead: every other caller stays
def mv.kept_unwind_nl(+i: Nat, +k: Nat, +cs: List<&2, F.Cl>, +ne: {Nat.is_eq(k, i) == False{} : Bool}, h: {SS.af_live(i, cs) == True{} : Bool}) -> {Bool.or(SS.af_live(i, S.af_cut(k, cs)), SS.af_ends(i, F.Acts{Nil{}})) == True{} : Bool}:
  %Equal.sym(Bool, SS.af_live(i, S.af_cut(k, cs)), SS.af_live(i, cs), AC.ad.live_cut_ne(i, k, cs, ne)) : {Bool.or(_, SS.af_ends(i, F.Acts{Nil{}})) == True{} : Bool}
  AL.ad.or_l(SS.af_live(i, cs), SS.af_ends(i, F.Acts{Nil{}}), h)

# an unwinding leader: its flight's callers fail; every other caller stays
def mv.kept_unwind_lead(+i: Nat, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +ne: {Nat.is_eq(k, i) == False{} : Bool}, h: {SS.af_live(i, cs) == True{} : Bool}) -> {Bool.or(SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))), SS.af_ends(i, F.Acts{S.af_wake(p, F.DoFail{S.af_gone(p)}, S.af_cut(k, cs))})) == True{} : Bool}:
  +hc = Equal.trans(Bool, SS.af_live(i, S.af_cut(k, cs)), SS.af_live(i, cs), True{}, AC.ad.live_cut_ne(i, k, cs, ne), h)
  AC.ad.live_or_ends(i, p, F.DoFail{S.af_gone(p)}, S.af_cut(k, cs), {==}, hc)

# One end
# -------

def mv.EndGoal(+i: Nat, +r: F.DRes) -> Type:
  ({SS.af_names(i, SS.af_out(r)) == 1n : Nat} & {SS.af_live(i, S.af_cs(SS.af_after(r))) == False{} : Bool} & {Nat.is_lt(i, mv.m_of(SS.af_after(r))) == True{} : Bool})

# a single pair whose act ends nothing ends no refresh
def mv.no_end1(-G: Type, +b: Bool, h: {Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(b, False{})), 0n)) == True{} : Bool}) -> G:
  match b:
    case True{}:
      LAE.ae.ft(G, h)
    case False{}:
      LAE.ae.ft(G, h)

def mv.end_done_v(v: Bool, +i: Nat, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, -x: F.Cl, +at: {S.af_find(k, cs) == Some{x} : Maybe<&2, F.Cl>}, +hb: {AC.ad.below(n, cs) == True{} : Bool}, +hd: {AC.ad.desc(cs) == True{} : Bool}, +ev: {Nat.is_eq(k, i) == v : Bool}, en: {Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(v, True{})), 0n)) == True{} : Bool}) -> mv.EndGoal(i, F.DRes{F.Desk{S.af_cut(k, cs), n}, F.Acts{[F.To{k, F.DoDone{}}]}}):
  match v:
    case True{}:
      +e = AL.ad.eq_true(k, i, ev)
      %Equal.sym(Bool, Nat.is_eq(k, i), True{}, ev) : ({Nat.add(S.af_bit(_), 0n) == 1n : Nat} & {SS.af_live(i, S.af_cut(k, cs)) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})
      %e : ({1n == 1n : Nat} & {SS.af_live(_, S.af_cut(k, cs)) == False{} : Bool} & {Nat.is_lt(_, n) == True{} : Bool})
      ({==}, AC.ad.gone_cut(k, cs, hd), AC.ad.live_below(k, n, cs, hb, AC.ad.find_live(k, cs, x, at)))
    case False{}:
      LAE.ae.ft(mv.EndGoal(i, F.DRes{F.Desk{S.af_cut(k, cs), n}, F.Acts{[F.To{k, F.DoDone{}}]}}), en)

# a caller done at its load is named once, leaves, and was numbered
# below the next caller
def mv.end_done(+i: Nat, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, -x: F.Cl, at: {S.af_find(k, cs) == Some{x} : Maybe<&2, F.Cl>}, hi: {mv.ids(F.Desk{cs, n}) == True{} : Bool}, en: {SS.af_ends(i, F.Acts{[F.To{k, F.DoDone{}}]}) == True{} : Bool}) -> mv.EndGoal(i, F.DRes{F.Desk{S.af_cut(k, cs), n}, F.Acts{[F.To{k, F.DoDone{}}]}}):
  +hi2 = hi
  mv.end_done_v(Nat.is_eq(k, i), i, k, cs, n, x, at, AL.ad.and_l(AC.ad.below(n, cs), AC.ad.desc(cs), hi2), AL.ad.and_r(AC.ad.below(n, cs), AC.ad.desc(cs), hi2), {==}, en)

# a caller a wake names was live before the wake's cut
def mv.named_live_v(v: Bool, +i: Nat, +p: String, +a: F.Act, +l: List<&2, F.Cl>, +ev: {SS.af_live(i, l) == v : Bool}, named: {Nat.is_lt(0n, SS.af_names_in(i, S.af_wake(p, a, l))) == True{} : Bool}) -> {SS.af_live(i, l) == True{} : Bool}:
  match v:
    case True{}:
      ev
    case False{}:
      +z = AC.ad.dead_wake(i, p, a, l, ev)
      LAE.ae.ft({SS.af_live(i, l) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(0n, SS.af_names_in(i, S.af_wake(p, a, l))), True{}, Equal.cong(Nat, Bool, y => Nat.is_lt(0n, y), 0n, SS.af_names_in(i, S.af_wake(p, a, l)), Equal.sym(Nat, SS.af_names_in(i, S.af_wake(p, a, l)), 0n, z)), named))

def mv.named_live(+i: Nat, +p: String, +a: F.Act, +l: List<&2, F.Cl>, named: {Nat.is_lt(0n, SS.af_names_in(i, S.af_wake(p, a, l))) == True{} : Bool}) -> {SS.af_live(i, l) == True{} : Bool}:
  mv.named_live_v(SS.af_live(i, l), i, p, a, l, {==}, named)

def mv.and3(-A: Type, -B: Type, -C: Type, ab: A & B, c: C) -> A & B & C:
  (a, b) = ab
  (a, b, c)

# a caller whose refresh a wake of the cut callers ends: named once, not
# live after the unwait, numbered below the next caller
def mv.end_wake(+i: Nat, +k: Nat, +p: String, +a: F.Act, +cs: List<&2, F.Cl>, +n: Nat, +hb: {AC.ad.below(n, cs) == True{} : Bool}, +hd: {AC.ad.desc(cs) == True{} : Bool}, en: {Nat.is_lt(0n, SS.af_ends_in(i, S.af_wake(p, a, S.af_cut(k, cs)))) == True{} : Bool}) -> ({SS.af_names_in(i, S.af_wake(p, a, S.af_cut(k, cs))) == 1n : Nat} & {SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool}):
  +named = AC.ad.ends_names(i, S.af_wake(p, a, S.af_cut(k, cs)), en)
  mv.and3({SS.af_names_in(i, S.af_wake(p, a, S.af_cut(k, cs))) == 1n : Nat}, {SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))) == False{} : Bool}, {Nat.is_lt(i, n) == True{} : Bool}, AC.ad.wake_once(i, p, a, S.af_cut(k, cs), AC.ad.desc_cut(k, cs, hd), named), AC.ad.live_below(i, n, cs, hb, AC.ad.live_cut_sub(i, k, cs, mv.named_live(i, p, a, S.af_cut(k, cs), named))))

def mv.end_land_v(v: Bool, +i: Nat, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, -x: F.Cl, +at: {S.af_find(k, cs) == Some{x} : Maybe<&2, F.Cl>}, +hb: {AC.ad.below(n, cs) == True{} : Bool}, +hd: {AC.ad.desc(cs) == True{} : Bool}, +ev: {Nat.is_eq(k, i) == v : Bool}, en: {Nat.is_lt(0n, Nat.add(S.af_bit(Bool.and(v, True{})), SS.af_ends_in(i, S.af_wake(p, F.DoDone{}, S.af_cut(k, cs))))) == True{} : Bool}) -> mv.EndGoal(i, F.DRes{F.Desk{S.af_unwait(p, S.af_cut(k, cs)), n}, F.Acts{F.To{k, F.DoDone{}} <> S.af_wake(p, F.DoDone{}, S.af_cut(k, cs))}}):
  match v:
    case True{}:
      +e = AL.ad.eq_true(k, i, ev)
      %Equal.sym(Bool, Nat.is_eq(k, i), True{}, ev) : ({Nat.add(S.af_bit(_), SS.af_names_in(i, S.af_wake(p, F.DoDone{}, S.af_cut(k, cs)))) == 1n : Nat} & {SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})
      %e : ({1n+SS.af_names_in(_, S.af_wake(p, F.DoDone{}, S.af_cut(k, cs))) == 1n : Nat} & {SS.af_live(_, S.af_unwait(p, S.af_cut(k, cs))) == False{} : Bool} & {Nat.is_lt(_, n) == True{} : Bool})
      +gone = AC.ad.gone_cut(k, cs, hd)
      %Equal.sym(Nat, SS.af_names_in(k, S.af_wake(p, F.DoDone{}, S.af_cut(k, cs))), 0n, AC.ad.dead_wake(k, p, F.DoDone{}, S.af_cut(k, cs), gone)) : ({1n+_ == 1n : Nat} & {SS.af_live(k, S.af_unwait(p, S.af_cut(k, cs))) == False{} : Bool} & {Nat.is_lt(k, n) == True{} : Bool})
      ({==}, AC.ad.dead_unwait(k, p, S.af_cut(k, cs), gone), AC.ad.live_below(k, n, cs, hb, AC.ad.find_live(k, cs, x, at)))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, ev) : ({Nat.add(S.af_bit(_), SS.af_names_in(i, S.af_wake(p, F.DoDone{}, S.af_cut(k, cs)))) == 1n : Nat} & {SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})
      mv.end_wake(i, k, p, F.DoDone{}, cs, n, hb, hd, en)

# a land: a caller of the flight it ends is named once, leaves, and was
# numbered below the next caller
def mv.end_land(+i: Nat, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, -x: F.Cl, at: {S.af_find(k, cs) == Some{x} : Maybe<&2, F.Cl>}, hi: {mv.ids(F.Desk{cs, n}) == True{} : Bool}, en: {SS.af_ends(i, F.Acts{F.To{k, F.DoDone{}} <> S.af_wake(p, F.DoDone{}, S.af_cut(k, cs))}) == True{} : Bool}) -> mv.EndGoal(i, F.DRes{F.Desk{S.af_unwait(p, S.af_cut(k, cs)), n}, F.Acts{F.To{k, F.DoDone{}} <> S.af_wake(p, F.DoDone{}, S.af_cut(k, cs))}}):
  +hi2 = hi
  mv.end_land_v(Nat.is_eq(k, i), i, k, p, cs, n, x, at, AL.ad.and_l(AC.ad.below(n, cs), AC.ad.desc(cs), hi2), AL.ad.and_r(AC.ad.below(n, cs), AC.ad.desc(cs), hi2), {==}, en)

# an unwinding leader: a caller of its flight is named once, leaves, and
# was numbered below the next caller
def mv.end_unwind(+i: Nat, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, hi: {mv.ids(F.Desk{cs, n}) == True{} : Bool}, en: {SS.af_ends(i, F.Acts{S.af_wake(p, F.DoFail{S.af_gone(p)}, S.af_cut(k, cs))}) == True{} : Bool}) -> mv.EndGoal(i, F.DRes{F.Desk{S.af_unwait(p, S.af_cut(k, cs)), n}, F.Acts{S.af_wake(p, F.DoFail{S.af_gone(p)}, S.af_cut(k, cs))}}):
  +hi2 = hi
  mv.end_wake(i, k, p, F.DoFail{S.af_gone(p)}, cs, n, AL.ad.and_l(AC.ad.below(n, cs), AC.ad.desc(cs), hi2), AL.ad.and_r(AC.ad.below(n, cs), AC.ad.desc(cs), hi2), en)

# Nothing after the end
# ---------------------

def mv.QGoal(+i: Nat, +r: F.DRes) -> Type:
  ({SS.af_names(i, SS.af_out(r)) == 0n : Nat} & {SS.af_live(i, S.af_cs(SS.af_after(r))) == False{} : Bool} & {Nat.is_lt(i, mv.m_of(SS.af_after(r))) == True{} : Bool})

# nothing named, nobody moved
def mv.q_keep(+i: Nat, +cs: List<&2, F.Cl>, +n: Nat, o: F.DOut, z: {SS.af_names(i, o) == 0n : Nat}, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> mv.QGoal(i, F.DRes{F.Desk{cs, n}, o}):
  (di, lt) = q
  (z, di, lt)

# a live caller is not one that is not live
def mv.live_ne_v(v: Bool, +k: Nat, +i: Nat, +cs: List<&2, F.Cl>, +ev: {Nat.is_eq(k, i) == v : Bool}, lk: {SS.af_live(k, cs) == True{} : Bool}, di: {SS.af_live(i, cs) == False{} : Bool}) -> {Nat.is_eq(k, i) == False{} : Bool}:
  match v:
    case True{}:
      +e = AL.ad.eq_true(k, i, ev)
      +lk2 = Equal.trans(Bool, SS.af_live(i, cs), SS.af_live(k, cs), True{}, Equal.cong(Nat, Bool, y => SS.af_live(y, cs), i, k, Equal.sym(Nat, k, i, e)), lk)
      LAE.ae.ft({Nat.is_eq(k, i) == False{} : Bool}, Equal.trans(Bool, False{}, SS.af_live(i, cs), True{}, Equal.sym(Bool, SS.af_live(i, cs), False{}, di), lk2))
    case False{}:
      ev

def mv.live_ne(+k: Nat, +i: Nat, +cs: List<&2, F.Cl>, lk: {SS.af_live(k, cs) == True{} : Bool}, di: {SS.af_live(i, cs) == False{} : Bool}) -> {Nat.is_eq(k, i) == False{} : Bool}:
  mv.live_ne_v(Nat.is_eq(k, i), k, i, cs, {==}, lk, di)

def mv.q_arrive(+i: Nat, +n: Nat, +p: String, +cs: List<&2, F.Cl>, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> mv.QGoal(i, F.DRes{F.Desk{F.Cl{n, p, F.Loads{}} <> cs, 1n+n}, F.Acts{[F.To{n, F.DoLoad{}}]}}):
  (di, lt) = q
  +lt2 = lt
  +ne = AL.ad.lt_ne(i, n, lt2)
  %Equal.sym(Bool, Nat.is_eq(n, i), False{}, ne) : ({Nat.add(S.af_bit(_), 0n) == 0n : Nat} & {Bool.or(_, SS.af_live(i, cs)) == False{} : Bool} & {Nat.is_lt(i, 1n+n) == True{} : Bool})
  ({==}, di, AL.ad.lt_succ(i, n, lt2))

# a single pair to the found caller k, who stays at a2
def mv.q_set(+i: Nat, +k: Nat, +a2: F.At, act: F.Act, +cs: List<&2, F.Cl>, +n: Nat, -x: F.Cl, at: {S.af_find(k, cs) == Some{x} : Maybe<&2, F.Cl>}, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> mv.QGoal(i, F.DRes{F.Desk{S.af_set(k, a2, cs), n}, F.Acts{[F.To{k, act}]}}):
  (di, lt) = q
  +di2 = di
  %Equal.sym(Bool, Nat.is_eq(k, i), False{}, mv.live_ne(k, i, cs, AC.ad.find_live(k, cs, x, at), di2)) : ({Nat.add(S.af_bit(_), 0n) == 0n : Nat} & {SS.af_live(i, S.af_set(k, a2, cs)) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})
  %Equal.sym(Bool, SS.af_live(i, S.af_set(k, a2, cs)), SS.af_live(i, cs), AC.ad.live_set(i, k, a2, cs)) : ({0n == 0n : Nat} & {_ == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})
  ({==}, di2, lt)

# a single pair to the found caller k, who leaves
def mv.q_cut1(+i: Nat, +k: Nat, act: F.Act, +cs: List<&2, F.Cl>, +n: Nat, -x: F.Cl, at: {S.af_find(k, cs) == Some{x} : Maybe<&2, F.Cl>}, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> mv.QGoal(i, F.DRes{F.Desk{S.af_cut(k, cs), n}, F.Acts{[F.To{k, act}]}}):
  (di, lt) = q
  +di2 = di
  %Equal.sym(Bool, Nat.is_eq(k, i), False{}, mv.live_ne(k, i, cs, AC.ad.find_live(k, cs, x, at), di2)) : ({Nat.add(S.af_bit(_), 0n) == 0n : Nat} & {SS.af_live(i, S.af_cut(k, cs)) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})
  ({==}, AC.ad.dead_cut(i, k, cs, di2), lt)

def mv.q_land(+i: Nat, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, -x: F.Cl, at: {S.af_find(k, cs) == Some{x} : Maybe<&2, F.Cl>}, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> mv.QGoal(i, F.DRes{F.Desk{S.af_unwait(p, S.af_cut(k, cs)), n}, F.Acts{F.To{k, F.DoDone{}} <> S.af_wake(p, F.DoDone{}, S.af_cut(k, cs))}}):
  (di, lt) = q
  +di2 = di
  +dc = AC.ad.dead_cut(i, k, cs, di2)
  %Equal.sym(Bool, Nat.is_eq(k, i), False{}, mv.live_ne(k, i, cs, AC.ad.find_live(k, cs, x, at), di2)) : ({Nat.add(S.af_bit(_), SS.af_names_in(i, S.af_wake(p, F.DoDone{}, S.af_cut(k, cs)))) == 0n : Nat} & {SS.af_live(i, S.af_unwait(p, S.af_cut(k, cs))) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})
  (AC.ad.dead_wake(i, p, F.DoDone{}, S.af_cut(k, cs), dc), AC.ad.dead_unwait(i, p, S.af_cut(k, cs), dc), lt)

def mv.q_cut0(+i: Nat, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> mv.QGoal(i, F.DRes{F.Desk{S.af_cut(k, cs), n}, F.Acts{Nil{}}}):
  (di, lt) = q
  ({==}, AC.ad.dead_cut(i, k, cs, di), lt)

def mv.q_unwind(+i: Nat, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat, q: ({SS.af_live(i, cs) == False{} : Bool} & {Nat.is_lt(i, n) == True{} : Bool})) -> mv.QGoal(i, F.DRes{F.Desk{S.af_unwait(p, S.af_cut(k, cs)), n}, F.Acts{S.af_wake(p, F.DoFail{S.af_gone(p)}, S.af_cut(k, cs))}}):
  (di, lt) = q
  +dc = AC.ad.dead_cut(i, k, cs, di)
  (AC.ad.dead_wake(i, p, F.DoFail{S.af_gone(p)}, S.af_cut(k, cs), dc), AC.ad.dead_unwait(i, p, S.af_cut(k, cs), dc), lt)
