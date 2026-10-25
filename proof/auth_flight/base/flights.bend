# eukhe: lemmas of the desk's safety proofs about its flights: how many
# lead each provider's flight, which providers stay in flight, and that
# every waiting caller's provider stays in flight.

import Base
import ../../../bend/auth_flight.bend as F
import ../../../laws/auth_flight/entry.bend as S
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../base/staging.bend as LStaging
import ../../../laws/auth_flight/safety.bend as SS
import ./entry.bend as LAE
import ./logic.bend as AL
import ./callers.bend as AC

# b || x stays true when x implies y
def ad.or_keep(+b: Bool, +x: Bool, +y: Bool, h: {Bool.or(b, x) == True{} : Bool}, ih: {x == True{} : Bool} -> {y == True{} : Bool}) -> {Bool.or(b, y) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

# Leaders
# -------

def ad.lead_cut_le_at(hit: Bool, +j: Nat, +p: String, +o: F.At, +t: List<&2, F.Cl>, +r: List<&2, F.Cl>, +q: String, ih: {Nat.is_le(SS.af_leaders(q, r), SS.af_leaders(q, t)) == True{} : Bool}) -> {Nat.is_le(SS.af_leaders(q, S.af_cut.pick(hit, F.Cl{j, p, o}, t, r)), Nat.add(S.af_bit(S.af_lead(q, F.Cl{j, p, o})), SS.af_leaders(q, t))) == True{} : Bool}:
  match hit:
    case True{}:
      AL.ad.le_add_l(S.af_bit(S.af_lead(q, F.Cl{j, p, o})), SS.af_leaders(q, t))
    case False{}:
      AL.ad.le_add_mono(S.af_bit(S.af_lead(q, F.Cl{j, p, o})), SS.af_leaders(q, r), SS.af_leaders(q, t), ih)

# a cut has no more leaders
def ad.lead_cut_le(+q: String, +k: Nat, cs: List<&2, F.Cl>) -> {Nat.is_le(SS.af_leaders(q, S.af_cut(k, cs)), SS.af_leaders(q, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          ad.lead_cut_le_at(Nat.is_eq(j, k), j, p, o, t, S.af_cut(k, t), q, ad.lead_cut_le(q, k, t))

def ad.lead_unwait_le_at(hit: Bool, +j: Nat, +p: String, +o: F.At, +t: List<&2, F.Cl>, +r: List<&2, F.Cl>, +q: String, ih: {Nat.is_le(SS.af_leaders(q, r), SS.af_leaders(q, t)) == True{} : Bool}) -> {Nat.is_le(SS.af_leaders(q, S.af_unwait.pick(hit, F.Cl{j, p, o}, r)), Nat.add(S.af_bit(S.af_lead(q, F.Cl{j, p, o})), SS.af_leaders(q, t))) == True{} : Bool}:
  match hit:
    case True{}:
      AL.ad.le_trans(SS.af_leaders(q, r), SS.af_leaders(q, t), Nat.add(S.af_bit(S.af_lead(q, F.Cl{j, p, o})), SS.af_leaders(q, t)), ih, AL.ad.le_add_l(S.af_bit(S.af_lead(q, F.Cl{j, p, o})), SS.af_leaders(q, t)))
    case False{}:
      AL.ad.le_add_mono(S.af_bit(S.af_lead(q, F.Cl{j, p, o})), SS.af_leaders(q, r), SS.af_leaders(q, t), ih)

# an unwait has no more leaders
def ad.lead_unwait_le(+q: String, +p: String, cs: List<&2, F.Cl>) -> {Nat.is_le(SS.af_leaders(q, S.af_unwait(p, cs)), SS.af_leaders(q, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j, +p0, +o}:
          ad.lead_unwait_le_at(S.af_waits(p, F.Cl{j, p0, o}), j, p0, o, t, S.af_unwait(p, t), q, ad.lead_unwait_le(q, p, t))

def ad.lead_set_same_at(v: Bool, +j0: Nat, +p0: String, +o0: F.At, +t: List<&2, F.Cl>, +k: Nat, +a2: F.At, +q: String, -j: Nat, -p: String, +a: F.At, +at: {S.af_find.pick(v, F.Cl{j0, p0, o0}, S.af_find(k, t)) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, same: {S.af_leads(a) == S.af_leads(a2) : Bool}, ih: {S.af_find(k, t) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>} -> {SS.af_leaders(q, S.af_set(k, a2, t)) == SS.af_leaders(q, t) : Nat}) -> {SS.af_leaders(q, S.af_set.pick(v, F.Cl{j0, p0, o0}, a2, t, S.af_set(k, a2, t))) == Nat.add(S.af_bit(S.af_lead(q, F.Cl{j0, p0, o0})), SS.af_leaders(q, t)) : Nat}:
  match v:
    case True{}:
      +eo = AC.ad.hit_o(j0, p0, o0, j, p, a, at)
      %Equal.sym(F.At, o0, a, eo) : {Nat.add(S.af_bit(Bool.and(S.af_leads(a2), String.eq(p0, q))), SS.af_leaders(q, t)) == Nat.add(S.af_bit(Bool.and(S.af_leads(_), String.eq(p0, q))), SS.af_leaders(q, t)) : Nat}
      %same : {Nat.add(S.af_bit(Bool.and(_, String.eq(p0, q))), SS.af_leaders(q, t)) == Nat.add(S.af_bit(Bool.and(S.af_leads(a), String.eq(p0, q))), SS.af_leaders(q, t)) : Nat}
      {==}
    case False{}:
      %ih(at) : {Nat.add(S.af_bit(S.af_lead(q, F.Cl{j0, p0, o0})), SS.af_leaders(q, S.af_set(k, a2, t))) == Nat.add(S.af_bit(S.af_lead(q, F.Cl{j0, p0, o0})), _) : Nat}
      {==}

# a set that keeps whether the caller leads keeps the leaders
def ad.lead_set_same(+q: String, +k: Nat, +a2: F.At, cs: List<&2, F.Cl>, -j: Nat, -p: String, +a: F.At, at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, +same: {S.af_leads(a) == S.af_leads(a2) : Bool}) -> {SS.af_leaders(q, S.af_set(k, a2, cs)) == SS.af_leaders(q, cs) : Nat}:
  match cs:
    case Nil{}:
      LAE.ae.none_some(F.Cl, {SS.af_leaders(q, S.af_set(k, a2, Nil{})) == SS.af_leaders(q, Nil{}) : Nat}, F.Cl{j, p, a}, at)
    case x <> +t:
      match x:
        case F.Cl{+j0, +p0, +o0}:
          ad.lead_set_same_at(Nat.is_eq(j0, k), j0, p0, o0, t, k, a2, q, j, p, a, at, same, g => ad.lead_set_same(q, k, a2, t, j, p, a, g, same))

def ad.lead_set_gain_at(v: Bool, +j0: Nat, +p0: String, +o0: F.At, +t: List<&2, F.Cl>, +k: Nat, +q: String, -j: Nat, +p: String, +at: {S.af_find.pick(v, F.Cl{j0, p0, o0}, S.af_find(k, t)) == Some{F.Cl{j, p, F.Loads{}}} : Maybe<&2, F.Cl>}, ih: {S.af_find(k, t) == Some{F.Cl{j, p, F.Loads{}}} : Maybe<&2, F.Cl>} -> {SS.af_leaders(q, S.af_set(k, F.Checks{}, t)) == Nat.add(S.af_bit(String.eq(p, q)), SS.af_leaders(q, t)) : Nat}) -> {SS.af_leaders(q, S.af_set.pick(v, F.Cl{j0, p0, o0}, F.Checks{}, t, S.af_set(k, F.Checks{}, t))) == Nat.add(S.af_bit(String.eq(p, q)), Nat.add(S.af_bit(S.af_lead(q, F.Cl{j0, p0, o0})), SS.af_leaders(q, t))) : Nat}:
  match v:
    case True{}:
      +eo = AC.ad.hit_o(j0, p0, o0, j, p, F.Loads{}, at)
      +ep = AC.ad.hit_p(j0, p0, o0, j, p, F.Loads{}, at)
      %Equal.sym(F.At, o0, F.Loads{}, eo) : {Nat.add(S.af_bit(String.eq(p0, q)), SS.af_leaders(q, t)) == Nat.add(S.af_bit(String.eq(p, q)), Nat.add(S.af_bit(Bool.and(S.af_leads(_), String.eq(p0, q))), SS.af_leaders(q, t))) : Nat}
      %Equal.sym(String, p0, p, ep) : {Nat.add(S.af_bit(String.eq(_, q)), SS.af_leaders(q, t)) == Nat.add(S.af_bit(String.eq(p, q)), SS.af_leaders(q, t)) : Nat}
      {==}
    case False{}:
      %Equal.sym(Nat, SS.af_leaders(q, S.af_set(k, F.Checks{}, t)), Nat.add(S.af_bit(String.eq(p, q)), SS.af_leaders(q, t)), ih(at)) : {Nat.add(S.af_bit(S.af_lead(q, F.Cl{j0, p0, o0})), _) == Nat.add(S.af_bit(String.eq(p, q)), Nat.add(S.af_bit(S.af_lead(q, F.Cl{j0, p0, o0})), SS.af_leaders(q, t))) : Nat}
      AL.ad.add_swap(S.af_bit(S.af_lead(q, F.Cl{j0, p0, o0})), S.af_bit(String.eq(p, q)), SS.af_leaders(q, t))

# a loading caller of p that leads adds one leader of p
def ad.lead_set_gain(+q: String, +k: Nat, cs: List<&2, F.Cl>, -j: Nat, +p: String, at: {S.af_find(k, cs) == Some{F.Cl{j, p, F.Loads{}}} : Maybe<&2, F.Cl>}) -> {SS.af_leaders(q, S.af_set(k, F.Checks{}, cs)) == Nat.add(S.af_bit(String.eq(p, q)), SS.af_leaders(q, cs)) : Nat}:
  match cs:
    case Nil{}:
      LAE.ae.none_some(F.Cl, {SS.af_leaders(q, S.af_set(k, F.Checks{}, Nil{})) == Nat.add(S.af_bit(String.eq(p, q)), SS.af_leaders(q, Nil{})) : Nat}, F.Cl{j, p, F.Loads{}}, at)
    case x <> +t:
      match x:
        case F.Cl{+j0, +p0, +o0}:
          ad.lead_set_gain_at(Nat.is_eq(j0, k), j0, p0, o0, t, k, q, j, p, at, g => ad.lead_set_gain(q, k, t, j, p, g))

# a provider with no flight in flight has no leader
def ad.lead_none(+q: String, cs: List<&2, F.Cl>, h: {S.af_inflight(q, cs) == False{} : Bool}) -> {SS.af_leaders(q, cs) == 0n : Nat}:
  match cs:
    case Nil{}:
      {==}
    case +x <> +t:
      +h2 = h
      %Equal.sym(Bool, S.af_lead(q, x), False{}, AC.ad.nor_l(S.af_lead(q, x), S.af_inflight(q, t), h2)) : {Nat.add(S.af_bit(_), SS.af_leaders(q, t)) == 0n : Nat}
      ad.lead_none(q, t, AC.ad.nor_r(S.af_lead(q, x), S.af_inflight(q, t), h2))

# a fetcher leads
def ad.fetch_le(+q: String, cs: List<&2, F.Cl>) -> {Nat.is_le(SS.af_fetchers(q, cs), SS.af_leaders(q, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{j, +p, a}:
          match a:
            case F.Loads{}:
              ad.fetch_le(q, t)
            case F.Checks{}:
              AL.ad.le_trans(SS.af_fetchers(q, t), SS.af_leaders(q, t), Nat.add(S.af_bit(String.eq(p, q)), SS.af_leaders(q, t)), ad.fetch_le(q, t), AL.ad.le_add_l(S.af_bit(String.eq(p, q)), SS.af_leaders(q, t)))
            case F.Fetches{}:
              AL.ad.le_add_mono(S.af_bit(String.eq(p, q)), SS.af_fetchers(q, t), SS.af_leaders(q, t), ad.fetch_le(q, t))
            case F.Stores{}:
              AL.ad.le_trans(SS.af_fetchers(q, t), SS.af_leaders(q, t), Nat.add(S.af_bit(String.eq(p, q)), SS.af_leaders(q, t)), ad.fetch_le(q, t), AL.ad.le_add_l(S.af_bit(String.eq(p, q)), SS.af_leaders(q, t)))
            case F.Waits{}:
              ad.fetch_le(q, t)

# Flights in flight
# -----------------

def ad.infl_cut_at(v: Bool, +j0: Nat, +p0: String, +o0: F.At, +t: List<&2, F.Cl>, +k: Nat, +q: String, -j: Nat, +p: String, +a: F.At, +at: {S.af_find.pick(v, F.Cl{j0, p0, o0}, S.af_find(k, t)) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, nl: {Bool.and(S.af_leads(a), String.eq(p, q)) == False{} : Bool}, h: {Bool.or(S.af_lead(q, F.Cl{j0, p0, o0}), S.af_inflight(q, t)) == True{} : Bool}, ih: {S.af_find(k, t) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>} -> {S.af_inflight(q, t) == True{} : Bool} -> {S.af_inflight(q, S.af_cut(k, t)) == True{} : Bool}) -> {S.af_inflight(q, S.af_cut.pick(v, F.Cl{j0, p0, o0}, t, S.af_cut(k, t))) == True{} : Bool}:
  match v:
    case True{}:
      +eo = AC.ad.hit_o(j0, p0, o0, j, p, a, at)
      +ep = AC.ad.hit_p(j0, p0, o0, j, p, a, at)
      +e1 = Equal.cong(String, Bool, s => Bool.and(S.af_leads(o0), String.eq(s, q)), p0, p, ep)
      +e2 = Equal.cong(F.At, Bool, z => Bool.and(S.af_leads(z), String.eq(p, q)), o0, a, eo)
      +ln = Equal.trans(Bool, Bool.and(S.af_leads(o0), String.eq(p0, q)), Bool.and(S.af_leads(o0), String.eq(p, q)), False{}, e1, Equal.trans(Bool, Bool.and(S.af_leads(o0), String.eq(p, q)), Bool.and(S.af_leads(a), String.eq(p, q)), False{}, e2, nl))
      AC.ad.or_false(Bool.and(S.af_leads(o0), String.eq(p0, q)), S.af_inflight(q, t), ln, h)
    case False{}:
      ad.or_keep(S.af_lead(q, F.Cl{j0, p0, o0}), S.af_inflight(q, t), S.af_inflight(q, S.af_cut(k, t)), h, g => ih(at, g))

# a cut of a caller that does not lead q's flight keeps it in flight
def ad.infl_cut(+q: String, +k: Nat, cs: List<&2, F.Cl>, -j: Nat, +p: String, +a: F.At, at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, +nl: {Bool.and(S.af_leads(a), String.eq(p, q)) == False{} : Bool}, h: {S.af_inflight(q, cs) == True{} : Bool}) -> {S.af_inflight(q, S.af_cut(k, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      LAE.ae.ft({S.af_inflight(q, S.af_cut(k, Nil{})) == True{} : Bool}, h)
    case x <> +t:
      match x:
        case F.Cl{+j0, +p0, +o0}:
          ad.infl_cut_at(Nat.is_eq(j0, k), j0, p0, o0, t, k, q, j, p, a, at, nl, h, g => g2 => ad.infl_cut(q, k, t, j, p, a, g, nl, g2))

def ad.infl_unwait_w(hit: Bool, +j0: Nat, +q0: String, +t: List<&2, F.Cl>, +p: String, +q: String, ih: {S.af_inflight(q, S.af_unwait(p, t)) == True{} : Bool}) -> {S.af_inflight(q, S.af_unwait.pick(hit, F.Cl{j0, q0, F.Waits{}}, S.af_unwait(p, t))) == True{} : Bool}:
  match hit:
    case True{}:
      ih
    case False{}:
      ih

# an unwait keeps every flight in flight
def ad.infl_unwait(+q: String, +p: String, cs: List<&2, F.Cl>, h: {S.af_inflight(q, cs) == True{} : Bool}) -> {S.af_inflight(q, S.af_unwait(p, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      h
    case x <> +t:
      match x:
        case F.Cl{+j0, +q0, o0}:
          match o0:
            case F.Loads{}:
              ad.infl_unwait(q, p, t, h)
            case F.Checks{}:
              ad.or_keep(String.eq(q0, q), S.af_inflight(q, t), S.af_inflight(q, S.af_unwait(p, t)), h, g => ad.infl_unwait(q, p, t, g))
            case F.Fetches{}:
              ad.or_keep(String.eq(q0, q), S.af_inflight(q, t), S.af_inflight(q, S.af_unwait(p, t)), h, g => ad.infl_unwait(q, p, t, g))
            case F.Stores{}:
              ad.or_keep(String.eq(q0, q), S.af_inflight(q, t), S.af_inflight(q, S.af_unwait(p, t)), h, g => ad.infl_unwait(q, p, t, g))
            case F.Waits{}:
              ad.infl_unwait_w(String.eq(q0, p), j0, q0, t, p, q, ad.infl_unwait(q, p, t, h))

def ad.infl_set_w(w: Bool, +o0: F.At, +a2: F.At, +p0: String, +q: String, +x: Bool, +ew: {Bool.and(S.af_leads(o0), String.eq(p0, q)) == w : Bool}, keep: {Bool.or(Bool.not(S.af_leads(o0)), S.af_leads(a2)) == True{} : Bool}, h: {Bool.or(w, x) == True{} : Bool}) -> {Bool.or(Bool.and(S.af_leads(a2), String.eq(p0, q)), x) == True{} : Bool}:
  match w:
    case True{}:
      +lo = AL.ad.and_l(S.af_leads(o0), String.eq(p0, q), ew)
      +eq = AL.ad.and_r(S.af_leads(o0), String.eq(p0, q), ew)
      +la = AC.ad.tr(b => Bool.or(Bool.not(b), S.af_leads(a2)), True{}, S.af_leads(o0), Equal.sym(Bool, S.af_leads(o0), True{}, lo), keep)
      AL.ad.or_l(Bool.and(S.af_leads(a2), String.eq(p0, q)), x, AL.ad.and_tt(S.af_leads(a2), String.eq(p0, q), la, eq))
    case False{}:
      AL.ad.or_r(Bool.and(S.af_leads(a2), String.eq(p0, q)), x, h)

def ad.infl_set_at(v: Bool, +j0: Nat, +p0: String, +o0: F.At, +t: List<&2, F.Cl>, +k: Nat, +a2: F.At, +q: String, -j: Nat, -p: String, +o: F.At, +at: {S.af_find.pick(v, F.Cl{j0, p0, o0}, S.af_find(k, t)) == Some{F.Cl{j, p, o}} : Maybe<&2, F.Cl>}, keep: {Bool.or(Bool.not(S.af_leads(o)), S.af_leads(a2)) == True{} : Bool}, h: {Bool.or(S.af_lead(q, F.Cl{j0, p0, o0}), S.af_inflight(q, t)) == True{} : Bool}, ih: {S.af_find(k, t) == Some{F.Cl{j, p, o}} : Maybe<&2, F.Cl>} -> {S.af_inflight(q, t) == True{} : Bool} -> {S.af_inflight(q, S.af_set(k, a2, t)) == True{} : Bool}) -> {S.af_inflight(q, S.af_set.pick(v, F.Cl{j0, p0, o0}, a2, t, S.af_set(k, a2, t))) == True{} : Bool}:
  match v:
    case True{}:
      +eo = AC.ad.hit_o(j0, p0, o0, j, p, o, at)
      +keep0 = AC.ad.tr(z => Bool.or(Bool.not(z), S.af_leads(a2)), S.af_leads(o0), S.af_leads(o), Equal.cong(F.At, Bool, z => S.af_leads(z), o0, o, eo), keep)
      ad.infl_set_w(Bool.and(S.af_leads(o0), String.eq(p0, q)), o0, a2, p0, q, S.af_inflight(q, t), {==}, keep0, h)
    case False{}:
      ad.or_keep(S.af_lead(q, F.Cl{j0, p0, o0}), S.af_inflight(q, t), S.af_inflight(q, S.af_set(k, a2, t)), h, g => ih(at, g))

# a set that keeps a leader leading keeps every flight in flight
def ad.infl_set(+q: String, +k: Nat, +a2: F.At, cs: List<&2, F.Cl>, -j: Nat, -p: String, +o: F.At, at: {S.af_find(k, cs) == Some{F.Cl{j, p, o}} : Maybe<&2, F.Cl>}, +keep: {Bool.or(Bool.not(S.af_leads(o)), S.af_leads(a2)) == True{} : Bool}, h: {S.af_inflight(q, cs) == True{} : Bool}) -> {S.af_inflight(q, S.af_set(k, a2, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      LAE.ae.ft({S.af_inflight(q, S.af_set(k, a2, Nil{})) == True{} : Bool}, h)
    case x <> +t:
      match x:
        case F.Cl{+j0, +p0, +o0}:
          ad.infl_set_at(Nat.is_eq(j0, k), j0, p0, o0, t, k, a2, q, j, p, o, at, keep, h, g => g2 => ad.infl_set(q, k, a2, t, j, p, o, g, keep, g2))

# Waiting callers led
# -------------------

def ad.led_cutL_at(hit: Bool, +j0: Nat, +p0: String, +o0: F.At, +t: List<&2, F.Cl>, +r: List<&2, F.Cl>, +c: List<&2, F.Cl>, hx: {SS.af_led(F.Cl{j0, p0, o0}, c) == True{} : Bool}, ht: {SS.af_led_all(t, c) == True{} : Bool}, ih: {SS.af_led_all(r, c) == True{} : Bool}) -> {SS.af_led_all(S.af_cut.pick(hit, F.Cl{j0, p0, o0}, t, r), c) == True{} : Bool}:
  match hit:
    case True{}:
      ht
    case False{}:
      AL.ad.and_tt(SS.af_led(F.Cl{j0, p0, o0}, c), SS.af_led_all(r, c), hx, ih)

# a cut keeps every waiting caller led
def ad.led_cutL(+k: Nat, xs: List<&2, F.Cl>, +c: List<&2, F.Cl>, h: {SS.af_led_all(xs, c) == True{} : Bool}) -> {SS.af_led_all(S.af_cut(k, xs), c) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j0, +p0, +o0}:
          +h2 = h
          +ht = AL.ad.and_r(SS.af_led(F.Cl{j0, p0, o0}, c), SS.af_led_all(t, c), h2)
          ad.led_cutL_at(Nat.is_eq(j0, k), j0, p0, o0, t, S.af_cut(k, t), c, AL.ad.and_l(SS.af_led(F.Cl{j0, p0, o0}, c), SS.af_led_all(t, c), h2), ht, ad.led_cutL(k, t, c, ht))

def ad.led_setL_at(v: Bool, +j0: Nat, +p0: String, +o0: F.At, +t: List<&2, F.Cl>, +k: Nat, +a2: F.At, +c: List<&2, F.Cl>, +j: Nat, +p: String, -o: F.At, +at: {S.af_find.pick(v, F.Cl{j0, p0, o0}, S.af_find(k, t)) == Some{F.Cl{j, p, o}} : Maybe<&2, F.Cl>}, ok: {SS.af_led(F.Cl{j, p, a2}, c) == True{} : Bool}, h: {Bool.and(SS.af_led(F.Cl{j0, p0, o0}, c), SS.af_led_all(t, c)) == True{} : Bool}, ih: {S.af_find(k, t) == Some{F.Cl{j, p, o}} : Maybe<&2, F.Cl>} -> {SS.af_led_all(t, c) == True{} : Bool} -> {SS.af_led_all(S.af_set(k, a2, t), c) == True{} : Bool}) -> {SS.af_led_all(S.af_set.pick(v, F.Cl{j0, p0, o0}, a2, t, S.af_set(k, a2, t)), c) == True{} : Bool}:
  match v:
    case True{}:
      +ep = AC.ad.hit_p(j0, p0, o0, j, p, o, at)
      +ej = AC.ad.hit_j(j0, p0, o0, j, p, o, at)
      %Equal.sym(String, p0, p, ep) : {Bool.and(SS.af_led(F.Cl{j0, _, a2}, c), SS.af_led_all(t, c)) == True{} : Bool}
      %Equal.sym(Nat, j0, j, ej) : {Bool.and(SS.af_led(F.Cl{_, p, a2}, c), SS.af_led_all(t, c)) == True{} : Bool}
      AL.ad.and_tt(SS.af_led(F.Cl{j, p, a2}, c), SS.af_led_all(t, c), ok, AL.ad.and_r(SS.af_led(F.Cl{j0, p0, o0}, c), SS.af_led_all(t, c), h))
    case False{}:
      +h2 = h
      AL.ad.and_tt(SS.af_led(F.Cl{j0, p0, o0}, c), SS.af_led_all(S.af_set(k, a2, t), c), AL.ad.and_l(SS.af_led(F.Cl{j0, p0, o0}, c), SS.af_led_all(t, c), h2), ih(at, AL.ad.and_r(SS.af_led(F.Cl{j0, p0, o0}, c), SS.af_led_all(t, c), h2)))

# a set keeps every waiting caller led when the caller set is led
def ad.led_setL(+k: Nat, +a2: F.At, xs: List<&2, F.Cl>, +c: List<&2, F.Cl>, +j: Nat, +p: String, -o: F.At, at: {S.af_find(k, xs) == Some{F.Cl{j, p, o}} : Maybe<&2, F.Cl>}, +ok: {SS.af_led(F.Cl{j, p, a2}, c) == True{} : Bool}, h: {SS.af_led_all(xs, c) == True{} : Bool}) -> {SS.af_led_all(S.af_set(k, a2, xs), c) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j0, +p0, +o0}:
          ad.led_setL_at(Nat.is_eq(j0, k), j0, p0, o0, t, k, a2, c, j, p, o, at, ok, h, g => g2 => ad.led_setL(k, a2, t, c, j, p, o, g, ok, g2))

# an arrival keeps every waiting caller led
def ad.led_arrive(xs: List<&2, F.Cl>, +n: Nat, +p: String, +cs: List<&2, F.Cl>, h: {SS.af_led_all(xs, cs) == True{} : Bool}) -> {SS.af_led_all(xs, F.Cl{n, p, F.Loads{}} <> cs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{j, +q, a}:
          match a:
            case F.Loads{}:
              ad.led_arrive(t, n, p, cs, h)
            case F.Checks{}:
              ad.led_arrive(t, n, p, cs, h)
            case F.Fetches{}:
              ad.led_arrive(t, n, p, cs, h)
            case F.Stores{}:
              ad.led_arrive(t, n, p, cs, h)
            case F.Waits{}:
              +h2 = h
              AL.ad.and_tt(S.af_inflight(q, cs), SS.af_led_all(t, F.Cl{n, p, F.Loads{}} <> cs), AL.ad.and_l(S.af_inflight(q, cs), SS.af_led_all(t, cs), h2), ad.led_arrive(t, n, p, cs, AL.ad.and_r(S.af_inflight(q, cs), SS.af_led_all(t, cs), h2)))

# a caller that does not lead leads no provider's flight
def ad.nl_of(+a: F.At, +p: String, +q: String, nl: {S.af_leads(a) == False{} : Bool}) -> {Bool.and(S.af_leads(a), String.eq(p, q)) == False{} : Bool}:
  %Equal.sym(Bool, S.af_leads(a), False{}, nl) : {Bool.and(_, String.eq(p, q)) == False{} : Bool}
  {==}

# the cut of a caller that does not lead keeps every waiting caller led
def ad.led_cutC(xs: List<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, -j: Nat, +p: String, +a: F.At, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, +nl: {S.af_leads(a) == False{} : Bool}, h: {SS.af_led_all(xs, cs) == True{} : Bool}) -> {SS.af_led_all(xs, S.af_cut(k, cs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{j0, +q0, o0}:
          match o0:
            case F.Loads{}:
              ad.led_cutC(t, k, cs, j, p, a, at, nl, h)
            case F.Checks{}:
              ad.led_cutC(t, k, cs, j, p, a, at, nl, h)
            case F.Fetches{}:
              ad.led_cutC(t, k, cs, j, p, a, at, nl, h)
            case F.Stores{}:
              ad.led_cutC(t, k, cs, j, p, a, at, nl, h)
            case F.Waits{}:
              +h2 = h
              AL.ad.and_tt(S.af_inflight(q0, S.af_cut(k, cs)), SS.af_led_all(t, S.af_cut(k, cs)), ad.infl_cut(q0, k, cs, j, p, a, at, ad.nl_of(a, p, q0, nl), AL.ad.and_l(S.af_inflight(q0, cs), SS.af_led_all(t, cs), h2)), ad.led_cutC(t, k, cs, j, p, a, at, nl, AL.ad.and_r(S.af_inflight(q0, cs), SS.af_led_all(t, cs), h2)))

# a set that keeps a leader leading keeps every waiting caller led
def ad.led_setC(xs: List<&2, F.Cl>, +k: Nat, +a2: F.At, +cs: List<&2, F.Cl>, -j: Nat, -p: String, +o: F.At, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, o}} : Maybe<&2, F.Cl>}, +keep: {Bool.or(Bool.not(S.af_leads(o)), S.af_leads(a2)) == True{} : Bool}, h: {SS.af_led_all(xs, cs) == True{} : Bool}) -> {SS.af_led_all(xs, S.af_set(k, a2, cs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{j0, +q0, o0}:
          match o0:
            case F.Loads{}:
              ad.led_setC(t, k, a2, cs, j, p, o, at, keep, h)
            case F.Checks{}:
              ad.led_setC(t, k, a2, cs, j, p, o, at, keep, h)
            case F.Fetches{}:
              ad.led_setC(t, k, a2, cs, j, p, o, at, keep, h)
            case F.Stores{}:
              ad.led_setC(t, k, a2, cs, j, p, o, at, keep, h)
            case F.Waits{}:
              +h2 = h
              AL.ad.and_tt(S.af_inflight(q0, S.af_set(k, a2, cs)), SS.af_led_all(t, S.af_set(k, a2, cs)), ad.infl_set(q0, k, a2, cs, j, p, o, at, keep, AL.ad.and_l(S.af_inflight(q0, cs), SS.af_led_all(t, cs), h2)), ad.led_setC(t, k, a2, cs, j, p, o, at, keep, AL.ad.and_r(S.af_inflight(q0, cs), SS.af_led_all(t, cs), h2)))

# a leader of p that lands leaves no other provider's flight
def ad.land_nl(+a: F.At, +p: String, +q: String, lead: {S.af_leads(a) == True{} : Bool}, ne: {String.eq(q, p) == False{} : Bool}) -> {Bool.and(S.af_leads(a), String.eq(p, q)) == False{} : Bool}:
  %Equal.sym(Bool, S.af_leads(a), True{}, lead) : {Bool.and(_, String.eq(p, q)) == False{} : Bool}
  AL.ad.str_ne_sym(p, q, ne)

def ad.led_land_w(hit: Bool, +q0: String, +j0: Nat, +t: List<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, -j: Nat, +p: String, +a: F.At, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, +lead: {S.af_leads(a) == True{} : Bool}, +eh: {String.eq(q0, p) == hit : Bool}, hq: {S.af_inflight(q0, cs) == True{} : Bool}, ih: {SS.af_led_all(S.af_unwait(p, t), S.af_unwait(p, S.af_cut(k, cs))) == True{} : Bool}) -> {SS.af_led_all(S.af_unwait.pick(hit, F.Cl{j0, q0, F.Waits{}}, S.af_unwait(p, t)), S.af_unwait(p, S.af_cut(k, cs))) == True{} : Bool}:
  match hit:
    case True{}:
      ih
    case False{}:
      AL.ad.and_tt(S.af_inflight(q0, S.af_unwait(p, S.af_cut(k, cs))), SS.af_led_all(S.af_unwait(p, t), S.af_unwait(p, S.af_cut(k, cs))), ad.infl_unwait(q0, p, S.af_cut(k, cs), ad.infl_cut(q0, k, cs, j, p, a, at, ad.land_nl(a, p, q0, lead, eh), hq)), ih)

# the land of p's flight by its leader keeps every remaining waiting
# caller led
def ad.led_landC(xs: List<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, -j: Nat, +p: String, +a: F.At, +at: {S.af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}, +lead: {S.af_leads(a) == True{} : Bool}, h: {SS.af_led_all(xs, cs) == True{} : Bool}) -> {SS.af_led_all(S.af_unwait(p, xs), S.af_unwait(p, S.af_cut(k, cs))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case F.Cl{+j0, +q0, o0}:
          match o0:
            case F.Loads{}:
              ad.led_landC(t, k, cs, j, p, a, at, lead, h)
            case F.Checks{}:
              ad.led_landC(t, k, cs, j, p, a, at, lead, h)
            case F.Fetches{}:
              ad.led_landC(t, k, cs, j, p, a, at, lead, h)
            case F.Stores{}:
              ad.led_landC(t, k, cs, j, p, a, at, lead, h)
            case F.Waits{}:
              +h2 = h
              ad.led_land_w(String.eq(q0, p), q0, j0, t, k, cs, j, p, a, at, lead, {==}, AL.ad.and_l(S.af_inflight(q0, cs), SS.af_led_all(t, cs), h2), ad.led_landC(t, k, cs, j, p, a, at, lead, AL.ad.and_r(S.af_inflight(q0, cs), SS.af_led_all(t, cs), h2)))
