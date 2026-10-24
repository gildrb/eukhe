# eukhe: the proof of LAW staging_entry_answers
#
# PROOF of LAW staging_entry_answers: every part of a request Rust spells
# reads back by the wire laws (wire_nat_round_trip, wire_str_round_trip;
# tags and Bools compute), a list item by item (the count, then each item:
# se.*_go), so the decoder reads the whole request and nothing is left
# (se.req); the entry then answers the rule's decision, spelled as the
# spec spells it (se.reply: each encoder is its speller, item by item).

import Base
import ../../bend/ffi_staging.bend as FSg
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../bend/wire.bend as Wr
import ../../laws/staging.bend as Staging
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../base/wire.bend as LWire

# Bool
# ----

def se.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def se.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : se.BT(_, G)
  Unit{}

def se.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def se.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      se.ft({b == True{} : Bool}, e)

# Items
# -----

def se.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def se.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def se.form(k: Sg.Form, +rest: String) -> {FSg.get_form(Staging.sp_w_form(k, rest)) == Wr.Got{k, rest} : Wr.Dec<Sg.Form>}:
  match k:
    case Sg.KDir{m}:
      match m:
        case True{}:
          {==}
        case False{}:
          {==}
    case Sg.KFile{}:
      {==}
    case Sg.KOther{}:
      {==}

def se.seen(e: Sg.Seen, +rest: String, h: {Staging.sp_fit_seen(e) == True{} : Bool}) -> {FSg.get_seen(Staging.sp_w_seen(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Sg.Seen>}:
  match e:
    case Sg.Seen{n, +k}:
      match n:
        case Sg.Utf{+s}:
          %se.str(s, Staging.sp_w_form(k, rest), h) : {FSg.get_seen.go(FSg.get_name.utf(_)) == Wr.Got{Sg.Seen{Sg.Utf{s}, k}, rest} : Wr.Dec<Sg.Seen>}
          %Equal.sym(Wr.Dec<Sg.Form>, FSg.get_form(Staging.sp_w_form(k, rest)), Wr.Got{k, rest}, se.form(k, rest)) : {FSg.get_seen.form(Sg.Utf{s}, _) == Wr.Got{Sg.Seen{Sg.Utf{s}, k}, rest} : Wr.Dec<Sg.Seen>}
          {==}
        case Sg.Raw{}:
          %Equal.sym(Wr.Dec<Sg.Form>, FSg.get_form(Staging.sp_w_form(k, rest)), Wr.Got{k, rest}, se.form(k, rest)) : {FSg.get_seen.form(Sg.Raw{}, _) == Wr.Got{Sg.Seen{Sg.Raw{}, k}, rest} : Wr.Dec<Sg.Seen>}
          {==}

def se.time(t: Sg.Time, +rest: String, h: {Staging.sp_fit_time(t) == True{} : Bool}) -> {FSg.get_time(Staging.sp_w_time(t, rest)) == Wr.Got{t, rest} : Wr.Dec<Sg.Time>}:
  match t:
    case Sg.Time{+s, +n}:
      +hh = h
      %se.nat(s, Wr.put_nat(n, rest), se.and_l(LawsBase.wire_fits(s), LawsBase.wire_fits(n), hh)) : {FSg.get_time.go(_) == Wr.Got{Sg.Time{s, n}, rest} : Wr.Dec<Sg.Time>}
      %se.nat(n, rest, se.and_r(LawsBase.wire_fits(s), LawsBase.wire_fits(n), hh)) : {FSg.get_time.nanos(s, _) == Wr.Got{Sg.Time{s, n}, rest} : Wr.Dec<Sg.Time>}
      {==}

def se.cwd(c: Maybe<&2, String>, +rest: String, h: {Staging.sp_fit_cwd(c) == True{} : Bool}) -> {FSg.get_cwd(Staging.sp_w_cwd(c, rest)) == Wr.Got{c, rest} : Wr.Dec<Maybe<&2, String>>}:
  match c:
    case None{}:
      {==}
    case Some{+s}:
      %se.str(s, rest, h) : {FSg.get_cwd.some(_) == Wr.Got{Some{s}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

# Lists of seens
# ------------

def se.seens_items(xs: List<&2, Sg.Seen>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Staging.sp_w_seen(x, se.seens_items(t, rest))

def se.seens_put_go(xs: List<&2, Sg.Seen>, -rest: String) -> {Wr.put_list.go(~Sg.Seen, ~Staging.sp_w_seen, xs, rest) == (List.length(&2, Sg.Seen, xs), se.seens_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sg.Seen, ~Staging.sp_w_seen, t, rest), (List.length(&2, Sg.Seen, t), se.seens_items(t, rest)), se.seens_put_go(t, rest)) : {Wr.put_list.step(~Sg.Seen, ~Staging.sp_w_seen, x, _) == (1n+List.length(&2, Sg.Seen, t), Staging.sp_w_seen(x, se.seens_items(t, rest))) : Nat & String}
      {==}

def se.seens_put(+xs: List<&2, Sg.Seen>, -rest: String) -> {Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, xs, rest) == Wr.put_nat(List.length(&2, Sg.Seen, xs), se.seens_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Sg.Seen, ~Staging.sp_w_seen, xs, rest), (List.length(&2, Sg.Seen, xs), se.seens_items(xs, rest)), se.seens_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Sg.Seen, xs), se.seens_items(xs, rest)) : String}
  {==}

def se.seens_go_rt(+t: List<&2, Sg.Seen>, +x: Sg.Seen, +rest: String, +hf: {Staging.sp_fit_seens.all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, List.length(&2, Sg.Seen, t), FSg.get_seen(Staging.sp_w_seen(x, se.seens_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Sg.Seen>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Sg.Seen>, FSg.get_seen(Staging.sp_w_seen(x, rest)), Wr.Got{x, rest}, se.seen(x, rest, se.and_l(Staging.sp_fit_seen(x), True{}, hf))) : {Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Sg.Seen>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Sg.Seen>, FSg.get_seen(Staging.sp_w_seen(x, Staging.sp_w_seen(y, se.seens_items(u, rest)))), Wr.Got{x, Staging.sp_w_seen(y, se.seens_items(u, rest))}, se.seen(x, Staging.sp_w_seen(y, se.seens_items(u, rest)), se.and_l(Staging.sp_fit_seen(x), Staging.sp_fit_seens.all(y <> u), hf))) : {Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, 1n+List.length(&2, Sg.Seen, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Sg.Seen>>}
      %Equal.sym(Wr.Dec<List<&2, Sg.Seen>>, Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, List.length(&2, Sg.Seen, u), FSg.get_seen(Staging.sp_w_seen(y, se.seens_items(u, rest)))), Wr.Got{y <> u, rest}, se.seens_go_rt(u, y, rest, se.and_r(Staging.sp_fit_seen(x), Staging.sp_fit_seens.all(y <> u), hf))) : {Wr.get_list.cons(Sg.Seen, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Sg.Seen>>}
      {==}

def se.seens_rt(+xs: List<&2, Sg.Seen>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Sg.Seen, xs)), Staging.sp_fit_seens.all(xs)) == True{} : Bool}) -> {Wr.get_list(~Sg.Seen, ~FSg.get_seen, Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Sg.Seen>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, x <> t, r), Wr.put_nat(List.length(&2, Sg.Seen, x <> t), se.seens_items(x <> t, r)), se.seens_put(x <> t, r)) : {Wr.get_list(~Sg.Seen, ~FSg.get_seen, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Sg.Seen>>}
      %se.nat(List.length(&2, Sg.Seen, x <> t), se.seens_items(x <> t, r), se.and_l(LawsBase.wire_fits(List.length(&2, Sg.Seen, x <> t)), Staging.sp_fit_seens.all(x <> t), hh)) : {Wr.get_list.start(~Sg.Seen, ~FSg.get_seen, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Sg.Seen>>}
      se.seens_go_rt(t, x, r, se.and_r(LawsBase.wire_fits(List.length(&2, Sg.Seen, x <> t)), Staging.sp_fit_seens.all(x <> t), hh))

# Lists of times
# ------------

def se.times_items(xs: List<&2, Sg.Time>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Staging.sp_w_time(x, se.times_items(t, rest))

def se.times_put_go(xs: List<&2, Sg.Time>, -rest: String) -> {Wr.put_list.go(~Sg.Time, ~Staging.sp_w_time, xs, rest) == (List.length(&2, Sg.Time, xs), se.times_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sg.Time, ~Staging.sp_w_time, t, rest), (List.length(&2, Sg.Time, t), se.times_items(t, rest)), se.times_put_go(t, rest)) : {Wr.put_list.step(~Sg.Time, ~Staging.sp_w_time, x, _) == (1n+List.length(&2, Sg.Time, t), Staging.sp_w_time(x, se.times_items(t, rest))) : Nat & String}
      {==}

def se.times_put(+xs: List<&2, Sg.Time>, -rest: String) -> {Wr.put_list(~Sg.Time, ~Staging.sp_w_time, xs, rest) == Wr.put_nat(List.length(&2, Sg.Time, xs), se.times_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Sg.Time, ~Staging.sp_w_time, xs, rest), (List.length(&2, Sg.Time, xs), se.times_items(xs, rest)), se.times_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Sg.Time, xs), se.times_items(xs, rest)) : String}
  {==}

def se.times_go_rt(+t: List<&2, Sg.Time>, +x: Sg.Time, +rest: String, +hf: {Staging.sp_fit_times.all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Sg.Time, ~FSg.get_time, List.length(&2, Sg.Time, t), FSg.get_time(Staging.sp_w_time(x, se.times_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Sg.Time>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Sg.Time>, FSg.get_time(Staging.sp_w_time(x, rest)), Wr.Got{x, rest}, se.time(x, rest, se.and_l(Staging.sp_fit_time(x), True{}, hf))) : {Wr.get_list.go(~Sg.Time, ~FSg.get_time, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Sg.Time>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Sg.Time>, FSg.get_time(Staging.sp_w_time(x, Staging.sp_w_time(y, se.times_items(u, rest)))), Wr.Got{x, Staging.sp_w_time(y, se.times_items(u, rest))}, se.time(x, Staging.sp_w_time(y, se.times_items(u, rest)), se.and_l(Staging.sp_fit_time(x), Staging.sp_fit_times.all(y <> u), hf))) : {Wr.get_list.go(~Sg.Time, ~FSg.get_time, 1n+List.length(&2, Sg.Time, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Sg.Time>>}
      %Equal.sym(Wr.Dec<List<&2, Sg.Time>>, Wr.get_list.go(~Sg.Time, ~FSg.get_time, List.length(&2, Sg.Time, u), FSg.get_time(Staging.sp_w_time(y, se.times_items(u, rest)))), Wr.Got{y <> u, rest}, se.times_go_rt(u, y, rest, se.and_r(Staging.sp_fit_time(x), Staging.sp_fit_times.all(y <> u), hf))) : {Wr.get_list.cons(Sg.Time, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Sg.Time>>}
      {==}

def se.times_rt(+xs: List<&2, Sg.Time>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Sg.Time, xs)), Staging.sp_fit_times.all(xs)) == True{} : Bool}) -> {Wr.get_list(~Sg.Time, ~FSg.get_time, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Sg.Time>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, x <> t, r), Wr.put_nat(List.length(&2, Sg.Time, x <> t), se.times_items(x <> t, r)), se.times_put(x <> t, r)) : {Wr.get_list(~Sg.Time, ~FSg.get_time, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Sg.Time>>}
      %se.nat(List.length(&2, Sg.Time, x <> t), se.times_items(x <> t, r), se.and_l(LawsBase.wire_fits(List.length(&2, Sg.Time, x <> t)), Staging.sp_fit_times.all(x <> t), hh)) : {Wr.get_list.start(~Sg.Time, ~FSg.get_time, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Sg.Time>>}
      se.times_go_rt(t, x, r, se.and_r(LawsBase.wire_fits(List.length(&2, Sg.Time, x <> t)), Staging.sp_fit_times.all(x <> t), hh))

def se.obs(o: Ls.Obs, +rest: String, h: {Staging.sp_fit_obs(o) == True{} : Bool}) -> {FSg.get_obs(Staging.sp_w_obs(o, rest)) == Wr.Got{o, rest} : Wr.Dec<Ls.Obs>}:
  match o:
    case Ls.Obs{+e, +c, +ts}:
      +hh = h
      +ht = se.and_r(Staging.sp_fit_cwd(c), Staging.sp_fit_times(ts), se.and_r(Staging.sp_fit_seen(e), Bool.and(Staging.sp_fit_cwd(c), Staging.sp_fit_times(ts)), hh))
      +hc = se.and_l(Staging.sp_fit_cwd(c), Staging.sp_fit_times(ts), se.and_r(Staging.sp_fit_seen(e), Bool.and(Staging.sp_fit_cwd(c), Staging.sp_fit_times(ts)), hh))
      %Equal.sym(Wr.Dec<Sg.Seen>, FSg.get_seen(Staging.sp_w_seen(e, Staging.sp_w_cwd(c, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, ts, rest)))), Wr.Got{e, Staging.sp_w_cwd(c, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, ts, rest))}, se.seen(e, Staging.sp_w_cwd(c, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, ts, rest)), se.and_l(Staging.sp_fit_seen(e), Bool.and(Staging.sp_fit_cwd(c), Staging.sp_fit_times(ts)), hh))) : {FSg.get_obs.go(_) == Wr.Got{Ls.Obs{e, c, ts}, rest} : Wr.Dec<Ls.Obs>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FSg.get_cwd(Staging.sp_w_cwd(c, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, ts, rest))), Wr.Got{c, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, ts, rest)}, se.cwd(c, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, ts, rest), hc)) : {FSg.get_obs.cwd(e, _) == Wr.Got{Ls.Obs{e, c, ts}, rest} : Wr.Dec<Ls.Obs>}
      %Equal.sym(Wr.Dec<List<&2, Sg.Time>>, Wr.get_list(~Sg.Time, ~FSg.get_time, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, ts, rest)), Wr.Got{ts, rest}, se.times_rt(ts, rest, ht)) : {FSg.get_obs.times(e, c, _) == Wr.Got{Ls.Obs{e, c, ts}, rest} : Wr.Dec<Ls.Obs>}
      {==}

# Lists of obss
# ------------

def se.obss_items(xs: List<&2, Ls.Obs>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Staging.sp_w_obs(x, se.obss_items(t, rest))

def se.obss_put_go(xs: List<&2, Ls.Obs>, -rest: String) -> {Wr.put_list.go(~Ls.Obs, ~Staging.sp_w_obs, xs, rest) == (List.length(&2, Ls.Obs, xs), se.obss_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Obs, ~Staging.sp_w_obs, t, rest), (List.length(&2, Ls.Obs, t), se.obss_items(t, rest)), se.obss_put_go(t, rest)) : {Wr.put_list.step(~Ls.Obs, ~Staging.sp_w_obs, x, _) == (1n+List.length(&2, Ls.Obs, t), Staging.sp_w_obs(x, se.obss_items(t, rest))) : Nat & String}
      {==}

def se.obss_put(+xs: List<&2, Ls.Obs>, -rest: String) -> {Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, xs, rest) == Wr.put_nat(List.length(&2, Ls.Obs, xs), se.obss_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Obs, ~Staging.sp_w_obs, xs, rest), (List.length(&2, Ls.Obs, xs), se.obss_items(xs, rest)), se.obss_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Ls.Obs, xs), se.obss_items(xs, rest)) : String}
  {==}

def se.obss_go_rt(+t: List<&2, Ls.Obs>, +x: Ls.Obs, +rest: String, +hf: {Staging.sp_fit_obss.all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, List.length(&2, Ls.Obs, t), FSg.get_obs(Staging.sp_w_obs(x, se.obss_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ls.Obs>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Ls.Obs>, FSg.get_obs(Staging.sp_w_obs(x, rest)), Wr.Got{x, rest}, se.obs(x, rest, se.and_l(Staging.sp_fit_obs(x), True{}, hf))) : {Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Ls.Obs>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Ls.Obs>, FSg.get_obs(Staging.sp_w_obs(x, Staging.sp_w_obs(y, se.obss_items(u, rest)))), Wr.Got{x, Staging.sp_w_obs(y, se.obss_items(u, rest))}, se.obs(x, Staging.sp_w_obs(y, se.obss_items(u, rest)), se.and_l(Staging.sp_fit_obs(x), Staging.sp_fit_obss.all(y <> u), hf))) : {Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, 1n+List.length(&2, Ls.Obs, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ls.Obs>>}
      %Equal.sym(Wr.Dec<List<&2, Ls.Obs>>, Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, List.length(&2, Ls.Obs, u), FSg.get_obs(Staging.sp_w_obs(y, se.obss_items(u, rest)))), Wr.Got{y <> u, rest}, se.obss_go_rt(u, y, rest, se.and_r(Staging.sp_fit_obs(x), Staging.sp_fit_obss.all(y <> u), hf))) : {Wr.get_list.cons(Ls.Obs, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ls.Obs>>}
      {==}

def se.obss_rt(+xs: List<&2, Ls.Obs>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Ls.Obs, xs)), Staging.sp_fit_obss.all(xs)) == True{} : Bool}) -> {Wr.get_list(~Ls.Obs, ~FSg.get_obs, Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Ls.Obs>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, x <> t, r), Wr.put_nat(List.length(&2, Ls.Obs, x <> t), se.obss_items(x <> t, r)), se.obss_put(x <> t, r)) : {Wr.get_list(~Ls.Obs, ~FSg.get_obs, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Ls.Obs>>}
      %se.nat(List.length(&2, Ls.Obs, x <> t), se.obss_items(x <> t, r), se.and_l(LawsBase.wire_fits(List.length(&2, Ls.Obs, x <> t)), Staging.sp_fit_obss.all(x <> t), hh)) : {Wr.get_list.start(~Ls.Obs, ~FSg.get_obs, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Ls.Obs>>}
      se.obss_go_rt(t, x, r, se.and_r(LawsBase.wire_fits(List.length(&2, Ls.Obs, x <> t)), Staging.sp_fit_obss.all(x <> t), hh))

# The request
# -----------

# the times of a judge request, after its tags (c and l concrete)
def se.judge.t(-c: Sg.Cand, -l: Sg.Lock, +now: Sg.Time, +own: Sg.Time, +inner: List<&2, Sg.Time>,
  e1: {FSg.get_time(Staging.sp_w_time(now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, "")))) == Wr.Got{now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, ""))} : Wr.Dec<Sg.Time>},
  e2: {FSg.get_time(Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, ""))) == Wr.Got{own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, "")} : Wr.Dec<Sg.Time>},
  e3: {Wr.get_list(~Sg.Time, ~FSg.get_time, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, "")) == Wr.Got{inner, ""} : Wr.Dec<List<&2, Sg.Time>>}) ->
  {FSg.get_judge.now(c, l, FSg.get_time(Staging.sp_w_time(now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, ""))))) == Wr.Got{FSg.Judge{c, l, now, own, inner}, ""} : Wr.Dec<FSg.Req>}:
  %Equal.sym(Wr.Dec<Sg.Time>, FSg.get_time(Staging.sp_w_time(now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, "")))), Wr.Got{now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, ""))}, e1) : {FSg.get_judge.now(c, l, _) == Wr.Got{FSg.Judge{c, l, now, own, inner}, ""} : Wr.Dec<FSg.Req>}
  %Equal.sym(Wr.Dec<Sg.Time>, FSg.get_time(Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, ""))), Wr.Got{own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, "")}, e2) : {FSg.get_judge.own(c, l, now, _) == Wr.Got{FSg.Judge{c, l, now, own, inner}, ""} : Wr.Dec<FSg.Req>}
  %Equal.sym(Wr.Dec<List<&2, Sg.Time>>, Wr.get_list(~Sg.Time, ~FSg.get_time, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, "")), Wr.Got{inner, ""}, e3) : {FSg.get_judge.inner(c, l, now, own, _) == Wr.Got{FSg.Judge{c, l, now, own, inner}, ""} : Wr.Dec<FSg.Req>}
  {==}

# the body of a judge request reads back, its times by the lemmas e1 e2 e3
def se.judge(c: Sg.Cand, l: Sg.Lock, +now: Sg.Time, +own: Sg.Time, +inner: List<&2, Sg.Time>,
  e1: {FSg.get_time(Staging.sp_w_time(now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, "")))) == Wr.Got{now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, ""))} : Wr.Dec<Sg.Time>},
  e2: {FSg.get_time(Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, ""))) == Wr.Got{own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, "")} : Wr.Dec<Sg.Time>},
  e3: {Wr.get_list(~Sg.Time, ~FSg.get_time, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, "")) == Wr.Got{inner, ""} : Wr.Dec<List<&2, Sg.Time>>}) ->
  {FSg.get_req(Staging.sp_w_req(FSg.Judge{c, l, now, own, inner}, "")) == Wr.Got{FSg.Judge{c, l, now, own, inner}, ""} : Wr.Dec<FSg.Req>}:
  match c l:
    case Sg.CDir{} Sg.LHeld{}:
      se.judge.t(Sg.CDir{}, Sg.LHeld{}, now, own, inner, e1, e2, e3)
    case Sg.CDir{} Sg.LFree{}:
      se.judge.t(Sg.CDir{}, Sg.LFree{}, now, own, inner, e1, e2, e3)
    case Sg.CDir{} Sg.LAbsent{}:
      se.judge.t(Sg.CDir{}, Sg.LAbsent{}, now, own, inner, e1, e2, e3)
    case Sg.CLock{} Sg.LHeld{}:
      se.judge.t(Sg.CLock{}, Sg.LHeld{}, now, own, inner, e1, e2, e3)
    case Sg.CLock{} Sg.LFree{}:
      se.judge.t(Sg.CLock{}, Sg.LFree{}, now, own, inner, e1, e2, e3)
    case Sg.CLock{} Sg.LAbsent{}:
      se.judge.t(Sg.CLock{}, Sg.LAbsent{}, now, own, inner, e1, e2, e3)

def se.req(r: FSg.Req, h: {Staging.sp_fit_req(r) == True{} : Bool}) -> {FSg.get_req(Staging.sp_w_req(r, "")) == Wr.Got{r, ""} : Wr.Dec<FSg.Req>}:
  match r:
    case FSg.Publish{b}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case FSg.Meet{+es}:
      %Equal.sym(Wr.Dec<List<&2, Sg.Seen>>, Wr.get_list(~Sg.Seen, ~FSg.get_seen, Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, es, "")), Wr.Got{es, ""}, se.seens_rt(es, "", h)) : {FSg.get_meet(_) == Wr.Got{FSg.Meet{es}, ""} : Wr.Dec<FSg.Req>}
      {==}
    case FSg.Judge{c, l, +now, +own, +inner}:
      +hh = h
      +rest2 = Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, "")
      +rest1 = Staging.sp_w_time(own, rest2)
      +h_now = se.and_l(Staging.sp_fit_time(now), Bool.and(Staging.sp_fit_time(own), Staging.sp_fit_times(inner)), hh)
      +h_own = se.and_l(Staging.sp_fit_time(own), Staging.sp_fit_times(inner), se.and_r(Staging.sp_fit_time(now), Bool.and(Staging.sp_fit_time(own), Staging.sp_fit_times(inner)), hh))
      +h_in = se.and_r(Staging.sp_fit_time(own), Staging.sp_fit_times(inner), se.and_r(Staging.sp_fit_time(now), Bool.and(Staging.sp_fit_time(own), Staging.sp_fit_times(inner)), hh))
      se.judge(c, l, now, own, inner, se.time(now, rest1, h_now), se.time(own, rest2, h_own), se.times_rt(inner, "", h_in))
    case FSg.Scan{+es}:
      %Equal.sym(Wr.Dec<List<&2, Sg.Seen>>, Wr.get_list(~Sg.Seen, ~FSg.get_seen, Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, es, "")), Wr.Got{es, ""}, se.seens_rt(es, "", h)) : {FSg.get_scan(_) == Wr.Got{FSg.Scan{es}, ""} : Wr.Dec<FSg.Req>}
      {==}
    case FSg.Rows{+os}:
      %Equal.sym(Wr.Dec<List<&2, Ls.Obs>>, Wr.get_list(~Ls.Obs, ~FSg.get_obs, Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, os, "")), Wr.Got{os, ""}, se.obss_rt(os, "", h)) : {FSg.get_rows(_) == Wr.Got{FSg.Rows{os}, ""} : Wr.Dec<FSg.Req>}
      {==}

# The reply
# ---------

def se.mets_items(xs: List<&2, Sg.Met>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Staging.sp_w_met(x, se.mets_items(t, rest))

def se.mets_spec(xs: List<&2, Sg.Met>, -rest: String) -> {Wr.put_list.go(~Sg.Met, ~Staging.sp_w_met, xs, rest) == (List.length(&2, Sg.Met, xs), se.mets_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sg.Met, ~Staging.sp_w_met, t, rest), (List.length(&2, Sg.Met, t), se.mets_items(t, rest)), se.mets_spec(t, rest)) : {Wr.put_list.step(~Sg.Met, ~Staging.sp_w_met, x, _) == (1n+List.length(&2, Sg.Met, t), Staging.sp_w_met(x, se.mets_items(t, rest))) : Nat & String}
      {==}

def se.mets_code(xs: List<&2, Sg.Met>, -rest: String) -> {Wr.put_list.go(~Sg.Met, ~FSg.put_met, xs, rest) == (List.length(&2, Sg.Met, xs), se.mets_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Sg.MKeep{} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sg.Met, ~FSg.put_met, t, rest), (List.length(&2, Sg.Met, t), se.mets_items(t, rest)), se.mets_code(t, rest)) : {Wr.put_list.step(~Sg.Met, ~FSg.put_met, Sg.MKeep{}, _) == (1n+List.length(&2, Sg.Met, t), Staging.sp_w_met(Sg.MKeep{}, se.mets_items(t, rest))) : Nat & String}
      {==}
    case Sg.MDescend{} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sg.Met, ~FSg.put_met, t, rest), (List.length(&2, Sg.Met, t), se.mets_items(t, rest)), se.mets_code(t, rest)) : {Wr.put_list.step(~Sg.Met, ~FSg.put_met, Sg.MDescend{}, _) == (1n+List.length(&2, Sg.Met, t), Staging.sp_w_met(Sg.MDescend{}, se.mets_items(t, rest))) : Nat & String}
      {==}
    case Sg.MLeftover{} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sg.Met, ~FSg.put_met, t, rest), (List.length(&2, Sg.Met, t), se.mets_items(t, rest)), se.mets_code(t, rest)) : {Wr.put_list.step(~Sg.Met, ~FSg.put_met, Sg.MLeftover{}, _) == (1n+List.length(&2, Sg.Met, t), Staging.sp_w_met(Sg.MLeftover{}, se.mets_items(t, rest))) : Nat & String}
      {==}
    case Sg.MOrphan{} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sg.Met, ~FSg.put_met, t, rest), (List.length(&2, Sg.Met, t), se.mets_items(t, rest)), se.mets_code(t, rest)) : {Wr.put_list.step(~Sg.Met, ~FSg.put_met, Sg.MOrphan{}, _) == (1n+List.length(&2, Sg.Met, t), Staging.sp_w_met(Sg.MOrphan{}, se.mets_items(t, rest))) : Nat & String}
      {==}

def se.mets(+xs: List<&2, Sg.Met>, -rest: String) -> {Wr.put_list.go(~Sg.Met, ~FSg.put_met, xs, rest) == Wr.put_list.go(~Sg.Met, ~Staging.sp_w_met, xs, rest) : Nat & String}:
  Equal.trans(Nat & String, Wr.put_list.go(~Sg.Met, ~FSg.put_met, xs, rest), (List.length(&2, Sg.Met, xs), se.mets_items(xs, rest)), Wr.put_list.go(~Sg.Met, ~Staging.sp_w_met, xs, rest), se.mets_code(xs, rest), Equal.sym(Nat & String, Wr.put_list.go(~Sg.Met, ~Staging.sp_w_met, xs, rest), (List.length(&2, Sg.Met, xs), se.mets_items(xs, rest)), se.mets_spec(xs, rest)))

def se.picks_items(xs: List<&2, Ls.Pick>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Staging.sp_w_pick(x, se.picks_items(t, rest))

def se.picks_spec(xs: List<&2, Ls.Pick>, -rest: String) -> {Wr.put_list.go(~Ls.Pick, ~Staging.sp_w_pick, xs, rest) == (List.length(&2, Ls.Pick, xs), se.picks_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Pick, ~Staging.sp_w_pick, t, rest), (List.length(&2, Ls.Pick, t), se.picks_items(t, rest)), se.picks_spec(t, rest)) : {Wr.put_list.step(~Ls.Pick, ~Staging.sp_w_pick, x, _) == (1n+List.length(&2, Ls.Pick, t), Staging.sp_w_pick(x, se.picks_items(t, rest))) : Nat & String}
      {==}

def se.picks_code(xs: List<&2, Ls.Pick>, -rest: String) -> {Wr.put_list.go(~Ls.Pick, ~FSg.put_pick, xs, rest) == (List.length(&2, Ls.Pick, xs), se.picks_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Ls.PSkip{} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Pick, ~FSg.put_pick, t, rest), (List.length(&2, Ls.Pick, t), se.picks_items(t, rest)), se.picks_code(t, rest)) : {Wr.put_list.step(~Ls.Pick, ~FSg.put_pick, Ls.PSkip{}, _) == (1n+List.length(&2, Ls.Pick, t), Staging.sp_w_pick(Ls.PSkip{}, se.picks_items(t, rest))) : Nat & String}
      {==}
    case Ls.PStore{a} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Pick, ~FSg.put_pick, t, rest), (List.length(&2, Ls.Pick, t), se.picks_items(t, rest)), se.picks_code(t, rest)) : {Wr.put_list.step(~Ls.Pick, ~FSg.put_pick, Ls.PStore{a}, _) == (1n+List.length(&2, Ls.Pick, t), Staging.sp_w_pick(Ls.PStore{a}, se.picks_items(t, rest))) : Nat & String}
      {==}
    case Ls.PLegacy{a} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Pick, ~FSg.put_pick, t, rest), (List.length(&2, Ls.Pick, t), se.picks_items(t, rest)), se.picks_code(t, rest)) : {Wr.put_list.step(~Ls.Pick, ~FSg.put_pick, Ls.PLegacy{a}, _) == (1n+List.length(&2, Ls.Pick, t), Staging.sp_w_pick(Ls.PLegacy{a}, se.picks_items(t, rest))) : Nat & String}
      {==}

def se.picks(+xs: List<&2, Ls.Pick>, -rest: String) -> {Wr.put_list.go(~Ls.Pick, ~FSg.put_pick, xs, rest) == Wr.put_list.go(~Ls.Pick, ~Staging.sp_w_pick, xs, rest) : Nat & String}:
  Equal.trans(Nat & String, Wr.put_list.go(~Ls.Pick, ~FSg.put_pick, xs, rest), (List.length(&2, Ls.Pick, xs), se.picks_items(xs, rest)), Wr.put_list.go(~Ls.Pick, ~Staging.sp_w_pick, xs, rest), se.picks_code(xs, rest), Equal.sym(Nat & String, Wr.put_list.go(~Ls.Pick, ~Staging.sp_w_pick, xs, rest), (List.length(&2, Ls.Pick, xs), se.picks_items(xs, rest)), se.picks_spec(xs, rest)))

def se.rows_items(xs: List<&2, Ls.Row>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Staging.sp_w_row(x, se.rows_items(t, rest))

def se.rows_spec(xs: List<&2, Ls.Row>, -rest: String) -> {Wr.put_list.go(~Ls.Row, ~Staging.sp_w_row, xs, rest) == (List.length(&2, Ls.Row, xs), se.rows_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Row, ~Staging.sp_w_row, t, rest), (List.length(&2, Ls.Row, t), se.rows_items(t, rest)), se.rows_spec(t, rest)) : {Wr.put_list.step(~Ls.Row, ~Staging.sp_w_row, x, _) == (1n+List.length(&2, Ls.Row, t), Staging.sp_w_row(x, se.rows_items(t, rest))) : Nat & String}
      {==}

def se.rows_code(xs: List<&2, Ls.Row>, -rest: String) -> {Wr.put_list.go(~Ls.Row, ~FSg.put_row, xs, rest) == (List.length(&2, Ls.Row, xs), se.rows_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Ls.Row{i, Ls.PSkip{}, Sg.Time{a, b}} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Row, ~FSg.put_row, t, rest), (List.length(&2, Ls.Row, t), se.rows_items(t, rest)), se.rows_code(t, rest)) : {Wr.put_list.step(~Ls.Row, ~FSg.put_row, Ls.Row{i, Ls.PSkip{}, Sg.Time{a, b}}, _) == (1n+List.length(&2, Ls.Row, t), Staging.sp_w_row(Ls.Row{i, Ls.PSkip{}, Sg.Time{a, b}}, se.rows_items(t, rest))) : Nat & String}
      {==}
    case Ls.Row{i, Ls.PStore{x}, Sg.Time{a, b}} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Row, ~FSg.put_row, t, rest), (List.length(&2, Ls.Row, t), se.rows_items(t, rest)), se.rows_code(t, rest)) : {Wr.put_list.step(~Ls.Row, ~FSg.put_row, Ls.Row{i, Ls.PStore{x}, Sg.Time{a, b}}, _) == (1n+List.length(&2, Ls.Row, t), Staging.sp_w_row(Ls.Row{i, Ls.PStore{x}, Sg.Time{a, b}}, se.rows_items(t, rest))) : Nat & String}
      {==}
    case Ls.Row{i, Ls.PLegacy{x}, Sg.Time{a, b}} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Row, ~FSg.put_row, t, rest), (List.length(&2, Ls.Row, t), se.rows_items(t, rest)), se.rows_code(t, rest)) : {Wr.put_list.step(~Ls.Row, ~FSg.put_row, Ls.Row{i, Ls.PLegacy{x}, Sg.Time{a, b}}, _) == (1n+List.length(&2, Ls.Row, t), Staging.sp_w_row(Ls.Row{i, Ls.PLegacy{x}, Sg.Time{a, b}}, se.rows_items(t, rest))) : Nat & String}
      {==}

def se.rows(+xs: List<&2, Ls.Row>, -rest: String) -> {Wr.put_list.go(~Ls.Row, ~FSg.put_row, xs, rest) == Wr.put_list.go(~Ls.Row, ~Staging.sp_w_row, xs, rest) : Nat & String}:
  Equal.trans(Nat & String, Wr.put_list.go(~Ls.Row, ~FSg.put_row, xs, rest), (List.length(&2, Ls.Row, xs), se.rows_items(xs, rest)), Wr.put_list.go(~Ls.Row, ~Staging.sp_w_row, xs, rest), se.rows_code(xs, rest), Equal.sym(Nat & String, Wr.put_list.go(~Ls.Row, ~Staging.sp_w_row, xs, rest), (List.length(&2, Ls.Row, xs), se.rows_items(xs, rest)), se.rows_spec(xs, rest)))

def se.verdict(v: Sg.Verdict) -> {FSg.put_verdict(v, "") == Staging.sp_w_verdict(v, "") : String}:
  match v:
    case Sg.Moved{}:
      {==}
    case Sg.Taken{}:
      {==}

def se.plan(p: Sg.Plan) -> {FSg.put_plan(p, "") == Staging.sp_w_plan(p, "") : String}:
  match p:
    case Sg.PKeep{}:
      {==}
    case Sg.PRmDir{}:
      {==}
    case Sg.PRmDirLock{}:
      {==}
    case Sg.PRmFile{}:
      {==}

def se.reply(r: FSg.Req) -> {FSg.reply(r) == Staging.sp_w_reply(r) : String}:
  match r:
    case FSg.Publish{b}:
      se.verdict(Sg.settle(b))
    case FSg.Meet{es}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sg.Met, ~FSg.put_met, Sg.meet(es), ""), Wr.put_list.go(~Sg.Met, ~Staging.sp_w_met, Sg.meet(es), ""), se.mets(Sg.meet(es), "")) : {Wr.put_list.fin(_) == Wr.put_list(~Sg.Met, ~Staging.sp_w_met, Sg.meet(es), "") : String}
      {==}
    case FSg.Judge{c, l, now, own, inner}:
      se.plan(Sg.judge(c, l, now, own, inner))
    case FSg.Scan{es}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Pick, ~FSg.put_pick, Ls.scan(es), ""), Wr.put_list.go(~Ls.Pick, ~Staging.sp_w_pick, Ls.scan(es), ""), se.picks(Ls.scan(es), "")) : {Wr.put_list.fin(_) == Wr.put_list(~Ls.Pick, ~Staging.sp_w_pick, Ls.scan(es), "") : String}
      {==}
    case FSg.Rows{os}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ls.Row, ~FSg.put_row, Ls.rows(os), ""), Wr.put_list.go(~Ls.Row, ~Staging.sp_w_row, Ls.rows(os), ""), se.rows(Ls.rows(os), "")) : {Wr.put_list.fin(_) == Wr.put_list(~Ls.Row, ~Staging.sp_w_row, Ls.rows(os), "") : String}
      {==}

def Staging.staging_entry_answers(r, h):
  %Equal.sym(Wr.Dec<FSg.Req>, FSg.get_req(Staging.sp_w_req(r, "")), Wr.Got{r, ""}, se.req(r, h)) : {FSg.answer(_) == Staging.sp_w_reply(r) : String}
  se.reply(r)
