# eukhe: the proof of LAW seen_entry_refines

import Base
import ../../bend/doc_seen.bend as Ds
import ../../bend/wire.bend as Wr
import ../../bend/ffi_doc_seen.bend as Fds
import ../../LAWS.bend as Laws
import ../base.bend as L

# ---- documents codecs ----

# The proofs of the codec laws of LAWS.bend section documents (F11, F4):
# the entries bend/ffi_doc_seen.bend and bend/ffi_doc_lines.bend read
# back every request whose numbers fit the wire (lemmas fsv_, fln_, on
# the wire laws and wr_and_l / wr_and_r of section wire).

# ==== seen codec ====

# a seen run reads back
def fsv_iv(iv: Ds.Iv, +rest: String, h: {Laws.seen.IvFit(iv) == True{} : Bool}) -> {Fds.get_iv(Fds.put_iv(iv, rest)) == Wr.Got{iv, rest} : Wr.Dec<Ds.Iv>}:
  match iv:
    case Ds.Iv{+lo, +hi}:
      +hh = h
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(lo, Wr.put_nat(hi, rest))), Wr.Got{lo, Wr.put_nat(hi, rest)}, Laws.wire_nat_round_trip(lo, Wr.put_nat(hi, rest), L.wr_and_l(Laws.wire_fits(lo), Laws.wire_fits(hi), hh))) : {Fds.get_iv.lo(_) == Wr.Got{Ds.Iv{lo, hi}, rest} : Wr.Dec<Ds.Iv>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(hi, rest)), Wr.Got{hi, rest}, Laws.wire_nat_round_trip(hi, rest, L.wr_and_r(Laws.wire_fits(lo), Laws.wire_fits(hi), hh))) : {Fds.get_iv.hi(lo, _) == Wr.Got{Ds.Iv{lo, hi}, rest} : Wr.Dec<Ds.Iv>}
      {==}

# an anchor reads back
def fsv_at(a: Ds.At, +rest: String, h: {Laws.seen.AtFit(a) == True{} : Bool}) -> {Fds.get_at(Fds.put_at(a, rest)) == Wr.Got{a, rest} : Wr.Dec<Ds.At>}:
  match a:
    case Ds.At{+n, w}:
      match w:
        case None{}:
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, Wr.put_nat(0n, rest))), Wr.Got{n, Wr.put_nat(0n, rest)}, Laws.wire_nat_round_trip(n, Wr.put_nat(0n, rest), h)) : {Fds.get_at.n(_) == Wr.Got{Ds.At{n, None{}}, rest} : Wr.Dec<Ds.At>}
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, {==})) : {Fds.get_at.w(n, Fds.get_mnat.tag(_)) == Wr.Got{Ds.At{n, None{}}, rest} : Wr.Dec<Ds.At>}
          {==}
        case Some{+x}:
          +hh = h
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, Wr.put_nat(1n, Wr.put_nat(x, rest)))), Wr.Got{n, Wr.put_nat(1n, Wr.put_nat(x, rest))}, Laws.wire_nat_round_trip(n, Wr.put_nat(1n, Wr.put_nat(x, rest)), L.wr_and_l(Laws.wire_fits(n), Laws.wire_fits(x), hh))) : {Fds.get_at.n(_) == Wr.Got{Ds.At{n, Some{x}}, rest} : Wr.Dec<Ds.At>}
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(x, rest))), Wr.Got{1n, Wr.put_nat(x, rest)}, Laws.wire_nat_round_trip(1n, Wr.put_nat(x, rest), {==})) : {Fds.get_at.w(n, Fds.get_mnat.tag(_)) == Wr.Got{Ds.At{n, Some{x}}, rest} : Wr.Dec<Ds.At>}
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(x, rest)), Wr.Got{x, rest}, Laws.wire_nat_round_trip(x, rest, L.wr_and_r(Laws.wire_fits(n), Laws.wire_fits(x), hh))) : {Fds.get_at.w(n, Fds.get_mnat.some(_)) == Wr.Got{Ds.At{n, Some{x}}, rest} : Wr.Dec<Ds.At>}
          {==}

# Lists of seen runs
# ------------------

def fsv_ivs_items(xs: List<&2, Ds.Iv>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Fds.put_iv(x, fsv_ivs_items(t, rest))

def fsv_ivs_go(xs: List<&2, Ds.Iv>, -rest: String) -> {Wr.put_list.go(~Ds.Iv, ~Fds.put_iv, xs, rest) == (List.length(&2, Ds.Iv, xs), fsv_ivs_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ds.Iv, ~Fds.put_iv, t, rest), (List.length(&2, Ds.Iv, t), fsv_ivs_items(t, rest)), fsv_ivs_go(t, rest)) : {Wr.put_list.step(~Ds.Iv, ~Fds.put_iv, x, _) == (1n+List.length(&2, Ds.Iv, t), Fds.put_iv(x, fsv_ivs_items(t, rest))) : Nat & String}
      {==}

def fsv_ivs_put(+xs: List<&2, Ds.Iv>, -rest: String) -> {Wr.put_list(~Ds.Iv, ~Fds.put_iv, xs, rest) == Wr.put_nat(List.length(&2, Ds.Iv, xs), fsv_ivs_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Ds.Iv, ~Fds.put_iv, xs, rest), (List.length(&2, Ds.Iv, xs), fsv_ivs_items(xs, rest)), fsv_ivs_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Ds.Iv, xs), fsv_ivs_items(xs, rest)) : String}
  {==}

def fsv_ivs_loop(+t: List<&2, Ds.Iv>, +x: Ds.Iv, +rest: String, +hf: {Laws.seen.IvsFit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, List.length(&2, Ds.Iv, t), Fds.get_iv(Fds.put_iv(x, fsv_ivs_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ds.Iv>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Ds.Iv>, Fds.get_iv(Fds.put_iv(x, rest)), Wr.Got{x, rest}, fsv_iv(x, rest, L.wr_and_l(Laws.seen.IvFit(x), True{}, hf))) : {Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Ds.Iv>>}
      {==}
    case Con{+y, +u}:
      +r2 = Fds.put_iv(y, fsv_ivs_items(u, rest))
      %Equal.sym(Wr.Dec<Ds.Iv>, Fds.get_iv(Fds.put_iv(x, r2)), Wr.Got{x, r2}, fsv_iv(x, r2, L.wr_and_l(Laws.seen.IvFit(x), Laws.seen.IvsFit(y <> u), hf))) : {Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, 1n+List.length(&2, Ds.Iv, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ds.Iv>>}
      %Equal.sym(Wr.Dec<List<&2, Ds.Iv>>, Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, List.length(&2, Ds.Iv, u), Fds.get_iv(r2)), Wr.Got{y <> u, rest}, fsv_ivs_loop(u, y, rest, L.wr_and_r(Laws.seen.IvFit(x), Laws.seen.IvsFit(y <> u), hf))) : {Wr.get_list.cons(Ds.Iv, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ds.Iv>>}
      {==}

# a list of seen runs reads back
def fsv_ivs(+xs: List<&2, Ds.Iv>, +rest: String, hl: {Laws.wire_fits(List.length(&2, Ds.Iv, xs)) == True{} : Bool}, hi: {Laws.seen.IvsFit(xs) == True{} : Bool}) -> {Wr.get_list(~Ds.Iv, ~Fds.get_iv, Wr.put_list(~Ds.Iv, ~Fds.put_iv, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Ds.Iv>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, hl)) : {Wr.get_list.start(~Ds.Iv, ~Fds.get_iv, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Ds.Iv>>}
      {==}
    case Con{+x, +t}:
      +items = fsv_ivs_items(x <> t, rest)
      %Equal.sym(String, Wr.put_list(~Ds.Iv, ~Fds.put_iv, x <> t, rest), Wr.put_nat(List.length(&2, Ds.Iv, x <> t), items), fsv_ivs_put(x <> t, rest)) : {Wr.get_list(~Ds.Iv, ~Fds.get_iv, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ds.Iv>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Ds.Iv, x <> t), items)), Wr.Got{List.length(&2, Ds.Iv, x <> t), items}, Laws.wire_nat_round_trip(List.length(&2, Ds.Iv, x <> t), items, hl)) : {Wr.get_list.start(~Ds.Iv, ~Fds.get_iv, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ds.Iv>>}
      fsv_ivs_loop(t, x, rest, hi)

# Lists of anchors
# ----------------

def fsv_ats_items(xs: List<&2, Ds.At>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Fds.put_at(x, fsv_ats_items(t, rest))

def fsv_ats_go(xs: List<&2, Ds.At>, -rest: String) -> {Wr.put_list.go(~Ds.At, ~Fds.put_at, xs, rest) == (List.length(&2, Ds.At, xs), fsv_ats_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ds.At, ~Fds.put_at, t, rest), (List.length(&2, Ds.At, t), fsv_ats_items(t, rest)), fsv_ats_go(t, rest)) : {Wr.put_list.step(~Ds.At, ~Fds.put_at, x, _) == (1n+List.length(&2, Ds.At, t), Fds.put_at(x, fsv_ats_items(t, rest))) : Nat & String}
      {==}

def fsv_ats_put(+xs: List<&2, Ds.At>, -rest: String) -> {Wr.put_list(~Ds.At, ~Fds.put_at, xs, rest) == Wr.put_nat(List.length(&2, Ds.At, xs), fsv_ats_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Ds.At, ~Fds.put_at, xs, rest), (List.length(&2, Ds.At, xs), fsv_ats_items(xs, rest)), fsv_ats_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Ds.At, xs), fsv_ats_items(xs, rest)) : String}
  {==}

def fsv_ats_loop(+t: List<&2, Ds.At>, +x: Ds.At, +rest: String, +hf: {Laws.seen.AtsFit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Ds.At, ~Fds.get_at, List.length(&2, Ds.At, t), Fds.get_at(Fds.put_at(x, fsv_ats_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ds.At>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Ds.At>, Fds.get_at(Fds.put_at(x, rest)), Wr.Got{x, rest}, fsv_at(x, rest, L.wr_and_l(Laws.seen.AtFit(x), True{}, hf))) : {Wr.get_list.go(~Ds.At, ~Fds.get_at, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Ds.At>>}
      {==}
    case Con{+y, +u}:
      +r2 = Fds.put_at(y, fsv_ats_items(u, rest))
      %Equal.sym(Wr.Dec<Ds.At>, Fds.get_at(Fds.put_at(x, r2)), Wr.Got{x, r2}, fsv_at(x, r2, L.wr_and_l(Laws.seen.AtFit(x), Laws.seen.AtsFit(y <> u), hf))) : {Wr.get_list.go(~Ds.At, ~Fds.get_at, 1n+List.length(&2, Ds.At, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ds.At>>}
      %Equal.sym(Wr.Dec<List<&2, Ds.At>>, Wr.get_list.go(~Ds.At, ~Fds.get_at, List.length(&2, Ds.At, u), Fds.get_at(r2)), Wr.Got{y <> u, rest}, fsv_ats_loop(u, y, rest, L.wr_and_r(Laws.seen.AtFit(x), Laws.seen.AtsFit(y <> u), hf))) : {Wr.get_list.cons(Ds.At, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Ds.At>>}
      {==}

# a list of anchors reads back
def fsv_ats(+xs: List<&2, Ds.At>, +rest: String, hl: {Laws.wire_fits(List.length(&2, Ds.At, xs)) == True{} : Bool}, hi: {Laws.seen.AtsFit(xs) == True{} : Bool}) -> {Wr.get_list(~Ds.At, ~Fds.get_at, Wr.put_list(~Ds.At, ~Fds.put_at, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Ds.At>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, hl)) : {Wr.get_list.start(~Ds.At, ~Fds.get_at, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Ds.At>>}
      {==}
    case Con{+x, +t}:
      +items = fsv_ats_items(x <> t, rest)
      %Equal.sym(String, Wr.put_list(~Ds.At, ~Fds.put_at, x <> t, rest), Wr.put_nat(List.length(&2, Ds.At, x <> t), items), fsv_ats_put(x <> t, rest)) : {Wr.get_list(~Ds.At, ~Fds.get_at, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ds.At>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Ds.At, x <> t), items)), Wr.Got{List.length(&2, Ds.At, x <> t), items}, Laws.wire_nat_round_trip(List.length(&2, Ds.At, x <> t), items, hl)) : {Wr.get_list.start(~Ds.At, ~Fds.get_at, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Ds.At>>}
      fsv_ats_loop(t, x, rest, hi)

# the entry reads a request back and answers the model's verdict
def fsv_entry(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, +h: {Laws.seen.WireFits(seen, ats) == True{} : Bool}) -> {Fds.ffi(Fds.put_req(seen, ats, "")) == Fds.put_check(Ds.check(seen, ats), "") : String}:
  +hs = L.wr_and_l(Bool.and(Laws.wire_fits(List.length(&2, Ds.Iv, seen)), Laws.seen.IvsFit(seen)), Bool.and(Laws.wire_fits(List.length(&2, Ds.At, ats)), Laws.seen.AtsFit(ats)), h)
  +ha = L.wr_and_r(Bool.and(Laws.wire_fits(List.length(&2, Ds.Iv, seen)), Laws.seen.IvsFit(seen)), Bool.and(Laws.wire_fits(List.length(&2, Ds.At, ats)), Laws.seen.AtsFit(ats)), h)
  +tail = Wr.put_list(~Ds.At, ~Fds.put_at, ats, "")
  %Equal.sym(Wr.Dec<List<&2, Ds.Iv>>, Wr.get_list(~Ds.Iv, ~Fds.get_iv, Wr.put_list(~Ds.Iv, ~Fds.put_iv, seen, tail)), Wr.Got{seen, tail}, fsv_ivs(seen, tail, L.wr_and_l(Laws.wire_fits(List.length(&2, Ds.Iv, seen)), Laws.seen.IvsFit(seen), hs), L.wr_and_r(Laws.wire_fits(List.length(&2, Ds.Iv, seen)), Laws.seen.IvsFit(seen), hs))) : {Fds.run.seen(_) == Fds.put_check(Ds.check(seen, ats), "") : String}
  %Equal.sym(Wr.Dec<List<&2, Ds.At>>, Wr.get_list(~Ds.At, ~Fds.get_at, tail), Wr.Got{ats, ""}, fsv_ats(ats, "", L.wr_and_l(Laws.wire_fits(List.length(&2, Ds.At, ats)), Laws.seen.AtsFit(ats), ha), L.wr_and_r(Laws.wire_fits(List.length(&2, Ds.At, ats)), Laws.seen.AtsFit(ats), ha))) : {Fds.run.ats(seen, _) == Fds.put_check(Ds.check(seen, ats), "") : String}
  {==}

def Laws.seen_entry_refines(seen, ats, h):
  fsv_entry(seen, ats, h)
