# eukhe: the proof of LAW screen_ffi_run

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/screen.bend as Sc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/screen.bend as Screen
import ../../laws/wire.bend as Wire
import ../base/bool.bend as LBool
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# ---- screen: the entry ----

# The proofs of LAWS.bend section `screen: the entry` (the compiled
# core's entry bend/ffi_screen.bend): every request Rust writes reads
# back (the item, list and record round trips on the wire laws), so the
# entry answers the model's result.

def fs.st_rt(s: Sc.St, +rest: String) -> {FSc.get_st(FSc.put_st(s, rest)) == Wr.Got{s, rest} : Wr.Dec<Sc.St>}:
  match s:
    case Sc.Active{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {FSc.get_st.of(_) == Wr.Got{Sc.Active{}, rest} : Wr.Dec<Sc.St>}
      {==}
    case Sc.Final{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, rest)), Wr.Got{1n, rest}, Wire.wire_nat_round_trip(1n, rest, {==})) : {FSc.get_st.of(_) == Wr.Got{Sc.Final{}, rest} : Wr.Dec<Sc.St>}
      {==}
    case Sc.Comm{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, rest)), Wr.Got{2n, rest}, Wire.wire_nat_round_trip(2n, rest, {==})) : {FSc.get_st.of(_) == Wr.Got{Sc.Comm{}, rest} : Wr.Dec<Sc.St>}
      {==}

def fs.blk_rt(b: Sc.Blk, +rest: String, +h0: {Screen.blk_fits(b) == True{} : Bool}) -> {FSc.get_blk(FSc.put_blk(b, rest)) == Wr.Got{b, rest} : Wr.Dec<Sc.Blk>}:
  match b:
    case Sc.Blk{+i, +s, +l}:
      +h = h0
      Equal.trans(Wr.Dec<Sc.Blk>, FSc.get_blk(FSc.put_blk(Sc.Blk{i, s, l}, rest)), FSc.get_blk.id(Wr.Got{i, FSc.put_st(s, Wr.put_nat(l, rest))}), Wr.Got{Sc.Blk{i, s, l}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Blk>, zq => FSc.get_blk.id(zq), Wr.get_nat(Wr.put_nat(i, FSc.put_st(s, Wr.put_nat(l, rest)))), Wr.Got{i, FSc.put_st(s, Wr.put_nat(l, rest))}, Wire.wire_nat_round_trip(i, FSc.put_st(s, Wr.put_nat(l, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(i), LawsBase.wire_fits(l), h))), Equal.trans(Wr.Dec<Sc.Blk>, FSc.get_blk.id(Wr.Got{i, FSc.put_st(s, Wr.put_nat(l, rest))}), FSc.get_blk.st(i, Wr.Got{s, Wr.put_nat(l, rest)}), Wr.Got{Sc.Blk{i, s, l}, rest}, Equal.cong(Wr.Dec<Sc.St>, Wr.Dec<Sc.Blk>, zq => FSc.get_blk.st(i, zq), FSc.get_st(FSc.put_st(s, Wr.put_nat(l, rest))), Wr.Got{s, Wr.put_nat(l, rest)}, fs.st_rt(s, Wr.put_nat(l, rest))), Equal.trans(Wr.Dec<Sc.Blk>, FSc.get_blk.st(i, Wr.Got{s, Wr.put_nat(l, rest)}), FSc.get_blk.len(i, s, Wr.Got{l, rest}), Wr.Got{Sc.Blk{i, s, l}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Blk>, zq => FSc.get_blk.len(i, s, zq), Wr.get_nat(Wr.put_nat(l, rest)), Wr.Got{l, rest}, Wire.wire_nat_round_trip(l, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(i), LawsBase.wire_fits(l), h))), {==})))

def fs.ev_rt(e: Sc.Ev, +rest: String, +h: {Screen.ev_fits(e) == True{} : Bool}) -> {FSc.get_ev(FSc.put_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Sc.Ev>}:
  match e:
    case Sc.Open{}:
      Equal.trans(Wr.Dec<Sc.Ev>, FSc.get_ev(FSc.put_ev(Sc.Open{}, rest)), FSc.get_ev.of(Wr.Got{0n, rest}), Wr.Got{Sc.Open{}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Ev>, zq => FSc.get_ev.of(zq), Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})), {==})
    case Sc.Grow{+x, +n}:
      Equal.trans(Wr.Dec<Sc.Ev>, FSc.get_ev(FSc.put_ev(Sc.Grow{x, n}, rest)), FSc.get_ev.of(Wr.Got{1n, Wr.put_nat(x, Wr.put_nat(n, rest))}), Wr.Got{Sc.Grow{x, n}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Ev>, zq => FSc.get_ev.of(zq), Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(x, Wr.put_nat(n, rest)))), Wr.Got{1n, Wr.put_nat(x, Wr.put_nat(n, rest))}, Wire.wire_nat_round_trip(1n, Wr.put_nat(x, Wr.put_nat(n, rest)), {==})), Equal.trans(Wr.Dec<Sc.Ev>, FSc.get_ev.of(Wr.Got{1n, Wr.put_nat(x, Wr.put_nat(n, rest))}), FSc.get_ev.x(Wr.Got{x, Wr.put_nat(n, rest)}), Wr.Got{Sc.Grow{x, n}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Ev>, zq => FSc.get_ev.x(zq), Wr.get_nat(Wr.put_nat(x, Wr.put_nat(n, rest))), Wr.Got{x, Wr.put_nat(n, rest)}, Wire.wire_nat_round_trip(x, Wr.put_nat(n, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(x), LawsBase.wire_fits(n), h))), Equal.trans(Wr.Dec<Sc.Ev>, FSc.get_ev.x(Wr.Got{x, Wr.put_nat(n, rest)}), FSc.get_ev.n(x, Wr.Got{n, rest}), Wr.Got{Sc.Grow{x, n}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Ev>, zq => FSc.get_ev.n(x, zq), Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(x), LawsBase.wire_fits(n), h))), {==})))
    case Sc.Fin{+x}:
      Equal.trans(Wr.Dec<Sc.Ev>, FSc.get_ev(FSc.put_ev(Sc.Fin{x}, rest)), FSc.get_ev.of(Wr.Got{2n, Wr.put_nat(x, rest)}), Wr.Got{Sc.Fin{x}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Ev>, zq => FSc.get_ev.of(zq), Wr.get_nat(Wr.put_nat(2n, Wr.put_nat(x, rest))), Wr.Got{2n, Wr.put_nat(x, rest)}, Wire.wire_nat_round_trip(2n, Wr.put_nat(x, rest), {==})), Equal.trans(Wr.Dec<Sc.Ev>, FSc.get_ev.of(Wr.Got{2n, Wr.put_nat(x, rest)}), FSc.get_ev.one(Wr.Got{x, rest}), Wr.Got{Sc.Fin{x}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Ev>, zq => FSc.get_ev.one(zq), Wr.get_nat(Wr.put_nat(x, rest)), Wr.Got{x, rest}, Wire.wire_nat_round_trip(x, rest, h)), {==}))
    case Sc.Flush{}:
      Equal.trans(Wr.Dec<Sc.Ev>, FSc.get_ev(FSc.put_ev(Sc.Flush{}, rest)), FSc.get_ev.of(Wr.Got{3n, rest}), Wr.Got{Sc.Flush{}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Ev>, zq => FSc.get_ev.of(zq), Wr.get_nat(Wr.put_nat(3n, rest)), Wr.Got{3n, rest}, Wire.wire_nat_round_trip(3n, rest, {==})), {==})
    case Sc.Resize{+w}:
      Equal.trans(Wr.Dec<Sc.Ev>, FSc.get_ev(FSc.put_ev(Sc.Resize{w}, rest)), FSc.get_ev.of(Wr.Got{4n, Wr.put_nat(w, rest)}), Wr.Got{Sc.Resize{w}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Ev>, zq => FSc.get_ev.of(zq), Wr.get_nat(Wr.put_nat(4n, Wr.put_nat(w, rest))), Wr.Got{4n, Wr.put_nat(w, rest)}, Wire.wire_nat_round_trip(4n, Wr.put_nat(w, rest), {==})), Equal.trans(Wr.Dec<Sc.Ev>, FSc.get_ev.of(Wr.Got{4n, Wr.put_nat(w, rest)}), FSc.get_ev.w(Wr.Got{w, rest}), Wr.Got{Sc.Resize{w}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Ev>, zq => FSc.get_ev.w(zq), Wr.get_nat(Wr.put_nat(w, rest)), Wr.Got{w, rest}, Wire.wire_nat_round_trip(w, rest, h)), {==}))

def fs.blks.items(xs: List<&2, Sc.Blk>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FSc.put_blk(x, fs.blks.items(t, rest))

def fs.blks.put_go(xs: List<&2, Sc.Blk>, -rest: String) ->
  {Wr.put_list.go(~Sc.Blk, ~FSc.put_blk, xs, rest) == (List.length(&2, Sc.Blk, xs), fs.blks.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Blk, ~FSc.put_blk, t, rest), (List.length(&2, Sc.Blk, t), fs.blks.items(t, rest)), fs.blks.put_go(t, rest)) : {Wr.put_list.step(~Sc.Blk, ~FSc.put_blk, x, _) == (1n+List.length(&2, Sc.Blk, t), FSc.put_blk(x, fs.blks.items(t, rest))) : Nat & String}
      {==}

def fs.blks.put(+xs: List<&2, Sc.Blk>, -rest: String) ->
  {Wr.put_list(~Sc.Blk, ~FSc.put_blk, xs, rest) == Wr.put_nat(List.length(&2, Sc.Blk, xs), fs.blks.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Blk, ~FSc.put_blk, xs, rest), (List.length(&2, Sc.Blk, xs), fs.blks.items(xs, rest)), fs.blks.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Sc.Blk, xs), fs.blks.items(xs, rest)) : String}
  {==}

def fs.blks.go_rt(+t: List<&2, Sc.Blk>, +x: Sc.Blk, +rest: String, +hf: {Screen.blks_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, List.length(&2, Sc.Blk, t), FSc.get_blk(FSc.put_blk(x, fs.blks.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Sc.Blk>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Sc.Blk>, FSc.get_blk(FSc.put_blk(x, rest)), Wr.Got{x, rest}, fs.blk_rt(x, rest, LLogicBool.wr_and_l(Screen.blk_fits(x), True{}, hf))) : {Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Sc.Blk>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Sc.Blk>, FSc.get_blk(FSc.put_blk(x, FSc.put_blk(y, fs.blks.items(u, rest)))), Wr.Got{x, FSc.put_blk(y, fs.blks.items(u, rest))}, fs.blk_rt(x, FSc.put_blk(y, fs.blks.items(u, rest)), LLogicBool.wr_and_l(Screen.blk_fits(x), Screen.blks_fit(y <> u), hf))) : {Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, 1n+List.length(&2, Sc.Blk, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Sc.Blk>>}
      %Equal.sym(Wr.Dec<List<&2, Sc.Blk>>, Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, List.length(&2, Sc.Blk, u), FSc.get_blk(FSc.put_blk(y, fs.blks.items(u, rest)))), Wr.Got{y <> u, rest}, fs.blks.go_rt(u, y, rest, LLogicBool.wr_and_r(Screen.blk_fits(x), Screen.blks_fit(y <> u), hf))) : {Wr.get_list.cons(Sc.Blk, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Sc.Blk>>}
      {==}

def fs.blks.rt(xs: List<&2, Sc.Blk>, +rest: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, Sc.Blk, xs)), Screen.blks_fit(xs)) == True{} : Bool}) ->
  {Wr.get_list(~Sc.Blk, ~FSc.get_blk, Wr.put_list(~Sc.Blk, ~FSc.put_blk, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Sc.Blk>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Wr.get_list.start(~Sc.Blk, ~FSc.get_blk, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Sc.Blk>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(String, Wr.put_list(~Sc.Blk, ~FSc.put_blk, x <> t, rest), Wr.put_nat(List.length(&2, Sc.Blk, x <> t), fs.blks.items(x <> t, rest)), fs.blks.put(x <> t, rest)) : {Wr.get_list(~Sc.Blk, ~FSc.get_blk, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Sc.Blk>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Sc.Blk, x <> t), fs.blks.items(x <> t, rest))), Wr.Got{List.length(&2, Sc.Blk, x <> t), fs.blks.items(x <> t, rest)}, Wire.wire_nat_round_trip(List.length(&2, Sc.Blk, x <> t), fs.blks.items(x <> t, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Sc.Blk, x <> t)), Screen.blks_fit(x <> t), h))) : {Wr.get_list.start(~Sc.Blk, ~FSc.get_blk, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Sc.Blk>>}
      fs.blks.go_rt(t, x, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Sc.Blk, x <> t)), Screen.blks_fit(x <> t), h))

def fs.evs.items(xs: List<&2, Sc.Ev>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FSc.put_ev(x, fs.evs.items(t, rest))

def fs.evs.put_go(xs: List<&2, Sc.Ev>, -rest: String) ->
  {Wr.put_list.go(~Sc.Ev, ~FSc.put_ev, xs, rest) == (List.length(&2, Sc.Ev, xs), fs.evs.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Ev, ~FSc.put_ev, t, rest), (List.length(&2, Sc.Ev, t), fs.evs.items(t, rest)), fs.evs.put_go(t, rest)) : {Wr.put_list.step(~Sc.Ev, ~FSc.put_ev, x, _) == (1n+List.length(&2, Sc.Ev, t), FSc.put_ev(x, fs.evs.items(t, rest))) : Nat & String}
      {==}

def fs.evs.put(+xs: List<&2, Sc.Ev>, -rest: String) ->
  {Wr.put_list(~Sc.Ev, ~FSc.put_ev, xs, rest) == Wr.put_nat(List.length(&2, Sc.Ev, xs), fs.evs.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Ev, ~FSc.put_ev, xs, rest), (List.length(&2, Sc.Ev, xs), fs.evs.items(xs, rest)), fs.evs.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Sc.Ev, xs), fs.evs.items(xs, rest)) : String}
  {==}

def fs.evs.go_rt(+t: List<&2, Sc.Ev>, +x: Sc.Ev, +rest: String, +hf: {Screen.evs_fit(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, List.length(&2, Sc.Ev, t), FSc.get_ev(FSc.put_ev(x, fs.evs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Sc.Ev>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Sc.Ev>, FSc.get_ev(FSc.put_ev(x, rest)), Wr.Got{x, rest}, fs.ev_rt(x, rest, LLogicBool.wr_and_l(Screen.ev_fits(x), True{}, hf))) : {Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Sc.Ev>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Sc.Ev>, FSc.get_ev(FSc.put_ev(x, FSc.put_ev(y, fs.evs.items(u, rest)))), Wr.Got{x, FSc.put_ev(y, fs.evs.items(u, rest))}, fs.ev_rt(x, FSc.put_ev(y, fs.evs.items(u, rest)), LLogicBool.wr_and_l(Screen.ev_fits(x), Screen.evs_fit(y <> u), hf))) : {Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, 1n+List.length(&2, Sc.Ev, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Sc.Ev>>}
      %Equal.sym(Wr.Dec<List<&2, Sc.Ev>>, Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, List.length(&2, Sc.Ev, u), FSc.get_ev(FSc.put_ev(y, fs.evs.items(u, rest)))), Wr.Got{y <> u, rest}, fs.evs.go_rt(u, y, rest, LLogicBool.wr_and_r(Screen.ev_fits(x), Screen.evs_fit(y <> u), hf))) : {Wr.get_list.cons(Sc.Ev, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Sc.Ev>>}
      {==}

def fs.evs.rt(xs: List<&2, Sc.Ev>, +rest: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, Sc.Ev, xs)), Screen.evs_fit(xs)) == True{} : Bool}) ->
  {Wr.get_list(~Sc.Ev, ~FSc.get_ev, Wr.put_list(~Sc.Ev, ~FSc.put_ev, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Sc.Ev>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Wr.get_list.start(~Sc.Ev, ~FSc.get_ev, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Sc.Ev>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(String, Wr.put_list(~Sc.Ev, ~FSc.put_ev, x <> t, rest), Wr.put_nat(List.length(&2, Sc.Ev, x <> t), fs.evs.items(x <> t, rest)), fs.evs.put(x <> t, rest)) : {Wr.get_list(~Sc.Ev, ~FSc.get_ev, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Sc.Ev>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Sc.Ev, x <> t), fs.evs.items(x <> t, rest))), Wr.Got{List.length(&2, Sc.Ev, x <> t), fs.evs.items(x <> t, rest)}, Wire.wire_nat_round_trip(List.length(&2, Sc.Ev, x <> t), fs.evs.items(x <> t, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Sc.Ev, x <> t)), Screen.evs_fit(x <> t), h))) : {Wr.get_list.start(~Sc.Ev, ~FSc.get_ev, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Sc.Ev>>}
      fs.evs.go_rt(t, x, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Sc.Ev, x <> t)), Screen.evs_fit(x <> t), h))

def fs.tx_rt(t: Sc.Tx, +rest: String, +h: {Screen.tx_fits(t) == True{} : Bool}) -> {FSc.get_tx(FSc.put_tx(t, rest)) == Wr.Got{t, rest} : Wr.Dec<Sc.Tx>}:
  match t:
    case Sc.Tx{+bs, +n, +w}:
      +a = LawsBase.wire_fits(List.length(&2, Sc.Blk, bs))
      +b = Screen.blks_fit(bs)
      +c = LawsBase.wire_fits(n)
      +d = LawsBase.wire_fits(w)
      +h2 = LLogicBool.wr_and_r(a, Bool.and(b, Bool.and(c, d)), h)
      +h3 = LLogicBool.wr_and_r(b, Bool.and(c, d), h2)
      +hl = LBool.wn_and_intro(a, b, LLogicBool.wr_and_l(a, Bool.and(b, Bool.and(c, d)), h), LLogicBool.wr_and_l(b, Bool.and(c, d), h2))
      Equal.trans(Wr.Dec<Sc.Tx>, FSc.get_tx(FSc.put_tx(Sc.Tx{bs, n, w}, rest)), FSc.get_tx.bs(Wr.Got{bs, Wr.put_nat(n, Wr.put_nat(w, rest))}), Wr.Got{Sc.Tx{bs, n, w}, rest}, Equal.cong(Wr.Dec<List<&2, Sc.Blk>>, Wr.Dec<Sc.Tx>, zq => FSc.get_tx.bs(zq), Wr.get_list(~Sc.Blk, ~FSc.get_blk, Wr.put_list(~Sc.Blk, ~FSc.put_blk, bs, Wr.put_nat(n, Wr.put_nat(w, rest)))), Wr.Got{bs, Wr.put_nat(n, Wr.put_nat(w, rest))}, fs.blks.rt(bs, Wr.put_nat(n, Wr.put_nat(w, rest)), hl)), Equal.trans(Wr.Dec<Sc.Tx>, FSc.get_tx.bs(Wr.Got{bs, Wr.put_nat(n, Wr.put_nat(w, rest))}), FSc.get_tx.n(bs, Wr.Got{n, Wr.put_nat(w, rest)}), Wr.Got{Sc.Tx{bs, n, w}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Tx>, zq => FSc.get_tx.n(bs, zq), Wr.get_nat(Wr.put_nat(n, Wr.put_nat(w, rest))), Wr.Got{n, Wr.put_nat(w, rest)}, Wire.wire_nat_round_trip(n, Wr.put_nat(w, rest), LLogicBool.wr_and_l(c, d, h3))), Equal.trans(Wr.Dec<Sc.Tx>, FSc.get_tx.n(bs, Wr.Got{n, Wr.put_nat(w, rest)}), FSc.get_tx.w(bs, n, Wr.Got{w, rest}), Wr.Got{Sc.Tx{bs, n, w}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Sc.Tx>, zq => FSc.get_tx.w(bs, n, zq), Wr.get_nat(Wr.put_nat(w, rest)), Wr.Got{w, rest}, Wire.wire_nat_round_trip(w, rest, LLogicBool.wr_and_r(c, d, h3))), {==})))

def fs.rt_run(+t: Sc.Tx, +es: List<&2, Sc.Ev>, +ft: {Screen.tx_fits(t) == True{} : Bool}, +fe: {Bool.and(LawsBase.wire_fits(List.length(&2, Sc.Ev, es)), Screen.evs_fit(es)) == True{} : Bool}) -> {FSc.get_req(FSc.put_req(FSc.ReqRun{t, es}, "")) == Wr.Got{FSc.ReqRun{t, es}, ""} : Wr.Dec<FSc.Req>}:
  Equal.trans(Wr.Dec<FSc.Req>, FSc.get_req(FSc.put_req(FSc.ReqRun{t, es}, "")), FSc.get_req.of(Wr.Got{0n, FSc.put_tx(t, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, ""))}), Wr.Got{FSc.ReqRun{t, es}, ""}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<FSc.Req>, zq => FSc.get_req.of(zq), Wr.get_nat(Wr.put_nat(0n, FSc.put_tx(t, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, "")))), Wr.Got{0n, FSc.put_tx(t, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, ""))}, Wire.wire_nat_round_trip(0n, FSc.put_tx(t, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, "")), {==})), Equal.trans(Wr.Dec<FSc.Req>, FSc.get_req.of(Wr.Got{0n, FSc.put_tx(t, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, ""))}), FSc.get_run(Wr.Got{t, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, "")}), Wr.Got{FSc.ReqRun{t, es}, ""}, Equal.cong(Wr.Dec<Sc.Tx>, Wr.Dec<FSc.Req>, zq => FSc.get_run(zq), FSc.get_tx(FSc.put_tx(t, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, ""))), Wr.Got{t, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, "")}, fs.tx_rt(t, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, ""), ft)), Equal.trans(Wr.Dec<FSc.Req>, FSc.get_run(Wr.Got{t, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, "")}), FSc.get_run.es(t, Wr.Got{es, ""}), Wr.Got{FSc.ReqRun{t, es}, ""}, Equal.cong(Wr.Dec<List<&2, Sc.Ev>>, Wr.Dec<FSc.Req>, zq => FSc.get_run.es(t, zq), Wr.get_list(~Sc.Ev, ~FSc.get_ev, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, "")), Wr.Got{es, ""}, fs.evs.rt(es, "", fe)), {==})))

def Screen.screen_ffi_run(t, es, ft, fe):
  Equal.trans(String, FSc.ffi(FSc.put_req(FSc.ReqRun{t, es}, "")), FSc.ffi.of(Wr.Got{FSc.ReqRun{t, es}, ""}), FSc.put_tx(Sc.run(es, t), ""), Equal.cong(Wr.Dec<FSc.Req>, String, FSc.ffi.of, FSc.get_req(FSc.put_req(FSc.ReqRun{t, es}, "")), Wr.Got{FSc.ReqRun{t, es}, ""}, fs.rt_run(t, es, ft, fe)), {==})
