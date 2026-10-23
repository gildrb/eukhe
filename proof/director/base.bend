# eukhe: lemmas the proofs of area director share

import Base
import ../../bend/director.bend as Dr
import ../../bend/ffi_director.bend as FDr
import ../../bend/wire.bend as Wr
import ../../laws/director.bend as Director
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ../base/wire.bend as LWire

# The bound
# ---------

def pd.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pd.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def pd.le_zero(q: Nat) -> {Nat.is_le(0n, q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

def pd.le_pred(x: Nat, cap: Nat, h: {Nat.is_le(1n+x, cap) == True{} : Bool}) -> {Nat.is_le(x, cap) == True{} : Bool}:
  match x cap:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LBoolMisc.tree.pt.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pd.le_pred(p, q, h)

def pd.lt_le(x: Nat, cap: Nat, h: {Nat.is_lt(x, cap) == True{} : Bool}) -> {Nat.is_le(1n+x, cap) == True{} : Bool}:
  match x cap:
    case 0n 0n:
      LBoolMisc.tree.pt.absurdF({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      pd.le_zero(q)
    case 1n+p 0n:
      LBoolMisc.tree.pt.absurdF({Nat.is_le(2n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pd.lt_le(p, q, h)

# one more layer above, one fewer below
def pd.shift(+above: Nat, +r: Nat, +cap: Nat, h: {Nat.is_le(Nat.add(above, 1n+r), cap) == True{} : Bool}) -> {Nat.is_le(Nat.add(1n+above, r), cap) == True{} : Bool}:
  %pd.add_succ(above, r) : {Nat.is_le(_, cap) == True{} : Bool}
  h

# the same for the room: the whole stack keeps its length
def pd.shift_lt(+above: Nat, +r: Nat, +cap: Nat, +room: Bool, h: {Nat.is_lt(Nat.add(above, 1n+r), cap) == room : Bool}) -> {Nat.is_lt(Nat.add(1n+above, r), cap) == room : Bool}:
  %pd.add_succ(above, r) : {Nat.is_lt(_, cap) == room : Bool}
  h

# a layer put back on the stack below it
def pd.under_ok(+l: Dr.Layer, d: Dr.Dec, +above: Nat, +cap: Nat, ih: {Nat.is_le(Nat.add(1n+above, List.length(&2, Dr.Layer, Dr.Dec.stack(d))), cap) == True{} : Bool}) -> {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.under(l, d)))), cap) == True{} : Bool}:
  match d:
    case Dr.Dec{o, +s}:
      +r = List.length(&2, Dr.Layer, s)
      %Equal.sym(Nat, Nat.add(above, 1n+r), 1n+Nat.add(above, r), pd.add_succ(above, r)) : {Nat.is_le(_, cap) == True{} : Bool}
      ih

# a Stack with room adds one layer to a stack with room for it
def pd.push_ok(+cap: Nat, +above: Nat, +rest: List<&2, Dr.Layer>, room: Bool, er: {Nat.is_lt(Nat.add(above, 1n+List.length(&2, Dr.Layer, rest)), cap) == room : Bool}, +l: Dr.Layer, +n: Dr.Layer, h: {Nat.is_le(Nat.add(above, 1n+List.length(&2, Dr.Layer, rest)), cap) == True{} : Bool}) -> {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.push.at(room, l, n, rest)))), cap) == True{} : Bool}:
  match room:
    case True{}:
      +r = List.length(&2, Dr.Layer, rest)
      %Equal.sym(Nat, Nat.add(above, 2n+r), 1n+Nat.add(above, 1n+r), pd.add_succ(above, 1n+r)) : {Nat.is_le(_, cap) == True{} : Bool}
      pd.lt_le(Nat.add(above, 1n+r), cap, er)
    case False{}:
      h

# an Again keeps the length
def pd.spend_ok(l: Dr.Layer, +rest: List<&2, Dr.Layer>, +above: Nat, +cap: Nat, h: {Nat.is_le(Nat.add(above, 1n+List.length(&2, Dr.Layer, rest)), cap) == True{} : Bool}) -> {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.spend(l, rest)))), cap) == True{} : Bool}:
  match l:
    case Dr.Layer{k, b}:
      match b:
        case 0n:
          h
        case 1n+c:
          h

# a Stack adds a layer only with room
def pd.pushed_ok(l: Dr.Layer, +n: Dr.Layer, +rest: List<&2, Dr.Layer>, +room: Bool, +above: Nat, +cap: Nat, +h: {Nat.is_le(Nat.add(above, 1n+List.length(&2, Dr.Layer, rest)), cap) == True{} : Bool}, er: {Nat.is_lt(Nat.add(above, 1n+List.length(&2, Dr.Layer, rest)), cap) == room : Bool}) -> {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.push(l, n, rest, room)))), cap) == True{} : Bool}:
  match l:
    case Dr.Layer{+k, b}:
      match b:
        case 0n:
          h
        case 1n+c:
          pd.push_ok(cap, above, rest, room, er, Dr.Layer{k, c}, n, h)

# a Lead stays (as a Defer) or leaves (as a Leave)
def pd.lead_ok(st: Bool, +l: Dr.Layer, d: Dr.Dec, +above: Nat, +cap: Nat, ih: {Nat.is_le(Nat.add(1n+above, List.length(&2, Dr.Layer, Dr.Dec.stack(d))), cap) == True{} : Bool}) -> {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.lead(st, l, d)))), cap) == True{} : Bool}:
  match st:
    case True{}:
      pd.under_ok(l, d, above, cap, ih)
    case False{}:
      pd.le_pred(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(d))), cap, ih)

# a decision under `above` layers keeps above + len(stack) within cap,
# with room telling whether above + len(s) is below cap
def pd.go_bounded(s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +room: Bool, +st: Bool, +cap: Nat, +above: Nat, +h: {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, s)), cap) == True{} : Bool}, +er: {Nat.is_lt(Nat.add(above, List.length(&2, Dr.Layer, s)), cap) == room : Bool}) -> {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.decide.go(s, vs, room, st)))), cap) == True{} : Bool}:
  match s:
    case Nil{}:
      h
    case +l <> +rest:
      match vs:
        case Nil{}:
          pd.under_ok(l, Dr.decide.go(rest, Nil{}, room, st), above, cap, pd.go_bounded(rest, Nil{}, room, st, cap, 1n+above, pd.shift(above, List.length(&2, Dr.Layer, rest), cap, h), pd.shift_lt(above, List.length(&2, Dr.Layer, rest), cap, room, er)))
        case v <> +vr:
          match v:
            case Dr.Defer{}:
              pd.under_ok(l, Dr.decide.go(rest, vr, room, st), above, cap, pd.go_bounded(rest, vr, room, st, cap, 1n+above, pd.shift(above, List.length(&2, Dr.Layer, rest), cap, h), pd.shift_lt(above, List.length(&2, Dr.Layer, rest), cap, room, er)))
            case Dr.Again{}:
              pd.spend_ok(l, rest, above, cap, h)
            case Dr.Yield{}:
              h
            case Dr.Stack{n}:
              pd.pushed_ok(l, n, rest, room, above, cap, h, er)
            case Dr.Leave{}:
              pd.le_pred(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.decide.go(rest, vr, room, st)))), cap, pd.go_bounded(rest, vr, room, st, cap, 1n+above, pd.shift(above, List.length(&2, Dr.Layer, rest), cap, h), pd.shift_lt(above, List.length(&2, Dr.Layer, rest), cap, room, er)))
            case Dr.Abort{}:
              h
            case Dr.Lead{}:
              pd.lead_ok(st, l, Dr.decide.go(rest, vr, room, st), above, cap, pd.go_bounded(rest, vr, room, st, cap, 1n+above, pd.shift(above, List.length(&2, Dr.Layer, rest), cap, h), pd.shift_lt(above, List.length(&2, Dr.Layer, rest), cap, room, er)))

def pd.dir_stack_bounded(+s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat, fits: {Nat.is_le(List.length(&2, Dr.Layer, s), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.decide(s, vs, cap))), cap) == True{} : Bool}:
  pd.go_bounded(s, vs, Nat.is_lt(List.length(&2, Dr.Layer, s), cap), False{}, cap, 0n, fits, {==})

# The rule, verdict by verdict
# ----------------------------

def pd.on_top(+l: Dr.Layer, d: Dr.Dec) -> {Dr.under(l, d) == Director.dir_on_top(l, d) : Dr.Dec}:
  match d:
    case Dr.Dec{o, s}:
      {==}

# Out is decidable: two different outcomes clash
def pd.out_eq(a: Dr.Out, b: Dr.Out) -> Bool:
  match a b:
    case Dr.Cont{} Dr.Cont{}:
      True{}
    case Dr.Hand{} Dr.Hand{}:
      True{}
    case Dr.Failed{} Dr.Failed{}:
      True{}
    case Dr.Cont{} Dr.Hand{}:
      False{}
    case Dr.Cont{} Dr.Failed{}:
      False{}
    case Dr.Hand{} Dr.Cont{}:
      False{}
    case Dr.Hand{} Dr.Failed{}:
      False{}
    case Dr.Failed{} Dr.Cont{}:
      False{}
    case Dr.Failed{} Dr.Hand{}:
      False{}

def pd.out_refl(a: Dr.Out) -> {pd.out_eq(a, a) == True{} : Bool}:
  match a:
    case Dr.Cont{}:
      {==}
    case Dr.Hand{}:
      {==}
    case Dr.Failed{}:
      {==}

def pd.out_eq_of(+a: Dr.Out, -b: Dr.Out, e: {a == b : Dr.Out}) -> {pd.out_eq(a, b) == True{} : Bool}:
  %e : {pd.out_eq(a, _) == True{} : Bool}
  pd.out_refl(a)

def pd.out_absurd(-G: Type, +a: Dr.Out, +b: Dr.Out, e: {a == b : Dr.Out}, ne: {pd.out_eq(a, b) == False{} : Bool}) -> G:
  LBoolMisc.tree.pt.absurdF(G, Equal.trans(Bool, False{}, pd.out_eq(a, b), True{}, Equal.sym(Bool, pd.out_eq(a, b), False{}, ne), pd.out_eq_of(a, b, e)))

# Leads
# -----

# a Lead that leaves is a Leave, whatever the decision does with leads
def pd.leave_as(s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +r: Bool, +x: Bool) -> {Dr.decide.go(s, vs, r, False{}) == Dr.decide.go(s, Director.dir_leads(vs, Dr.Leave{}), r, x) : Dr.Dec}:
  match s:
    case Nil{}:
      {==}
    case +l <> +rest:
      match vs:
        case Nil{}:
          Equal.cong(Dr.Dec, Dr.Dec, d => Dr.under(l, d), Dr.decide.go(rest, Nil{}, r, False{}), Dr.decide.go(rest, Nil{}, r, x), pd.leave_as(rest, Nil{}, r, x))
        case v <> +vr:
          match v:
            case Dr.Defer{}:
              Equal.cong(Dr.Dec, Dr.Dec, d => Dr.under(l, d), Dr.decide.go(rest, vr, r, False{}), Dr.decide.go(rest, Director.dir_leads(vr, Dr.Leave{}), r, x), pd.leave_as(rest, vr, r, x))
            case Dr.Again{}:
              {==}
            case Dr.Yield{}:
              {==}
            case Dr.Stack{n}:
              {==}
            case Dr.Leave{}:
              pd.leave_as(rest, vr, r, x)
            case Dr.Abort{}:
              {==}
            case Dr.Lead{}:
              pd.leave_as(rest, vr, r, x)

# ---- director_entry ----

# The entry of the compiled core (bend/ffi_director.bend): each decoder
# reads back what its encoder wrote, one field at a time (`Equal.cong` of
# the decoder's next step over the field's round trip, joined by
# `Equal.trans`), from the wire laws (LAWS.bend section wire).

def pdf.layer_rt(+l: Dr.Layer, +rest: String, +h: {Director.dir_layer_fits(l) == True{} : Bool}) -> {FDr.get_layer(FDr.put_layer(l, rest)) == Wr.Got{l, rest} : Wr.Dec<Dr.Layer>}:
  match l:
    case Dr.Layer{+k, +b}:
      Equal.trans(Wr.Dec<Dr.Layer>, FDr.get_layer.k(Wr.get_nat(Wr.put_nat(k, Wr.put_nat(b, rest)))), FDr.get_layer.k(Wr.Got{k, Wr.put_nat(b, rest)}), Wr.Got{Dr.Layer{k, b}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Dr.Layer>, d => FDr.get_layer.k(d), Wr.get_nat(Wr.put_nat(k, Wr.put_nat(b, rest))), Wr.Got{k, Wr.put_nat(b, rest)}, Wire.wire_nat_round_trip(k, Wr.put_nat(b, rest), LBoolAnd.wr_and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(b), h))), Equal.cong(Wr.Dec<Nat>, Wr.Dec<Dr.Layer>, d => FDr.get_layer.b(k, d), Wr.get_nat(Wr.put_nat(b, rest)), Wr.Got{b, rest}, Wire.wire_nat_round_trip(b, rest, LBoolAnd.wr_and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(b), h))))

def pdf.verdict_rt(+v: Dr.Verdict, +rest: String, +h: {Director.dir_verdict_fits(v) == True{} : Bool}) -> {FDr.get_verdict(FDr.put_verdict(v, rest)) == Wr.Got{v, rest} : Wr.Dec<Dr.Verdict>}:
  match v:
    case Dr.Defer{}:
      Equal.cong(Wr.Dec<Nat>, Wr.Dec<Dr.Verdict>, d => FDr.get_verdict.go(d), Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==}))
    case Dr.Again{}:
      Equal.cong(Wr.Dec<Nat>, Wr.Dec<Dr.Verdict>, d => FDr.get_verdict.go(d), Wr.get_nat(Wr.put_nat(1n, rest)), Wr.Got{1n, rest}, Wire.wire_nat_round_trip(1n, rest, {==}))
    case Dr.Yield{}:
      Equal.cong(Wr.Dec<Nat>, Wr.Dec<Dr.Verdict>, d => FDr.get_verdict.go(d), Wr.get_nat(Wr.put_nat(2n, rest)), Wr.Got{2n, rest}, Wire.wire_nat_round_trip(2n, rest, {==}))
    case Dr.Leave{}:
      Equal.cong(Wr.Dec<Nat>, Wr.Dec<Dr.Verdict>, d => FDr.get_verdict.go(d), Wr.get_nat(Wr.put_nat(4n, rest)), Wr.Got{4n, rest}, Wire.wire_nat_round_trip(4n, rest, {==}))
    case Dr.Abort{}:
      Equal.cong(Wr.Dec<Nat>, Wr.Dec<Dr.Verdict>, d => FDr.get_verdict.go(d), Wr.get_nat(Wr.put_nat(5n, rest)), Wr.Got{5n, rest}, Wire.wire_nat_round_trip(5n, rest, {==}))
    case Dr.Lead{}:
      Equal.cong(Wr.Dec<Nat>, Wr.Dec<Dr.Verdict>, d => FDr.get_verdict.go(d), Wr.get_nat(Wr.put_nat(6n, rest)), Wr.Got{6n, rest}, Wire.wire_nat_round_trip(6n, rest, {==}))
    case Dr.Stack{+l}:
      Equal.trans(Wr.Dec<Dr.Verdict>, FDr.get_verdict.go(Wr.get_nat(Wr.put_nat(3n, FDr.put_layer(l, rest)))), FDr.get_verdict.go(Wr.Got{3n, FDr.put_layer(l, rest)}), Wr.Got{Dr.Stack{l}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Dr.Verdict>, d => FDr.get_verdict.go(d), Wr.get_nat(Wr.put_nat(3n, FDr.put_layer(l, rest))), Wr.Got{3n, FDr.put_layer(l, rest)}, Wire.wire_nat_round_trip(3n, FDr.put_layer(l, rest), {==})), Equal.cong(Wr.Dec<Dr.Layer>, Wr.Dec<Dr.Verdict>, d => FDr.get_verdict.stack(d), FDr.get_layer(FDr.put_layer(l, rest)), Wr.Got{l, rest}, pdf.layer_rt(l, rest, h)))

def pdf.end_rt(+e: Maybe<&2, Dr.Out>, +rest: String) -> {FDr.get_end(FDr.put_end(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Maybe<&2, Dr.Out>>}:
  match e:
    case None{}:
      Equal.cong(Wr.Dec<Nat>, Wr.Dec<Maybe<&2, Dr.Out>>, d => FDr.get_end.go(d), Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==}))
    case Some{o}:
      match o:
        case Dr.Cont{}:
          Equal.trans(Wr.Dec<Maybe<&2, Dr.Out>>, FDr.get_end.go(Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(0n, rest)))), FDr.get_end.go(Wr.Got{1n, Wr.put_nat(0n, rest)}), Wr.Got{Some{Dr.Cont{}}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Maybe<&2, Dr.Out>>, d => FDr.get_end.go(d), Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(0n, rest))), Wr.Got{1n, Wr.put_nat(0n, rest)}, Wire.wire_nat_round_trip(1n, Wr.put_nat(0n, rest), {==})), Equal.cong(Wr.Dec<Nat>, Wr.Dec<Maybe<&2, Dr.Out>>, d => FDr.get_end.some(d), Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})))
        case Dr.Hand{}:
          Equal.trans(Wr.Dec<Maybe<&2, Dr.Out>>, FDr.get_end.go(Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(1n, rest)))), FDr.get_end.go(Wr.Got{1n, Wr.put_nat(1n, rest)}), Wr.Got{Some{Dr.Hand{}}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Maybe<&2, Dr.Out>>, d => FDr.get_end.go(d), Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(1n, rest))), Wr.Got{1n, Wr.put_nat(1n, rest)}, Wire.wire_nat_round_trip(1n, Wr.put_nat(1n, rest), {==})), Equal.cong(Wr.Dec<Nat>, Wr.Dec<Maybe<&2, Dr.Out>>, d => FDr.get_end.some(d), Wr.get_nat(Wr.put_nat(1n, rest)), Wr.Got{1n, rest}, Wire.wire_nat_round_trip(1n, rest, {==})))
        case Dr.Failed{}:
          Equal.trans(Wr.Dec<Maybe<&2, Dr.Out>>, FDr.get_end.go(Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(2n, rest)))), FDr.get_end.go(Wr.Got{1n, Wr.put_nat(2n, rest)}), Wr.Got{Some{Dr.Failed{}}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Maybe<&2, Dr.Out>>, d => FDr.get_end.go(d), Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(2n, rest))), Wr.Got{1n, Wr.put_nat(2n, rest)}, Wire.wire_nat_round_trip(1n, Wr.put_nat(2n, rest), {==})), Equal.cong(Wr.Dec<Nat>, Wr.Dec<Maybe<&2, Dr.Out>>, d => FDr.get_end.some(d), Wr.get_nat(Wr.put_nat(2n, rest)), Wr.Got{2n, rest}, Wire.wire_nat_round_trip(2n, rest, {==})))

# the items of a list of Dr.Layer, then rest
def pdf.ls.items(xs: List<&2, Dr.Layer>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FDr.put_layer(x, pdf.ls.items(t, rest))

def pdf.ls.put_go(xs: List<&2, Dr.Layer>, -rest: String) -> {Wr.put_list.go(~Dr.Layer, ~FDr.put_layer, xs, rest) == (List.length(&2, Dr.Layer, xs), pdf.ls.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dr.Layer, ~FDr.put_layer, t, rest), (List.length(&2, Dr.Layer, t), pdf.ls.items(t, rest)), pdf.ls.put_go(t, rest)) : {Wr.put_list.step(~Dr.Layer, ~FDr.put_layer, x, _) == (1n+List.length(&2, Dr.Layer, t), FDr.put_layer(x, pdf.ls.items(t, rest))) : Nat & String}
      {==}

# a list of Dr.Layer is its count, then its items
def pdf.ls.put(+xs: List<&2, Dr.Layer>, -rest: String) -> {Wr.put_list(~Dr.Layer, ~FDr.put_layer, xs, rest) == Wr.put_nat(List.length(&2, Dr.Layer, xs), pdf.ls.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dr.Layer, ~FDr.put_layer, xs, rest), (List.length(&2, Dr.Layer, xs), pdf.ls.items(xs, rest)), pdf.ls.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Dr.Layer, xs), pdf.ls.items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def pdf.ls.go_rt(+t: List<&2, Dr.Layer>, +x: Dr.Layer, +rest: String, +hf: {Director.dir_layers_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Dr.Layer, ~FDr.get_layer, List.length(&2, Dr.Layer, t), FDr.get_layer(FDr.put_layer(x, pdf.ls.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dr.Layer>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Dr.Layer>, FDr.get_layer(FDr.put_layer(x, rest)), Wr.Got{x, rest}, pdf.layer_rt(x, rest, LBoolAnd.wr_and_l(Director.dir_layer_fits(x), True{}, hf))) : {Wr.get_list.go(~Dr.Layer, ~FDr.get_layer, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Dr.Layer>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Dr.Layer>, FDr.get_layer(FDr.put_layer(x, FDr.put_layer(y, pdf.ls.items(u, rest)))), Wr.Got{x, FDr.put_layer(y, pdf.ls.items(u, rest))}, pdf.layer_rt(x, FDr.put_layer(y, pdf.ls.items(u, rest)), LBoolAnd.wr_and_l(Director.dir_layer_fits(x), Director.dir_layers_fit(y <> u), hf))) : {Wr.get_list.go(~Dr.Layer, ~FDr.get_layer, 1n+List.length(&2, Dr.Layer, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dr.Layer>>}
      %Equal.sym(Wr.Dec<List<&2, Dr.Layer>>, Wr.get_list.go(~Dr.Layer, ~FDr.get_layer, List.length(&2, Dr.Layer, u), FDr.get_layer(FDr.put_layer(y, pdf.ls.items(u, rest)))), Wr.Got{y <> u, rest}, pdf.ls.go_rt(u, y, rest, LBoolAnd.wr_and_r(Director.dir_layer_fits(x), Director.dir_layers_fit(y <> u), hf))) : {Wr.get_list.cons(Dr.Layer, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dr.Layer>>}
      {==}

# a list of Dr.Layer that fits reads back
def pdf.ls.rt(+xs: List<&2, Dr.Layer>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Layer, xs)), Director.dir_layers_fit(xs)) == True{} : Bool}) -> {Wr.get_list(~Dr.Layer, ~FDr.get_layer, Wr.put_list(~Dr.Layer, ~FDr.put_layer, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Dr.Layer>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LBoolAnd.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Dr.Layer, ~FDr.get_layer, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Dr.Layer>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Dr.Layer, ~FDr.put_layer, x <> t, r), Wr.put_nat(List.length(&2, Dr.Layer, x <> t), pdf.ls.items(x <> t, r)), pdf.ls.put(x <> t, r)) : {Wr.get_list(~Dr.Layer, ~FDr.get_layer, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Dr.Layer>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Dr.Layer, x <> t), pdf.ls.items(x <> t, r))), Wr.Got{List.length(&2, Dr.Layer, x <> t), pdf.ls.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Dr.Layer, x <> t), pdf.ls.items(x <> t, r), LBoolAnd.wr_and_l(LawsBase.wire_fits(List.length(&2, Dr.Layer, x <> t)), Director.dir_layers_fit(x <> t), hh))) : {Wr.get_list.start(~Dr.Layer, ~FDr.get_layer, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Dr.Layer>>}
      pdf.ls.go_rt(t, x, r, LBoolAnd.wr_and_r(LawsBase.wire_fits(List.length(&2, Dr.Layer, x <> t)), Director.dir_layers_fit(x <> t), hh))

# the items of a list of Dr.Verdict, then rest
def pdf.vs.items(xs: List<&2, Dr.Verdict>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FDr.put_verdict(x, pdf.vs.items(t, rest))

def pdf.vs.put_go(xs: List<&2, Dr.Verdict>, -rest: String) -> {Wr.put_list.go(~Dr.Verdict, ~FDr.put_verdict, xs, rest) == (List.length(&2, Dr.Verdict, xs), pdf.vs.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dr.Verdict, ~FDr.put_verdict, t, rest), (List.length(&2, Dr.Verdict, t), pdf.vs.items(t, rest)), pdf.vs.put_go(t, rest)) : {Wr.put_list.step(~Dr.Verdict, ~FDr.put_verdict, x, _) == (1n+List.length(&2, Dr.Verdict, t), FDr.put_verdict(x, pdf.vs.items(t, rest))) : Nat & String}
      {==}

# a list of Dr.Verdict is its count, then its items
def pdf.vs.put(+xs: List<&2, Dr.Verdict>, -rest: String) -> {Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, xs, rest) == Wr.put_nat(List.length(&2, Dr.Verdict, xs), pdf.vs.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dr.Verdict, ~FDr.put_verdict, xs, rest), (List.length(&2, Dr.Verdict, xs), pdf.vs.items(xs, rest)), pdf.vs.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Dr.Verdict, xs), pdf.vs.items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def pdf.vs.go_rt(+t: List<&2, Dr.Verdict>, +x: Dr.Verdict, +rest: String, +hf: {Director.dir_verdicts_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, List.length(&2, Dr.Verdict, t), FDr.get_verdict(FDr.put_verdict(x, pdf.vs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dr.Verdict>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Dr.Verdict>, FDr.get_verdict(FDr.put_verdict(x, rest)), Wr.Got{x, rest}, pdf.verdict_rt(x, rest, LBoolAnd.wr_and_l(Director.dir_verdict_fits(x), True{}, hf))) : {Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Dr.Verdict>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Dr.Verdict>, FDr.get_verdict(FDr.put_verdict(x, FDr.put_verdict(y, pdf.vs.items(u, rest)))), Wr.Got{x, FDr.put_verdict(y, pdf.vs.items(u, rest))}, pdf.verdict_rt(x, FDr.put_verdict(y, pdf.vs.items(u, rest)), LBoolAnd.wr_and_l(Director.dir_verdict_fits(x), Director.dir_verdicts_fit(y <> u), hf))) : {Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, 1n+List.length(&2, Dr.Verdict, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dr.Verdict>>}
      %Equal.sym(Wr.Dec<List<&2, Dr.Verdict>>, Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, List.length(&2, Dr.Verdict, u), FDr.get_verdict(FDr.put_verdict(y, pdf.vs.items(u, rest)))), Wr.Got{y <> u, rest}, pdf.vs.go_rt(u, y, rest, LBoolAnd.wr_and_r(Director.dir_verdict_fits(x), Director.dir_verdicts_fit(y <> u), hf))) : {Wr.get_list.cons(Dr.Verdict, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dr.Verdict>>}
      {==}

# a list of Dr.Verdict that fits reads back
def pdf.vs.rt(+xs: List<&2, Dr.Verdict>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Verdict, xs)), Director.dir_verdicts_fit(xs)) == True{} : Bool}) -> {Wr.get_list(~Dr.Verdict, ~FDr.get_verdict, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Dr.Verdict>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LBoolAnd.wr_and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Dr.Verdict, ~FDr.get_verdict, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Dr.Verdict>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, x <> t, r), Wr.put_nat(List.length(&2, Dr.Verdict, x <> t), pdf.vs.items(x <> t, r)), pdf.vs.put(x <> t, r)) : {Wr.get_list(~Dr.Verdict, ~FDr.get_verdict, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Dr.Verdict>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Dr.Verdict, x <> t), pdf.vs.items(x <> t, r))), Wr.Got{List.length(&2, Dr.Verdict, x <> t), pdf.vs.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Dr.Verdict, x <> t), pdf.vs.items(x <> t, r), LBoolAnd.wr_and_l(LawsBase.wire_fits(List.length(&2, Dr.Verdict, x <> t)), Director.dir_verdicts_fit(x <> t), hh))) : {Wr.get_list.start(~Dr.Verdict, ~FDr.get_verdict, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Dr.Verdict>>}
      pdf.vs.go_rt(t, x, r, LBoolAnd.wr_and_r(LawsBase.wire_fits(List.length(&2, Dr.Verdict, x <> t)), Director.dir_verdicts_fit(x <> t), hh))

def pdf.loop_rt(+l: Dr.Loop, +rest: String, +h: {Director.dir_loop_fits(l) == True{} : Bool}) -> {FDr.get_loop(FDr.put_loop(l, rest)) == Wr.Got{l, rest} : Wr.Dec<Dr.Loop>}:
  match l:
    case Dr.Loop{+n, +s, +e}:
      Equal.trans(Wr.Dec<Dr.Loop>, FDr.get_loop.left(Wr.get_nat(Wr.put_nat(n, Wr.put_list(~Dr.Layer, ~FDr.put_layer, s, FDr.put_end(e, rest))))), FDr.get_loop.left(Wr.Got{n, Wr.put_list(~Dr.Layer, ~FDr.put_layer, s, FDr.put_end(e, rest))}), Wr.Got{Dr.Loop{n, s, e}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Dr.Loop>, d => FDr.get_loop.left(d), Wr.get_nat(Wr.put_nat(n, Wr.put_list(~Dr.Layer, ~FDr.put_layer, s, FDr.put_end(e, rest)))), Wr.Got{n, Wr.put_list(~Dr.Layer, ~FDr.put_layer, s, FDr.put_end(e, rest))}, Wire.wire_nat_round_trip(n, Wr.put_list(~Dr.Layer, ~FDr.put_layer, s, FDr.put_end(e, rest)), LBoolAnd.wr_and_l(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Layer, s)), Director.dir_layers_fit(s)), h))), Equal.trans(Wr.Dec<Dr.Loop>, FDr.get_loop.stack(n, Wr.get_list(~Dr.Layer, ~FDr.get_layer, Wr.put_list(~Dr.Layer, ~FDr.put_layer, s, FDr.put_end(e, rest)))), FDr.get_loop.stack(n, Wr.Got{s, FDr.put_end(e, rest)}), Wr.Got{Dr.Loop{n, s, e}, rest}, Equal.cong(Wr.Dec<List<&2, Dr.Layer>>, Wr.Dec<Dr.Loop>, d => FDr.get_loop.stack(n, d), Wr.get_list(~Dr.Layer, ~FDr.get_layer, Wr.put_list(~Dr.Layer, ~FDr.put_layer, s, FDr.put_end(e, rest))), Wr.Got{s, FDr.put_end(e, rest)}, pdf.ls.rt(s, FDr.put_end(e, rest), LBoolAnd.wr_and_r(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Layer, s)), Director.dir_layers_fit(s)), h))), Equal.cong(Wr.Dec<Maybe<&2, Dr.Out>>, Wr.Dec<Dr.Loop>, d => FDr.get_loop.end(n, s, d), FDr.get_end(FDr.put_end(e, rest)), Wr.Got{e, rest}, pdf.end_rt(e, rest))))

def pdf.req_rt(+q: FDr.Req, +rest: String, +h: {Director.dir_req_fits(q) == True{} : Bool}) -> {FDr.get_req(FDr.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FDr.Req>}:
  match q:
    case FDr.Req{+c, +l, +vs}:
      +h2 = LBoolAnd.wr_and_r(LawsBase.wire_fits(c), Bool.and(Director.dir_loop_fits(l), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Verdict, vs)), Director.dir_verdicts_fit(vs))), h)
      Equal.trans(Wr.Dec<FDr.Req>, FDr.get_req.cap(Wr.get_nat(Wr.put_nat(c, FDr.put_loop(l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest))))), FDr.get_req.cap(Wr.Got{c, FDr.put_loop(l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest))}), Wr.Got{FDr.Req{c, l, vs}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<FDr.Req>, d => FDr.get_req.cap(d), Wr.get_nat(Wr.put_nat(c, FDr.put_loop(l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest)))), Wr.Got{c, FDr.put_loop(l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest))}, Wire.wire_nat_round_trip(c, FDr.put_loop(l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest)), LBoolAnd.wr_and_l(LawsBase.wire_fits(c), Bool.and(Director.dir_loop_fits(l), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Verdict, vs)), Director.dir_verdicts_fit(vs))), h))), Equal.trans(Wr.Dec<FDr.Req>, FDr.get_req.loop(c, FDr.get_loop(FDr.put_loop(l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest)))), FDr.get_req.loop(c, Wr.Got{l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest)}), Wr.Got{FDr.Req{c, l, vs}, rest}, Equal.cong(Wr.Dec<Dr.Loop>, Wr.Dec<FDr.Req>, d => FDr.get_req.loop(c, d), FDr.get_loop(FDr.put_loop(l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest))), Wr.Got{l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest)}, pdf.loop_rt(l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest), LBoolAnd.wr_and_l(Director.dir_loop_fits(l), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Verdict, vs)), Director.dir_verdicts_fit(vs)), h2))), Equal.cong(Wr.Dec<List<&2, Dr.Verdict>>, Wr.Dec<FDr.Req>, d => FDr.get_req.vs(c, l, d), Wr.get_list(~Dr.Verdict, ~FDr.get_verdict, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest)), Wr.Got{vs, rest}, pdf.vs.rt(vs, rest, LBoolAnd.wr_and_r(Director.dir_loop_fits(l), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Verdict, vs)), Director.dir_verdicts_fit(vs)), h2)))))
