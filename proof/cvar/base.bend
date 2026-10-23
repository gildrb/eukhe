# eukhe: lemmas the proofs of area cvar share

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/wire.bend as Wr
import ../../bend/ffi_cvar.bend as FCv
import ../../LAWS.bend as Laws
import ../base.bend as L
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

def pv.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : L.cvar.pv.BD(_, A, Unit)
  Unit{}

def cvar.pv.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pv.absurdF({False{} == True{} : Bool}, h)

def cvar.pv.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pv.absurdF({b == True{} : Bool}, h)

def pv.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Numbers and types
# -----------------

def cvar.pv.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cvar.pv.eq_refl(p)

def pv.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pv.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pv.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pv.eq_true(p, q, h))

def pv.all_typed_snoc(ds: List<&2, Cv.Decl>, +d: Cv.Decl, +h: {Cv.all_typed(ds) == True{} : Bool}, g: {Cv.Decl.typed(d) == True{} : Bool}) -> {Cv.all_typed(List.append(&2, Cv.Decl, ds, [d])) == True{} : Bool}:
  match ds:
    case Nil{}:
      %Equal.sym(Bool, Cv.Decl.typed(d), True{}, g) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case +x <> +r:
      pv.and_t(Cv.Decl.typed(x), Cv.all_typed(List.append(&2, Cv.Decl, r, [d])), cvar.pv.and_l(Cv.Decl.typed(x), Cv.all_typed(r), h), pv.all_typed_snoc(r, d, cvar.pv.and_r(Cv.Decl.typed(x), Cv.all_typed(r), h), g))

def pv.declare_typed(t: Bool, g: Bool, +ds: List<&2, Cv.Decl>, +d: Cv.Decl, eg: {Cv.Decl.typed(d) == g : Bool}, h: {Cv.all_typed(ds) == True{} : Bool}) -> {Cv.all_typed(Cv.declare.at(t, g, ds, d)) == True{} : Bool}:
  match t:
    case True{}:
      h
    case False{}:
      match g:
        case True{}:
          pv.all_typed_snoc(ds, d, h, eg)
        case False{}:
          h

def pv.reg_typed(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, h: {Cv.all_typed(ds) == True{} : Bool}) -> {Cv.all_typed(Cv.registry.go(xs, ds)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +d <> rest:
      pv.reg_typed(rest, Cv.declare(ds, d), pv.declare_typed(Maybe.is_some(&2, Cv.Decl, Cv.find(ds, Cv.Decl.id(d))), Cv.Decl.typed(d), ds, d, {==}, h))

# Layers
# ------

def pv.layer_cons_go(b: Bool, +s: Cv.Bind, +r: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer.go(s <> r, ds, l, x, cur, b) == Cv.layer(r, ds, l, x, Cv.layer.go([s], ds, l, x, cur, b)) : Maybe<&2, Cv.Val>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a layer reads its first set, then the rest
def pv.layer_cons(+s: Cv.Bind, +r: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer(s <> r, ds, l, x, cur) == Cv.layer(r, ds, l, x, Cv.layer([s], ds, l, x, cur)) : Maybe<&2, Cv.Val>}:
  pv.layer_cons_go(Cv.hit.at([s], ds, l, x), s, r, ds, l, x, cur)

# a layer reads its last set on the value of the sets before it
def pv.layer_snoc(ss: List<&2, Cv.Bind>, +s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>) -> {Cv.layer(List.append(&2, Cv.Bind, ss, [s]), ds, l, x, cur) == Cv.layer([s], ds, l, x, Cv.layer(ss, ds, l, x, cur)) : Maybe<&2, Cv.Val>}:
  match ss:
    case Nil{}:
      {==}
    case +h <> +r:
      +c1 = Cv.layer([h], ds, l, x, cur)
      +rs = List.append(&2, Cv.Bind, r, [s])
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(h <> r, ds, l, x, cur), Cv.layer(r, ds, l, x, c1), pv.layer_cons(h, r, ds, l, x, cur)) : {Cv.layer(h <> rs, ds, l, x, cur) == Cv.layer([s], ds, l, x, _) : Maybe<&2, Cv.Val>}
      %Equal.sym(Maybe<&2, Cv.Val>, Cv.layer(h <> rs, ds, l, x, cur), Cv.layer(rs, ds, l, x, c1), pv.layer_cons(h, rs, ds, l, x, cur)) : {_ == Cv.layer([s], ds, l, x, Cv.layer(r, ds, l, x, c1)) : Maybe<&2, Cv.Val>}
      pv.layer_snoc(r, s, ds, l, x, c1)

def pv.layer_hit(+s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>, h: {Cv.hit.at([s], ds, l, x) == True{} : Bool}) -> {Cv.layer([s], ds, l, x, cur) == Some{Cv.Bind.val(s)} : Maybe<&2, Cv.Val>}:
  %Equal.sym(Bool, Cv.hit.at([s], ds, l, x), True{}, h) : {Cv.layer.go([s], ds, l, x, cur, _) == Some{Cv.Bind.val(s)} : Maybe<&2, Cv.Val>}
  {==}

def pv.layer_miss(+s: Cv.Bind, +ds: List<&2, Cv.Decl>, +l: Cv.Layer, +x: Nat, +cur: Maybe<&2, Cv.Val>, h: {Cv.hit.at([s], ds, l, x) == False{} : Bool}) -> {Cv.layer([s], ds, l, x, cur) == cur : Maybe<&2, Cv.Val>}:
  %Equal.sym(Bool, Cv.hit.at([s], ds, l, x), False{}, h) : {Cv.layer.go([s], ds, l, x, cur, _) == cur : Maybe<&2, Cv.Val>}
  {==}

# a valid set of x is valid under the declaration found for x
def pv.valid_m(+ds: List<&2, Cv.Decl>, l: Cv.Layer, +s: Cv.Bind, +x: Nat, m: Maybe<&2, Cv.Decl>, em: {Cv.find(ds, x) == m : Maybe<&2, Cv.Decl>}, ex: {Cv.Bind.id(s) == x : Nat}, h: {Cv.valid(ds, l, s) == True{} : Bool}) -> {Cv.valid.at(m, l, s) == True{} : Bool}:
  %em : {Cv.valid.at(_, l, s) == True{} : Bool}
  %ex : {Cv.valid.at(Cv.find(ds, _), l, s) == True{} : Bool}
  h

# Chains
# ------

def pv.chain_snoc(fam: List<&2, Cv.Ag>, +a: Cv.Ag, +ds: List<&2, Cv.Decl>, +x: Nat, +b: Cv.Val) -> {Cv.chain(List.append(&2, Cv.Ag, fam, [a]), ds, x, b) == Cv.over(ds, a, x, Cv.chain(fam, ds, x, b)) : Cv.Val}:
  match fam:
    case Nil{}:
      {==}
    case +h <> r:
      pv.chain_snoc(r, a, ds, x, Cv.over(ds, h, x, b))

# Aliases
# -------

def pv.body_head(+n: Nat, +b: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> {Cv.body(Cv.Alias{n, b} <> as, n) == b : List<&2, Cv.Cmd>}:
  %cvar.pv.eq_refl(n) : {Cv.body.go(Cv.Alias{n, b} <> as, n, _) == b : List<&2, Cv.Cmd>}
  {==}

# Reversal
# --------

# a plain list reversed onto a plain list is plain
def pv.rev_plain(xs: List<&2, Cv.Cmd>, +o: List<&2, Cv.Cmd>, hx: {Cv.plain(xs) == True{} : Bool}, ho: {Cv.plain(o) == True{} : Bool}) -> {Cv.plain(Cv.rev(xs, o)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ho
    case c <> rest:
      match c:
        case Cv.CSet{+i, +v}:
          pv.rev_plain(rest, Cv.CSet{i, v} <> o, hx, ho)
        case Cv.CToggle{+i}:
          pv.rev_plain(rest, Cv.CToggle{i} <> o, hx, ho)
        case Cv.CRun{n}:
          pv.absurdF({Cv.plain(Cv.rev(Cv.CRun{n} <> rest, o)) == True{} : Bool}, hx)
        case Cv.CGone{n}:
          pv.absurdF({Cv.plain(Cv.rev(Cv.CGone{n} <> rest, o)) == True{} : Bool}, hx)

# an expansion onto a plain accumulator is plain
def pv.go_plain(d: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, acc: Cv.Exp, ha: {Cv.Exp.plain(acc) == True{} : Bool}) -> {Cv.Exp.plain(Cv.expand.go(d, cs, as, acc)) == True{} : Bool}:
  match d:
    case 0n:
      match cs:
        case Nil{}:
          ha
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              match acc:
                case Cv.Flat{out}:
                  pv.go_plain(0n, rest, as, Cv.Flat{Cv.CSet{i, v} <> out}, ha)
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CToggle{i}:
              match acc:
                case Cv.Flat{out}:
                  pv.go_plain(0n, rest, as, Cv.Flat{Cv.CToggle{i} <> out}, ha)
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CRun{n}:
              match acc:
                case Cv.Flat{out}:
                  {==}
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CGone{n}:
              match acc:
                case Cv.Flat{out}:
                  {==}
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
    case 1n+(+e):
      match cs:
        case Nil{}:
          ha
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              match acc:
                case Cv.Flat{out}:
                  pv.go_plain(1n+e, rest, as, Cv.Flat{Cv.CSet{i, v} <> out}, ha)
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CToggle{i}:
              match acc:
                case Cv.Flat{out}:
                  pv.go_plain(1n+e, rest, as, Cv.Flat{Cv.CToggle{i} <> out}, ha)
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CRun{+n}:
              match acc:
                case Cv.Flat{+out}:
                  pv.go_plain(1n+e, rest, as, Cv.expand.go(e, Cv.body(as, n), as, Cv.Flat{out}), pv.go_plain(e, Cv.body(as, n), as, Cv.Flat{out}, ha))
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CGone{n}:
              match acc:
                case Cv.Flat{out}:
                  {==}
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}

# putting the gathered commands in order keeps them plain
def pv.fin_plain(e: Cv.Exp, h: {Cv.Exp.plain(e) == True{} : Bool}) -> {Cv.Exp.plain(Cv.fin(e)) == True{} : Bool}:
  match e:
    case Cv.Flat{out}:
      pv.rev_plain(out, Nil{}, h, {==})
    case Cv.Cycle{m}:
      {==}
    case Cv.Unknown{m}:
      {==}

# an expansion is plain
def pv.expand_plain(+d: Nat, +cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> {Cv.Exp.plain(Cv.fin(Cv.expand.go(d, cs, as, Cv.Flat{Nil{}}))) == True{} : Bool}:
  pv.fin_plain(Cv.expand.go(d, cs, as, Cv.Flat{Nil{}}), pv.go_plain(d, cs, as, Cv.Flat{Nil{}}, {==}))

def pv.cvar_registry_typed(xs: List<&2, Cv.Decl>) -> {Cv.all_typed(Cv.registry(xs)) == True{} : Bool}:
  pv.reg_typed(xs, Nil{}, {==})

# ---- cvar_entry ----

# The entries of the compiled core (bend/ffi_cvar.bend), field by field
# as proof_director's entry.

def pvf.val_rt(+v: Cv.Val, +rest: String, +h: {Laws.cvar_val_fits(v) == True{} : Bool}) -> {FCv.get_val(FCv.put_val(v, rest)) == Wr.Got{v, rest} : Wr.Dec<Cv.Val>}:
  match v:
    case Cv.VNat{+n}:
      Equal.trans(Wr.Dec<Cv.Val>, FCv.get_val.go(Wr.get_nat(Wr.put_nat(0n, Wr.put_nat(n, rest)))), FCv.get_val.go(Wr.Got{0n, Wr.put_nat(n, rest)}), Wr.Got{Cv.VNat{n}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Val>, d => FCv.get_val.go(d), Wr.get_nat(Wr.put_nat(0n, Wr.put_nat(n, rest))), Wr.Got{0n, Wr.put_nat(n, rest)}, Laws.wire_nat_round_trip(0n, Wr.put_nat(n, rest), {==})), Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Val>, d => FCv.get_val.nat(d), Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Laws.wire_nat_round_trip(n, rest, h)))
    case Cv.VBool{+b}:
      Equal.trans(Wr.Dec<Cv.Val>, FCv.get_val.go(Wr.get_nat(Wr.put_nat(1n, Wr.put_bool(b, rest)))), FCv.get_val.go(Wr.Got{1n, Wr.put_bool(b, rest)}), Wr.Got{Cv.VBool{b}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Val>, d => FCv.get_val.go(d), Wr.get_nat(Wr.put_nat(1n, Wr.put_bool(b, rest))), Wr.Got{1n, Wr.put_bool(b, rest)}, Laws.wire_nat_round_trip(1n, Wr.put_bool(b, rest), {==})), Equal.cong(Wr.Dec<Bool>, Wr.Dec<Cv.Val>, d => FCv.get_val.bool(d), Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Laws.wire_bool_round_trip(b, rest)))

def pvf.cmd_rt(+c: Cv.Cmd, +rest: String, +h: {Laws.cvar_cmd_fits(c) == True{} : Bool}) -> {FCv.get_cmd(FCv.put_cmd(c, rest)) == Wr.Got{c, rest} : Wr.Dec<Cv.Cmd>}:
  match c:
    case Cv.CSet{+i, +v}:
      Equal.trans(Wr.Dec<Cv.Cmd>, FCv.get_cmd.go(Wr.get_nat(Wr.put_nat(0n, Wr.put_nat(i, FCv.put_val(v, rest))))), FCv.get_cmd.go(Wr.Got{0n, Wr.put_nat(i, FCv.put_val(v, rest))}), Wr.Got{Cv.CSet{i, v}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Cmd>, d => FCv.get_cmd.go(d), Wr.get_nat(Wr.put_nat(0n, Wr.put_nat(i, FCv.put_val(v, rest)))), Wr.Got{0n, Wr.put_nat(i, FCv.put_val(v, rest))}, Laws.wire_nat_round_trip(0n, Wr.put_nat(i, FCv.put_val(v, rest)), {==})), Equal.trans(Wr.Dec<Cv.Cmd>, FCv.get_cmd.set(Wr.get_nat(Wr.put_nat(i, FCv.put_val(v, rest)))), FCv.get_cmd.set(Wr.Got{i, FCv.put_val(v, rest)}), Wr.Got{Cv.CSet{i, v}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Cmd>, d => FCv.get_cmd.set(d), Wr.get_nat(Wr.put_nat(i, FCv.put_val(v, rest))), Wr.Got{i, FCv.put_val(v, rest)}, Laws.wire_nat_round_trip(i, FCv.put_val(v, rest), L.wr_and_l(Laws.wire_fits(i), Laws.cvar_val_fits(v), h))), Equal.cong(Wr.Dec<Cv.Val>, Wr.Dec<Cv.Cmd>, d => FCv.get_cmd.set.v(i, d), FCv.get_val(FCv.put_val(v, rest)), Wr.Got{v, rest}, pvf.val_rt(v, rest, L.wr_and_r(Laws.wire_fits(i), Laws.cvar_val_fits(v), h)))))
    case Cv.CToggle{+n}:
      Equal.trans(Wr.Dec<Cv.Cmd>, FCv.get_cmd.go(Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(n, rest)))), FCv.get_cmd.go(Wr.Got{1n, Wr.put_nat(n, rest)}), Wr.Got{Cv.CToggle{n}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Cmd>, d => FCv.get_cmd.go(d), Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(n, rest))), Wr.Got{1n, Wr.put_nat(n, rest)}, Laws.wire_nat_round_trip(1n, Wr.put_nat(n, rest), {==})), Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Cmd>, d => FCv.get_cmd.toggle(d), Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Laws.wire_nat_round_trip(n, rest, h)))
    case Cv.CRun{+n}:
      Equal.trans(Wr.Dec<Cv.Cmd>, FCv.get_cmd.go(Wr.get_nat(Wr.put_nat(2n, Wr.put_nat(n, rest)))), FCv.get_cmd.go(Wr.Got{2n, Wr.put_nat(n, rest)}), Wr.Got{Cv.CRun{n}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Cmd>, d => FCv.get_cmd.go(d), Wr.get_nat(Wr.put_nat(2n, Wr.put_nat(n, rest))), Wr.Got{2n, Wr.put_nat(n, rest)}, Laws.wire_nat_round_trip(2n, Wr.put_nat(n, rest), {==})), Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Cmd>, d => FCv.get_cmd.run(d), Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Laws.wire_nat_round_trip(n, rest, h)))
    case Cv.CGone{+n}:
      Equal.trans(Wr.Dec<Cv.Cmd>, FCv.get_cmd.go(Wr.get_nat(Wr.put_nat(3n, Wr.put_nat(n, rest)))), FCv.get_cmd.go(Wr.Got{3n, Wr.put_nat(n, rest)}), Wr.Got{Cv.CGone{n}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Cmd>, d => FCv.get_cmd.go(d), Wr.get_nat(Wr.put_nat(3n, Wr.put_nat(n, rest))), Wr.Got{3n, Wr.put_nat(n, rest)}, Laws.wire_nat_round_trip(3n, Wr.put_nat(n, rest), {==})), Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Cmd>, d => FCv.get_cmd.gone(d), Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Laws.wire_nat_round_trip(n, rest, h)))

# the items of a list of Cv.Cmd, then rest
def pvf.cs.items(xs: List<&2, Cv.Cmd>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FCv.put_cmd(x, pvf.cs.items(t, rest))

def pvf.cs.put_go(xs: List<&2, Cv.Cmd>, -rest: String) -> {Wr.put_list.go(~Cv.Cmd, ~FCv.put_cmd, xs, rest) == (List.length(&2, Cv.Cmd, xs), pvf.cs.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Cv.Cmd, ~FCv.put_cmd, t, rest), (List.length(&2, Cv.Cmd, t), pvf.cs.items(t, rest)), pvf.cs.put_go(t, rest)) : {Wr.put_list.step(~Cv.Cmd, ~FCv.put_cmd, x, _) == (1n+List.length(&2, Cv.Cmd, t), FCv.put_cmd(x, pvf.cs.items(t, rest))) : Nat & String}
      {==}

# a list of Cv.Cmd is its count, then its items
def pvf.cs.put(+xs: List<&2, Cv.Cmd>, -rest: String) -> {Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, xs, rest) == Wr.put_nat(List.length(&2, Cv.Cmd, xs), pvf.cs.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Cv.Cmd, ~FCv.put_cmd, xs, rest), (List.length(&2, Cv.Cmd, xs), pvf.cs.items(xs, rest)), pvf.cs.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Cv.Cmd, xs), pvf.cs.items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def pvf.cs.go_rt(+t: List<&2, Cv.Cmd>, +x: Cv.Cmd, +rest: String, +hf: {Laws.cvar_cmds_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, List.length(&2, Cv.Cmd, t), FCv.get_cmd(FCv.put_cmd(x, pvf.cs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cv.Cmd>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Cv.Cmd>, FCv.get_cmd(FCv.put_cmd(x, rest)), Wr.Got{x, rest}, pvf.cmd_rt(x, rest, L.wr_and_l(Laws.cvar_cmd_fits(x), True{}, hf))) : {Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Cv.Cmd>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Cv.Cmd>, FCv.get_cmd(FCv.put_cmd(x, FCv.put_cmd(y, pvf.cs.items(u, rest)))), Wr.Got{x, FCv.put_cmd(y, pvf.cs.items(u, rest))}, pvf.cmd_rt(x, FCv.put_cmd(y, pvf.cs.items(u, rest)), L.wr_and_l(Laws.cvar_cmd_fits(x), Laws.cvar_cmds_all(y <> u), hf))) : {Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, 1n+List.length(&2, Cv.Cmd, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cv.Cmd>>}
      %Equal.sym(Wr.Dec<List<&2, Cv.Cmd>>, Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, List.length(&2, Cv.Cmd, u), FCv.get_cmd(FCv.put_cmd(y, pvf.cs.items(u, rest)))), Wr.Got{y <> u, rest}, pvf.cs.go_rt(u, y, rest, L.wr_and_r(Laws.cvar_cmd_fits(x), Laws.cvar_cmds_all(y <> u), hf))) : {Wr.get_list.cons(Cv.Cmd, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cv.Cmd>>}
      {==}

# a list of Cv.Cmd that fits reads back
def pvf.cs.rt(+xs: List<&2, Cv.Cmd>, +rest: String, h: {Bool.and(Laws.wire_fits(List.length(&2, Cv.Cmd, xs)), Laws.cvar_cmds_all(xs)) == True{} : Bool}) -> {Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Cv.Cmd>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, L.wr_and_l(Laws.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Cv.Cmd, ~FCv.get_cmd, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Cv.Cmd>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, x <> t, r), Wr.put_nat(List.length(&2, Cv.Cmd, x <> t), pvf.cs.items(x <> t, r)), pvf.cs.put(x <> t, r)) : {Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Cv.Cmd>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Cv.Cmd, x <> t), pvf.cs.items(x <> t, r))), Wr.Got{List.length(&2, Cv.Cmd, x <> t), pvf.cs.items(x <> t, r)}, Laws.wire_nat_round_trip(List.length(&2, Cv.Cmd, x <> t), pvf.cs.items(x <> t, r), L.wr_and_l(Laws.wire_fits(List.length(&2, Cv.Cmd, x <> t)), Laws.cvar_cmds_all(x <> t), hh))) : {Wr.get_list.start(~Cv.Cmd, ~FCv.get_cmd, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Cv.Cmd>>}
      pvf.cs.go_rt(t, x, r, L.wr_and_r(Laws.wire_fits(List.length(&2, Cv.Cmd, x <> t)), Laws.cvar_cmds_all(x <> t), hh))

def pvf.alias_rt(+a: Cv.Alias, +rest: String, +h: {Laws.cvar_alias_fits(a) == True{} : Bool}) -> {FCv.get_alias(FCv.put_alias(a, rest)) == Wr.Got{a, rest} : Wr.Dec<Cv.Alias>}:
  match a:
    case Cv.Alias{+n, +b}:
      Equal.trans(Wr.Dec<Cv.Alias>, FCv.get_alias.name(Wr.get_nat(Wr.put_nat(n, FCv.put_cmds(b, rest)))), FCv.get_alias.name(Wr.Got{n, FCv.put_cmds(b, rest)}), Wr.Got{Cv.Alias{n, b}, rest}, Equal.cong(Wr.Dec<Nat>, Wr.Dec<Cv.Alias>, d => FCv.get_alias.name(d), Wr.get_nat(Wr.put_nat(n, FCv.put_cmds(b, rest))), Wr.Got{n, FCv.put_cmds(b, rest)}, Laws.wire_nat_round_trip(n, FCv.put_cmds(b, rest), L.wr_and_l(Laws.wire_fits(n), Laws.cvar_cmds_fit(b), h))), Equal.cong(Wr.Dec<List<&2, Cv.Cmd>>, Wr.Dec<Cv.Alias>, d => FCv.get_alias.body(n, d), Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, b, rest)), Wr.Got{b, rest}, pvf.cs.rt(b, rest, L.wr_and_r(Laws.wire_fits(n), Laws.cvar_cmds_fit(b), h))))

# the items of a list of Cv.Alias, then rest
def pvf.as.items(xs: List<&2, Cv.Alias>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      FCv.put_alias(x, pvf.as.items(t, rest))

def pvf.as.put_go(xs: List<&2, Cv.Alias>, -rest: String) -> {Wr.put_list.go(~Cv.Alias, ~FCv.put_alias, xs, rest) == (List.length(&2, Cv.Alias, xs), pvf.as.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Cv.Alias, ~FCv.put_alias, t, rest), (List.length(&2, Cv.Alias, t), pvf.as.items(t, rest)), pvf.as.put_go(t, rest)) : {Wr.put_list.step(~Cv.Alias, ~FCv.put_alias, x, _) == (1n+List.length(&2, Cv.Alias, t), FCv.put_alias(x, pvf.as.items(t, rest))) : Nat & String}
      {==}

# a list of Cv.Alias is its count, then its items
def pvf.as.put(+xs: List<&2, Cv.Alias>, -rest: String) -> {Wr.put_list(~Cv.Alias, ~FCv.put_alias, xs, rest) == Wr.put_nat(List.length(&2, Cv.Alias, xs), pvf.as.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Cv.Alias, ~FCv.put_alias, xs, rest), (List.length(&2, Cv.Alias, xs), pvf.as.items(xs, rest)), pvf.as.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Cv.Alias, xs), pvf.as.items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def pvf.as.go_rt(+t: List<&2, Cv.Alias>, +x: Cv.Alias, +rest: String, +hf: {Laws.cvar_aliases_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, List.length(&2, Cv.Alias, t), FCv.get_alias(FCv.put_alias(x, pvf.as.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cv.Alias>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Cv.Alias>, FCv.get_alias(FCv.put_alias(x, rest)), Wr.Got{x, rest}, pvf.alias_rt(x, rest, L.wr_and_l(Laws.cvar_alias_fits(x), True{}, hf))) : {Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Cv.Alias>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<Cv.Alias>, FCv.get_alias(FCv.put_alias(x, FCv.put_alias(y, pvf.as.items(u, rest)))), Wr.Got{x, FCv.put_alias(y, pvf.as.items(u, rest))}, pvf.alias_rt(x, FCv.put_alias(y, pvf.as.items(u, rest)), L.wr_and_l(Laws.cvar_alias_fits(x), Laws.cvar_aliases_all(y <> u), hf))) : {Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, 1n+List.length(&2, Cv.Alias, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cv.Alias>>}
      %Equal.sym(Wr.Dec<List<&2, Cv.Alias>>, Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, List.length(&2, Cv.Alias, u), FCv.get_alias(FCv.put_alias(y, pvf.as.items(u, rest)))), Wr.Got{y <> u, rest}, pvf.as.go_rt(u, y, rest, L.wr_and_r(Laws.cvar_alias_fits(x), Laws.cvar_aliases_all(y <> u), hf))) : {Wr.get_list.cons(Cv.Alias, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cv.Alias>>}
      {==}

# a list of Cv.Alias that fits reads back
def pvf.as.rt(+xs: List<&2, Cv.Alias>, +rest: String, h: {Bool.and(Laws.wire_fits(List.length(&2, Cv.Alias, xs)), Laws.cvar_aliases_all(xs)) == True{} : Bool}) -> {Wr.get_list(~Cv.Alias, ~FCv.get_alias, Wr.put_list(~Cv.Alias, ~FCv.put_alias, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Cv.Alias>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Laws.wire_nat_round_trip(0n, rest, L.wr_and_l(Laws.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~Cv.Alias, ~FCv.get_alias, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Cv.Alias>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~Cv.Alias, ~FCv.put_alias, x <> t, r), Wr.put_nat(List.length(&2, Cv.Alias, x <> t), pvf.as.items(x <> t, r)), pvf.as.put(x <> t, r)) : {Wr.get_list(~Cv.Alias, ~FCv.get_alias, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Cv.Alias>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Cv.Alias, x <> t), pvf.as.items(x <> t, r))), Wr.Got{List.length(&2, Cv.Alias, x <> t), pvf.as.items(x <> t, r)}, Laws.wire_nat_round_trip(List.length(&2, Cv.Alias, x <> t), pvf.as.items(x <> t, r), L.wr_and_l(Laws.wire_fits(List.length(&2, Cv.Alias, x <> t)), Laws.cvar_aliases_all(x <> t), hh))) : {Wr.get_list.start(~Cv.Alias, ~FCv.get_alias, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Cv.Alias>>}
      pvf.as.go_rt(t, x, r, L.wr_and_r(Laws.wire_fits(List.length(&2, Cv.Alias, x <> t)), Laws.cvar_aliases_all(x <> t), hh))

def pvf.xreq_rt(+as: List<&2, Cv.Alias>, +cs: List<&2, Cv.Cmd>, +rest: String, +h: {Bool.and(Laws.cvar_aliases_fit(as), Laws.cvar_cmds_fit(cs)) == True{} : Bool}) -> {FCv.get_xreq(FCv.put_xreq(FCv.Xreq{as, cs}, rest)) == Wr.Got{FCv.Xreq{as, cs}, rest} : Wr.Dec<FCv.Xreq>}:
  Equal.trans(Wr.Dec<FCv.Xreq>, FCv.get_xreq.aliases(Wr.get_list(~Cv.Alias, ~FCv.get_alias, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, FCv.put_cmds(cs, rest)))), FCv.get_xreq.aliases(Wr.Got{as, FCv.put_cmds(cs, rest)}), Wr.Got{FCv.Xreq{as, cs}, rest}, Equal.cong(Wr.Dec<List<&2, Cv.Alias>>, Wr.Dec<FCv.Xreq>, d => FCv.get_xreq.aliases(d), Wr.get_list(~Cv.Alias, ~FCv.get_alias, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, FCv.put_cmds(cs, rest))), Wr.Got{as, FCv.put_cmds(cs, rest)}, pvf.as.rt(as, FCv.put_cmds(cs, rest), L.wr_and_l(Laws.cvar_aliases_fit(as), Laws.cvar_cmds_fit(cs), h))), Equal.cong(Wr.Dec<List<&2, Cv.Cmd>>, Wr.Dec<FCv.Xreq>, d => FCv.get_xreq.cmds(as, d), Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, cs, rest)), Wr.Got{cs, rest}, pvf.cs.rt(cs, rest, L.wr_and_r(Laws.cvar_aliases_fit(as), Laws.cvar_cmds_fit(cs), h))))
