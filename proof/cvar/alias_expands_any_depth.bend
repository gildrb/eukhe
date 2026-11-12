# eukhe: the proof of LAW alias_expands_any_depth
#
# PROOF, in three parts, all by induction on the fuel, then the commands:
# (1) the laws' unfolding with fuel d, when it ends with e, is what the
#     code's walk with d levels of nesting builds onto any accumulator
#     (dp.align; the code's body lookup is the laws', dp.body);
# (2) an unfolding that ends with fuel f ends, the same, with more fuel
#     (dp.mono, dp.mono_add);
# (3) the pigeonhole: an unfolding that ends with any fuel f ends, the
#     same, with fuel 1 + (the entries of the table whose name is on no
#     alias of the path) (dp.bound): a run of n off the path enters a body
#     with n on the path, which drops the entries named n, at least one
#     when n has an alias (dp.split, dp.has); a missing alias needs no
#     fuel (dp.gone). With the empty path that count is the table's
#     length (dp.cnt_nil), the code's own depth 1 + length, so (1) at that
#     depth gives the code's expansion, and fin reads it in order
#     (dp.fin_J).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/entry.bend as CvarEntry
import ./base.bend as LA
import ./base/expand.bend as LE
import ./alias_runs_body.bend as PRB
import ./alias_expands_in_order.bend as PIO
import ../base/nat.bend as LNat

# The body lookup
# ---------------

def dp.body_go(as: List<&2, Cv.Alias>, +n: Nat, hit: Bool, eh: {Cv.name.at(as, n) == hit : Bool}) -> {Cv.body.go(as, n, hit) == CvarEntry.spec_body.of(CvarEntry.spec_alias(as, n), n) : List<&2, Cv.Cmd>}:
  match as:
    case Nil{}:
      {==}
    case Cv.Alias{+m, +d} <> +t:
      match hit:
        case True{}:
          %Equal.sym(Bool, Nat.is_eq(m, n), True{}, eh) : {d == CvarEntry.spec_body.of(CvarEntry.spec_alias.pick(_, d, CvarEntry.spec_alias(t, n)), n) : List<&2, Cv.Cmd>}
          {==}
        case False{}:
          %Equal.sym(Bool, Nat.is_eq(m, n), False{}, eh) : {Cv.body.go(t, n, Cv.name.at(t, n)) == CvarEntry.spec_body.of(CvarEntry.spec_alias.pick(_, d, CvarEntry.spec_alias(t, n)), n) : List<&2, Cv.Cmd>}
          dp.body_go(t, n, Cv.name.at(t, n), {==})

# the code's body of n is the laws' body of n
def dp.body(+as: List<&2, Cv.Alias>, +n: Nat) -> {Cv.body(as, n) == CvarEntry.spec_body(as, n) : List<&2, Cv.Cmd>}:
  dp.body_go(as, n, Cv.name.at(as, n), {==})

# (1) The code's walk is the unfolding
# ------------------------------------

# the code's accumulator out after the expansion e (the code gathers the
# commands last first)
def dp.J(out: List<&2, Cv.Cmd>, e: Cv.Exp) -> Cv.Exp:
  match e:
    case Cv.Flat{xs}:
      Cv.Flat{Cv.rev(xs, out)}
    case Cv.Cycle{k}:
      Cv.Cycle{k}
    case Cv.Unknown{k}:
      Cv.Unknown{k}

# a set or toggle c: the code puts it onto its accumulator, the unfolding
# in front of the rest
def dp.al_put(c: Cv.Cmd, m: Maybe<&2, Cv.Exp>, -code: Cv.Exp, +out: List<&2, Cv.Cmd>, +e: Cv.Exp, ih: @x: Cv.Exp -> {m == Some{x} : Maybe<&2, Cv.Exp>} -> {code == dp.J(c <> out, x) : Cv.Exp}, h: {CvarEntry.spec_put(c, m) == Some{e} : Maybe<&2, Cv.Exp>}) -> {code == dp.J(out, e) : Cv.Exp}:
  match m:
    case None{}:
      LE.ex.none_some(Cv.Exp, e, {code == dp.J(out, e) : Cv.Exp}, h)
    case Some{x}:
      match x:
        case Cv.Flat{+xs}:
          %LE.ex.some_inj(Cv.Exp, Cv.Flat{c <> xs}, e, h) : {code == dp.J(out, _) : Cv.Exp}
          ih(Cv.Flat{xs}, {==})
        case Cv.Cycle{+k}:
          %LE.ex.some_inj(Cv.Exp, Cv.Cycle{k}, e, h) : {code == dp.J(out, _) : Cv.Exp}
          ih(Cv.Cycle{k}, {==})
        case Cv.Unknown{+k}:
          %LE.ex.some_inj(Cv.Exp, Cv.Unknown{k}, e, h) : {code == dp.J(out, _) : Cv.Exp}
          ih(Cv.Unknown{k}, {==})

# a body that ended with the commands xs, then the rest
def dp.al_flat(y: Cv.Exp, +g: Nat, +rest: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>, +xs: List<&2, Cv.Cmd>, +e: Cv.Exp, ih: {Cv.expand.go(1n+g, rest, as, Cv.Flat{Cv.rev(xs, out)}) == dp.J(Cv.rev(xs, out), y) : Cv.Exp}, h: {CvarEntry.spec_then(Some{Cv.Flat{xs}}, Some{y}) == Some{e} : Maybe<&2, Cv.Exp>}) -> {Cv.expand.go(1n+g, rest, as, Cv.Flat{Cv.rev(xs, out)}) == dp.J(out, e) : Cv.Exp}:
  match y:
    case Cv.Flat{+ys}:
      %LE.ex.some_inj(Cv.Exp, Cv.Flat{List.append(&2, Cv.Cmd, xs, ys)}, e, h) : {Cv.expand.go(1n+g, rest, as, Cv.Flat{Cv.rev(xs, out)}) == dp.J(out, _) : Cv.Exp}
      %Equal.sym(List<&2, Cv.Cmd>, Cv.rev(List.append(&2, Cv.Cmd, xs, ys), out), Cv.rev(ys, Cv.rev(xs, out)), PIO.pv.rev_app(xs, ys, out)) : {Cv.expand.go(1n+g, rest, as, Cv.Flat{Cv.rev(xs, out)}) == Cv.Flat{_} : Cv.Exp}
      ih
    case Cv.Cycle{+k}:
      %LE.ex.some_inj(Cv.Exp, Cv.Cycle{k}, e, h) : {Cv.expand.go(1n+g, rest, as, Cv.Flat{Cv.rev(xs, out)}) == dp.J(out, _) : Cv.Exp}
      ih
    case Cv.Unknown{+k}:
      %LE.ex.some_inj(Cv.Exp, Cv.Unknown{k}, e, h) : {Cv.expand.go(1n+g, rest, as, Cv.Flat{Cv.rev(xs, out)}) == dp.J(out, _) : Cv.Exp}
      ih

# the body ended with x: the rest goes on from the code's accumulator
def dp.al_then(x: Cv.Exp, m2: Maybe<&2, Cv.Exp>, +g: Nat, +rest: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>, +e: Cv.Exp, ih2: @o: List<&2, Cv.Cmd> -> @y: Cv.Exp -> {m2 == Some{y} : Maybe<&2, Cv.Exp>} -> {Cv.expand.go(1n+g, rest, as, Cv.Flat{o}) == dp.J(o, y) : Cv.Exp}, h: {CvarEntry.spec_then(Some{x}, m2) == Some{e} : Maybe<&2, Cv.Exp>}) -> {Cv.expand.go(1n+g, rest, as, dp.J(out, x)) == dp.J(out, e) : Cv.Exp}:
  match x:
    case Cv.Flat{+xs}:
      match m2:
        case None{}:
          LE.ex.none_some(Cv.Exp, e, {Cv.expand.go(1n+g, rest, as, Cv.Flat{Cv.rev(xs, out)}) == dp.J(out, e) : Cv.Exp}, h)
        case Some{+y}:
          dp.al_flat(y, g, rest, as, out, xs, e, ih2(Cv.rev(xs, out), y, {==}), h)
    case Cv.Cycle{+k}:
      %LE.ex.some_inj(Cv.Exp, Cv.Cycle{k}, e, h) : {Cv.expand.go(1n+g, rest, as, Cv.Cycle{k}) == dp.J(out, _) : Cv.Exp}
      PIO.pv.go_cycle(1n+g, rest, as, k)
    case Cv.Unknown{+k}:
      %LE.ex.some_inj(Cv.Exp, Cv.Unknown{k}, e, h) : {Cv.expand.go(1n+g, rest, as, Cv.Unknown{k}) == dp.J(out, _) : Cv.Exp}
      PIO.pv.go_unknown(1n+g, rest, as, k)

# a run: off the path, the code walks the body one level down, then the
# rest from its accumulator
def dp.al_run(blk: Bool, m1: Maybe<&2, Cv.Exp>, m2: Maybe<&2, Cv.Exp>, -inner: Cv.Exp, +g: Nat, +rest: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>, +e: Cv.Exp, ih1: @x: Cv.Exp -> {m1 == Some{x} : Maybe<&2, Cv.Exp>} -> {inner == dp.J(out, x) : Cv.Exp}, ih2: @o: List<&2, Cv.Cmd> -> @y: Cv.Exp -> {m2 == Some{y} : Maybe<&2, Cv.Exp>} -> {Cv.expand.go(1n+g, rest, as, Cv.Flat{o}) == dp.J(o, y) : Cv.Exp}, h: {CvarEntry.spec_run(blk, m1, m2) == Some{e} : Maybe<&2, Cv.Exp>}) -> {Cv.expand.go(1n+g, rest, as, inner) == dp.J(out, e) : Cv.Exp}:
  match blk:
    case True{}:
      LE.ex.none_some(Cv.Exp, e, {Cv.expand.go(1n+g, rest, as, inner) == dp.J(out, e) : Cv.Exp}, h)
    case False{}:
      match m1:
        case None{}:
          LE.ex.none_some(Cv.Exp, e, {Cv.expand.go(1n+g, rest, as, inner) == dp.J(out, e) : Cv.Exp}, h)
        case Some{+x}:
          %Equal.sym(Cv.Exp, inner, dp.J(out, x), ih1(x, {==})) : {Cv.expand.go(1n+g, rest, as, _) == dp.J(out, e) : Cv.Exp}
          dp.al_then(x, m2, g, rest, as, out, e, ih2, h)

# the unfolding of cs with fuel d, path p, ended with e: the code's walk
# with d levels onto the accumulator out is e onto out
def dp.align(d: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, +out: List<&2, Cv.Cmd>, +e: Cv.Exp, h: {CvarEntry.spec_exp(d, cs, as, p) == Some{e} : Maybe<&2, Cv.Exp>}) -> {Cv.expand.go(d, cs, as, Cv.Flat{out}) == dp.J(out, e) : Cv.Exp}:
  match d:
    case 0n:
      match cs:
        case Nil{}:
          %LE.ex.some_inj(Cv.Exp, Cv.Flat{Nil{}}, e, h) : {Cv.Flat{out} == dp.J(out, _) : Cv.Exp}
          {==}
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              dp.al_put(Cv.CSet{i, v}, CvarEntry.spec_exp(0n, rest, as, p), Cv.expand.go(0n, rest, as, Cv.Flat{Cv.CSet{i, v} <> out}), out, e, x => hx => dp.align(0n, rest, as, p, Cv.CSet{i, v} <> out, x, hx), h)
            case Cv.CToggle{+i}:
              dp.al_put(Cv.CToggle{i}, CvarEntry.spec_exp(0n, rest, as, p), Cv.expand.go(0n, rest, as, Cv.Flat{Cv.CToggle{i} <> out}), out, e, x => hx => dp.align(0n, rest, as, p, Cv.CToggle{i} <> out, x, hx), h)
            case Cv.CRun{+n}:
              LE.ex.none_some(Cv.Exp, e, {Cv.expand.go(0n, Cv.CRun{n} <> rest, as, Cv.Flat{out}) == dp.J(out, e) : Cv.Exp}, h)
            case Cv.CGone{+n}:
              %LE.ex.some_inj(Cv.Exp, Cv.Unknown{n}, e, h) : {Cv.Unknown{n} == dp.J(out, _) : Cv.Exp}
              {==}
    case 1n++g:
      match cs:
        case Nil{}:
          %LE.ex.some_inj(Cv.Exp, Cv.Flat{Nil{}}, e, h) : {Cv.Flat{out} == dp.J(out, _) : Cv.Exp}
          {==}
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              dp.al_put(Cv.CSet{i, v}, CvarEntry.spec_exp(1n+g, rest, as, p), Cv.expand.go(1n+g, rest, as, Cv.Flat{Cv.CSet{i, v} <> out}), out, e, x => hx => dp.align(1n+g, rest, as, p, Cv.CSet{i, v} <> out, x, hx), h)
            case Cv.CToggle{+i}:
              dp.al_put(Cv.CToggle{i}, CvarEntry.spec_exp(1n+g, rest, as, p), Cv.expand.go(1n+g, rest, as, Cv.Flat{Cv.CToggle{i} <> out}), out, e, x => hx => dp.align(1n+g, rest, as, p, Cv.CToggle{i} <> out, x, hx), h)
            case Cv.CRun{+n}:
              +B = CvarEntry.spec_body(as, n)
              %Equal.sym(List<&2, Cv.Cmd>, Cv.body(as, n), B, dp.body(as, n)) : {Cv.expand.go(1n+g, rest, as, Cv.expand.go(g, _, as, Cv.Flat{out})) == dp.J(out, e) : Cv.Exp}
              dp.al_run(CvarEntry.spec_in(p, n), CvarEntry.spec_exp(g, B, as, n <> p), CvarEntry.spec_exp(1n+g, rest, as, p), Cv.expand.go(g, B, as, Cv.Flat{out}), g, rest, as, out, e, x => hx => dp.align(g, B, as, n <> p, out, x, hx), o => y => hy => dp.align(1n+g, rest, as, p, o, y, hy), h)
            case Cv.CGone{+n}:
              %LE.ex.some_inj(Cv.Exp, Cv.Unknown{n}, e, h) : {Cv.Unknown{n} == dp.J(out, _) : Cv.Exp}
              {==}

# (2) More fuel changes no ended unfolding
# ----------------------------------------

def dp.lift_put(c: Cv.Cmd, a: Maybe<&2, Cv.Exp>, -b: Maybe<&2, Cv.Exp>, -e: Cv.Exp, ih: @x: Cv.Exp -> {a == Some{x} : Maybe<&2, Cv.Exp>} -> {b == Some{x} : Maybe<&2, Cv.Exp>}, h: {CvarEntry.spec_put(c, a) == Some{e} : Maybe<&2, Cv.Exp>}) -> {CvarEntry.spec_put(c, b) == Some{e} : Maybe<&2, Cv.Exp>}:
  match a:
    case None{}:
      LE.ex.none_some(Cv.Exp, e, {CvarEntry.spec_put(c, b) == Some{e} : Maybe<&2, Cv.Exp>}, h)
    case Some{+x}:
      %Equal.sym(Maybe<&2, Cv.Exp>, b, Some{x}, ih(x, {==})) : {CvarEntry.spec_put(c, _) == Some{e} : Maybe<&2, Cv.Exp>}
      h

def dp.lift_then2(x: Cv.Exp, a2: Maybe<&2, Cv.Exp>, -b2: Maybe<&2, Cv.Exp>, -e: Cv.Exp, ih2: @y: Cv.Exp -> {a2 == Some{y} : Maybe<&2, Cv.Exp>} -> {b2 == Some{y} : Maybe<&2, Cv.Exp>}, h: {CvarEntry.spec_then(Some{x}, a2) == Some{e} : Maybe<&2, Cv.Exp>}) -> {CvarEntry.spec_then(Some{x}, b2) == Some{e} : Maybe<&2, Cv.Exp>}:
  match x:
    case Cv.Flat{+xs}:
      match a2:
        case None{}:
          LE.ex.none_some(Cv.Exp, e, {CvarEntry.spec_then(Some{Cv.Flat{xs}}, b2) == Some{e} : Maybe<&2, Cv.Exp>}, h)
        case Some{+y}:
          %Equal.sym(Maybe<&2, Cv.Exp>, b2, Some{y}, ih2(y, {==})) : {CvarEntry.spec_then(Some{Cv.Flat{xs}}, _) == Some{e} : Maybe<&2, Cv.Exp>}
          h
    case Cv.Cycle{k}:
      h
    case Cv.Unknown{k}:
      h

def dp.lift_then(a1: Maybe<&2, Cv.Exp>, a2: Maybe<&2, Cv.Exp>, -b1: Maybe<&2, Cv.Exp>, -b2: Maybe<&2, Cv.Exp>, -e: Cv.Exp, ih1: @x: Cv.Exp -> {a1 == Some{x} : Maybe<&2, Cv.Exp>} -> {b1 == Some{x} : Maybe<&2, Cv.Exp>}, ih2: @y: Cv.Exp -> {a2 == Some{y} : Maybe<&2, Cv.Exp>} -> {b2 == Some{y} : Maybe<&2, Cv.Exp>}, h: {CvarEntry.spec_then(a1, a2) == Some{e} : Maybe<&2, Cv.Exp>}) -> {CvarEntry.spec_then(b1, b2) == Some{e} : Maybe<&2, Cv.Exp>}:
  match a1:
    case None{}:
      LE.ex.none_some(Cv.Exp, e, {CvarEntry.spec_then(b1, b2) == Some{e} : Maybe<&2, Cv.Exp>}, h)
    case Some{+x}:
      %Equal.sym(Maybe<&2, Cv.Exp>, b1, Some{x}, ih1(x, {==})) : {CvarEntry.spec_then(_, b2) == Some{e} : Maybe<&2, Cv.Exp>}
      dp.lift_then2(x, a2, b2, e, ih2, h)

# a run: its body's lift only matters off the path
def dp.lift_run(blk: Bool, a1: Maybe<&2, Cv.Exp>, a2: Maybe<&2, Cv.Exp>, -b1: Maybe<&2, Cv.Exp>, -b2: Maybe<&2, Cv.Exp>, -e: Cv.Exp, ih1: @nb: {blk == False{} : Bool} -> @x: Cv.Exp -> {a1 == Some{x} : Maybe<&2, Cv.Exp>} -> {b1 == Some{x} : Maybe<&2, Cv.Exp>}, ih2: @y: Cv.Exp -> {a2 == Some{y} : Maybe<&2, Cv.Exp>} -> {b2 == Some{y} : Maybe<&2, Cv.Exp>}, h: {CvarEntry.spec_run(blk, a1, a2) == Some{e} : Maybe<&2, Cv.Exp>}) -> {CvarEntry.spec_run(blk, b1, b2) == Some{e} : Maybe<&2, Cv.Exp>}:
  match blk:
    case True{}:
      LE.ex.none_some(Cv.Exp, e, {CvarEntry.spec_run(True{}, b1, b2) == Some{e} : Maybe<&2, Cv.Exp>}, h)
    case False{}:
      dp.lift_then(a1, a2, b1, b2, e, ih1({==}), ih2, h)

# one more unit of fuel
def dp.mono(f: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, -e: Cv.Exp, h: {CvarEntry.spec_exp(f, cs, as, p) == Some{e} : Maybe<&2, Cv.Exp>}) -> {CvarEntry.spec_exp(1n+f, cs, as, p) == Some{e} : Maybe<&2, Cv.Exp>}:
  match f:
    case 0n:
      match cs:
        case Nil{}:
          h
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              dp.lift_put(Cv.CSet{i, v}, CvarEntry.spec_exp(0n, rest, as, p), CvarEntry.spec_exp(1n, rest, as, p), e, x => hx => dp.mono(0n, rest, as, p, x, hx), h)
            case Cv.CToggle{+i}:
              dp.lift_put(Cv.CToggle{i}, CvarEntry.spec_exp(0n, rest, as, p), CvarEntry.spec_exp(1n, rest, as, p), e, x => hx => dp.mono(0n, rest, as, p, x, hx), h)
            case Cv.CRun{+n}:
              LE.ex.none_some(Cv.Exp, e, {CvarEntry.spec_exp(1n, Cv.CRun{n} <> rest, as, p) == Some{e} : Maybe<&2, Cv.Exp>}, h)
            case Cv.CGone{n}:
              h
    case 1n++g:
      match cs:
        case Nil{}:
          h
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              dp.lift_put(Cv.CSet{i, v}, CvarEntry.spec_exp(1n+g, rest, as, p), CvarEntry.spec_exp(1n+(1n+g), rest, as, p), e, x => hx => dp.mono(1n+g, rest, as, p, x, hx), h)
            case Cv.CToggle{+i}:
              dp.lift_put(Cv.CToggle{i}, CvarEntry.spec_exp(1n+g, rest, as, p), CvarEntry.spec_exp(1n+(1n+g), rest, as, p), e, x => hx => dp.mono(1n+g, rest, as, p, x, hx), h)
            case Cv.CRun{+n}:
              +B = CvarEntry.spec_body(as, n)
              dp.lift_run(CvarEntry.spec_in(p, n), CvarEntry.spec_exp(g, B, as, n <> p), CvarEntry.spec_exp(1n+g, rest, as, p), CvarEntry.spec_exp(1n+g, B, as, n <> p), CvarEntry.spec_exp(1n+(1n+g), rest, as, p), e, nb => x => hx => dp.mono(g, B, as, n <> p, x, hx), x => hx => dp.mono(1n+g, rest, as, p, x, hx), h)
            case Cv.CGone{n}:
              h

# k more units of fuel
def dp.mono_add(k: Nat, +f: Nat, +cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, -e: Cv.Exp, h: {CvarEntry.spec_exp(f, cs, as, p) == Some{e} : Maybe<&2, Cv.Exp>}) -> {CvarEntry.spec_exp(Nat.add(k, f), cs, as, p) == Some{e} : Maybe<&2, Cv.Exp>}:
  match k:
    case 0n:
      h
    case 1n++j:
      dp.mono(Nat.add(j, f), cs, as, p, e, dp.mono_add(j, f, cs, as, p, e, h))

# (3) The pigeonhole: the table bounds the fuel an unfolding needs
# ----------------------------------------------------------------

def dp.bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the entries of as whose name is on no alias of the path p
def dp.cnt(as: List<&2, Cv.Alias>, +p: List<&2, Nat>) -> Nat:
  match as:
    case Nil{}:
      0n
    case Cv.Alias{+k, c} <> t:
      Nat.add(dp.bit(Bool.not(CvarEntry.spec_in(p, k))), dp.cnt(t, p))

# the entries of as named n
def dp.cntn(as: List<&2, Cv.Alias>, +n: Nat) -> Nat:
  match as:
    case Nil{}:
      0n
    case Cv.Alias{+k, c} <> t:
      Nat.add(dp.bit(Nat.is_eq(n, k)), dp.cntn(t, n))

def dp.crest.pick(hit: Bool, a: Nat, b: Nat) -> Nat:
  match hit:
    case True{}:
      a
    case False{}:
      b

# the entries of as named n, but the first
def dp.crest(as: List<&2, Cv.Alias>, +n: Nat) -> Nat:
  match as:
    case Nil{}:
      0n
    case Cv.Alias{+k, c} <> +t:
      dp.crest.pick(Nat.is_eq(n, k), dp.cntn(t, n), dp.crest(t, n))

def dp.split_at(hit: Bool, +k: Nat, +t: List<&2, Cv.Alias>, +p: List<&2, Nat>, +n: Nat, +eh: {Nat.is_eq(n, k) == hit : Bool}, off: {CvarEntry.spec_in(p, n) == False{} : Bool}, ih: {dp.cnt(t, p) == Nat.add(dp.cntn(t, n), dp.cnt(t, n <> p)) : Nat}) -> {Nat.add(dp.bit(Bool.not(CvarEntry.spec_in(p, k))), dp.cnt(t, p)) == Nat.add(Nat.add(dp.bit(Nat.is_eq(n, k)), dp.cntn(t, n)), Nat.add(dp.bit(Bool.not(Bool.or(Nat.is_eq(n, k), CvarEntry.spec_in(p, k)))), dp.cnt(t, n <> p))) : Nat}:
  match hit:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(n, k), True{}, eh) : {Nat.add(dp.bit(Bool.not(CvarEntry.spec_in(p, k))), dp.cnt(t, p)) == Nat.add(Nat.add(dp.bit(_), dp.cntn(t, n)), Nat.add(dp.bit(Bool.not(Bool.or(_, CvarEntry.spec_in(p, k)))), dp.cnt(t, n <> p))) : Nat}
      %LA.pv.eq_true(n, k, eh) : {Nat.add(dp.bit(Bool.not(CvarEntry.spec_in(p, _))), dp.cnt(t, p)) == 1n+Nat.add(dp.cntn(t, n), dp.cnt(t, n <> p)) : Nat}
      %Equal.sym(Bool, CvarEntry.spec_in(p, n), False{}, off) : {Nat.add(dp.bit(Bool.not(_)), dp.cnt(t, p)) == 1n+Nat.add(dp.cntn(t, n), dp.cnt(t, n <> p)) : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, dp.cnt(t, p), Nat.add(dp.cntn(t, n), dp.cnt(t, n <> p)), ih)
    case False{}:
      +B = dp.bit(Bool.not(CvarEntry.spec_in(p, k)))
      %Equal.sym(Bool, Nat.is_eq(n, k), False{}, eh) : {Nat.add(B, dp.cnt(t, p)) == Nat.add(Nat.add(dp.bit(_), dp.cntn(t, n)), Nat.add(dp.bit(Bool.not(Bool.or(_, CvarEntry.spec_in(p, k)))), dp.cnt(t, n <> p))) : Nat}
      %Equal.sym(Nat, dp.cnt(t, p), Nat.add(dp.cntn(t, n), dp.cnt(t, n <> p)), ih) : {Nat.add(B, _) == Nat.add(dp.cntn(t, n), Nat.add(B, dp.cnt(t, n <> p))) : Nat}
      LNat.add_lcomm(B, dp.cntn(t, n), dp.cnt(t, n <> p))

# off the path, n's entries leave the count when n joins the path
def dp.split(as: List<&2, Cv.Alias>, +p: List<&2, Nat>, +n: Nat, +off: {CvarEntry.spec_in(p, n) == False{} : Bool}) -> {dp.cnt(as, p) == Nat.add(dp.cntn(as, n), dp.cnt(as, n <> p)) : Nat}:
  match as:
    case Nil{}:
      {==}
    case Cv.Alias{+k, c} <> +t:
      dp.split_at(Nat.is_eq(n, k), k, t, p, n, {==}, off, dp.split(t, p, n, off))

def dp.has_at(hit: Bool, +k: Nat, +c: List<&2, Cv.Cmd>, +t: List<&2, Cv.Alias>, +n: Nat, +b: List<&2, Cv.Cmd>, +eh: {Nat.is_eq(n, k) == hit : Bool}, h: {CvarEntry.spec_alias.pick(Nat.is_eq(k, n), c, CvarEntry.spec_alias(t, n)) == Some{b} : Maybe<&2, List<&2, Cv.Cmd>>}, ih: @ht: {CvarEntry.spec_alias(t, n) == Some{b} : Maybe<&2, List<&2, Cv.Cmd>>} -> {dp.cntn(t, n) == 1n+dp.crest(t, n) : Nat}) -> {Nat.add(dp.bit(Nat.is_eq(n, k)), dp.cntn(t, n)) == 1n+dp.crest.pick(Nat.is_eq(n, k), dp.cntn(t, n), dp.crest(t, n)) : Nat}:
  match hit:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(n, k), True{}, eh) : {Nat.add(dp.bit(_), dp.cntn(t, n)) == 1n+dp.crest.pick(_, dp.cntn(t, n), dp.crest(t, n)) : Nat}
      {==}
    case False{}:
      +r = CvarEntry.spec_alias(t, n)
      ekn = Equal.trans(Bool, Nat.is_eq(k, n), Nat.is_eq(n, k), False{}, LNat.pt.eq_comm(k, n), eh)
      %Equal.sym(Bool, Nat.is_eq(n, k), False{}, eh) : {Nat.add(dp.bit(_), dp.cntn(t, n)) == 1n+dp.crest.pick(_, dp.cntn(t, n), dp.crest(t, n)) : Nat}
      ih(Equal.trans(Maybe<&2, List<&2, Cv.Cmd>>, r, CvarEntry.spec_alias.pick(Nat.is_eq(k, n), c, r), Some{b}, Equal.cong(Bool, Maybe<&2, List<&2, Cv.Cmd>>, z => CvarEntry.spec_alias.pick(z, c, r), False{}, Nat.is_eq(k, n), Equal.sym(Bool, Nat.is_eq(k, n), False{}, ekn)), h))

# a name with an alias has at least one entry
def dp.has(as: List<&2, Cv.Alias>, +n: Nat, +b: List<&2, Cv.Cmd>, h: {CvarEntry.spec_alias(as, n) == Some{b} : Maybe<&2, List<&2, Cv.Cmd>>}) -> {dp.cntn(as, n) == 1n+dp.crest(as, n) : Nat}:
  match as:
    case Nil{}:
      LE.ex.none_some(List<&2, Cv.Cmd>, b, {dp.cntn(Nil{}, n) == 1n+dp.crest(Nil{}, n) : Nat}, h)
    case Cv.Alias{+k, +c} <> +t:
      dp.has_at(Nat.is_eq(n, k), k, c, t, n, b, {==}, h, ht => dp.has(t, n, b, ht))

# a run of a missing alias is unknown at any fuel
def dp.gone(f: Nat, +n: Nat, +as: List<&2, Cv.Alias>, +q: List<&2, Nat>) -> {CvarEntry.spec_exp(f, [Cv.CGone{n}], as, q) == Some{Cv.Unknown{n}} : Maybe<&2, Cv.Exp>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# off the path, the body of n needs no more fuel than the entries off the
# path, n's included, minus one
def dp.down(mb: Maybe<&2, List<&2, Cv.Cmd>>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, +n: Nat, -x: Cv.Exp, em: {CvarEntry.spec_alias(as, n) == mb : Maybe<&2, List<&2, Cv.Cmd>>}, off: {CvarEntry.spec_in(p, n) == False{} : Bool}, r: {CvarEntry.spec_exp(1n+dp.cnt(as, n <> p), CvarEntry.spec_body.of(mb, n), as, n <> p) == Some{x} : Maybe<&2, Cv.Exp>}) -> {CvarEntry.spec_exp(dp.cnt(as, p), CvarEntry.spec_body.of(mb, n), as, n <> p) == Some{x} : Maybe<&2, Cv.Exp>}:
  match mb:
    case None{}:
      %Equal.sym(Maybe<&2, Cv.Exp>, CvarEntry.spec_exp(dp.cnt(as, p), [Cv.CGone{n}], as, n <> p), Some{Cv.Unknown{n}}, dp.gone(dp.cnt(as, p), n, as, n <> p)) : {_ == Some{x} : Maybe<&2, Cv.Exp>}
      r
    case Some{+b}:
      +C = dp.cnt(as, n <> p)
      +R = dp.crest(as, n)
      +N = dp.cntn(as, n)
      %Equal.sym(Nat, dp.cnt(as, p), Nat.add(R, 1n+C), Equal.trans(Nat, dp.cnt(as, p), Nat.add(N, C), Nat.add(R, 1n+C), dp.split(as, p, n, off), Equal.trans(Nat, Nat.add(N, C), 1n+Nat.add(R, C), Nat.add(R, 1n+C), Equal.cong(Nat, Nat, z => Nat.add(z, C), N, 1n+R, dp.has(as, n, b, em)), Equal.sym(Nat, Nat.add(R, 1n+C), 1n+Nat.add(R, C), LNat.add_succ(R, C))))) : {CvarEntry.spec_exp(_, b, as, n <> p) == Some{x} : Maybe<&2, Cv.Exp>}
      dp.mono_add(R, 1n+C, b, as, n <> p, x, r)

# an unfolding that ends with any fuel ends, the same, with one unit more
# than the entries off the path
def dp.bound(f: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, +e: Cv.Exp, h: {CvarEntry.spec_exp(f, cs, as, p) == Some{e} : Maybe<&2, Cv.Exp>}) -> {CvarEntry.spec_exp(1n+dp.cnt(as, p), cs, as, p) == Some{e} : Maybe<&2, Cv.Exp>}:
  match f:
    case 0n:
      match cs:
        case Nil{}:
          h
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              dp.lift_put(Cv.CSet{i, v}, CvarEntry.spec_exp(0n, rest, as, p), CvarEntry.spec_exp(1n+dp.cnt(as, p), rest, as, p), e, x => hx => dp.bound(0n, rest, as, p, x, hx), h)
            case Cv.CToggle{+i}:
              dp.lift_put(Cv.CToggle{i}, CvarEntry.spec_exp(0n, rest, as, p), CvarEntry.spec_exp(1n+dp.cnt(as, p), rest, as, p), e, x => hx => dp.bound(0n, rest, as, p, x, hx), h)
            case Cv.CRun{+n}:
              LE.ex.none_some(Cv.Exp, e, {CvarEntry.spec_exp(1n+dp.cnt(as, p), Cv.CRun{n} <> rest, as, p) == Some{e} : Maybe<&2, Cv.Exp>}, h)
            case Cv.CGone{n}:
              h
    case 1n++g:
      match cs:
        case Nil{}:
          h
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              dp.lift_put(Cv.CSet{i, v}, CvarEntry.spec_exp(1n+g, rest, as, p), CvarEntry.spec_exp(1n+dp.cnt(as, p), rest, as, p), e, x => hx => dp.bound(1n+g, rest, as, p, x, hx), h)
            case Cv.CToggle{+i}:
              dp.lift_put(Cv.CToggle{i}, CvarEntry.spec_exp(1n+g, rest, as, p), CvarEntry.spec_exp(1n+dp.cnt(as, p), rest, as, p), e, x => hx => dp.bound(1n+g, rest, as, p, x, hx), h)
            case Cv.CRun{+n}:
              +B = CvarEntry.spec_body(as, n)
              dp.lift_run(CvarEntry.spec_in(p, n), CvarEntry.spec_exp(g, B, as, n <> p), CvarEntry.spec_exp(1n+g, rest, as, p), CvarEntry.spec_exp(dp.cnt(as, p), B, as, n <> p), CvarEntry.spec_exp(1n+dp.cnt(as, p), rest, as, p), e, nb => x => hx => dp.down(CvarEntry.spec_alias(as, n), as, p, n, x, {==}, nb, dp.bound(g, B, as, n <> p, x, hx)), x => hx => dp.bound(1n+g, rest, as, p, x, hx), h)
            case Cv.CGone{n}:
              h

# with the empty path every entry counts
def dp.cnt_nil(as: List<&2, Cv.Alias>) -> {dp.cnt(as, Nil{}) == List.length(&2, Cv.Alias, as) : Nat}:
  match as:
    case Nil{}:
      {==}
    case Cv.Alias{k, c} <> t:
      Equal.cong(Nat, Nat, z => 1n+z, dp.cnt(t, Nil{}), List.length(&2, Cv.Alias, t), dp.cnt_nil(t))

# fin reads the code's accumulator in order
def dp.fin_J(e: Cv.Exp) -> {Cv.fin(dp.J(Nil{}, e)) == e : Cv.Exp}:
  match e:
    case Cv.Flat{+xs}:
      Equal.cong(List<&2, Cv.Cmd>, Cv.Exp, l => Cv.Flat{l}, Cv.rev(Cv.rev(xs, Nil{}), Nil{}), xs, Equal.trans(List<&2, Cv.Cmd>, Cv.rev(Cv.rev(xs, Nil{}), Nil{}), List.append(&2, Cv.Cmd, xs, Nil{}), xs, PRB.pv.rev_rev(xs, Nil{}, Nil{}), PRB.pv.app_nil(xs)))
    case Cv.Cycle{k}:
      {==}
    case Cv.Unknown{k}:
      {==}

def CvarEntry.alias_expands_any_depth(f, cs, as, e, ends):
  +L = List.length(&2, Cv.Alias, as)
  %Equal.sym(Cv.Exp, Cv.expand.go(1n+L, cs, as, Cv.Flat{Nil{}}), dp.J(Nil{}, e), dp.align(1n+L, cs, as, Nil{}, Nil{}, e, Equal.trans(Maybe<&2, Cv.Exp>, CvarEntry.spec_exp(1n+L, cs, as, Nil{}), CvarEntry.spec_exp(1n+dp.cnt(as, Nil{}), cs, as, Nil{}), Some{e}, Equal.cong(Nat, Maybe<&2, Cv.Exp>, z => CvarEntry.spec_exp(1n+z, cs, as, Nil{}), L, dp.cnt(as, Nil{}), Equal.sym(Nat, dp.cnt(as, Nil{}), L, dp.cnt_nil(as))), dp.bound(f, cs, as, Nil{}, e, ends)))) : {Cv.fin(_) == e : Cv.Exp}
  dp.fin_J(e)
