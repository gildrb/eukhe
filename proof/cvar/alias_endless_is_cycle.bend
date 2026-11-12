# eukhe: the proof of LAW alias_endless_is_cycle
#
# PROOF. The code's walk with ANY number d of nesting levels left ends in
# a cycle on a nest whose unfolding runs an alias it is inside of
# (dcy.cy), by induction on d, then the commands. The invariant on the
# path p: the body of each alias of p, walked with that alias and the
# ones after it on the path, runs an alias it is inside of, with the
# law's fuel F (dcy.W). A set or a toggle goes on with the rest; a run at
# depth 0 is the code's cycle; a run of n with levels left walks n's body
# one level down:
# - n on the path: the invariant at n (dcy.re) gives a looping walk of
#   n's body, so that body is a cycle one level down;
# - the body loops: a cycle one level down, with n added to the path
#   (more fuel keeps a loop, dcy.lm_add);
# - the body ends with commands xs and the rest loops: the code's body is
#   a cycle, or else it is exactly xs (dcy.dk: alias_expands_any_depth's
#   walk, dp.align, at a depth past the pigeonhole bound dp.bound, and
#   more levels change no expansion that is not a cycle, dcy.cm), and
#   the rest goes on from it.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/entry.bend as CvarEntry
import ./base.bend as LA
import ./alias_expands_in_order.bend as PIO
import ./alias_expands_any_depth.bend as PAD
import ../base/nat.bend as LNat

# Cycles
# ------

# a cycle met as the accumulator is the outcome
def dcy.go_cyc(x: Cv.Exp, d: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, hx: {CvarEntry.spec_is_cycle(x) == True{} : Bool}) -> {CvarEntry.spec_is_cycle(Cv.expand.go(d, cs, as, x)) == True{} : Bool}:
  match x:
    case Cv.Flat{o}:
      LA.pv.absurdF({CvarEntry.spec_is_cycle(Cv.expand.go(d, cs, as, Cv.Flat{o})) == True{} : Bool}, hx)
    case Cv.Cycle{+k}:
      %Equal.sym(Cv.Exp, Cv.expand.go(d, cs, as, Cv.Cycle{k}), Cv.Cycle{k}, PIO.pv.go_cycle(d, cs, as, k)) : {CvarEntry.spec_is_cycle(_) == True{} : Bool}
      {==}
    case Cv.Unknown{k}:
      LA.pv.absurdF({CvarEntry.spec_is_cycle(Cv.expand.go(d, cs, as, Cv.Unknown{k})) == True{} : Bool}, hx)

# a walk that is no cycle started from no cycle
def dcy.nb(x: Cv.Exp, +d: Nat, +cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, nc: {CvarEntry.spec_is_cycle(Cv.expand.go(d, cs, as, x)) == False{} : Bool}) -> {CvarEntry.spec_is_cycle(x) == False{} : Bool}:
  match x:
    case Cv.Flat{o}:
      {==}
    case Cv.Cycle{+k}:
      LA.pv.absurdF({CvarEntry.spec_is_cycle(Cv.Cycle{k}) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, Equal.trans(Bool, True{}, CvarEntry.spec_is_cycle(Cv.expand.go(d, cs, as, Cv.Cycle{k})), False{}, Equal.cong(Cv.Exp, Bool, z => CvarEntry.spec_is_cycle(z), Cv.Cycle{k}, Cv.expand.go(d, cs, as, Cv.Cycle{k}), Equal.sym(Cv.Exp, Cv.expand.go(d, cs, as, Cv.Cycle{k}), Cv.Cycle{k}, PIO.pv.go_cycle(d, cs, as, k))), nc)))
    case Cv.Unknown{k}:
      {==}

# fin keeps a cycle
def dcy.fin_cyc(x: Cv.Exp) -> {CvarEntry.spec_is_cycle(Cv.fin(x)) == CvarEntry.spec_is_cycle(x) : Bool}:
  match x:
    case Cv.Flat{o}:
      {==}
    case Cv.Cycle{k}:
      {==}
    case Cv.Unknown{k}:
      {==}

def dcy.isf(e: Cv.Exp) -> Bool:
  match e:
    case Cv.Flat{o}:
      True{}
    case Cv.Cycle{k}:
      False{}
    case Cv.Unknown{k}:
      False{}

# More levels change no walk that is not a cycle
# ----------------------------------------------

def dcy.cm_acc(x: Cv.Exp, +e: Nat, +rest: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, ih: @o: List<&2, Cv.Cmd> -> {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, Cv.Flat{o})) == False{} : Bool} -> {Cv.expand.go(1n+(1n+e), rest, as, Cv.Flat{o}) == Cv.expand.go(1n+e, rest, as, Cv.Flat{o}) : Cv.Exp}, nc: {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, x)) == False{} : Bool}) -> {Cv.expand.go(1n+(1n+e), rest, as, x) == Cv.expand.go(1n+e, rest, as, x) : Cv.Exp}:
  match x:
    case Cv.Flat{+o}:
      ih(o, nc)
    case Cv.Cycle{+k}:
      Equal.trans(Cv.Exp, Cv.expand.go(1n+(1n+e), rest, as, Cv.Cycle{k}), Cv.Cycle{k}, Cv.expand.go(1n+e, rest, as, Cv.Cycle{k}), PIO.pv.go_cycle(1n+(1n+e), rest, as, k), Equal.sym(Cv.Exp, Cv.expand.go(1n+e, rest, as, Cv.Cycle{k}), Cv.Cycle{k}, PIO.pv.go_cycle(1n+e, rest, as, k)))
    case Cv.Unknown{+k}:
      Equal.trans(Cv.Exp, Cv.expand.go(1n+(1n+e), rest, as, Cv.Unknown{k}), Cv.Unknown{k}, Cv.expand.go(1n+e, rest, as, Cv.Unknown{k}), PIO.pv.go_unknown(1n+(1n+e), rest, as, k), Equal.sym(Cv.Exp, Cv.expand.go(1n+e, rest, as, Cv.Unknown{k}), Cv.Unknown{k}, PIO.pv.go_unknown(1n+e, rest, as, k)))

# one more level
def dcy.cm(d: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>, +nc: {CvarEntry.spec_is_cycle(Cv.expand.go(d, cs, as, Cv.Flat{out})) == False{} : Bool}) -> {Cv.expand.go(1n+d, cs, as, Cv.Flat{out}) == Cv.expand.go(d, cs, as, Cv.Flat{out}) : Cv.Exp}:
  match d:
    case 0n:
      match cs:
        case Nil{}:
          {==}
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              dcy.cm(0n, rest, as, Cv.CSet{i, v} <> out, nc)
            case Cv.CToggle{+i}:
              dcy.cm(0n, rest, as, Cv.CToggle{i} <> out, nc)
            case Cv.CRun{+n}:
              LA.pv.absurdF({Cv.expand.go(1n, Cv.CRun{n} <> rest, as, Cv.Flat{out}) == Cv.expand.go(0n, Cv.CRun{n} <> rest, as, Cv.Flat{out}) : Cv.Exp}, Equal.sym(Bool, True{}, False{}, nc))
            case Cv.CGone{n}:
              {==}
    case 1n++e:
      match cs:
        case Nil{}:
          {==}
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              dcy.cm(1n+e, rest, as, Cv.CSet{i, v} <> out, nc)
            case Cv.CToggle{+i}:
              dcy.cm(1n+e, rest, as, Cv.CToggle{i} <> out, nc)
            case Cv.CRun{+n}:
              +X = Cv.expand.go(e, Cv.body(as, n), as, Cv.Flat{out})
              %Equal.sym(Cv.Exp, Cv.expand.go(1n+e, Cv.body(as, n), as, Cv.Flat{out}), X, dcy.cm(e, Cv.body(as, n), as, out, dcy.nb(X, 1n+e, rest, as, nc))) : {Cv.expand.go(1n+(1n+e), rest, as, _) == Cv.expand.go(1n+e, rest, as, X) : Cv.Exp}
              dcy.cm_acc(X, e, rest, as, o => ho => dcy.cm(1n+e, rest, as, o, ho), nc)
            case Cv.CGone{n}:
              {==}

def dcy.cm_step(+j: Nat, +d: Nat, +cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>, nc: {CvarEntry.spec_is_cycle(Cv.expand.go(d, cs, as, Cv.Flat{out})) == False{} : Bool}, +ih: {Cv.expand.go(Nat.add(j, d), cs, as, Cv.Flat{out}) == Cv.expand.go(d, cs, as, Cv.Flat{out}) : Cv.Exp}) -> {Cv.expand.go(1n+Nat.add(j, d), cs, as, Cv.Flat{out}) == Cv.expand.go(d, cs, as, Cv.Flat{out}) : Cv.Exp}:
  +Y = Cv.expand.go(Nat.add(j, d), cs, as, Cv.Flat{out})
  +Z = Cv.expand.go(d, cs, as, Cv.Flat{out})
  Equal.trans(Cv.Exp, Cv.expand.go(1n+Nat.add(j, d), cs, as, Cv.Flat{out}), Y, Z, dcy.cm(Nat.add(j, d), cs, as, out, Equal.trans(Bool, CvarEntry.spec_is_cycle(Y), CvarEntry.spec_is_cycle(Z), False{}, Equal.cong(Cv.Exp, Bool, z => CvarEntry.spec_is_cycle(z), Y, Z, ih), nc)), ih)

# k more levels
def dcy.cm_add(k: Nat, +d: Nat, +cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>, +nc: {CvarEntry.spec_is_cycle(Cv.expand.go(d, cs, as, Cv.Flat{out})) == False{} : Bool}) -> {Cv.expand.go(Nat.add(k, d), cs, as, Cv.Flat{out}) == Cv.expand.go(d, cs, as, Cv.Flat{out}) : Cv.Exp}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      dcy.cm_step(j, d, cs, as, out, nc, dcy.cm_add(j, d, cs, as, out, nc))

# an unfolding that ended with x: the code's walk at any depth that is no
# cycle is x onto the accumulator
def dcy.dk(g: Nat, +cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, +out: List<&2, Cv.Cmd>, +x: Cv.Exp, h: {CvarEntry.spec_exp(g, cs, as, p) == Some{x} : Maybe<&2, Cv.Exp>}, +d: Nat, nc: {CvarEntry.spec_is_cycle(Cv.expand.go(d, cs, as, Cv.Flat{out})) == False{} : Bool}) -> {Cv.expand.go(d, cs, as, Cv.Flat{out}) == PAD.dp.J(out, x) : Cv.Exp}:
  +C = {1n+PAD.dp.cnt(as, p) : Nat}
  +E = Nat.add(d, C)
  ha = PAD.dp.align(E, cs, as, p, out, x, PAD.dp.mono_add(d, C, cs, as, p, x, PAD.dp.bound(g, cs, as, p, x, h)))
  Equal.trans(Cv.Exp, Cv.expand.go(d, cs, as, Cv.Flat{out}), Cv.expand.go(Nat.add(C, d), cs, as, Cv.Flat{out}), PAD.dp.J(out, x), Equal.sym(Cv.Exp, Cv.expand.go(Nat.add(C, d), cs, as, Cv.Flat{out}), Cv.expand.go(d, cs, as, Cv.Flat{out}), dcy.cm_add(C, d, cs, as, out, nc)), Equal.trans(Cv.Exp, Cv.expand.go(Nat.add(C, d), cs, as, Cv.Flat{out}), Cv.expand.go(E, cs, as, Cv.Flat{out}), PAD.dp.J(out, x), Equal.cong(Nat, Cv.Exp, z => Cv.expand.go(z, cs, as, Cv.Flat{out}), Nat.add(C, d), E, LNat.add_comm(C, d)), ha))

# More fuel keeps a loop
# ---------------------

def dcy.then_t(-b: Bool, -eb: Maybe<&2, Cv.Exp>, -lr: Bool, hb: {b == True{} : Bool}) -> {CvarEntry.spec_loop.then(b, eb, lr) == True{} : Bool}:
  %Equal.sym(Bool, b, True{}, hb) : {CvarEntry.spec_loop.then(_, eb, lr) == True{} : Bool}
  {==}

def dcy.then_flat(lb: Bool, -xs: List<&2, Cv.Cmd>, -lr: Bool, hr: {lr == True{} : Bool}) -> {CvarEntry.spec_loop.then(lb, Some{Cv.Flat{xs}}, lr) == True{} : Bool}:
  match lb:
    case True{}:
      {==}
    case False{}:
      hr

def dcy.lift_then(lb: Bool, eb: Maybe<&2, Cv.Exp>, lr: Bool, +lb2: Bool, -eb2: Maybe<&2, Cv.Exp>, -lr2: Bool, ih1: {lb == True{} : Bool} -> {lb2 == True{} : Bool}, ih2: @x: Cv.Exp -> {eb == Some{x} : Maybe<&2, Cv.Exp>} -> {eb2 == Some{x} : Maybe<&2, Cv.Exp>}, ih3: {lr == True{} : Bool} -> {lr2 == True{} : Bool}, h: {CvarEntry.spec_loop.then(lb, eb, lr) == True{} : Bool}) -> {CvarEntry.spec_loop.then(lb2, eb2, lr2) == True{} : Bool}:
  match lb:
    case True{}:
      dcy.then_t(lb2, eb2, lr2, ih1({==}))
    case False{}:
      match eb:
        case None{}:
          LA.pv.absurdF({CvarEntry.spec_loop.then(lb2, eb2, lr2) == True{} : Bool}, h)
        case Some{x}:
          match x:
            case Cv.Flat{+xs}:
              %Equal.sym(Maybe<&2, Cv.Exp>, eb2, Some{Cv.Flat{xs}}, ih2(Cv.Flat{xs}, {==})) : {CvarEntry.spec_loop.then(lb2, _, lr2) == True{} : Bool}
              dcy.then_flat(lb2, xs, lr2, ih3(h))
            case Cv.Cycle{k}:
              LA.pv.absurdF({CvarEntry.spec_loop.then(lb2, eb2, lr2) == True{} : Bool}, h)
            case Cv.Unknown{k}:
              LA.pv.absurdF({CvarEntry.spec_loop.then(lb2, eb2, lr2) == True{} : Bool}, h)

def dcy.lift_run(on: Bool, lb: Bool, eb: Maybe<&2, Cv.Exp>, lr: Bool, +lb2: Bool, -eb2: Maybe<&2, Cv.Exp>, -lr2: Bool, ih1: {lb == True{} : Bool} -> {lb2 == True{} : Bool}, ih2: @x: Cv.Exp -> {eb == Some{x} : Maybe<&2, Cv.Exp>} -> {eb2 == Some{x} : Maybe<&2, Cv.Exp>}, ih3: {lr == True{} : Bool} -> {lr2 == True{} : Bool}, h: {CvarEntry.spec_loop.run(on, lb, eb, lr) == True{} : Bool}) -> {CvarEntry.spec_loop.run(on, lb2, eb2, lr2) == True{} : Bool}:
  match on:
    case True{}:
      {==}
    case False{}:
      dcy.lift_then(lb, eb, lr, lb2, eb2, lr2, ih1, ih2, ih3, h)

def dcy.run_t(-on: Bool, -lb: Bool, -eb: Maybe<&2, Cv.Exp>, -lr: Bool, h: {on == True{} : Bool}) -> {CvarEntry.spec_loop.run(on, lb, eb, lr) == True{} : Bool}:
  %Equal.sym(Bool, on, True{}, h) : {CvarEntry.spec_loop.run(_, lb, eb, lr) == True{} : Bool}
  {==}

# one more unit of fuel
def dcy.lm(f: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, h: {CvarEntry.spec_loop(f, cs, as, p) == True{} : Bool}) -> {CvarEntry.spec_loop(1n+f, cs, as, p) == True{} : Bool}:
  match f:
    case 0n:
      match cs:
        case Nil{}:
          h
        case c <> +rest:
          match c:
            case Cv.CSet{i, v}:
              dcy.lm(0n, rest, as, p, h)
            case Cv.CToggle{i}:
              dcy.lm(0n, rest, as, p, h)
            case Cv.CRun{+n}:
              +B = CvarEntry.spec_body(as, n)
              dcy.run_t(CvarEntry.spec_in(p, n), CvarEntry.spec_loop(0n, B, as, n <> p), CvarEntry.spec_exp(0n, B, as, n <> p), CvarEntry.spec_loop(1n, rest, as, p), h)
            case Cv.CGone{n}:
              h
    case 1n++g:
      match cs:
        case Nil{}:
          h
        case c <> +rest:
          match c:
            case Cv.CSet{i, v}:
              dcy.lm(1n+g, rest, as, p, h)
            case Cv.CToggle{i}:
              dcy.lm(1n+g, rest, as, p, h)
            case Cv.CRun{+n}:
              +B = CvarEntry.spec_body(as, n)
              dcy.lift_run(CvarEntry.spec_in(p, n), CvarEntry.spec_loop(g, B, as, n <> p), CvarEntry.spec_exp(g, B, as, n <> p), CvarEntry.spec_loop(1n+g, rest, as, p), CvarEntry.spec_loop(1n+g, B, as, n <> p), CvarEntry.spec_exp(1n+g, B, as, n <> p), CvarEntry.spec_loop(1n+(1n+g), rest, as, p), hb => dcy.lm(g, B, as, n <> p, hb), x => hx => PAD.dp.mono(g, B, as, n <> p, x, hx), hr => dcy.lm(1n+g, rest, as, p, hr), h)
            case Cv.CGone{n}:
              h

# k more units of fuel
def dcy.lm_add(k: Nat, +f: Nat, +cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, h: {CvarEntry.spec_loop(f, cs, as, p) == True{} : Bool}) -> {CvarEntry.spec_loop(Nat.add(k, f), cs, as, p) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n++j:
      dcy.lm(Nat.add(j, f), cs, as, p, dcy.lm_add(j, f, cs, as, p, h))

# The path invariant
# ------------------

# the body of each alias of the path, walked with it and the aliases
# after it on the path, loops with fuel F
def dcy.W(+F: Nat, +as: List<&2, Cv.Alias>, p: List<&2, Nat>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case +n <> +q:
      Bool.and(CvarEntry.spec_loop(F, CvarEntry.spec_body(as, n), as, n <> q), dcy.W(F, as, q))

def dcy.suf.pick(hit: Bool, q: List<&2, Nat>, r: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      q
    case False{}:
      r

# the path after the first n on it
def dcy.suf(p: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  match p:
    case Nil{}:
      Nil{}
    case +m <> +q:
      dcy.suf.pick(Nat.is_eq(m, n), q, dcy.suf(q, n))

def dcy.re_at(hit: Bool, +m: Nat, +q: List<&2, Nat>, +F: Nat, +as: List<&2, Cv.Alias>, +n: Nat, eh: {Nat.is_eq(m, n) == hit : Bool}, mem: {Bool.or(hit, CvarEntry.spec_in(q, n)) == True{} : Bool}, hw: {Bool.and(CvarEntry.spec_loop(F, CvarEntry.spec_body(as, m), as, m <> q), dcy.W(F, as, q)) == True{} : Bool}, ih: {CvarEntry.spec_in(q, n) == True{} : Bool} -> {dcy.W(F, as, q) == True{} : Bool} -> {dcy.W(F, as, n <> dcy.suf(q, n)) == True{} : Bool}) -> {dcy.W(F, as, n <> dcy.suf.pick(hit, q, dcy.suf(q, n))) == True{} : Bool}:
  match hit:
    case True{}:
      Equal.trans(Bool, dcy.W(F, as, n <> q), dcy.W(F, as, m <> q), True{}, Equal.cong(Nat, Bool, z => dcy.W(F, as, z <> q), n, m, Equal.sym(Nat, m, n, LA.pv.eq_true(m, n, eh))), hw)
    case False{}:
      ih(mem, LA.cvar.pv.and_r(CvarEntry.spec_loop(F, CvarEntry.spec_body(as, m), as, m <> q), dcy.W(F, as, q), hw))

# an alias n on the path: its body loops from its place on the path
def dcy.re(p: List<&2, Nat>, +F: Nat, +as: List<&2, Cv.Alias>, +n: Nat, mem: {CvarEntry.spec_in(p, n) == True{} : Bool}, hw: {dcy.W(F, as, p) == True{} : Bool}) -> {dcy.W(F, as, n <> dcy.suf(p, n)) == True{} : Bool}:
  match p:
    case Nil{}:
      LA.pv.absurdF({dcy.W(F, as, n <> dcy.suf(Nil{}, n)) == True{} : Bool}, mem)
    case +m <> +q:
      dcy.re_at(Nat.is_eq(m, n), m, q, F, as, n, {==}, mem, hw, hi => hq => dcy.re(q, F, as, n, hi, hq))

# F covers fuel g below the fuel 1 + g of a run
def dcy.k_step(+F: Nat, +k: Nat, +g: Nat, hk: {F == Nat.add(k, 1n+g) : Nat}) -> {F == Nat.add(1n+k, g) : Nat}:
  Equal.trans(Nat, F, Nat.add(k, 1n+g), 1n+Nat.add(k, g), hk, LNat.add_succ(k, g))

def dcy.lift_to(+F: Nat, +k: Nat, +g: Nat, +B: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +q: List<&2, Nat>, hk: {F == Nat.add(k, 1n+g) : Nat}, hl: {CvarEntry.spec_loop(g, B, as, q) == True{} : Bool}) -> {CvarEntry.spec_loop(F, B, as, q) == True{} : Bool}:
  %Equal.sym(Nat, F, Nat.add(1n+k, g), dcy.k_step(F, k, g, hk)) : {CvarEntry.spec_loop(_, B, as, q) == True{} : Bool}
  dcy.lm_add(1n+k, g, B, as, q, hl)

# a body that loops joins the path
def dcy.push_w(+g: Nat, +F: Nat, +k: Nat, +n: Nat, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, hk: {F == Nat.add(k, 1n+g) : Nat}, +hlb: {CvarEntry.spec_loop(g, CvarEntry.spec_body(as, n), as, n <> p) == True{} : Bool}, hw: {dcy.W(F, as, p) == True{} : Bool}) -> {Bool.and(CvarEntry.spec_loop(g, CvarEntry.spec_body(as, n), as, n <> p), dcy.W(F, as, n <> p)) == True{} : Bool}:
  +B = CvarEntry.spec_body(as, n)
  LA.pv.and_t(CvarEntry.spec_loop(g, B, as, n <> p), dcy.W(F, as, n <> p), hlb, LA.pv.and_t(CvarEntry.spec_loop(F, B, as, n <> p), dcy.W(F, as, p), dcy.lift_to(F, k, g, B, as, n <> p, hk, hlb), hw))

# The walk at any depth
# ---------------------

def dcy.nil_f(f: Nat, -as: List<&2, Cv.Alias>, -p: List<&2, Nat>, h: {CvarEntry.spec_loop(f, Nil{}, as, p) == True{} : Bool}) -> {False{} == True{} : Bool}:
  match f:
    case 0n:
      h
    case 1n+g:
      h

def dcy.gone_f(f: Nat, -n: Nat, -rest: List<&2, Cv.Cmd>, -as: List<&2, Cv.Alias>, -p: List<&2, Nat>, h: {CvarEntry.spec_loop(f, Cv.CGone{n} <> rest, as, p) == True{} : Bool}) -> {False{} == True{} : Bool}:
  match f:
    case 0n:
      h
    case 1n+g:
      h

def dcy.set_f(f: Nat, -i: Nat, -v: Cv.Val, -rest: List<&2, Cv.Cmd>, -as: List<&2, Cv.Alias>, -p: List<&2, Nat>) -> {CvarEntry.spec_loop(f, Cv.CSet{i, v} <> rest, as, p) == CvarEntry.spec_loop(f, rest, as, p) : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def dcy.tog_f(f: Nat, -i: Nat, -rest: List<&2, Cv.Cmd>, -as: List<&2, Cv.Alias>, -p: List<&2, Nat>) -> {CvarEntry.spec_loop(f, Cv.CToggle{i} <> rest, as, p) == CvarEntry.spec_loop(f, rest, as, p) : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def dcy.and_swap(-a: Bool, -b: Bool, -w: Bool, e: {a == b : Bool}, h: {Bool.and(a, w) == True{} : Bool}) -> {Bool.and(b, w) == True{} : Bool}:
  %e : {Bool.and(_, w) == True{} : Bool}
  h

# the body's walk x ended with xs unless it is a cycle: the rest goes on
# from it
def dcy.after(x: Cv.Exp, +e: Nat, +rest: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>, +xs: List<&2, Cv.Cmd>, ne: {CvarEntry.spec_is_cycle(x) == False{} : Bool} -> {x == Cv.Flat{Cv.rev(xs, out)} : Cv.Exp}, ih: {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, Cv.Flat{Cv.rev(xs, out)})) == True{} : Bool}) -> {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, x)) == True{} : Bool}:
  match x:
    case Cv.Flat{+o}:
      %Equal.sym(Cv.Exp, Cv.Flat{o}, Cv.Flat{Cv.rev(xs, out)}, ne({==})) : {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, _)) == True{} : Bool}
      ih
    case Cv.Cycle{+k}:
      dcy.go_cyc(Cv.Cycle{k}, 1n+e, rest, as, {==})
    case Cv.Unknown{+k}:
      LA.pv.absurdF({CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, Cv.Unknown{k})) == True{} : Bool}, Equal.cong(Cv.Exp, Bool, z => dcy.isf(z), Cv.Unknown{k}, Cv.Flat{Cv.rev(xs, out)}, ne({==})))

# a run whose body loops (kon: n on the path; klb: off it), or ends with
# commands only before a rest that loops (kfl)
def dcy.cy_on(on: Bool, lb: Bool, eb: Maybe<&2, Cv.Exp>, lr: Bool, +x: Cv.Exp, +e: Nat, +rest: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, h: {CvarEntry.spec_loop.run(on, lb, eb, lr) == True{} : Bool}, kon: {on == True{} : Bool} -> {CvarEntry.spec_is_cycle(x) == True{} : Bool}, klb: {lb == True{} : Bool} -> {CvarEntry.spec_is_cycle(x) == True{} : Bool}, kfl: @xs: List<&2, Cv.Cmd> -> {eb == Some{Cv.Flat{xs}} : Maybe<&2, Cv.Exp>} -> {lr == True{} : Bool} -> {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, x)) == True{} : Bool}) -> {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, x)) == True{} : Bool}:
  match on:
    case True{}:
      dcy.go_cyc(x, 1n+e, rest, as, kon({==}))
    case False{}:
      match lb:
        case True{}:
          dcy.go_cyc(x, 1n+e, rest, as, klb({==}))
        case False{}:
          match eb:
            case None{}:
              LA.pv.absurdF({CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, x)) == True{} : Bool}, h)
            case Some{y}:
              match y:
                case Cv.Flat{+xs}:
                  kfl(xs, {==}, h)
                case Cv.Cycle{m}:
                  LA.pv.absurdF({CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, x)) == True{} : Bool}, h)
                case Cv.Unknown{m}:
                  LA.pv.absurdF({CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, x)) == True{} : Bool}, h)

# the body ended with the commands xs, the rest loops
def dcy.flat_case(+xs: List<&2, Cv.Cmd>, +g: Nat, +e: Nat, +n: Nat, +rest: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, +F: Nat, +k: Nat, +out: List<&2, Cv.Cmd>, hx: {CvarEntry.spec_exp(g, CvarEntry.spec_body(as, n), as, n <> p) == Some{Cv.Flat{xs}} : Maybe<&2, Cv.Exp>}, hr: {CvarEntry.spec_loop(1n+g, rest, as, p) == True{} : Bool}, hk: {F == Nat.add(k, 1n+g) : Nat}, hw: {dcy.W(F, as, p) == True{} : Bool}, rrest: @g2: Nat -> @o: List<&2, Cv.Cmd> -> {F == Nat.add(k, 1n+g2) : Nat} -> {Bool.and(CvarEntry.spec_loop(1n+g2, rest, as, p), dcy.W(F, as, p)) == True{} : Bool} -> {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, Cv.Flat{o})) == True{} : Bool}) -> {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, Cv.expand.go(e, CvarEntry.spec_body(as, n), as, Cv.Flat{out}))) == True{} : Bool}:
  +B = CvarEntry.spec_body(as, n)
  dcy.after(Cv.expand.go(e, B, as, Cv.Flat{out}), e, rest, as, out, xs, nc => dcy.dk(g, B, as, n <> p, out, Cv.Flat{xs}, hx, e, nc), rrest(g, Cv.rev(xs, out), hk, LA.pv.and_t(CvarEntry.spec_loop(1n+g, rest, as, p), dcy.W(F, as, p), hr, hw)))

# a run of n with levels left: the code walks n's body one level down
# (rre: n is on the path; rpush: n's body loops; rrest: the rest loops)
def dcy.cy_run(f: Nat, +e: Nat, +n: Nat, +rest: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, +F: Nat, +k: Nat, +out: List<&2, Cv.Cmd>, +hk: {F == Nat.add(k, f) : Nat}, hl: {CvarEntry.spec_loop(f, Cv.CRun{n} <> rest, as, p) == True{} : Bool}, +hw: {dcy.W(F, as, p) == True{} : Bool}, rre: {dcy.W(F, as, n <> dcy.suf(p, n)) == True{} : Bool} -> {CvarEntry.spec_is_cycle(Cv.expand.go(e, CvarEntry.spec_body(as, n), as, Cv.Flat{out})) == True{} : Bool}, rpush: @g2: Nat -> {F == Nat.add(1n+k, g2) : Nat} -> {Bool.and(CvarEntry.spec_loop(g2, CvarEntry.spec_body(as, n), as, n <> p), dcy.W(F, as, n <> p)) == True{} : Bool} -> {CvarEntry.spec_is_cycle(Cv.expand.go(e, CvarEntry.spec_body(as, n), as, Cv.Flat{out})) == True{} : Bool}, rrest: @g2: Nat -> @o: List<&2, Cv.Cmd> -> {F == Nat.add(k, 1n+g2) : Nat} -> {Bool.and(CvarEntry.spec_loop(1n+g2, rest, as, p), dcy.W(F, as, p)) == True{} : Bool} -> {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, Cv.Flat{o})) == True{} : Bool}) -> {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, Cv.expand.go(e, CvarEntry.spec_body(as, n), as, Cv.Flat{out}))) == True{} : Bool}:
  match f:
    case 0n:
      dcy.go_cyc(Cv.expand.go(e, CvarEntry.spec_body(as, n), as, Cv.Flat{out}), 1n+e, rest, as, rre(dcy.re(p, F, as, n, hl, hw)))
    case 1n++g:
      +B = CvarEntry.spec_body(as, n)
      dcy.cy_on(CvarEntry.spec_in(p, n), CvarEntry.spec_loop(g, B, as, n <> p), CvarEntry.spec_exp(g, B, as, n <> p), CvarEntry.spec_loop(1n+g, rest, as, p), Cv.expand.go(e, B, as, Cv.Flat{out}), e, rest, as, hl, hin => rre(dcy.re(p, F, as, n, hin, hw)), hlb => rpush(g, dcy.k_step(F, k, g, hk), dcy.push_w(g, F, k, n, as, p, hk, hlb, hw)), xs => hx => hr => dcy.flat_case(xs, g, e, n, rest, as, p, F, k, out, hx, hr, hk, hw, rrest))

# the loop of the body of the alias at the head of the path is also the
# head of the invariant on that path
def dcy.dup(+a: Bool, +w: Bool, +h: {Bool.and(a, w) == True{} : Bool}) -> {Bool.and(a, Bool.and(a, w)) == True{} : Bool}:
  LA.pv.and_t(a, Bool.and(a, w), LA.cvar.pv.and_l(a, w, h), h)

# the code's walk with any number d of levels left, of a nest whose
# unfolding (fuel f, k below the law's fuel F, path p) loops, is a cycle
def dcy.cy(d: Nat, cs: List<&2, Cv.Cmd>, +f: Nat, +as: List<&2, Cv.Alias>, +p: List<&2, Nat>, +F: Nat, +k: Nat, +out: List<&2, Cv.Cmd>, +hk: {F == Nat.add(k, f) : Nat}, +hlw: {Bool.and(CvarEntry.spec_loop(f, cs, as, p), dcy.W(F, as, p)) == True{} : Bool}) -> {CvarEntry.spec_is_cycle(Cv.expand.go(d, cs, as, Cv.Flat{out})) == True{} : Bool}:
  match d:
    case 0n:
      match cs:
        case Nil{}:
          dcy.nil_f(f, as, p, LA.cvar.pv.and_l(CvarEntry.spec_loop(f, Nil{}, as, p), dcy.W(F, as, p), hlw))
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              dcy.cy(0n, rest, f, as, p, F, k, Cv.CSet{i, v} <> out, hk, dcy.and_swap(CvarEntry.spec_loop(f, Cv.CSet{i, v} <> rest, as, p), CvarEntry.spec_loop(f, rest, as, p), dcy.W(F, as, p), dcy.set_f(f, i, v, rest, as, p), hlw))
            case Cv.CToggle{+i}:
              dcy.cy(0n, rest, f, as, p, F, k, Cv.CToggle{i} <> out, hk, dcy.and_swap(CvarEntry.spec_loop(f, Cv.CToggle{i} <> rest, as, p), CvarEntry.spec_loop(f, rest, as, p), dcy.W(F, as, p), dcy.tog_f(f, i, rest, as, p), hlw))
            case Cv.CRun{n}:
              {==}
            case Cv.CGone{+n}:
              dcy.gone_f(f, n, rest, as, p, LA.cvar.pv.and_l(CvarEntry.spec_loop(f, Cv.CGone{n} <> rest, as, p), dcy.W(F, as, p), hlw))
    case 1n++e:
      match cs:
        case Nil{}:
          dcy.nil_f(f, as, p, LA.cvar.pv.and_l(CvarEntry.spec_loop(f, Nil{}, as, p), dcy.W(F, as, p), hlw))
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              dcy.cy(1n+e, rest, f, as, p, F, k, Cv.CSet{i, v} <> out, hk, dcy.and_swap(CvarEntry.spec_loop(f, Cv.CSet{i, v} <> rest, as, p), CvarEntry.spec_loop(f, rest, as, p), dcy.W(F, as, p), dcy.set_f(f, i, v, rest, as, p), hlw))
            case Cv.CToggle{+i}:
              dcy.cy(1n+e, rest, f, as, p, F, k, Cv.CToggle{i} <> out, hk, dcy.and_swap(CvarEntry.spec_loop(f, Cv.CToggle{i} <> rest, as, p), CvarEntry.spec_loop(f, rest, as, p), dcy.W(F, as, p), dcy.tog_f(f, i, rest, as, p), hlw))
            case Cv.CRun{+n}:
              +B = CvarEntry.spec_body(as, n)
              %Equal.sym(List<&2, Cv.Cmd>, Cv.body(as, n), B, PAD.dp.body(as, n)) : {CvarEntry.spec_is_cycle(Cv.expand.go(1n+e, rest, as, Cv.expand.go(e, _, as, Cv.Flat{out}))) == True{} : Bool}
              dcy.cy_run(f, e, n, rest, as, p, F, k, out, hk, LA.cvar.pv.and_l(CvarEntry.spec_loop(f, Cv.CRun{n} <> rest, as, p), dcy.W(F, as, p), hlw), LA.cvar.pv.and_r(CvarEntry.spec_loop(f, Cv.CRun{n} <> rest, as, p), dcy.W(F, as, p), hlw), hq => dcy.cy(e, B, F, as, n <> dcy.suf(p, n), F, 0n, out, {==}, dcy.dup(CvarEntry.spec_loop(F, B, as, n <> dcy.suf(p, n)), dcy.W(F, as, dcy.suf(p, n)), hq)), g2 => hk2 => h2 => dcy.cy(e, B, g2, as, n <> p, F, 1n+k, out, hk2, h2), g2 => o => hk3 => h3 => dcy.cy(1n+e, rest, 1n+g2, as, p, F, k, o, hk3, h3))
            case Cv.CGone{+n}:
              dcy.gone_f(f, n, rest, as, p, LA.cvar.pv.and_l(CvarEntry.spec_loop(f, Cv.CGone{n} <> rest, as, p), dcy.W(F, as, p), hlw))

def CvarEntry.alias_endless_is_cycle(f, cs, as, loops):
  +Y = Cv.expand.go(1n+List.length(&2, Cv.Alias, as), cs, as, Cv.Flat{Nil{}})
  Equal.trans(Bool, CvarEntry.spec_is_cycle(Cv.fin(Y)), CvarEntry.spec_is_cycle(Y), True{}, dcy.fin_cyc(Y), dcy.cy(1n+List.length(&2, Cv.Alias, as), cs, f, as, Nil{}, f, 0n, Nil{}, {==}, LA.pv.and_t(CvarEntry.spec_loop(f, cs, as, Nil{}), True{}, loops, {==})))
