# eukhe: lemmas of the cvar expansion and press proofs: the model's body
# lookup against the laws' own name checks, and the laws' "sets only" test
# against the model's plain test.

import Base
import ../../../bend/cvar.bend as Cv
import ../../../laws/cvar/entry.bend as CvarEntry
import ../base.bend as LA

# not b holds: b is False
def ex.miss(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {False{} == b : Bool}:
  match b:
    case True{}:
      LA.pv.absurdF({False{} == True{} : Bool}, h)
    case False{}:
      {==}

# the body of n past aliases of other names, to the first alias named n
def ex.body_first(pre: List<&2, Cv.Alias>, +n: Nat, +b: List<&2, Cv.Cmd>, +post: List<&2, Cv.Alias>, +fresh: {CvarEntry.spec_no_alias(pre, n) == True{} : Bool}) -> {Cv.body(List.append(&2, Cv.Alias, pre, Cv.Alias{n, b} <> post), n) == b : List<&2, Cv.Cmd>}:
  match pre:
    case Nil{}:
      LA.pv.body_head(n, b, post)
    case Cv.Alias{+m, +c} <> +t:
      %ex.miss(Nat.is_eq(m, n), LA.cvar.pv.and_l(Bool.not(Nat.is_eq(m, n)), CvarEntry.spec_no_alias(t, n), fresh)) : {Cv.body.go(Cv.Alias{m, c} <> List.append(&2, Cv.Alias, t, Cv.Alias{n, b} <> post), n, _) == b : List<&2, Cv.Cmd>}
      ex.body_first(t, n, b, post, LA.cvar.pv.and_r(Bool.not(Nat.is_eq(m, n)), CvarEntry.spec_no_alias(t, n), fresh))

# the body of a name no alias has is the run of a missing alias
def ex.body_absent(as: List<&2, Cv.Alias>, +n: Nat, +none: {CvarEntry.spec_no_alias(as, n) == True{} : Bool}) -> {Cv.body(as, n) == [Cv.CGone{n}] : List<&2, Cv.Cmd>}:
  match as:
    case Nil{}:
      {==}
    case Cv.Alias{+m, +c} <> +t:
      %ex.miss(Nat.is_eq(m, n), LA.cvar.pv.and_l(Bool.not(Nat.is_eq(m, n)), CvarEntry.spec_no_alias(t, n), none)) : {Cv.body.go(Cv.Alias{m, c} <> t, n, _) == [Cv.CGone{n}] : List<&2, Cv.Cmd>}
      ex.body_absent(t, n, LA.cvar.pv.and_r(Bool.not(Nat.is_eq(m, n)), CvarEntry.spec_no_alias(t, n), none))

# a list that only sets or toggles is plain
def ex.plain(cs: List<&2, Cv.Cmd>, h: {CvarEntry.spec_sets_only(cs) == True{} : Bool}) -> {Cv.plain(cs) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> rest:
      match c:
        case Cv.CSet{i, v}:
          ex.plain(rest, h)
        case Cv.CToggle{i}:
          ex.plain(rest, h)
        case Cv.CRun{n}:
          LA.pv.absurdF({Cv.plain(Cv.CRun{n} <> rest) == True{} : Bool}, h)
        case Cv.CGone{n}:
          LA.pv.absurdF({Cv.plain(Cv.CGone{n} <> rest) == True{} : Bool}, h)

# Maybe
# -----

def ex.If(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# a claim that None is Some proves anything
def ex.none_some(-A: Data, -x: A, -G: Type, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %e : ex.If(A, _, G)
  Unit{}

def ex.some_inj(-A: Data, -x: A, -y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, x), Some{x}, Some{y}, e)

# The laws' alias lookup against the model's body
# -----------------------------------------------

def ex.body_go(as: List<&2, Cv.Alias>, +n: Nat, +c: List<&2, Cv.Cmd>, hit: Bool, eh: {Cv.name.at(as, n) == hit : Bool}, h: {CvarEntry.spec_alias(as, n) == Some{c} : Maybe<&2, List<&2, Cv.Cmd>>}) -> {Cv.body.go(as, n, hit) == c : List<&2, Cv.Cmd>}:
  match as:
    case Nil{}:
      ex.none_some(List<&2, Cv.Cmd>, c, {Cv.body.go(Nil{}, n, hit) == c : List<&2, Cv.Cmd>}, h)
    case Cv.Alias{+m, +d} <> +t:
      match hit:
        case True{}:
          +r = CvarEntry.spec_alias(t, n)
          ex.some_inj(List<&2, Cv.Cmd>, d, c, Equal.trans(Maybe<&2, List<&2, Cv.Cmd>>, Some{d}, CvarEntry.spec_alias.pick(Nat.is_eq(m, n), d, r), Some{c}, Equal.cong(Bool, Maybe<&2, List<&2, Cv.Cmd>>, z => CvarEntry.spec_alias.pick(z, d, r), True{}, Nat.is_eq(m, n), Equal.sym(Bool, Nat.is_eq(m, n), True{}, eh)), h))
        case False{}:
          +r = CvarEntry.spec_alias(t, n)
          ex.body_go(t, n, c, Cv.name.at(t, n), {==}, Equal.trans(Maybe<&2, List<&2, Cv.Cmd>>, r, CvarEntry.spec_alias.pick(Nat.is_eq(m, n), d, r), Some{c}, Equal.cong(Bool, Maybe<&2, List<&2, Cv.Cmd>>, z => CvarEntry.spec_alias.pick(z, d, r), False{}, Nat.is_eq(m, n), Equal.sym(Bool, Nat.is_eq(m, n), False{}, eh)), h))

# the body the laws read for n is the model's body of n
def ex.body_of(+as: List<&2, Cv.Alias>, +n: Nat, +c: List<&2, Cv.Cmd>, h: {CvarEntry.spec_alias(as, n) == Some{c} : Maybe<&2, List<&2, Cv.Cmd>>}) -> {Cv.body(as, n) == c : List<&2, Cv.Cmd>}:
  ex.body_go(as, n, c, Cv.name.at(as, n), {==}, h)

# Expansions
# ----------

# sets and toggles first: they go onto the accumulator, at any depth
def ex.go_app(ps: List<&2, Cv.Cmd>, k: Nat, +rest: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>, h: {CvarEntry.spec_sets_only(ps) == True{} : Bool}) -> {Cv.expand.go(k, List.append(&2, Cv.Cmd, ps, rest), as, Cv.Flat{out}) == Cv.expand.go(k, rest, as, Cv.Flat{Cv.rev(ps, out)}) : Cv.Exp}:
  match ps:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case Cv.CSet{+i, +v}:
          match k:
            case 0n:
              ex.go_app(t, 0n, rest, as, Cv.CSet{i, v} <> out, h)
            case 1n+e:
              ex.go_app(t, 1n+e, rest, as, Cv.CSet{i, v} <> out, h)
        case Cv.CToggle{+i}:
          match k:
            case 0n:
              ex.go_app(t, 0n, rest, as, Cv.CToggle{i} <> out, h)
            case 1n+e:
              ex.go_app(t, 1n+e, rest, as, Cv.CToggle{i} <> out, h)
        case Cv.CRun{n}:
          LA.pv.absurdF({Cv.expand.go(k, List.append(&2, Cv.Cmd, Cv.CRun{n} <> t, rest), as, Cv.Flat{out}) == Cv.expand.go(k, rest, as, Cv.Flat{Cv.rev(Cv.CRun{n} <> t, out)}) : Cv.Exp}, h)
        case Cv.CGone{n}:
          LA.pv.absurdF({Cv.expand.go(k, List.append(&2, Cv.Cmd, Cv.CGone{n} <> t, rest), as, Cv.Flat{out}) == Cv.expand.go(k, rest, as, Cv.Flat{Cv.rev(Cv.CGone{n} <> t, out)}) : Cv.Exp}, h)

# a cycle stops the expansion: nothing after it is looked at
def ex.go_cyc(k: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +m: Nat) -> {Cv.expand.go(k, cs, as, Cv.Cycle{m}) == Cv.Cycle{m} : Cv.Exp}:
  match k:
    case 0n:
      match cs:
        case Nil{}:
          {==}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              {==}
            case Cv.CToggle{i}:
              {==}
            case Cv.CRun{n}:
              {==}
            case Cv.CGone{n}:
              {==}
    case 1n+e:
      match cs:
        case Nil{}:
          {==}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              {==}
            case Cv.CToggle{i}:
              {==}
            case Cv.CRun{n}:
              {==}
            case Cv.CGone{n}:
              {==}

# Cycles through a closed set of names
# ------------------------------------

# n is x, or one of rest: either way its alias runs into ns
def ex.closed_pick(hit: Bool, +x: Nat, +rest: List<&2, Nat>, +as: List<&2, Cv.Alias>, +ns: List<&2, Nat>, +n: Nat, eh: {Nat.is_eq(x, n) == hit : Bool}, ca: {CvarEntry.spec_runs_into.at(CvarEntry.spec_alias(as, x), ns) == True{} : Bool}, mem: {Bool.or(hit, CvarEntry.spec_in(rest, n)) == True{} : Bool}, ih: {CvarEntry.spec_in(rest, n) == True{} : Bool} -> {CvarEntry.spec_runs_into.at(CvarEntry.spec_alias(as, n), ns) == True{} : Bool}) -> {CvarEntry.spec_runs_into.at(CvarEntry.spec_alias(as, n), ns) == True{} : Bool}:
  match hit:
    case True{}:
      %LA.pv.eq_true(x, n, eh) : {CvarEntry.spec_runs_into.at(CvarEntry.spec_alias(as, _), ns) == True{} : Bool}
      ca
    case False{}:
      ih(mem)

# a name of a closed set has an alias that runs into the set
def ex.closed_at(xs: List<&2, Nat>, +as: List<&2, Cv.Alias>, +ns: List<&2, Nat>, +n: Nat, +cl: {CvarEntry.spec_closed(as, xs, ns) == True{} : Bool}, mem: {CvarEntry.spec_in(xs, n) == True{} : Bool}) -> {CvarEntry.spec_runs_into.at(CvarEntry.spec_alias(as, n), ns) == True{} : Bool}:
  match xs:
    case Nil{}:
      LA.pv.absurdF({CvarEntry.spec_runs_into.at(CvarEntry.spec_alias(as, n), ns) == True{} : Bool}, mem)
    case +x <> +rest:
      +a = CvarEntry.spec_runs_into.at(CvarEntry.spec_alias(as, x), ns)
      +b = CvarEntry.spec_closed(as, rest, ns)
      ex.closed_pick(Nat.is_eq(x, n), x, rest, as, ns, n, {==}, LA.cvar.pv.and_l(a, b, cl), mem, h => ex.closed_at(rest, as, ns, n, LA.cvar.pv.and_r(a, b, cl), h))

# the hypothesis on one level less: every alias of ns, on any accumulator,
# expands to a cycle named in ns (nothing to assume at depth 0)
def ex.IH(d: Nat, as: List<&2, Cv.Alias>, ns: List<&2, Nat>) -> Type:
  match d:
    case 0n:
      Unit
    case 1n+e:
      @m: Nat -> @o: List<&2, Cv.Cmd> -> {CvarEntry.spec_in(ns, m) == True{} : Bool} -> {CvarEntry.spec_cycle_in(Cv.expand.go(e, Cv.body(as, m), as, Cv.Flat{o}), ns) == True{} : Bool}

# a cycle named in ns, met as the accumulator, is the outcome
def ex.keep_in(r: Cv.Exp, k: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +ns: List<&2, Nat>, h: {CvarEntry.spec_cycle_in(r, ns) == True{} : Bool}) -> {CvarEntry.spec_cycle_in(Cv.expand.go(k, cs, as, r), ns) == True{} : Bool}:
  match r:
    case Cv.Flat{o}:
      LA.pv.absurdF({CvarEntry.spec_cycle_in(Cv.expand.go(k, cs, as, Cv.Flat{o}), ns) == True{} : Bool}, h)
    case Cv.Cycle{+m}:
      %Equal.sym(Cv.Exp, Cv.expand.go(k, cs, as, Cv.Cycle{m}), Cv.Cycle{m}, ex.go_cyc(k, cs, as, m)) : {CvarEntry.spec_cycle_in(_, ns) == True{} : Bool}
      h
    case Cv.Unknown{m}:
      LA.pv.absurdF({CvarEntry.spec_cycle_in(Cv.expand.go(k, cs, as, Cv.Unknown{m}), ns) == True{} : Bool}, h)

# a body that runs into ns, at depth d: its sets go onto the accumulator,
# then the run of an alias of ns is a cycle (depth 0) or that alias's
# expansion one level down (the hypothesis), a cycle named in ns
def ex.walk(c: List<&2, Cv.Cmd>, d: Nat, +as: List<&2, Cv.Alias>, +ns: List<&2, Nat>, +out: List<&2, Cv.Cmd>, hl: {CvarEntry.spec_runs_into(c, ns) == True{} : Bool}, ih: ex.IH(d, as, ns)) -> {CvarEntry.spec_cycle_in(Cv.expand.go(d, c, as, Cv.Flat{out}), ns) == True{} : Bool}:
  match c:
    case Nil{}:
      LA.pv.absurdF({CvarEntry.spec_cycle_in(Cv.expand.go(d, Nil{}, as, Cv.Flat{out}), ns) == True{} : Bool}, hl)
    case x <> rest:
      match x:
        case Cv.CSet{+i, +v}:
          match d:
            case 0n:
              ex.walk(rest, 0n, as, ns, Cv.CSet{i, v} <> out, hl, ih)
            case 1n+e:
              ex.walk(rest, 1n+e, as, ns, Cv.CSet{i, v} <> out, hl, ih)
        case Cv.CToggle{+i}:
          match d:
            case 0n:
              ex.walk(rest, 0n, as, ns, Cv.CToggle{i} <> out, hl, ih)
            case 1n+e:
              ex.walk(rest, 1n+e, as, ns, Cv.CToggle{i} <> out, hl, ih)
        case Cv.CRun{+m}:
          match d:
            case 0n:
              hl
            case 1n++e:
              ex.keep_in(Cv.expand.go(e, Cv.body(as, m), as, Cv.Flat{out}), 1n+e, rest, as, ns, ih(m, out, hl))
        case Cv.CGone{m}:
          LA.pv.absurdF({CvarEntry.spec_cycle_in(Cv.expand.go(d, Cv.CGone{m} <> rest, as, Cv.Flat{out}), ns) == True{} : Bool}, hl)

# the alias of a name of ns, at depth d, given its laws' body
def ex.inv_at(mb: Maybe<&2, List<&2, Cv.Cmd>>, d: Nat, +as: List<&2, Cv.Alias>, +ns: List<&2, Nat>, +n: Nat, +out: List<&2, Cv.Cmd>, em: {CvarEntry.spec_alias(as, n) == mb : Maybe<&2, List<&2, Cv.Cmd>>}, hl: {CvarEntry.spec_runs_into.at(mb, ns) == True{} : Bool}, ih: ex.IH(d, as, ns)) -> {CvarEntry.spec_cycle_in(Cv.expand.go(d, Cv.body(as, n), as, Cv.Flat{out}), ns) == True{} : Bool}:
  match mb:
    case None{}:
      LA.pv.absurdF({CvarEntry.spec_cycle_in(Cv.expand.go(d, Cv.body(as, n), as, Cv.Flat{out}), ns) == True{} : Bool}, hl)
    case Some{+c}:
      %Equal.sym(List<&2, Cv.Cmd>, Cv.body(as, n), c, ex.body_of(as, n, c, em)) : {CvarEntry.spec_cycle_in(Cv.expand.go(d, _, as, Cv.Flat{out}), ns) == True{} : Bool}
      ex.walk(c, d, as, ns, out, hl, ih)

# the alias of any name of a closed ns expands, at any depth and onto any
# accumulator, to a cycle named in ns
def ex.inv(d: Nat, +as: List<&2, Cv.Alias>, +ns: List<&2, Nat>, +n: Nat, +out: List<&2, Cv.Cmd>, +cl: {CvarEntry.spec_closed(as, ns, ns) == True{} : Bool}, mem: {CvarEntry.spec_in(ns, n) == True{} : Bool}) -> {CvarEntry.spec_cycle_in(Cv.expand.go(d, Cv.body(as, n), as, Cv.Flat{out}), ns) == True{} : Bool}:
  match d:
    case 0n:
      ex.inv_at(CvarEntry.spec_alias(as, n), 0n, as, ns, n, out, {==}, ex.closed_at(ns, as, ns, n, cl, mem), Unit{})
    case 1n++e:
      ex.inv_at(CvarEntry.spec_alias(as, n), 1n+e, as, ns, n, out, {==}, ex.closed_at(ns, as, ns, n, cl, mem), m => o => h => ex.inv(e, as, ns, m, o, cl, h))

# fin keeps a cycle and its name
def ex.fin_in(e: Cv.Exp, +ns: List<&2, Nat>) -> {CvarEntry.spec_cycle_in(Cv.fin(e), ns) == CvarEntry.spec_cycle_in(e, ns) : Bool}:
  match e:
    case Cv.Flat{o}:
      {==}
    case Cv.Cycle{n}:
      {==}
    case Cv.Unknown{n}:
      {==}
