# eukhe: lemmas of the proofs of area codemode_describe: a tool's namespace
# and the tools shown
#
# A tool's namespace: the model's single pass (Dsc.best) is the first
# longest of the spec's hits (cd.best). The tools shown: the model keeps
# only the queues still in, the spec flags each group in or out; a round of
# the model over the queues in is the spec's round over all groups
# (cdsel.round), so the rounds agree (cdsel.rounds), from the first queues
# (cdsel.lives).

import Base
import ../../bend/codemode_describe.bend as Dsc
import ../../laws/codemode_describe.bend as CodemodeDescribe

# ---- logic ----

def cd.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def cd.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : cd.BT(_, G)
  Unit{}

# ---- a tool's namespace ----

def cd.longer(b: Bool, i: Nat, n: Nat, j: Nat, m: Nat) -> {Dsc.best.at(b, i, n, j, m) == Some{CodemodeDescribe.longer_of(b, Dsc.Hit{i, n}, Dsc.Hit{j, m})} : Maybe<&2, Dsc.Hit>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cd.of(+i: Nat, +n: Nat, l: Maybe<&2, Dsc.Hit>) -> {Dsc.best.of(i, n, l) == Some{CodemodeDescribe.longest_first(Dsc.Hit{i, n}, l)} : Maybe<&2, Dsc.Hit>}:
  match l:
    case None{}:
      {==}
    case Some{y}:
      match y:
        case Dsc.Hit{j, +m}:
          cd.longer(Nat.is_lt(n, m), i, n, j, m)

def cd.pick(b: Bool, +i: Nat, +n: Nat, hs: List<&2, Dsc.Hit>, -l: Maybe<&2, Dsc.Hit>, e: {l == CodemodeDescribe.longest_spec(hs) : Maybe<&2, Dsc.Hit>}) -> {Dsc.best.pick(b, i, n, l) == CodemodeDescribe.longest_spec(CodemodeDescribe.hit_one(b, i, n, hs)) : Maybe<&2, Dsc.Hit>}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Dsc.Hit>, l, CodemodeDescribe.longest_spec(hs), e) : {Dsc.best.of(i, n, _) == Some{CodemodeDescribe.longest_first(Dsc.Hit{i, n}, CodemodeDescribe.longest_spec(hs))} : Maybe<&2, Dsc.Hit>}
      cd.of(i, n, CodemodeDescribe.longest_spec(hs))
    case False{}:
      e

# the model's longest prefix is the first longest of the spec's hits
def cd.best(ps: List<&2, String>, +name: String, +i: Nat) -> {Dsc.best(ps, name, i) == CodemodeDescribe.longest_spec(CodemodeDescribe.hits_spec(ps, name, i)) : Maybe<&2, Dsc.Hit>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      cd.pick(String.starts_with(name, p), i, String.length(p), CodemodeDescribe.hits_spec(r, name, 1n+i), Dsc.best(r, name, 1n+i), cd.best(r, name, 1n+i))

def cd.index(m: Maybe<&2, Dsc.Hit>) -> {Dsc.space.index(m) == CodemodeDescribe.hit_index(m) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{h}:
      match h:
        case Dsc.Hit{i, n}:
          {==}

# a tool's namespace is the spec's
def cd.space(+name: String, +ps: List<&2, String>) -> {Dsc.space_of(name, ps) == CodemodeDescribe.space_spec(name, ps) : Maybe<&2, Nat>}:
  %cd.best(ps, name, 0n) : {Dsc.space.index(Dsc.best(ps, name, 0n)) == CodemodeDescribe.hit_index(_) : Maybe<&2, Nat>}
  cd.index(Dsc.best(ps, name, 0n))

# ---- the queues ----

def cd.sel_at(b: Bool, x: Dsc.Item, h: Dsc.Item, t: List<&2, Dsc.Item>, l: List<&2, Dsc.Item>) -> {Dsc.cheap.sel(b, x, h, t, l) == CodemodeDescribe.by_cost_at(b, x, h, t, l) : List<&2, Dsc.Item>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cd.put(x: Dsc.Item, xs: List<&2, Dsc.Item>) -> {Dsc.cheap.insert(x, xs) == CodemodeDescribe.by_cost_put(x, xs) : List<&2, Dsc.Item>}:
  match x:
    case Dsc.Item{+a, +c}:
      match xs:
        case Nil{}:
          {==}
        case Con{h, +t}:
          match h:
            case Dsc.Item{+b, +d}:
              %cd.put(Dsc.Item{a, c}, t) : {Dsc.cheap.sel(Nat.is_le(c, d), Dsc.Item{a, c}, Dsc.Item{b, d}, t, Dsc.cheap.insert(Dsc.Item{a, c}, t)) == CodemodeDescribe.by_cost_at(Nat.is_le(c, d), Dsc.Item{a, c}, Dsc.Item{b, d}, t, _) : List<&2, Dsc.Item>}
              cd.sel_at(Nat.is_le(c, d), Dsc.Item{a, c}, Dsc.Item{b, d}, t, Dsc.cheap.insert(Dsc.Item{a, c}, t))

# a group's queue is the spec's
def cd.cheap(xs: List<&2, Dsc.Item>) -> {Dsc.cheap(xs) == CodemodeDescribe.by_cost(xs) : List<&2, Dsc.Item>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %cd.cheap(r) : {Dsc.cheap.insert(x, Dsc.cheap(r)) == CodemodeDescribe.by_cost_put(x, _) : List<&2, Dsc.Item>}
      cd.put(x, Dsc.cheap(r))

# ---- a round ----

# the queues of the groups still in
def cdsel.live(fs: List<&2, CodemodeDescribe.Live>) -> List<&2, List<&2, Dsc.Item>>:
  match fs:
    case Nil{}:
      []
    case Con{f, r}:
      match f:
        case CodemodeDescribe.Live{on, q}:
          match on:
            case True{}:
              q <> cdsel.live(r)
            case False{}:
              cdsel.live(r)

def cdsel.cons(xs: List<&2, List<&2, Dsc.Item>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      True{}

# the model's round result o is the spec's round t: the queues in, the
# budget left and the tools placed, and the spec's flag says a queue is in
def cdsel.Rel(o: Dsc.Out, t: CodemodeDescribe.Turn) -> Type:
  match t:
    case CodemodeDescribe.Turn{fs, left, placed, any}:
      {o == Dsc.Out{cdsel.live(fs), left, placed} : Dsc.Out} & {any == cdsel.cons(cdsel.live(fs)) : Bool}

def cdsel.off(q: List<&2, Dsc.Item>, t: CodemodeDescribe.Turn, -o: Dsc.Out, h: cdsel.Rel(o, t)) -> cdsel.Rel(o, CodemodeDescribe.out_before(q, t)):
  match t:
    case CodemodeDescribe.Turn{fs, left, placed, any}:
      h

def cdsel.keep.nil(x: Nat, t: CodemodeDescribe.Turn, -o: Dsc.Out, h: cdsel.Rel(o, t)) -> cdsel.Rel(Dsc.round.keep([], x, o), CodemodeDescribe.placed_before([], x, t)):
  match t:
    case CodemodeDescribe.Turn{+fs, +left, +placed, +any}:
      (e1, e2) = h
      %Equal.sym(Dsc.Out, o, Dsc.Out{cdsel.live(fs), left, placed}, e1) : cdsel.Rel(Dsc.round.keep([], x, _), CodemodeDescribe.placed_before([], x, CodemodeDescribe.Turn{fs, left, placed, any}))
      ({==}, e2)

def cdsel.keep.con(y: Dsc.Item, u: List<&2, Dsc.Item>, x: Nat, t: CodemodeDescribe.Turn, -o: Dsc.Out, h: cdsel.Rel(o, t)) -> cdsel.Rel(Dsc.round.keep(Con{y, u}, x, o), CodemodeDescribe.placed_before(Con{y, u}, x, t)):
  match t:
    case CodemodeDescribe.Turn{+fs, +left, +placed, +any}:
      (e1, e2) = h
      %Equal.sym(Dsc.Out, o, Dsc.Out{cdsel.live(fs), left, placed}, e1) : cdsel.Rel(Dsc.round.keep(Con{y, u}, x, _), CodemodeDescribe.placed_before(Con{y, u}, x, CodemodeDescribe.Turn{fs, left, placed, any}))
      ({==}, {==})

def cdsel.keep(rest: List<&2, Dsc.Item>, x: Nat, t: CodemodeDescribe.Turn, -o: Dsc.Out, h: cdsel.Rel(o, t)) -> cdsel.Rel(Dsc.round.keep(rest, x, o), CodemodeDescribe.placed_before(rest, x, t)):
  match rest:
    case Nil{}:
      cdsel.keep.nil(x, t, o, h)
    case Con{y, u}:
      cdsel.keep.con(y, u, x, t, o, h)

def cdsel.on(b: Bool, t: Nat, +c: Nat, rest: List<&2, Dsc.Item>, +r: List<&2, CodemodeDescribe.Live>, +rem: Nat, ihp: cdsel.Rel(Dsc.round(cdsel.live(r), Dsc.fits(cdsel.live(r), Nat.sub(rem, c)), Nat.sub(rem, c)), CodemodeDescribe.turn(r, CodemodeDescribe.head_fits(r, Nat.sub(rem, c)), Nat.sub(rem, c))), ihd: cdsel.Rel(Dsc.round(cdsel.live(r), Dsc.fits(cdsel.live(r), rem), rem), CodemodeDescribe.turn(r, CodemodeDescribe.head_fits(r, rem), rem))) -> cdsel.Rel(Dsc.round(Con{Con{Dsc.Item{t, c}, rest}, cdsel.live(r)}, b, rem), CodemodeDescribe.turn(Con{CodemodeDescribe.Live{True{}, Con{Dsc.Item{t, c}, rest}}, r}, b, rem)):
  match b:
    case True{}:
      cdsel.keep(rest, t, CodemodeDescribe.turn(r, CodemodeDescribe.head_fits(r, Nat.sub(rem, c)), Nat.sub(rem, c)), Dsc.round(cdsel.live(r), Dsc.fits(cdsel.live(r), Nat.sub(rem, c)), Nat.sub(rem, c)), ihp)
    case False{}:
      cdsel.off(Con{Dsc.Item{t, c}, rest}, CodemodeDescribe.turn(r, CodemodeDescribe.head_fits(r, rem), rem), Dsc.round(cdsel.live(r), Dsc.fits(cdsel.live(r), rem), rem), ihd)

# a model round over the queues in is the spec's round over every group
def cdsel.round(fs: List<&2, CodemodeDescribe.Live>, +rem: Nat) -> cdsel.Rel(Dsc.round(cdsel.live(fs), Dsc.fits(cdsel.live(fs), rem), rem), CodemodeDescribe.turn(fs, CodemodeDescribe.head_fits(fs, rem), rem)):
  match fs:
    case Nil{}:
      ({==}, {==})
    case Con{f, +r}:
      match f:
        case CodemodeDescribe.Live{on, q}:
          match on:
            case False{}:
              cdsel.off(q, CodemodeDescribe.turn(r, CodemodeDescribe.head_fits(r, rem), rem), Dsc.round(cdsel.live(r), Dsc.fits(cdsel.live(r), rem), rem), cdsel.round(r, rem))
            case True{}:
              match q:
                case Nil{}:
                  cdsel.off([], CodemodeDescribe.turn(r, CodemodeDescribe.head_fits(r, rem), rem), Dsc.round(cdsel.live(r), Dsc.fits(cdsel.live(r), rem), rem), cdsel.round(r, rem))
                case Con{x, rest}:
                  match x:
                    case Dsc.Item{t, +c}:
                      cdsel.on(Nat.is_le(c, rem), t, c, rest, r, rem, cdsel.round(r, Nat.sub(rem, c)), cdsel.round(r, rem))

# ---- the rounds ----

def cdsel.rounds_at(g: Nat, l: List<&2, List<&2, Dsc.Item>>, -fs: List<&2, CodemodeDescribe.Live>, +left: Nat, placed: List<&2, Nat>, any: Bool, ea: {any == cdsel.cons(l) : Bool}, el: {l == cdsel.live(fs) : List<&2, List<&2, Dsc.Item>>}, ih: {Dsc.rounds(g, Dsc.round(cdsel.live(fs), Dsc.fits(cdsel.live(fs), left), left)) == CodemodeDescribe.turns(g, CodemodeDescribe.turn(fs, CodemodeDescribe.head_fits(fs, left), left)) : List<&2, Nat>}) -> {Dsc.rounds(1n+g, Dsc.Out{l, left, placed}) == CodemodeDescribe.turns(1n+g, CodemodeDescribe.Turn{fs, left, placed, any}) : List<&2, Nat>}:
  match l:
    case Nil{}:
      %Equal.sym(Bool, any, False{}, ea) : {Dsc.rounds(1n+g, Dsc.Out{[], left, placed}) == CodemodeDescribe.turns(1n+g, CodemodeDescribe.Turn{fs, left, placed, _}) : List<&2, Nat>}
      {==}
    case Con{q, r}:
      %Equal.sym(Bool, any, True{}, ea) : {Dsc.rounds(1n+g, Dsc.Out{Con{q, r}, left, placed}) == CodemodeDescribe.turns(1n+g, CodemodeDescribe.Turn{fs, left, placed, _}) : List<&2, Nat>}
      %Equal.sym(List<&2, List<&2, Dsc.Item>>, Con{q, r}, cdsel.live(fs), el) : {List.append(&2, Nat, placed, Dsc.rounds(g, Dsc.round(_, Dsc.fits(_, left), left))) == List.append(&2, Nat, placed, CodemodeDescribe.turns(g, CodemodeDescribe.turn(fs, CodemodeDescribe.head_fits(fs, left), left))) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => List.append(&2, Nat, placed, z), Dsc.rounds(g, Dsc.round(cdsel.live(fs), Dsc.fits(cdsel.live(fs), left), left)), CodemodeDescribe.turns(g, CodemodeDescribe.turn(fs, CodemodeDescribe.head_fits(fs, left), left)), ih)

# the model's rounds from a round result are the spec's from its round
def cdsel.rounds(f: Nat, t: CodemodeDescribe.Turn, -o: Dsc.Out, h: cdsel.Rel(o, t)) -> {Dsc.rounds(f, o) == CodemodeDescribe.turns(f, t) : List<&2, Nat>}:
  match f:
    case 0n:
      {==}
    case 1n++g:
      match t:
        case CodemodeDescribe.Turn{+fs, +left, placed, any}:
          (e1, e2) = h
          %Equal.sym(Dsc.Out, o, Dsc.Out{cdsel.live(fs), left, placed}, e1) : {Dsc.rounds(1n+g, _) == CodemodeDescribe.turns(1n+g, CodemodeDescribe.Turn{fs, left, placed, any}) : List<&2, Nat>}
          cdsel.rounds_at(g, cdsel.live(fs), fs, left, placed, any, e2, {==}, cdsel.rounds(g, CodemodeDescribe.turn(fs, CodemodeDescribe.head_fits(fs, left), left), Dsc.round(cdsel.live(fs), Dsc.fits(cdsel.live(fs), left), left), cdsel.round(fs, left)))

# ---- the first queues ----

def cdsel.queues(gs: List<&2, List<&2, Dsc.Item>>) -> {Dsc.queues(gs) == cdsel.live(CodemodeDescribe.lives(gs)) : List<&2, List<&2, Dsc.Item>>}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +r}:
      match g:
        case Nil{}:
          cdsel.queues(r)
        case Con{+x, +t}:
          %cdsel.queues(r) : {Dsc.cheap(Con{x, t}) <> Dsc.queues(r) == CodemodeDescribe.by_cost(Con{x, t}) <> _ : List<&2, List<&2, Dsc.Item>>}
          %cd.cheap(Con{x, t}) : {Dsc.cheap(Con{x, t}) <> Dsc.queues(r) == _ <> Dsc.queues(r) : List<&2, List<&2, Dsc.Item>>}
          {==}

def cdsel.any(gs: List<&2, List<&2, Dsc.Item>>) -> {CodemodeDescribe.any_on(CodemodeDescribe.lives(gs)) == cdsel.cons(cdsel.live(CodemodeDescribe.lives(gs))) : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +r}:
      match g:
        case Nil{}:
          cdsel.any(r)
        case Con{x, t}:
          {==}

def cdsel.total(gs: List<&2, List<&2, Dsc.Item>>) -> {Dsc.total(gs) == CodemodeDescribe.count(gs) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +r}:
      %cdsel.total(r) : {Nat.add(List.length(&2, Dsc.Item, g), Dsc.total(r)) == Nat.add(List.length(&2, Dsc.Item, g), _) : Nat}
      {==}

# the tools shown are the spec's
def cdsel.select(+gs: List<&2, List<&2, Dsc.Item>>, +budget: Nat) -> {Dsc.select(gs, budget) == CodemodeDescribe.select_spec(gs, budget) : List<&2, Nat>}:
  +fs = CodemodeDescribe.lives(gs)
  %cdsel.total(gs) : {Dsc.rounds(1n+Dsc.total(gs), Dsc.Out{Dsc.queues(gs), budget, []}) == CodemodeDescribe.turns(1n+_, CodemodeDescribe.Turn{fs, budget, [], CodemodeDescribe.any_on(fs)}) : List<&2, Nat>}
  cdsel.rounds(1n+Dsc.total(gs), CodemodeDescribe.Turn{fs, budget, [], CodemodeDescribe.any_on(fs)}, Dsc.Out{Dsc.queues(gs), budget, []}, (Equal.cong(List<&2, List<&2, Dsc.Item>>, Dsc.Out, z => Dsc.Out{z, budget, []}, Dsc.queues(gs), cdsel.live(fs), cdsel.queues(gs)), cdsel.any(gs)))
