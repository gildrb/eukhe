# eukhe: the matcher's chars, leaves and capture helpers equal the spec's
# (laws/shape/match.bend R1-R4), one lemma each.

import Base
import ../../../bend/shape.bend as S
import ../../../bend/text_pat.bend as TP
import ../../../laws/shape/match.bend as Shape
import ../base.bend as LA

# Chars
# -----

def shl.rgs(rs: List<&2, S.Rg>, +x: U32) -> {S.in_rgs(rs, x) == Shape.sp_codes(rs, x) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case S.Rg{lo, hi}:
          %Equal.sym(Bool, S.in_rgs(t, x), Shape.sp_codes(t, x), shl.rgs(t, x)) : {Bool.or(S.in_range(x, lo, hi), _) == Shape.sp_codes(S.Rg{lo, hi} <> t, x) : Bool}
          {==}

def shl.set(st: S.Chars, +x: U32) -> {S.in_set(st, Chr{x}) == Shape.sp_names(st, x) : Bool}:
  match st:
    case S.Codes{rs}:
      shl.rgs(rs, x)
    case S.Space{}:
      {==}

def shl.swap_at(+x: U32, u: Bool, l: Bool) -> {S.swap.at(x, u, l) == Chr{Shape.sp_other.at(x, u, l)} : Char}:
  match u l:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def shl.fold(fold: Bool, +st: S.Chars, +x: U32) -> {S.is_in.fold(fold, st, Chr{x}) == Bool.and(fold, Shape.sp_names(st, Shape.sp_other(x))) : Bool}:
  match fold:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Char, S.swap(Chr{x}), Chr{Shape.sp_other(x)}, shl.swap_at(x, S.in_range(x, 65, 90), S.in_range(x, 97, 122))) : {S.in_set(st, _) == Shape.sp_names(st, Shape.sp_other(x)) : Bool}
      shl.set(st, Shape.sp_other(x))

# R1: the code's class test is the spec's
def shl.cls(k: S.Cls, c: Char) -> {S.is_in(k, c) == Shape.sp_cls(k, c) : Bool}:
  match k:
    case S.Cls{+st, neg, fold}:
      match c:
        case Chr{+x}:
          %Equal.sym(Bool, S.in_set(st, Chr{x}), Shape.sp_names(st, x), shl.set(st, x)) : {Bool.xor(neg, Bool.or(_, S.is_in.fold(fold, st, Chr{x}))) == Shape.sp_cls(S.Cls{st, neg, fold}, Chr{x}) : Bool}
          %Equal.sym(Bool, S.is_in.fold(fold, st, Chr{x}), Bool.and(fold, Shape.sp_names(st, Shape.sp_other(x))), shl.fold(fold, st, x)) : {Bool.xor(neg, Bool.or(Shape.sp_names(st, x), _)) == Shape.sp_cls(S.Cls{st, neg, fold}, Chr{x}) : Bool}
          {==}

# R2: the code's word chars are the spec's
def shl.word(c: Char) -> {S.is_word(c) == Shape.sp_word(c) : Bool}:
  match c:
    case Chr{v}:
      {==}

def shl.low_at(+x: U32, u: Bool) -> {S.low.at(x, u) == Chr{Shape.sp_other.at(x, u, False{})} : Char}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

# R4: chars compared as Lit and Fold ask
def shl.same(fold: Bool, x: Char, y: Char) -> {S.lit.same(fold, x, y) == Shape.sp_ch_eq(fold, x, y) : Bool}:
  match fold:
    case True{}:
      match x y:
        case Chr{+a} Chr{+b}:
          %Equal.sym(Char, S.low(Chr{a}), Chr{Shape.sp_small(a)}, shl.low_at(a, S.in_range(a, 65, 90))) : {Char.is_eq(_, S.low(Chr{b})) == Shape.sp_ch_eq(True{}, Chr{a}, Chr{b}) : Bool}
          %Equal.sym(Char, S.low(Chr{b}), Chr{Shape.sp_small(b)}, shl.low_at(b, S.in_range(b, 65, 90))) : {Char.is_eq(Chr{Shape.sp_small(a)}, _) == Shape.sp_ch_eq(True{}, Chr{a}, Chr{b}) : Bool}
          {==}
    case False{}:
      match x y:
        case Chr{a} Chr{b}:
          {==}

# Leaves
# ------

def shl.pred(n: Nat) -> {S.pred(n) == Shape.sp_dec(n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

# a lazy guard is the spec's guard
def shl.when(b: Bool, -X: List<&2, S.St>, -Y: List<&2, S.St>, h: {X == Y : List<&2, S.St>}) -> {S.when(b, k => X) == Shape.sp_if(b, Y) : List<&2, S.St>}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def shl.keep(b: Bool, s: S.St) -> {S.keep(b, s) == Shape.sp_if(b, [s]) : List<&2, S.St>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def shl.lit_go(u: String, +fold: Bool, rest: String, +pos: Nat, +left: Nat, word: Bool, caps: List<&2, Maybe<&2, S.Got>>) -> {S.lit.go(u, fold, rest, pos, left, word, caps) == Shape.sp_eat(u, fold, S.St{pos, left, word, rest, caps}) : List<&2, S.St>}:
  match u:
    case SNil{}:
      {==}
    case SCon{+y, +v}:
      match rest:
        case SNil{}:
          {==}
        case SCon{+x, +t}:
          %Equal.sym(Bool, S.lit.same(fold, x, y), Shape.sp_ch_eq(fold, x, y), shl.same(fold, x, y)) : {S.when(_, k => S.lit.go(v, fold, t, 1n+pos, S.pred(left), S.is_word(x), caps)) == Shape.sp_eat(SCon{y, v}, fold, S.St{pos, left, word, SCon{x, t}, caps}) : List<&2, S.St>}
          %Equal.sym(Bool, S.is_word(x), Shape.sp_word(x), shl.word(x)) : {S.when(Shape.sp_ch_eq(fold, x, y), k => S.lit.go(v, fold, t, 1n+pos, S.pred(left), _, caps)) == Shape.sp_eat(SCon{y, v}, fold, S.St{pos, left, word, SCon{x, t}, caps}) : List<&2, S.St>}
          %Equal.sym(Nat, S.pred(left), Shape.sp_dec(left), shl.pred(left)) : {S.when(Shape.sp_ch_eq(fold, x, y), k => S.lit.go(v, fold, t, 1n+pos, _, Shape.sp_word(x), caps)) == Shape.sp_eat(SCon{y, v}, fold, S.St{pos, left, word, SCon{x, t}, caps}) : List<&2, S.St>}
          shl.when(Shape.sp_ch_eq(fold, x, y), S.lit.go(v, fold, t, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps), Shape.sp_eat(v, fold, S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps}), shl.lit_go(v, fold, t, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps))

# R4: Lit and Fold
def shl.lit(u: String, fold: Bool, s: S.St) -> {S.lit(u, fold, s) == Shape.sp_eat(u, fold, s) : List<&2, S.St>}:
  match s:
    case S.St{pos, left, word, rest, caps}:
      shl.lit_go(u, fold, rest, pos, left, word, caps)

def shl.push(need: Nat, s: S.St, acc: List<&2, S.St>) -> {S.run.push(need, s, acc) == List.append(&2, S.St, Shape.sp_zero(need, s), acc) : List<&2, S.St>}:
  match need:
    case 0n:
      {==}
    case 1n+n:
      {==}

def shl.room(room: Maybe<&2, Nat>) -> {S.run.room(room) == Shape.sp_room(room) : Bool}:
  match room:
    case None{}:
      {==}
    case Some{n}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          {==}

def shl.less(room: Maybe<&2, Nat>) -> {S.run.less(room) == Shape.sp_less(room) : Maybe<&2, Nat>}:
  match room:
    case None{}:
      {==}
    case Some{n}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          {==}

# a guarded step of a run: taken, the readings past it then those here
def shl.or_else(b: Bool, -X: List<&2, S.St>, +Y: List<&2, S.St>, +Z: List<&2, S.St>, +acc: List<&2, S.St>, h: {X == List.append(&2, S.St, Y, List.append(&2, S.St, Z, acc)) : List<&2, S.St>}) -> {S.or_else(b, k => X, List.append(&2, S.St, Z, acc)) == List.append(&2, S.St, List.append(&2, S.St, Shape.sp_if(b, Y), Z), acc) : List<&2, S.St>}:
  match b:
    case True{}:
      %Equal.sym(List<&2, S.St>, X, List.append(&2, S.St, Y, List.append(&2, S.St, Z, acc)), h) : {_ == List.append(&2, S.St, List.append(&2, S.St, Y, Z), acc) : List<&2, S.St>}
      Equal.sym(List<&2, S.St>, List.append(&2, S.St, List.append(&2, S.St, Y, Z), acc), List.append(&2, S.St, Y, List.append(&2, S.St, Z, acc)), LA.shb.app_assoc(Y, Z, acc))
    case False{}:
      {==}

def shl.run_go(rest: String, +c: S.Cls, +need: Nat, +room: Maybe<&2, Nat>, +pos: Nat, +left: Nat, +word: Bool, +caps: List<&2, Maybe<&2, S.Got>>, +acc: List<&2, S.St>) -> {S.run.go(rest, c, need, room, pos, left, word, caps, acc) == List.append(&2, S.St, Shape.sp_run.go(rest, c, need, room, pos, left, word, caps), acc) : List<&2, S.St>}:
  match rest:
    case SNil{}:
      shl.push(need, S.St{pos, left, word, SNil{}, caps}, acc)
    case SCon{+x, +t}:
      +h = {S.St{pos, left, word, SCon{x, t}, caps} : S.St}
      +z = {Shape.sp_zero(need, h) : List<&2, S.St>}
      %Equal.sym(List<&2, S.St>, S.run.push(need, h, acc), List.append(&2, S.St, z, acc), shl.push(need, h, acc)) : {S.or_else(Bool.and(S.run.room(room), S.is_in(c, x)), k => S.run.go(t, c, S.pred(need), S.run.less(room), 1n+pos, S.pred(left), S.is_word(x), caps, _), _) == List.append(&2, S.St, Shape.sp_run.go(SCon{x, t}, c, need, room, pos, left, word, caps), acc) : List<&2, S.St>}
      %Equal.sym(Bool, S.run.room(room), Shape.sp_room(room), shl.room(room)) : {S.or_else(Bool.and(_, S.is_in(c, x)), k => S.run.go(t, c, S.pred(need), S.run.less(room), 1n+pos, S.pred(left), S.is_word(x), caps, List.append(&2, S.St, z, acc)), List.append(&2, S.St, z, acc)) == List.append(&2, S.St, Shape.sp_run.go(SCon{x, t}, c, need, room, pos, left, word, caps), acc) : List<&2, S.St>}
      %Equal.sym(Bool, S.is_in(c, x), Shape.sp_cls(c, x), shl.cls(c, x)) : {S.or_else(Bool.and(Shape.sp_room(room), _), k => S.run.go(t, c, S.pred(need), S.run.less(room), 1n+pos, S.pred(left), S.is_word(x), caps, List.append(&2, S.St, z, acc)), List.append(&2, S.St, z, acc)) == List.append(&2, S.St, Shape.sp_run.go(SCon{x, t}, c, need, room, pos, left, word, caps), acc) : List<&2, S.St>}
      %Equal.sym(Nat, S.pred(need), Shape.sp_dec(need), shl.pred(need)) : {S.or_else(Bool.and(Shape.sp_room(room), Shape.sp_cls(c, x)), k => S.run.go(t, c, _, S.run.less(room), 1n+pos, S.pred(left), S.is_word(x), caps, List.append(&2, S.St, z, acc)), List.append(&2, S.St, z, acc)) == List.append(&2, S.St, Shape.sp_run.go(SCon{x, t}, c, need, room, pos, left, word, caps), acc) : List<&2, S.St>}
      %Equal.sym(Maybe<&2, Nat>, S.run.less(room), Shape.sp_less(room), shl.less(room)) : {S.or_else(Bool.and(Shape.sp_room(room), Shape.sp_cls(c, x)), k => S.run.go(t, c, Shape.sp_dec(need), _, 1n+pos, S.pred(left), S.is_word(x), caps, List.append(&2, S.St, z, acc)), List.append(&2, S.St, z, acc)) == List.append(&2, S.St, Shape.sp_run.go(SCon{x, t}, c, need, room, pos, left, word, caps), acc) : List<&2, S.St>}
      %Equal.sym(Bool, S.is_word(x), Shape.sp_word(x), shl.word(x)) : {S.or_else(Bool.and(Shape.sp_room(room), Shape.sp_cls(c, x)), k => S.run.go(t, c, Shape.sp_dec(need), Shape.sp_less(room), 1n+pos, S.pred(left), _, caps, List.append(&2, S.St, z, acc)), List.append(&2, S.St, z, acc)) == List.append(&2, S.St, Shape.sp_run.go(SCon{x, t}, c, need, room, pos, left, word, caps), acc) : List<&2, S.St>}
      %Equal.sym(Nat, S.pred(left), Shape.sp_dec(left), shl.pred(left)) : {S.or_else(Bool.and(Shape.sp_room(room), Shape.sp_cls(c, x)), k => S.run.go(t, c, Shape.sp_dec(need), Shape.sp_less(room), 1n+pos, _, Shape.sp_word(x), caps, List.append(&2, S.St, z, acc)), List.append(&2, S.St, z, acc)) == List.append(&2, S.St, Shape.sp_run.go(SCon{x, t}, c, need, room, pos, left, word, caps), acc) : List<&2, S.St>}
      +y = {Shape.sp_run.go(t, c, Shape.sp_dec(need), Shape.sp_less(room), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps) : List<&2, S.St>}
      shl.or_else(Bool.and(Shape.sp_room(room), Shape.sp_cls(c, x)), S.run.go(t, c, Shape.sp_dec(need), Shape.sp_less(room), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps, List.append(&2, S.St, z, acc)), y, z, acc, shl.run_go(t, c, Shape.sp_dec(need), Shape.sp_less(room), 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps, List.append(&2, S.St, z, acc)))

# R4: Run
def shl.run(+c: S.Cls, +need: Nat, +room: Maybe<&2, Nat>, s: S.St) -> {S.run(c, need, room, s) == Shape.sp_run(c, need, room, s) : List<&2, S.St>}:
  match s:
    case S.St{+pos, +left, +word, +rest, +caps}:
      %LA.shb.app_nil(Shape.sp_run.go(rest, c, need, room, pos, left, word, caps)) : {S.run(c, need, room, S.St{pos, left, word, rest, caps}) == _ : List<&2, S.St>}
      shl.run_go(rest, c, need, room, pos, left, word, caps, Nil{})

def shl.same_go(n: Nat, from: String, rest: String, +pos: Nat, +left: Nat, word: Bool, caps: List<&2, Maybe<&2, S.Got>>) -> {S.same.go(n, from, rest, pos, left, word, caps) == Shape.sp_eat(String.take(from, n), False{}, S.St{pos, left, word, rest, caps}) : List<&2, S.St>}:
  match n:
    case 0n:
      match from:
        case SNil{}:
          {==}
        case SCon{y, f}:
          {==}
    case 1n+m:
      match from:
        case SNil{}:
          {==}
        case SCon{+y, +f}:
          match rest:
            case SNil{}:
              {==}
            case SCon{+x, +t}:
              %Equal.sym(Bool, S.is_word(x), Shape.sp_word(x), shl.word(x)) : {S.when(Char.is_eq(x, y), k => S.same.go(m, f, t, 1n+pos, S.pred(left), _, caps)) == Shape.sp_eat(String.take(SCon{y, f}, 1n+m), False{}, S.St{pos, left, word, SCon{x, t}, caps}) : List<&2, S.St>}
              %Equal.sym(Bool, Char.is_eq(x, y), Shape.sp_ch_eq(False{}, x, y), shl.same(False{}, x, y)) : {S.when(_, k => S.same.go(m, f, t, 1n+pos, S.pred(left), Shape.sp_word(x), caps)) == Shape.sp_eat(String.take(SCon{y, f}, 1n+m), False{}, S.St{pos, left, word, SCon{x, t}, caps}) : List<&2, S.St>}
              %Equal.sym(Nat, S.pred(left), Shape.sp_dec(left), shl.pred(left)) : {S.when(Shape.sp_ch_eq(False{}, x, y), k => S.same.go(m, f, t, 1n+pos, _, Shape.sp_word(x), caps)) == Shape.sp_eat(String.take(SCon{y, f}, 1n+m), False{}, S.St{pos, left, word, SCon{x, t}, caps}) : List<&2, S.St>}
              shl.when(Shape.sp_ch_eq(False{}, x, y), S.same.go(m, f, t, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps), Shape.sp_eat(String.take(f, m), False{}, S.St{1n+pos, Shape.sp_dec(left), Shape.sp_word(x), t, caps}), shl.same_go(m, f, t, 1n+pos, Shape.sp_dec(left), Shape.sp_word(x), caps))

def shl.same_got(g: Maybe<&2, Maybe<&2, S.Got>>, s: S.St) -> {S.same.got(g, s) == Shape.sp_same.at(Shape.sp_took.got(g), s) : List<&2, S.St>}:
  match g:
    case None{}:
      {==}
    case Some{c}:
      match c:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case S.Got{at, to, from}:
              match s:
                case S.St{pos, left, word, rest, caps}:
                  shl.same_go(Nat.sub(to, at), from, rest, pos, left, word, caps)

# R4: Same
def shl.same_k(k: Nat, s: S.St) -> {S.same(k, s) == Shape.sp_same(k, s) : List<&2, S.St>}:
  match k:
    case 0n:
      match s:
        case S.St{pos, left, word, rest, caps}:
          {==}
    case 1n+j:
      match s:
        case S.St{pos, left, word, rest, +caps}:
          shl.same_got(List.get(&2, Maybe<&2, S.Got>, caps, j), S.St{pos, left, word, rest, caps})

def shl.next_word(s: String) -> {S.next_word(s) == Shape.sp_starts_word(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, t}:
      shl.word(x)

# R4: Bound, Begin, End
def shl.bound(s: S.St) -> {S.bound(s) == Shape.sp_bound(s) : List<&2, S.St>}:
  match s:
    case S.St{+pos, left, +word, +rest, +caps}:
      %Equal.sym(Bool, S.next_word(rest), Shape.sp_starts_word(rest), shl.next_word(rest)) : {S.keep(Bool.xor(word, _), S.St{pos, left, word, rest, caps}) == Shape.sp_bound(S.St{pos, left, word, rest, caps}) : List<&2, S.St>}
      shl.keep(Bool.xor(word, Shape.sp_starts_word(rest)), S.St{pos, left, word, rest, caps})

def shl.begin(s: S.St) -> {S.begin(s) == Shape.sp_begin(s) : List<&2, S.St>}:
  match s:
    case S.St{+pos, left, word, rest, caps}:
      shl.keep(Nat.is_eq(pos, 0n), S.St{pos, left, word, rest, caps})

def shl.end(s: S.St) -> {S.end(s) == Shape.sp_end(s) : List<&2, S.St>}:
  match s:
    case S.St{pos, left, word, +rest, caps}:
      shl.keep(String.is_empty(rest), S.St{pos, left, word, rest, caps})

# Captures and the compound pieces' helpers
# -----------------------------------------

def shl.ncaps(ps: List<&2, S.Piece>) -> {S.ncaps(ps) == Shape.sp_ncaps(ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case p <> +t:
      match p:
        case S.Lit{u}:
          shl.ncaps(t)
        case S.Fold{u}:
          shl.ncaps(t)
        case S.Run{c, need, room}:
          shl.ncaps(t)
        case S.Cap{+i}:
          %Equal.sym(Nat, S.ncaps(i), Shape.sp_ncaps(i), shl.ncaps(i)) : {1n+Nat.add(_, S.ncaps(t)) == Shape.sp_ncaps(S.Cap{i} <> t) : Nat}
          %Equal.sym(Nat, S.ncaps(t), Shape.sp_ncaps(t), shl.ncaps(t)) : {1n+Nat.add(Shape.sp_ncaps(i), _) == Shape.sp_ncaps(S.Cap{i} <> t) : Nat}
          {==}
        case S.Opt{+i}:
          %Equal.sym(Nat, S.ncaps(i), Shape.sp_ncaps(i), shl.ncaps(i)) : {Nat.add(_, S.ncaps(t)) == Shape.sp_ncaps(S.Opt{i} <> t) : Nat}
          %Equal.sym(Nat, S.ncaps(t), Shape.sp_ncaps(t), shl.ncaps(t)) : {Nat.add(Shape.sp_ncaps(i), _) == Shape.sp_ncaps(S.Opt{i} <> t) : Nat}
          {==}
        case S.Alt{+a, +b}:
          %Equal.sym(Nat, S.ncaps(a), Shape.sp_ncaps(a), shl.ncaps(a)) : {Nat.add(Nat.add(_, S.ncaps(b)), S.ncaps(t)) == Shape.sp_ncaps(S.Alt{a, b} <> t) : Nat}
          %Equal.sym(Nat, S.ncaps(b), Shape.sp_ncaps(b), shl.ncaps(b)) : {Nat.add(Nat.add(Shape.sp_ncaps(a), _), S.ncaps(t)) == Shape.sp_ncaps(S.Alt{a, b} <> t) : Nat}
          %Equal.sym(Nat, S.ncaps(t), Shape.sp_ncaps(t), shl.ncaps(t)) : {Nat.add(Nat.add(Shape.sp_ncaps(a), Shape.sp_ncaps(b)), _) == Shape.sp_ncaps(S.Alt{a, b} <> t) : Nat}
          {==}
        case S.Many{+i, min}:
          %Equal.sym(Nat, S.ncaps(i), Shape.sp_ncaps(i), shl.ncaps(i)) : {Nat.add(_, S.ncaps(t)) == Shape.sp_ncaps(S.Many{i, min} <> t) : Nat}
          %Equal.sym(Nat, S.ncaps(t), Shape.sp_ncaps(t), shl.ncaps(t)) : {Nat.add(Shape.sp_ncaps(i), _) == Shape.sp_ncaps(S.Many{i, min} <> t) : Nat}
          {==}
        case S.Ahead{+i, neg}:
          %Equal.sym(Nat, S.ncaps(i), Shape.sp_ncaps(i), shl.ncaps(i)) : {Nat.add(_, S.ncaps(t)) == Shape.sp_ncaps(S.Ahead{i, neg} <> t) : Nat}
          %Equal.sym(Nat, S.ncaps(t), Shape.sp_ncaps(t), shl.ncaps(t)) : {Nat.add(Shape.sp_ncaps(i), _) == Shape.sp_ncaps(S.Ahead{i, neg} <> t) : Nat}
          {==}
        case S.Same{k}:
          shl.ncaps(t)
        case S.Bound{}:
          shl.ncaps(t)
        case S.Begin{}:
          shl.ncaps(t)
        case S.End{}:
          shl.ncaps(t)

def shl.close(xs: List<&2, S.St>, +k: Nat, +at: Nat, +from: String) -> {S.close(xs, k, at, from) == Shape.sp_cap(xs, k, at, from) : List<&2, S.St>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case S.St{+pos, left, word, rest, caps}:
          Equal.cong(List<&2, S.St>, List<&2, S.St>, r => S.St{pos, left, word, rest, List.set(&2, Maybe<&2, S.Got>, caps, k, Some{S.Got{at, pos, from}})} <> r, S.close(t, k, at, from), Shape.sp_cap(t, k, at, from), shl.close(t, k, at, from))

def shl.grew_if(b: Bool, x: S.St, +t: List<&2, S.St>) -> {S.grew.if(b, x, t) == List.append(&2, S.St, Shape.sp_if(b, [x]), t) : List<&2, S.St>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def shl.grew(+l: Nat, xs: List<&2, S.St>) -> {S.grew(l, xs) == Shape.sp_moved(l, xs) : List<&2, S.St>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case S.St{+pos, +left, +word, +rest, +caps}:
          %Equal.sym(List<&2, S.St>, S.grew(l, t), Shape.sp_moved(l, t), shl.grew(l, t)) : {S.grew.if(Nat.is_lt(left, l), S.St{pos, left, word, rest, caps}, _) == Shape.sp_moved(l, S.St{pos, left, word, rest, caps} <> t) : List<&2, S.St>}
          shl.grew_if(Nat.is_lt(left, l), S.St{pos, left, word, rest, caps}, Shape.sp_moved(l, t))

def shl.zero(min: Nat, s: S.St) -> {S.many.zero(min, s) == Shape.sp_zero(min, s) : List<&2, S.St>}:
  match min:
    case 0n:
      {==}
    case 1n+m:
      {==}

def shl.ahead(neg: Bool, xs: List<&2, S.St>, s: S.St) -> {S.ahead.if(neg, LA.shb.take1(xs), s) == Shape.sp_ahead(neg, xs, s) : List<&2, S.St>}:
  match neg:
    case True{}:
      match xs:
        case Nil{}:
          {==}
        case x <> t:
          {==}
    case False{}:
      match xs:
        case Nil{}:
          {==}
        case x <> t:
          {==}

def shl.remain(s: S.St) -> {S.remain(s) == Shape.sp_left(s) : Nat}:
  match s:
    case S.St{pos, left, word, rest, caps}:
      {==}

def shl.place(s: S.St) -> {S.place(s) == Shape.sp_pos(s) : Nat}:
  match s:
    case S.St{pos, left, word, rest, caps}:
      {==}

def shl.after(s: S.St) -> {S.after(s) == Shape.sp_text(s) : String}:
  match s:
    case S.St{pos, left, word, rest, caps}:
      {==}
