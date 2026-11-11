# eukhe: lemmas of the proofs of area mcp_url: a host whose first word w
# (`f` then w1, then `:`) the model refuses whatever the other seven words
# are, is refused whatever follows the `:` (m6.go): it reads as itself up
# to the `:`, is no IPv4 quad (its first part starts with `f`), and every
# way the model splits it into words starts with w or is malformed.

import Base
import ../../../bend/mcp_url.bend as Mu
import ../../../laws/mcp_url.bend as McpUrl
import ./text.bend as LT

# w's chars pushed onto the halves of what follows w
def m6.pw(w: String, h: Mu.Halves) -> Mu.Halves:
  match w:
    case SNil{}:
      h
    case SCon{c, t}:
      Mu.halves.push(c, m6.pw(t, h))

def m6.pw_one(w: String, +a: String) -> {m6.pw(w, Mu.One{a}) == Mu.One{String.append(w, a)} : Mu.Halves}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Mu.Halves, m6.pw(t, Mu.One{a}), Mu.One{String.append(t, a)}, m6.pw_one(t, a)) : {Mu.halves.push(c, _) == Mu.One{SCon{c, String.append(t, a)}} : Mu.Halves}
      {==}

def m6.pw_two(w: String, +a: String, +b: String) -> {m6.pw(w, Mu.Two{a, b}) == Mu.Two{String.append(w, a), b} : Mu.Halves}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Mu.Halves, m6.pw(t, Mu.Two{a, b}), Mu.Two{String.append(t, a), b}, m6.pw_two(t, a, b)) : {Mu.halves.push(c, _) == Mu.Two{SCon{c, String.append(t, a)}, b} : Mu.Halves}
      {==}

# the first word w of a host, its value W: what the model does with w
def m6.F(+w1: String, +W: U32) -> Type:
  (@r: String -> {Mu.drop_open(String.append(SCon{'f', w1}, r)) == String.append(SCon{'f', w1}, r) : String}) & ((@r: String -> {String.to_lower(String.append(SCon{'f', w1}, r)) == String.append(SCon{'f', w1}, String.to_lower(r)) : String}) & ((@y: String -> {Mu.halves(String.append(SCon{'f', w1}, y)) == m6.pw(SCon{'f', w1}, Mu.halves(y)) : Mu.Halves}) & ((@a: String -> {String.split(String.append(SCon{'f', w1}, SCon{':', a}), ':') == SCon{'f', w1} <> String.split(a, ':') : List<&2, String>}) & ({String.split(SCon{'f', w1}, ':') == [SCon{'f', w1}] : List<&2, String>} & ({Mu.word(SCon{'f', w1}) == Some{W} : Maybe<&2, U32>} & ((@a1: U32 -> @a2: U32 -> @a3: U32 -> @a4: U32 -> @a5: U32 -> @a6: U32 -> @a7: U32 -> {Mu.v6.check(W, a1, a2, a3, a4, a5, a6, a7) == True{} : Bool}) & (@r: String -> {String.contains(String.append(SCon{'f', w1}, SCon{':', r}), ":") == True{} : Bool})))))))

# eight words that start with W are refused
def m6.vw(+W: U32, L: List<&2, U32>, ck: @a1: U32 -> @a2: U32 -> @a3: U32 -> @a4: U32 -> @a5: U32 -> @a6: U32 -> @a7: U32 -> {Mu.v6.check(W, a1, a2, a3, a4, a5, a6, a7) == True{} : Bool}) -> {Mu.v6.words(W <> L) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case w1 <> t1:
      match t1:
        case Nil{}:
          {==}
        case w2 <> t2:
          match t2:
            case Nil{}:
              {==}
            case w3 <> t3:
              match t3:
                case Nil{}:
                  {==}
                case w4 <> t4:
                  match t4:
                    case Nil{}:
                      {==}
                    case w5 <> t5:
                      match t5:
                        case Nil{}:
                          {==}
                        case w6 <> t6:
                          match t6:
                            case Nil{}:
                              {==}
                            case w7 <> t7:
                              match t7:
                                case Nil{}:
                                  ck(w1)(w2)(w3)(w4)(w5)(w6)(w7)
                                case x <> t8:
                                  {==}

# W then the words of the rest, if any: refused
def m6.cons(m: Maybe<&2, List<&2, U32>>, +W: U32, ck: @a1: U32 -> @a2: U32 -> @a3: U32 -> @a4: U32 -> @a5: U32 -> @a6: U32 -> @a7: U32 -> {Mu.v6.check(W, a1, a2, a3, a4, a5, a6, a7) == True{} : Bool}) -> {Mu.v6.of(Mu.words.cons(Some{W}, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      m6.vw(W, x, ck)

# W then the words of the rest, the zeros and the words after `::`: refused
def m6.join(m1: Maybe<&2, List<&2, U32>>, +z: List<&2, U32>, m2: Maybe<&2, List<&2, U32>>, +W: U32, ck: @a1: U32 -> @a2: U32 -> @a3: U32 -> @a4: U32 -> @a5: U32 -> @a6: U32 -> @a7: U32 -> {Mu.v6.check(W, a1, a2, a3, a4, a5, a6, a7) == True{} : Bool}) -> {Mu.v6.of(Mu.join3(Mu.words.cons(Some{W}, m1), z, m2)) == True{} : Bool}:
  match m1:
    case None{}:
      {==}
    case Some{x}:
      match m2:
        case None{}:
          {==}
        case Some{y}:
          m6.vw(W, List.append(&2, U32, x, List.append(&2, U32, z, y)), ck)

# `::` in the address, w the first part before it
def m6.two_at(b: Bool, +P: List<&2, String>, +Q: List<&2, String>, +n: Nat, +w1: String, +W: U32, g6: {Mu.word(SCon{'f', w1}) == Some{W} : Maybe<&2, U32>}, ck: @a1: U32 -> @a2: U32 -> @a3: U32 -> @a4: U32 -> @a5: U32 -> @a6: U32 -> @a7: U32 -> {Mu.v6.check(W, a1, a2, a3, a4, a5, a6, a7) == True{} : Bool}) -> {Mu.v6.of(Mu.expand.two.at(b, SCon{'f', w1} <> P, Q, n)) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Maybe<&2, U32>, Mu.word(SCon{'f', w1}), Some{W}, g6) : {Mu.v6.of(Mu.join3(Mu.words.cons(_, Mu.words(P)), Mu.zeros(Nat.sub(8n, n)), Mu.words(Q))) == True{} : Bool}
      m6.join(Mu.words(P), Mu.zeros(Nat.sub(8n, n)), Mu.words(Q), W, ck)

# no `::`, w the first part
def m6.one_at(b: Bool, +P: List<&2, String>, +w1: String, +W: U32, g6: {Mu.word(SCon{'f', w1}) == Some{W} : Maybe<&2, U32>}, ck: @a1: U32 -> @a2: U32 -> @a3: U32 -> @a4: U32 -> @a5: U32 -> @a6: U32 -> @a7: U32 -> {Mu.v6.check(W, a1, a2, a3, a4, a5, a6, a7) == True{} : Bool}) -> {Mu.v6.of(Mu.expand.one.at(b, SCon{'f', w1} <> P)) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Maybe<&2, U32>, Mu.word(SCon{'f', w1}), Some{W}, g6) : {Mu.v6.of(Mu.words.cons(_, Mu.words(P))) == True{} : Bool}
      m6.cons(Mu.words(P), W, ck)

# the halves of w then `:` and R, by whether R starts with `:`
def m6.hal(g: Bool, +R: String, H: Mu.Halves, +w1: String, +W: U32, g4: @a: String -> {String.split(String.append(SCon{'f', w1}, SCon{':', a}), ':') == SCon{'f', w1} <> String.split(a, ':') : List<&2, String>}, g5: {String.split(SCon{'f', w1}, ':') == [SCon{'f', w1}] : List<&2, String>}, g6: {Mu.word(SCon{'f', w1}) == Some{W} : Maybe<&2, U32>}, ck: @a1: U32 -> @a2: U32 -> @a3: U32 -> @a4: U32 -> @a5: U32 -> @a6: U32 -> @a7: U32 -> {Mu.v6.check(W, a1, a2, a3, a4, a5, a6, a7) == True{} : Bool}) -> {Mu.v6.of(Mu.expand.of(m6.pw(SCon{'f', w1}, Mu.halves.at(g, ':', R, H)))) == True{} : Bool}:
  match g:
    case True{}:
      +w = {SCon{'f', w1} : String}
      +D = String.drop(R, 1n)
      %Equal.sym(Mu.Halves, m6.pw(w, Mu.Two{SNil{}, D}), Mu.Two{String.append(w, SNil{}), D}, m6.pw_two(w, SNil{}, D)) : {Mu.v6.of(Mu.expand.of(_)) == True{} : Bool}
      %Equal.sym(String, String.append(w, SNil{}), w, LT.mt.app_nil(w)) : {Mu.v6.of(Mu.expand.of(Mu.Two{_, D})) == True{} : Bool}
      %Equal.sym(List<&2, String>, String.split(w, ':'), [w], g5) : {Mu.v6.of(Mu.expand.two(_, Mu.side(D))) == True{} : Bool}
      m6.two_at(Nat.is_le(Nat.add(1n, List.length(&2, String, Mu.side(D))), 7n), [], Mu.side(D), Nat.add(1n, List.length(&2, String, Mu.side(D))), w1, W, g6, ck)
    case False{}:
      match H:
        case Mu.One{+a}:
          +w = {SCon{'f', w1} : String}
          %Equal.sym(Mu.Halves, m6.pw(w, Mu.One{SCon{':', a}}), Mu.One{String.append(w, SCon{':', a})}, m6.pw_one(w, SCon{':', a})) : {Mu.v6.of(Mu.expand.of(_)) == True{} : Bool}
          %Equal.sym(List<&2, String>, String.split(String.append(w, SCon{':', a}), ':'), w <> String.split(a, ':'), g4(a)) : {Mu.v6.of(Mu.expand.one(_)) == True{} : Bool}
          m6.one_at(Bool.and(Nat.is_eq(List.length(&2, String, w <> String.split(a, ':')), 8n), Bool.not(Mu.any_empty(w <> String.split(a, ':')))), String.split(a, ':'), w1, W, g6, ck)
        case Mu.Two{+a, +b}:
          +w = {SCon{'f', w1} : String}
          %Equal.sym(Mu.Halves, m6.pw(w, Mu.Two{SCon{':', a}, b}), Mu.Two{String.append(w, SCon{':', a}), b}, m6.pw_two(w, SCon{':', a}, b)) : {Mu.v6.of(Mu.expand.of(_)) == True{} : Bool}
          %Equal.sym(List<&2, String>, String.split(String.append(w, SCon{':', a}), ':'), w <> String.split(a, ':'), g4(a)) : {Mu.v6.of(Mu.expand.two(_, Mu.side(b))) == True{} : Bool}
          +n = Nat.add(List.length(&2, String, w <> String.split(a, ':')), List.length(&2, String, Mu.side(b)))
          m6.two_at(Nat.is_le(n, 7n), String.split(a, ':'), Mu.side(b), n, w1, W, g6, ck)

# a host that starts with a char `f` is no IPv4 quad
def m6.nov4(ps: List<&2, String>) -> {Mu.v4.parts(String.split.push('f', ps)) == Mu.V4No{} : Mu.V4}:
  match ps:
    case Nil{}:
      {==}
    case p <> t1:
      match t1:
        case Nil{}:
          {==}
        case q <> t2:
          match t2:
            case Nil{}:
              {==}
            case r <> t3:
              match t3:
                case Nil{}:
                  {==}
                case s <> t4:
                  match t4:
                    case Nil{}:
                      {==}
                    case x <> t5:
                      {==}

def m6.at(g: Bool, +s: String, e: {Mu.after_v4(Mu.v4(s), s) == True{} : Bool}) -> {Mu.refused.at(g, s) == True{} : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      e

def m6.after(+s: String, +R: String, +w1: String, +W: U32, e1: {Mu.V4No{} == Mu.v4(s) : Mu.V4}, e2: {True{} == String.contains(s, ":") : Bool}, e3: {m6.pw(SCon{'f', w1}, Mu.halves(SCon{':', R})) == Mu.halves(s) : Mu.Halves}, h: {Mu.v6.of(Mu.expand.of(m6.pw(SCon{'f', w1}, Mu.halves(SCon{':', R})))) == True{} : Bool}) -> {Mu.after_v4(Mu.v4(s), s) == True{} : Bool}:
  %e1 : {Mu.after_v4(_, s) == True{} : Bool}
  %e2 : {Mu.v6(_, s) == True{} : Bool}
  %e3 : {Mu.v6.of(Mu.expand.of(_)) == True{} : Bool}
  h

# the host w `:` rest is refused
def m6.go(+w1: String, +W: U32, +rest: String, F: m6.F(w1, W)) -> {Mu.refused(String.append(SCon{'f', w1}, SCon{':', rest})) == True{} : Bool}:
  (g1, F1) = F
  (g2, F2) = F1
  (g3, F3) = F2
  (g4, F4) = F3
  (g5, F5) = F4
  (g6, F6) = F5
  (g7, g8) = F6
  +w = {SCon{'f', w1} : String}
  +I = String.append(w, SCon{':', rest})
  +R = String.to_lower(Mu.drop_close(rest))
  +s = String.append(w, SCon{':', R})
  +EB = Equal.trans(String, Mu.bare(I), String.to_lower(Mu.drop_close(I)), s, Equal.cong(String, String, z => String.to_lower(Mu.drop_close(z)), Mu.drop_open(I), I, g1(SCon{':', rest})), Equal.trans(String, String.to_lower(Mu.drop_close(I)), String.to_lower(String.append(w, SCon{':', Mu.drop_close(rest)})), s, Equal.cong(String, String, z => String.to_lower(z), Mu.drop_close(I), String.append(w, SCon{':', Mu.drop_close(rest)}), LT.mt.dca(w, SCon{':', rest}, {==})), g2(SCon{':', Mu.drop_close(rest)})))
  %Equal.sym(String, Mu.bare(I), s, EB) : {Mu.refused.at(Bool.or(String.eq(_, "localhost"), String.ends_with(_, ".localhost")), _) == True{} : Bool}
  +e1 = Equal.sym(Mu.V4, Mu.v4(s), Mu.V4No{}, m6.nov4(String.split(String.append(w1, SCon{':', R}), '.')))
  +e2 = Equal.sym(Bool, String.contains(s, ":"), True{}, g8(R))
  +e3 = Equal.sym(Mu.Halves, Mu.halves(s), m6.pw(w, Mu.halves(SCon{':', R})), g3(SCon{':', R}))
  +AF = m6.after(s, R, w1, W, e1, e2, e3, m6.hal(String.starts_with(R, ":"), R, Mu.halves(R), w1, W, g4, g5, g6, g7))
  m6.at(Bool.or(String.eq(s, "localhost"), String.ends_with(s, ".localhost")), s, AF)
