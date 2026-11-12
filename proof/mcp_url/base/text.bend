# eukhe: lemmas of the proofs of area mcp_url: logic, and what the model's
# bracket drops (Mu.drop_open, Mu.drop_close), Base's lowercasing and
# reversal do to a text and what follows it (mt.*).

import Base
import ../../../bend/mcp_url.bend as Mu
import ../../../laws/mcp_url.bend as McpUrl

# Logic
# -----

def mt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def mt.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : mt.BD(_, Unit, G)
  Unit{}

def mt.absurdF(-G: Type, e: {False{} == True{} : Bool}) -> G:
  mt.absurd(G, Equal.sym(Bool, False{}, True{}, e))

def mt.SD(s: String, t: Type, f: Type) -> Type:
  match s:
    case SNil{}:
      t
    case SCon{x, r}:
      f

# the empty text is no text with a char
def mt.nil_cons(-G: Type, -x: Char, -r: String, e: {SNil{} == SCon{x, r} : String}) -> G:
  %e : mt.SD(_, Unit, G)
  Unit{}

def mt.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def mt.and_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      mt.absurdF({b == True{} : Bool}, e)

def mt.or_fl(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

def mt.or_fr(a: Bool, b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      mt.absurd({b == False{} : Bool}, e)
    case False{}:
      e

def mt.not_t(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      mt.absurdF({True{} == False{} : Bool}, e)
    case False{}:
      {==}

# no Nat is below 0
def mt.lt_zero(-G: Type, p: Nat, h: {Nat.is_lt(p, 0n) == True{} : Bool}) -> G:
  match p:
    case 0n:
      mt.absurdF(G, h)
    case 1n+q:
      mt.absurdF(G, h)

# Texts
# -----

def mt.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.cong(String, String, z => SCon{c, z}, String.append(t, SNil{}), t, mt.app_nil(t))

# a text with a char after anything holds a char
def mt.ne_app(x: String, -y: String, ne: {String.is_empty(y) == False{} : Bool}) -> {String.is_empty(String.append(x, y)) == False{} : Bool}:
  match x:
    case SNil{}:
      ne
    case SCon{c, t}:
      {==}

# the reverse of a then b is the reverse of b after that of a
def mt.rev_app(a: String, +b: String, +acc: String) -> {String.reverse.go(String.append(a, b), acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      mt.rev_app(t, b, SCon{h, acc})

# lowercasing a then b lowercases each
def mt.tl_app(x: String, +y: String) -> {String.to_lower(String.append(x, y)) == String.append(String.to_lower(x), String.to_lower(y)) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      Equal.cong(String, String, z => SCon{Char.to_lower(c), z}, String.to_lower(String.append(r, y)), String.append(String.to_lower(r), String.to_lower(y)), mt.tl_app(r, y))

# Brackets
# --------

def mt.do_app.at(g: Bool, +y: Char, +r: String, +z: String, ih: {Mu.drop_open(String.append(r, z)) == String.append(Mu.drop_open(r), z) : String}) -> {Mu.drop_open.at(g, y, String.append(r, z), Mu.drop_open(String.append(r, z))) == String.append(Mu.drop_open.at(g, y, r, Mu.drop_open(r)), z) : String}:
  match g:
    case True{}:
      ih
    case False{}:
      {==}

# the leading `[`s of x then a text that starts with no `[`: x's dropped
def mt.do_app(x: String, +c: Char, +t: String, hc: {Char.is_eq(c, '[') == False{} : Bool}) -> {Mu.drop_open(String.append(x, SCon{c, t})) == String.append(Mu.drop_open(x), SCon{c, t}) : String}:
  match x:
    case SNil{}:
      %Equal.sym(Bool, Char.is_eq(c, '['), False{}, hc) : {Mu.drop_open.at(_, c, t, Mu.drop_open(t)) == SCon{c, t} : String}
      {==}
    case SCon{+y, +r}:
      mt.do_app.at(Char.is_eq(y, '['), y, r, SCon{c, t}, mt.do_app(r, c, t, hc))

# a char before a text with a char is kept
def mt.dc_at(g: Bool, R: String, +c: Char, ne: {String.is_empty(R) == False{} : Bool}) -> {Mu.drop_close.at(g, c, R) == SCon{c, R} : String}:
  match g:
    case False{}:
      {==}
    case True{}:
      match R:
        case SNil{}:
          mt.absurd({Mu.drop_close.at(True{}, c, SNil{}) == SCon{c, SNil{}} : String}, ne)
        case SCon{x, u}:
          {==}

# the trailing `]`s of x then y are y's when y keeps a char
def mt.dca(x: String, +y: String, +ne: {String.is_empty(Mu.drop_close(y)) == False{} : Bool}) -> {Mu.drop_close(String.append(x, y)) == String.append(x, Mu.drop_close(y)) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      Equal.trans(String, Mu.drop_close.at(Char.is_eq(c, ']'), c, Mu.drop_close(String.append(r, y))), Mu.drop_close.at(Char.is_eq(c, ']'), c, String.append(r, Mu.drop_close(y))), SCon{c, String.append(r, Mu.drop_close(y))}, Equal.cong(String, String, z => Mu.drop_close.at(Char.is_eq(c, ']'), c, z), Mu.drop_close(String.append(r, y)), String.append(r, Mu.drop_close(y)), mt.dca(r, y, ne)), mt.dc_at(Char.is_eq(c, ']'), String.append(r, Mu.drop_close(y)), c, mt.ne_app(r, Mu.drop_close(y), ne)))

# one more trailing `]` is dropped too
def mt.dc_snoc(x: String) -> {Mu.drop_close(String.append(x, SCon{']', SNil{}})) == Mu.drop_close(x) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      Equal.cong(String, String, z => Mu.drop_close.at(Char.is_eq(c, ']'), c, z), Mu.drop_close(String.append(r, SCon{']', SNil{}})), Mu.drop_close(r), mt.dc_snoc(r))

# The verdict of a host read as another
# -------------------------------------

# hosts read alike get one verdict
def mt.same(+h1: String, +h2: String, e: {Mu.bare(h1) == Mu.bare(h2) : String}) -> {Mu.refused(h1) == Mu.refused(h2) : Bool}:
  %Equal.sym(String, Mu.bare(h1), Mu.bare(h2), e) : {Mu.refused.at(Bool.or(String.eq(_, "localhost"), String.ends_with(_, ".localhost")), _) == Mu.refused(h2) : Bool}
  {==}
