# eukhe: lemmas of the proofs of area redirect_input: logic, the list
# facts of append and reverse, and the model's drop of noise chars (rt.*).

import Base
import ../../../bend/redirect_input.bend as Ri
import ../../../bend/gateway_answer.bend as Ga
import ../../../laws/redirect_input.bend as RedirectInput

# Logic
# -----

def rt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def rt.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : rt.BD(_, Unit, G)
  Unit{}

def rt.absurdF(-G: Type, e: {False{} == True{} : Bool}) -> G:
  rt.absurd(G, Equal.sym(Bool, False{}, True{}, e))

def rt.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def rt.and_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      rt.absurdF({b == True{} : Bool}, e)

def rt.and_t(+a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def rt.or_fl(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

def rt.or_fr(a: Bool, b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      rt.absurd({b == False{} : Bool}, e)
    case False{}:
      e

def rt.not_t(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      rt.absurdF({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def rt.not_f(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      rt.absurd({Bool.not(True{}) == True{} : Bool}, e)
    case False{}:
      {==}

# Strings
# -------

def rt.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.cong(String, String, z => SCon{c, z}, String.append(t, SNil{}), t, rt.app_nil(t))

def rt.app_assoc(a: String, +b: String, +c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      Equal.cong(String, String, z => SCon{x, z}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), rt.app_assoc(t, b, c))

# reverse.go keeps what is after its accumulator
def rt.rev_go(s: String, +a: String, +b: String) -> {String.reverse.go(s, String.append(a, b)) == String.append(String.reverse.go(s, a), b) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rt.rev_go(t, SCon{h, a}, b)

def rt.rev_acc(+s: String, +a: String) -> {String.reverse.go(s, a) == String.append(String.reverse(s), a) : String}:
  rt.rev_go(s, SNil{}, a)

def rt.rev_snoc(s: String, +w: Char, +a: String) -> {String.reverse.go(String.append(s, SCon{w, SNil{}}), a) == SCon{w, String.reverse.go(s, a)} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rt.rev_snoc(t, w, SCon{h, a})

def rt.rev_rev(s: String) -> {String.reverse(String.reverse(s)) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(String, String.reverse.go(t, SCon{h, SNil{}}), String.append(String.reverse(t), SCon{h, SNil{}}), rt.rev_acc(t, SCon{h, SNil{}})) : {String.reverse(_) == SCon{h, t} : String}
      %Equal.sym(String, String.reverse.go(String.append(String.reverse(t), SCon{h, SNil{}}), SNil{}), SCon{h, String.reverse(String.reverse(t))}, rt.rev_snoc(String.reverse(t), h, SNil{})) : {_ == SCon{h, t} : String}
      Equal.cong(String, String, z => SCon{h, z}, String.reverse(String.reverse(t)), t, rt.rev_rev(t))

# the reverse of a then b is the reverse of b then that of a
def rt.rev_app(a: String, +b: String, +acc: String) -> {String.reverse.go(String.append(a, b), acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rt.rev_app(t, b, SCon{h, acc})


# a noise char anywhere is dropped
def rt.compact_drop(a: String, +x: Char, +b: String, n: {RedirectInput.ri_noise(x) == True{} : Bool}) -> {Ri.compact(String.append(a, SCon{x, b})) == Ri.compact(String.append(a, b)) : String}:
  match a:
    case SNil{}:
      %Equal.sym(Bool, RedirectInput.ri_noise(x), True{}, n) : {Ri.compact.at(_, x, Ri.compact(b)) == Ri.compact(b) : String}
      {==}
    case SCon{+c, +t}:
      Equal.cong(String, String, z => Ri.compact.at(Bool.or(Ga.space(c), Ri.zero_width(c)), c, z), Ri.compact(String.append(t, SCon{x, b})), Ri.compact(String.append(t, b)), rt.compact_drop(t, x, b, n))

# a char that is no noise is kept
def rt.compact_keep(+w: Char, +s: String, nn: {RedirectInput.ri_noise(w) == False{} : Bool}) -> {Ri.compact(SCon{w, s}) == SCon{w, Ri.compact(s)} : String}:
  %Equal.sym(Bool, RedirectInput.ri_noise(w), False{}, nn) : {Ri.compact.at(_, w, Ri.compact(s)) == SCon{w, Ri.compact(s)} : String}
  {==}

def rt.cat_at(g: Bool, +c: Char, +r: String, +q: String) -> {Ri.compact.at(g, c, String.append(r, q)) == String.append(Ri.compact.at(g, c, r), q) : String}:
  match g:
    case True{}:
      {==}
    case False{}:
      {==}

def rt.compact_app(a: String, +b: String) -> {Ri.compact(String.append(a, b)) == String.append(Ri.compact(a), Ri.compact(b)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ri.compact(String.append(t, b)), String.append(Ri.compact(t), Ri.compact(b)), rt.compact_app(t, b)) : {Ri.compact.at(Bool.or(Ga.space(c), Ri.zero_width(c)), c, _) == String.append(Ri.compact.at(Bool.or(Ga.space(c), Ri.zero_width(c)), c, Ri.compact(t)), Ri.compact(b)) : String}
      rt.cat_at(Bool.or(Ga.space(c), Ri.zero_width(c)), c, Ri.compact(t), Ri.compact(b))

def rt.ne_app(x: String, +z: Char, -t: String) -> {String.is_empty(String.append(x, SCon{z, t})) == False{} : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, r}:
      {==}

# the reverse of a text with a char is no empty text
def rt.rev_ne(+z: Char, +t: String) -> {String.is_empty(String.reverse(SCon{z, t})) == False{} : Bool}:
  %Equal.sym(String, String.reverse.go(t, SCon{z, SNil{}}), String.append(String.reverse(t), SCon{z, SNil{}}), rt.rev_acc(t, SCon{z, SNil{}})) : {String.is_empty(_) == False{} : Bool}
  rt.ne_app(String.reverse(t), z, SNil{})
