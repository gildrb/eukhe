# eukhe: lemmas of the proofs of area redirect_input: the cleaned paste
# (Ri.clean, R1). A noise char is dropped wherever it is (rcl.noise); a
# wrapping char is no noise, so it reaches the trim: in front it is
# trimmed (rcl.lead), at the end too, whatever came before it (rcl.trail);
# a quiet text with no wrapper at either end is kept (rcl.keeps).

import Base
import ../../../bend/redirect_input.bend as Ri
import ../../../bend/gateway_answer.bend as Ga
import ../../../laws/redirect_input.bend as RedirectInput
import ../../shape/base/chars.bend as LCh
import ./text.bend as LT

# A wrapping char is no noise
# ---------------------------

def rcl.nn_all(ks: List<&2, U32>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case k <> r:
      Bool.and(Bool.not(RedirectInput.ri_noise(Chr{k})), rcl.nn_all(r))

def rcl.nn_at(b: Bool, +x: U32, +k: U32, -r: List<&2, U32>, eb: {U32.is_eq(x, k) == b : Bool}, h: {Bool.or(b, RedirectInput.ri_in(x, r)) == True{} : Bool}, hk: {Bool.not(RedirectInput.ri_noise(Chr{k})) == True{} : Bool}, ih: {RedirectInput.ri_in(x, r) == True{} : Bool} -> {RedirectInput.ri_noise(Chr{x}) == False{} : Bool}) -> {RedirectInput.ri_noise(Chr{x}) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, x, k, LCh.shq.eq_sound(x, k, eb)) : {RedirectInput.ri_noise(Chr{_}) == False{} : Bool}
      LT.rt.not_t(RedirectInput.ri_noise(Chr{k}), hk)
    case False{}:
      ih(h)

def rcl.nn_go(ks: List<&2, U32>, +x: U32, h: {RedirectInput.ri_in(x, ks) == True{} : Bool}, all: {rcl.nn_all(ks) == True{} : Bool}) -> {RedirectInput.ri_noise(Chr{x}) == False{} : Bool}:
  match ks:
    case Nil{}:
      LT.rt.absurdF({RedirectInput.ri_noise(Chr{x}) == False{} : Bool}, h)
    case +k <> +r:
      +a0 = all
      rcl.nn_at(U32.is_eq(x, k), x, k, r, {==}, h, LT.rt.and_l(Bool.not(RedirectInput.ri_noise(Chr{k})), rcl.nn_all(r), a0), h2 => rcl.nn_go(r, x, h2, LT.rt.and_r(Bool.not(RedirectInput.ri_noise(Chr{k})), rcl.nn_all(r), a0)))

def rcl.wrap_nn(w: Char, h: {RedirectInput.ri_wrapper(w) == True{} : Bool}) -> {RedirectInput.ri_noise(w) == False{} : Bool}:
  match w:
    case Chr{+x}:
      rcl.nn_go([34, 39, 96, 60, 62, 8220, 8221, 8216, 8217], x, h, {==})

# The cleaned paste
# -----------------

def rcl.f(z: String) -> String:
  String.reverse(Ri.unwrap(String.reverse(z)))

# a noise char anywhere changes nothing
def rcl.noise(+a: String, +x: Char, +b: String, n: {RedirectInput.ri_noise(x) == True{} : Bool}) -> {Ri.clean(String.append(a, SCon{x, b})) == Ri.clean(String.append(a, b)) : String}:
  Equal.cong(String, String, z => rcl.f(Ri.unwrap(z)), Ri.compact(String.append(a, SCon{x, b})), Ri.compact(String.append(a, b)), LT.rt.compact_drop(a, x, b, n))

# a wrapping char in front is trimmed
def rcl.lead(+w: Char, +s: String, hw: {RedirectInput.ri_wrapper(w) == True{} : Bool}) -> {Ri.clean(SCon{w, s}) == Ri.clean(s) : String}:
  +h0 = hw
  %Equal.sym(String, Ri.compact(SCon{w, s}), SCon{w, Ri.compact(s)}, LT.rt.compact_keep(w, s, rcl.wrap_nn(w, h0))) : {rcl.f(Ri.unwrap(_)) == Ri.clean(s) : String}
  %Equal.sym(Bool, RedirectInput.ri_wrapper(w), True{}, h0) : {rcl.f(Ri.unwrap.at(_, w, Ri.compact(s), Ri.unwrap(Ri.compact(s)))) == Ri.clean(s) : String}
  {==}

def rcl.trail_at(g: Bool, +c: Char, +r: String, +w: Char, hw: {RedirectInput.ri_wrapper(w) == True{} : Bool}, ih: {rcl.f(Ri.unwrap(String.append(r, SCon{w, SNil{}}))) == rcl.f(Ri.unwrap(r)) : String}) -> {rcl.f(Ri.unwrap.at(g, c, String.append(r, SCon{w, SNil{}}), Ri.unwrap(String.append(r, SCon{w, SNil{}})))) == rcl.f(Ri.unwrap.at(g, c, r, Ri.unwrap(r))) : String}:
  match g:
    case True{}:
      ih
    case False{}:
      %Equal.sym(String, String.reverse.go(String.append(r, SCon{w, SNil{}}), SCon{c, SNil{}}), SCon{w, String.reverse.go(r, SCon{c, SNil{}})}, LT.rt.rev_snoc(r, w, SCon{c, SNil{}})) : {String.reverse(Ri.unwrap(_)) == rcl.f(SCon{c, r}) : String}
      %Equal.sym(Bool, RedirectInput.ri_wrapper(w), True{}, hw) : {String.reverse(Ri.unwrap.at(_, w, String.reverse.go(r, SCon{c, SNil{}}), Ri.unwrap(String.reverse.go(r, SCon{c, SNil{}})))) == rcl.f(SCon{c, r}) : String}
      {==}

def rcl.trail_go(cs: String, +w: Char, +hw: {RedirectInput.ri_wrapper(w) == True{} : Bool}) -> {rcl.f(Ri.unwrap(String.append(cs, SCon{w, SNil{}}))) == rcl.f(Ri.unwrap(cs)) : String}:
  match cs:
    case SNil{}:
      %Equal.sym(Bool, RedirectInput.ri_wrapper(w), True{}, hw) : {rcl.f(Ri.unwrap.at(_, w, SNil{}, SNil{})) == SNil{} : String}
      {==}
    case SCon{+c, +r}:
      rcl.trail_at(Ri.wrapper(c), c, r, w, hw, rcl.trail_go(r, w, hw))

# a wrapping char at the end is trimmed
def rcl.trail(+s: String, +w: Char, hw: {RedirectInput.ri_wrapper(w) == True{} : Bool}) -> {Ri.clean(String.append(s, SCon{w, SNil{}})) == Ri.clean(s) : String}:
  +h0 = hw
  +e = Equal.trans(String, Ri.compact(String.append(s, SCon{w, SNil{}})), String.append(Ri.compact(s), Ri.compact(SCon{w, SNil{}})), String.append(Ri.compact(s), SCon{w, SNil{}}), LT.rt.compact_app(s, SCon{w, SNil{}}), Equal.cong(String, String, z => String.append(Ri.compact(s), z), Ri.compact(SCon{w, SNil{}}), SCon{w, SNil{}}, LT.rt.compact_keep(w, SNil{}, rcl.wrap_nn(w, h0))))
  %Equal.sym(String, Ri.compact(String.append(s, SCon{w, SNil{}})), String.append(Ri.compact(s), SCon{w, SNil{}}), e) : {rcl.f(Ri.unwrap(_)) == Ri.clean(s) : String}
  rcl.trail_go(Ri.compact(s), w, h0)

# a quiet text is kept by the drop
def rcl.compact_quiet(s: String, h: {RedirectInput.ri_quiet(s) == True{} : Bool}) -> {Ri.compact(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      Equal.trans(String, Ri.compact(SCon{c, t}), SCon{c, Ri.compact(t)}, SCon{c, t}, LT.rt.compact_keep(c, t, LT.rt.not_t(RedirectInput.ri_noise(c), LT.rt.and_l(Bool.not(RedirectInput.ri_noise(c)), RedirectInput.ri_quiet(t), h0))), Equal.cong(String, String, z => SCon{c, z}, Ri.compact(t), t, rcl.compact_quiet(t, LT.rt.and_r(Bool.not(RedirectInput.ri_noise(c)), RedirectInput.ri_quiet(t), h0))))

# a text whose first char is no wrapper is kept by the trim
def rcl.unwrap_first(r: String, h: {RedirectInput.ri_wrap_first(r) == False{} : Bool}) -> {Ri.unwrap(r) == r : String}:
  match r:
    case SNil{}:
      {==}
    case SCon{+q, +qs}:
      %Equal.sym(Bool, RedirectInput.ri_wrapper(q), False{}, h) : {Ri.unwrap.at(_, q, qs, Ri.unwrap(qs)) == SCon{q, qs} : String}
      {==}

# a quiet text with no wrapper at either end is kept
def rcl.keeps(+x: Char, +t: String, quiet: {RedirectInput.ri_quiet(SCon{x, t}) == True{} : Bool}, head: {RedirectInput.ri_wrapper(x) == False{} : Bool}, last: {RedirectInput.ri_wrap_first(String.reverse(SCon{x, t})) == False{} : Bool}) -> {Ri.clean(SCon{x, t}) == SCon{x, t} : String}:
  %Equal.sym(String, Ri.compact(SCon{x, t}), SCon{x, t}, rcl.compact_quiet(SCon{x, t}, quiet)) : {rcl.f(Ri.unwrap(_)) == SCon{x, t} : String}
  %Equal.sym(Bool, RedirectInput.ri_wrapper(x), False{}, head) : {rcl.f(Ri.unwrap.at(_, x, t, Ri.unwrap(t))) == SCon{x, t} : String}
  %Equal.sym(String, Ri.unwrap(String.reverse(SCon{x, t})), String.reverse(SCon{x, t}), rcl.unwrap_first(String.reverse(SCon{x, t}), last)) : {String.reverse(_) == SCon{x, t} : String}
  LT.rt.rev_rev(SCon{x, t})

# a paste wrapped at both ends cleans as the paste
def rcl.wrapped(+w1: Char, +s: String, +w2: Char, h1: {RedirectInput.ri_wrapper(w1) == True{} : Bool}, h2: {RedirectInput.ri_wrapper(w2) == True{} : Bool}) -> {Ri.clean(SCon{w1, String.append(s, SCon{w2, SNil{}})}) == Ri.clean(s) : String}:
  Equal.trans(String, Ri.clean(SCon{w1, String.append(s, SCon{w2, SNil{}})}), Ri.clean(String.append(s, SCon{w2, SNil{}})), Ri.clean(s), rcl.lead(w1, String.append(s, SCon{w2, SNil{}}), h1), rcl.trail(s, w2, h2))

# the answer of a paste depends on its cleaned text only
def rcl.parse(+s: String, +t: String, e: {Ri.clean(s) == Ri.clean(t) : String}) -> {Ri.parse(s) == Ri.parse(t) : Ri.Answer}:
  Equal.cong(String, Ri.Answer, z => Ri.parse.at(Ri.split(z, '?'), z), Ri.clean(s), Ri.clean(t), e)
