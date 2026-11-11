# eukhe: lemmas of the proofs of area redirect_input: what the model's
# cuts (Ri.split, String.split, Ri.scheme, Ri.unslash) and decoding
# (Ri.decode) do to texts of known chars (rp.*): a cut at a char a text
# lacks finds none or falls after the text; a plain value decodes to
# itself.

import Base
import ../../../bend/redirect_input.bend as Ri
import ../../../bend/gateway_answer.bend as Ga
import ../../../laws/redirect_input.bend as RedirectInput
import ./text.bend as LT

# Lacking a char
# --------------

def rp.lk_hd(+c: Char, -t: String, +k: Char, h: {LT.rt.lacks(SCon{c, t}, k) == True{} : Bool}) -> {Char.is_eq(c, k) == False{} : Bool}:
  LT.rt.not_t(Char.is_eq(c, k), LT.rt.and_l(Bool.not(Char.is_eq(c, k)), LT.rt.lacks(t, k), h))

def rp.lk_tl(+c: Char, t: String, +k: Char, h: {LT.rt.lacks(SCon{c, t}, k) == True{} : Bool}) -> {LT.rt.lacks(t, k) == True{} : Bool}:
  LT.rt.and_r(Bool.not(Char.is_eq(c, k)), LT.rt.lacks(t, k), h)

def rp.lk_drop_at(g: Bool, +c: Char, +r: String, +k: Char, hc: {Char.is_eq(c, k) == False{} : Bool}, hr: {LT.rt.lacks(r, k) == True{} : Bool}) -> {LT.rt.lacks(Ri.compact.at(g, c, r), k) == True{} : Bool}:
  match g:
    case True{}:
      hr
    case False{}:
      LT.rt.and_t(Bool.not(Char.is_eq(c, k)), LT.rt.lacks(r, k), LT.rt.not_f(Char.is_eq(c, k), hc), hr)

# the drop keeps a lack
def rp.lk_compact(s: String, +k: Char, h: {LT.rt.lacks(s, k) == True{} : Bool}) -> {LT.rt.lacks(Ri.compact(s), k) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      rp.lk_drop_at(Bool.or(Ga.space(c), Ri.zero_width(c)), c, Ri.compact(t), k, rp.lk_hd(c, t, k, h0), rp.lk_compact(t, k, rp.lk_tl(c, t, k, h0)))

def rp.lk_unwrap_at(g: Bool, +c: Char, +t: String, +k: Char, h: {LT.rt.lacks(SCon{c, t}, k) == True{} : Bool}, ih: {LT.rt.lacks(Ri.unwrap(t), k) == True{} : Bool}) -> {LT.rt.lacks(Ri.unwrap.at(g, c, t, Ri.unwrap(t)), k) == True{} : Bool}:
  match g:
    case True{}:
      ih
    case False{}:
      h

# the trim keeps a lack
def rp.lk_unwrap(s: String, +k: Char, h: {LT.rt.lacks(s, k) == True{} : Bool}) -> {LT.rt.lacks(Ri.unwrap(s), k) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      rp.lk_unwrap_at(Ri.wrapper(c), c, t, k, h0, rp.lk_unwrap(t, k, rp.lk_tl(c, t, k, h0)))

# Cuts
# ----

# a cut at a char the text before it lacks falls there
def rp.split_hit(y: String, +sep: Char, +r: String, hs: {Char.is_eq(sep, sep) == True{} : Bool}, hl: {LT.rt.lacks(y, sep) == True{} : Bool}) -> {Ri.split(String.append(y, SCon{sep, r}), sep) == Some{Ri.Cut{y, r}} : Maybe<&2, Ri.Cut>}:
  match y:
    case SNil{}:
      %Equal.sym(Bool, Char.is_eq(sep, sep), True{}, hs) : {Ri.split.at(_, sep, r, Ri.split(r, sep)) == Some{Ri.Cut{SNil{}, r}} : Maybe<&2, Ri.Cut>}
      {==}
    case SCon{+c, +t}:
      +h0 = hl
      %Equal.sym(Bool, Char.is_eq(c, sep), False{}, rp.lk_hd(c, t, sep, h0)) : {Ri.split.at(_, c, String.append(t, SCon{sep, r}), Ri.split(String.append(t, SCon{sep, r}), sep)) == Some{Ri.Cut{SCon{c, t}, r}} : Maybe<&2, Ri.Cut>}
      %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(String.append(t, SCon{sep, r}), sep), Some{Ri.Cut{t, r}}, rp.split_hit(t, sep, r, hs, rp.lk_tl(c, t, sep, h0))) : {Ri.split.at(False{}, c, String.append(t, SCon{sep, r}), _) == Some{Ri.Cut{SCon{c, t}, r}} : Maybe<&2, Ri.Cut>}
      {==}

# a cut at a char the text lacks finds none
def rp.split_none(y: String, +sep: Char, hl: {LT.rt.lacks(y, sep) == True{} : Bool}) -> {Ri.split(y, sep) == None{} : Maybe<&2, Ri.Cut>}:
  match y:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = hl
      %Equal.sym(Bool, Char.is_eq(c, sep), False{}, rp.lk_hd(c, t, sep, h0)) : {Ri.split.at(_, c, t, Ri.split(t, sep)) == None{} : Maybe<&2, Ri.Cut>}
      %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(t, sep), None{}, rp.split_none(t, sep, rp.lk_tl(c, t, sep, h0))) : {Ri.split.at(False{}, c, t, _) == None{} : Maybe<&2, Ri.Cut>}
      {==}

# Base's split at `&` of a text that lacks it is the text
def rp.bs1(x: String, h: {LT.rt.lacks(x, '&') == True{} : Bool}) -> {String.split(x, '&') == [x] : List<&2, String>}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      %Equal.sym(List<&2, String>, String.split(t, '&'), [t], rp.bs1(t, rp.lk_tl(c, t, '&', h0))) : {String.split.fin(c, _, Char.is_eq(c, '&')) == [SCon{c, t}] : List<&2, String>}
      %Equal.sym(Bool, Char.is_eq(c, '&'), False{}, rp.lk_hd(c, t, '&', h0)) : {String.split.fin(c, [t], _) == [SCon{c, t}] : List<&2, String>}
      {==}

# Base's split at `&`: the text before the first `&`, then the rest's parts
def rp.bs2(x: String, +y: String, h: {LT.rt.lacks(x, '&') == True{} : Bool}) -> {String.split(String.append(x, SCon{'&', y}), '&') == x <> String.split(y, '&') : List<&2, String>}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      %Equal.sym(List<&2, String>, String.split(String.append(t, SCon{'&', y}), '&'), t <> String.split(y, '&'), rp.bs2(t, y, rp.lk_tl(c, t, '&', h0))) : {String.split.fin(c, _, Char.is_eq(c, '&')) == SCon{c, t} <> String.split(y, '&') : List<&2, String>}
      %Equal.sym(Bool, Char.is_eq(c, '&'), False{}, rp.lk_hd(c, t, '&', h0)) : {String.split.fin(c, t <> String.split(y, '&'), _) == SCon{c, t} <> String.split(y, '&') : List<&2, String>}
      {==}

# Decoding
# --------

def rp.plain_hd(+c: Char, -t: String, h: {RedirectInput.ri_plain(SCon{c, t}) == True{} : Bool}) -> {RedirectInput.ri_plain_char(c) == True{} : Bool}:
  LT.rt.and_l(RedirectInput.ri_plain_char(c), RedirectInput.ri_plain(t), h)

def rp.plain_tl(+c: Char, t: String, h: {RedirectInput.ri_plain(SCon{c, t}) == True{} : Bool}) -> {RedirectInput.ri_plain(t) == True{} : Bool}:
  LT.rt.and_r(RedirectInput.ri_plain_char(c), RedirectInput.ri_plain(t), h)

# a plain text, then y, decodes as the text then y decoded
def rp.dec_app(c: String, +y: String, h: {RedirectInput.ri_plain(c) == True{} : Bool}) -> {Ri.utf(Ri.units(String.append(c, y), Ri.PPlain{}), Ri.UIdle{}) == String.append(c, Ri.utf(Ri.units(y, Ri.PPlain{}), Ri.UIdle{})) : String}:
  match c:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      +h0 = h
      +hx = rp.plain_hd(x, t, h0)
      %Equal.sym(Bool, Char.is_eq(x, '%'), False{}, LT.rt.pc_mark(0n, x, hx)) : {Ri.utf(List.append(&2, Ri.Piece, Ri.plain.out(_, Char.is_eq(x, '+'), x), Ri.units(String.append(t, y), Ri.plain.next(_))), Ri.UIdle{}) == SCon{x, String.append(t, Ri.utf(Ri.units(y, Ri.PPlain{}), Ri.UIdle{}))} : String}
      %Equal.sym(Bool, Char.is_eq(x, '+'), False{}, LT.rt.pc_mark(1n, x, hx)) : {Ri.utf(List.append(&2, Ri.Piece, Ri.plain.out(False{}, _, x), Ri.units(String.append(t, y), Ri.PPlain{})), Ri.UIdle{}) == SCon{x, String.append(t, Ri.utf(Ri.units(y, Ri.PPlain{}), Ri.UIdle{}))} : String}
      Equal.cong(String, String, z => SCon{x, z}, Ri.utf(Ri.units(String.append(t, y), Ri.PPlain{}), Ri.UIdle{}), String.append(t, Ri.utf(Ri.units(y, Ri.PPlain{}), Ri.UIdle{})), rp.dec_app(t, y, rp.plain_tl(x, t, h0)))

# a plain text decodes to itself
def rp.dec(+c: String, h: {RedirectInput.ri_plain(c) == True{} : Bool}) -> {Ri.decode(c) == c : String}:
  %LT.rt.app_nil(c) : {Ri.utf(Ri.units(_, Ri.PPlain{}), Ri.UIdle{}) == _ : String}
  rp.dec_app(c, SNil{}, h)

# a `+` between plain texts decodes to a space
def rp.dec_plus(+c: String, +d: String, hc: {RedirectInput.ri_plain(c) == True{} : Bool}, hd: {RedirectInput.ri_plain(d) == True{} : Bool}) -> {Ri.decode(String.append(c, SCon{'+', d})) == String.append(c, SCon{' ', d}) : String}:
  %Equal.sym(String, Ri.utf(Ri.units(String.append(c, SCon{'+', d}), Ri.PPlain{}), Ri.UIdle{}), String.append(c, Ri.utf(Ri.units(SCon{'+', d}, Ri.PPlain{}), Ri.UIdle{})), rp.dec_app(c, SCon{'+', d}, hc)) : {_ == String.append(c, SCon{' ', d}) : String}
  %Equal.sym(String, Ri.decode(d), d, rp.dec(d, hd)) : {String.append(c, SCon{' ', _}) == String.append(c, SCon{' ', d}) : String}
  {==}

# Trailing slashes
# ----------------

# the text starts with no `/`
def rp.nofs(x: String) -> Bool:
  match x:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.not(Char.is_eq(c, '/'))

def rp.sl_shift(n: Nat, +acc: String) -> {String.append(RedirectInput.ri_slashes(n), SCon{'/', acc}) == SCon{'/', String.append(RedirectInput.ri_slashes(n), acc)} : String}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      Equal.cong(String, String, z => SCon{'/', z}, String.append(RedirectInput.ri_slashes(m), SCon{'/', acc}), SCon{'/', String.append(RedirectInput.ri_slashes(m), acc)}, rp.sl_shift(m, acc))

# slashes reversed are slashes
def rp.sl_rev(n: Nat, +acc: String) -> {String.reverse.go(RedirectInput.ri_slashes(n), acc) == String.append(RedirectInput.ri_slashes(n), acc) : String}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      Equal.trans(String, String.reverse.go(RedirectInput.ri_slashes(m), SCon{'/', acc}), String.append(RedirectInput.ri_slashes(m), SCon{'/', acc}), SCon{'/', String.append(RedirectInput.ri_slashes(m), acc)}, rp.sl_rev(m, SCon{'/', acc}), rp.sl_shift(m, acc))

def rp.sl_drop(n: Nat, +x: String) -> {Ri.slashes(String.append(RedirectInput.ri_slashes(n), x)) == Ri.slashes(x) : String}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      rp.sl_drop(m, x)

def rp.sl_keep(x: String, h: {rp.nofs(x) == True{} : Bool}) -> {Ri.slashes(x) == x : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, '/'), False{}, LT.rt.not_t(Char.is_eq(c, '/'), h)) : {Ri.slashes.at(_, c, t, Ri.slashes(t)) == SCon{c, t} : String}
      {==}

# a text whose last char is no `/`, then slashes, loses the slashes
def rp.unslash(+r: String, +n: Nat, h: {rp.nofs(String.reverse(r)) == True{} : Bool}) -> {Ri.unslash(String.append(r, RedirectInput.ri_slashes(n))) == r : String}:
  %Equal.sym(String, String.reverse.go(String.append(r, RedirectInput.ri_slashes(n)), SNil{}), String.reverse.go(RedirectInput.ri_slashes(n), String.reverse(r)), LT.rt.rev_app(r, RedirectInput.ri_slashes(n), SNil{})) : {String.reverse(Ri.slashes(_)) == r : String}
  %Equal.sym(String, String.reverse.go(RedirectInput.ri_slashes(n), String.reverse(r)), String.append(RedirectInput.ri_slashes(n), String.reverse(r)), rp.sl_rev(n, String.reverse(r))) : {String.reverse(Ri.slashes(_)) == r : String}
  %Equal.sym(String, Ri.slashes(String.append(RedirectInput.ri_slashes(n), String.reverse(r))), Ri.slashes(String.reverse(r)), rp.sl_drop(n, String.reverse(r))) : {String.reverse(_) == r : String}
  %Equal.sym(String, Ri.slashes(String.reverse(r)), String.reverse(r), rp.sl_keep(String.reverse(r), h)) : {String.reverse(_) == r : String}
  LT.rt.rev_rev(r)

# a text with no trailing slash keeps its end
def rp.unslash0(+r: String, h: {rp.nofs(String.reverse(r)) == True{} : Bool}) -> {Ri.unslash(r) == r : String}:
  %LT.rt.app_nil(r) : {Ri.unslash(_) == r : String}
  rp.unslash(r, 0n, h)

def rp.plain_rev(s: String, +acc: String, ha: {RedirectInput.ri_plain(acc) == True{} : Bool}, h: {RedirectInput.ri_plain(s) == True{} : Bool}) -> {RedirectInput.ri_plain(String.reverse.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      ha
    case SCon{+c, +t}:
      +h0 = h
      rp.plain_rev(t, SCon{c, acc}, LT.rt.and_t(RedirectInput.ri_plain_char(c), RedirectInput.ri_plain(acc), rp.plain_hd(c, t, h0), ha), rp.plain_tl(c, t, h0))

def rp.nofs_plain(x: String, h: {RedirectInput.ri_plain(x) == True{} : Bool}) -> {rp.nofs(x) == True{} : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      LT.rt.not_f(Char.is_eq(c, '/'), LT.rt.pc_mark(6n, c, rp.plain_hd(c, t, h)))

def rp.nofs_app(x: String, -y: String, h: {rp.nofs(x) == True{} : Bool}, ne: {String.is_empty(x) == False{} : Bool}) -> {rp.nofs(String.append(x, y)) == True{} : Bool}:
  match x:
    case SNil{}:
      LT.rt.absurd({rp.nofs(y) == True{} : Bool}, ne)
    case SCon{c, t}:
      h

# a text that ends with a plain value has no trailing slash
def rp.nofs_end(+p: String, +v: String, hv: {RedirectInput.ri_value(v) == True{} : Bool}) -> {rp.nofs(String.reverse(String.append(p, v))) == True{} : Bool}:
  match v:
    case SNil{}:
      LT.rt.absurdF({rp.nofs(String.reverse(String.append(p, SNil{}))) == True{} : Bool}, hv)
    case SCon{+c, +t}:
      %Equal.sym(String, String.reverse.go(String.append(p, SCon{c, t}), SNil{}), String.reverse.go(SCon{c, t}, String.reverse(p)), LT.rt.rev_app(p, SCon{c, t}, SNil{})) : {rp.nofs(_) == True{} : Bool}
      %Equal.sym(String, String.reverse.go(SCon{c, t}, String.reverse(p)), String.append(String.reverse(SCon{c, t}), String.reverse(p)), LT.rt.rev_acc(SCon{c, t}, String.reverse(p))) : {rp.nofs(_) == True{} : Bool}
      rp.nofs_app(String.reverse(SCon{c, t}), String.reverse(p), rp.nofs_plain(String.reverse(SCon{c, t}), rp.plain_rev(SCon{c, t}, SNil{}, {==}, hv)), LT.rt.rev_ne(c, t))

# Schemes
# -------

def rp.sw_slash(t: String, ht: {LT.rt.lacks(t, '/') == True{} : Bool}) -> {String.starts_with.go(SCon{'/', SCon{'/', SNil{}}}, t) == False{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+d, u}:
      %Equal.sym(Bool, Char.is_eq(d, '/'), False{}, rp.lk_hd(d, u, '/', ht)) : {String.starts_with.go.if(SCon{'/', SNil{}}, u, _) == False{} : Bool}
      {==}

def rp.sw_at(b: Bool, t: String, ht: {LT.rt.lacks(t, '/') == True{} : Bool}) -> {String.starts_with.go.if(SCon{'/', SCon{'/', SNil{}}}, t, b) == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      rp.sw_slash(t, ht)

# a text without `/` holds no `://`
def rp.scheme_none(v: String, h: {LT.rt.lacks(v, '/') == True{} : Bool}) -> {Ri.scheme(v) == None{} : Maybe<&2, String>}:
  match v:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      %Equal.sym(Bool, String.starts_with(SCon{c, t}, "://"), False{}, rp.sw_at(Char.is_eq(c, ':'), t, rp.lk_tl(c, t, '/', h0))) : {Ri.scheme.at(_, t, Ri.scheme(t)) == None{} : Maybe<&2, String>}
      rp.scheme_none(t, rp.lk_tl(c, t, '/', h0))

def rp.drop0(s: String) -> {String.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# a text without `:` then `://`: the scheme ends there
def rp.scheme_hit(b: String, +rest: String, h: {LT.rt.lacks(b, ':') == True{} : Bool}) -> {Ri.scheme(String.append(b, SCon{':', SCon{'/', SCon{'/', rest}}})) == Some{rest} : Maybe<&2, String>}:
  match b:
    case SNil{}:
      Equal.cong(String, Maybe<&2, String>, z => Some{z}, String.drop(rest, 0n), rest, rp.drop0(rest))
    case SCon{+c, +t}:
      +h0 = h
      %Equal.sym(Bool, Char.is_eq(c, ':'), False{}, rp.lk_hd(c, t, ':', h0)) : {Ri.scheme.at(String.starts_with.go.if(SCon{'/', SCon{'/', SNil{}}}, String.append(t, SCon{':', SCon{'/', SCon{'/', rest}}}), _), String.append(t, SCon{':', SCon{'/', SCon{'/', rest}}}), Ri.scheme(String.append(t, SCon{':', SCon{'/', SCon{'/', rest}}}))) == Some{rest} : Maybe<&2, String>}
      rp.scheme_hit(t, rest, rp.lk_tl(c, t, ':', h0))

# Carriers
# --------

def rp.get_at_none(m: Maybe<&2, String>) -> {Ri.get.at(m, None{}) == m : Maybe<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

# a name's value over a carrier, then an empty one: its first non-empty value there
def rp.get2(+name: String, +r: String, +ps: List<&2, Ri.Param>, e: {Ri.params(r) == ps : List<&2, Ri.Param>}) -> {Ri.get(name, [r, SNil{}]) == Ri.find(name, ps) : Maybe<&2, String>}:
  %Equal.sym(List<&2, Ri.Param>, Ri.params(r), ps, e) : {Ri.get.at(Ri.find(name, _), None{}) == Ri.find(name, ps) : Maybe<&2, String>}
  rp.get_at_none(Ri.find(name, ps))

# a name's value over one carrier: its first non-empty value
def rp.get1(+name: String, +r: String, +ps: List<&2, Ri.Param>, e: {Ri.params(r) == ps : List<&2, Ri.Param>}) -> {Ri.get(name, [r]) == Ri.find(name, ps) : Maybe<&2, String>}:
  %Equal.sym(List<&2, Ri.Param>, Ri.params(r), ps, e) : {Ri.get.at(Ri.find(name, _), None{}) == Ri.find(name, ps) : Maybe<&2, String>}
  rp.get_at_none(Ri.find(name, ps))
