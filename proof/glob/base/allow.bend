# eukhe: lemmas of the proofs of the allowlist laws: text append and
# reverse, trimming White_Space at both ends of w1 ++ p ++ w2 gives p
# (al.trim), and one pattern's verdict on a trimmed pattern (al.e).

import Base
import ../../../bend/glob/parse.bend as GParse
import ../../../bend/glob/items.bend as GItems
import ../../../bend/glob/match.bend as GMatch
import ../../../bend/glob/queries.bend as GQuery
import ../../../laws/glob.bend as Glob
import ./logic.bend as GL
import ./seq.bend as GS

# Texts
# -----

def al.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      Equal.cong(String, String, z => SCon{c, z}, String.append(t, SNil{}), t, al.app_nil(t))

def al.app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, z => SCon{h, z}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), al.app_assoc(t, b, c))

# reversing onto acc is reversing, then acc
def al.rgo(s: String, +acc: String) -> {String.reverse.go(s, acc) == String.append(String.reverse(s), acc) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, String.reverse.go(t, SCon{c, acc}), String.append(String.reverse(t), SCon{c, acc}), al.rgo(t, SCon{c, acc})) : {_ == String.append(String.reverse.go(t, SCon{c, SNil{}}), acc) : String}
      %Equal.sym(String, String.reverse.go(t, SCon{c, SNil{}}), String.append(String.reverse(t), SCon{c, SNil{}}), al.rgo(t, SCon{c, SNil{}})) : {String.append(String.reverse(t), SCon{c, acc}) == String.append(_, acc) : String}
      Equal.sym(String, String.append(String.append(String.reverse(t), SCon{c, SNil{}}), acc), String.append(String.reverse(t), SCon{c, acc}), al.app_assoc(String.reverse(t), SCon{c, SNil{}}, acc))

def al.rev_app(a: String, +b: String) -> {String.reverse(String.append(a, b)) == String.append(String.reverse(b), String.reverse(a)) : String}:
  match a:
    case SNil{}:
      Equal.sym(String, String.append(String.reverse(b), SNil{}), String.reverse(b), al.app_nil(String.reverse(b)))
    case SCon{+c, +t}:
      +rb = String.reverse(b)
      +rt = String.reverse(t)
      +one = {SCon{c, SNil{}} : String}
      %Equal.sym(String, String.reverse.go(String.append(t, b), one), String.append(String.reverse(String.append(t, b)), one), al.rgo(String.append(t, b), one)) : {_ == String.append(rb, String.reverse.go(t, one)) : String}
      %Equal.sym(String, String.reverse.go(t, one), String.append(rt, one), al.rgo(t, one)) : {String.append(String.reverse(String.append(t, b)), one) == String.append(rb, _) : String}
      %Equal.sym(String, String.reverse(String.append(t, b)), String.append(rb, rt), al.rev_app(t, b)) : {String.append(_, one) == String.append(rb, String.append(rt, one)) : String}
      al.app_assoc(rb, rt, one)

def al.rev_rev(s: String) -> {String.reverse(String.reverse(s)) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +one = {SCon{c, SNil{}} : String}
      %Equal.sym(String, String.reverse.go(t, one), String.append(String.reverse(t), one), al.rgo(t, one)) : {String.reverse(_) == SCon{c, t} : String}
      %Equal.sym(String, String.reverse(String.append(String.reverse(t), one)), String.append(String.reverse(one), String.reverse(String.reverse(t))), al.rev_app(String.reverse(t), one)) : {_ == SCon{c, t} : String}
      %Equal.sym(String, String.reverse(String.reverse(t)), t, al.rev_rev(t)) : {String.append(String.reverse(one), _) == SCon{c, t} : String}
      {==}

# White_Space
# -----------

def al.ws(c: Char) -> {GQuery.ws(c) == Glob.sp_ws(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

def al.all_app(a: String, +b: String) -> {Glob.sp_all_ws(String.append(a, b)) == Bool.and(Glob.sp_all_ws(a), Glob.sp_all_ws(b)) : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Glob.sp_all_ws(String.append(t, b)), Bool.and(Glob.sp_all_ws(t), Glob.sp_all_ws(b)), al.all_app(t, b)) : {Bool.and(Glob.sp_ws(c), _) == Bool.and(Bool.and(Glob.sp_ws(c), Glob.sp_all_ws(t)), Glob.sp_all_ws(b)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(Glob.sp_ws(c), Glob.sp_all_ws(t)), Glob.sp_all_ws(b)), Bool.and(Glob.sp_ws(c), Bool.and(Glob.sp_all_ws(t), Glob.sp_all_ws(b))), GL.gl.and_assoc(Glob.sp_ws(c), Glob.sp_all_ws(t), Glob.sp_all_ws(b)))

# a text of White_Space reversed is of White_Space
def al.all_rev(w: String, +h: {Glob.sp_all_ws(w) == True{} : Bool}) -> {Glob.sp_all_ws(String.reverse(w)) == True{} : Bool}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +one = {SCon{c, SNil{}} : String}
      +hc = GL.gl.and_l(Glob.sp_ws(c), Glob.sp_all_ws(t), h)
      +ht = GL.gl.and_r(Glob.sp_ws(c), Glob.sp_all_ws(t), h)
      %Equal.sym(String, String.reverse.go(t, one), String.append(String.reverse(t), one), al.rgo(t, one)) : {Glob.sp_all_ws(_) == True{} : Bool}
      %Equal.sym(Bool, Glob.sp_all_ws(String.append(String.reverse(t), one)), Bool.and(Glob.sp_all_ws(String.reverse(t)), Glob.sp_all_ws(one)), al.all_app(String.reverse(t), one)) : {_ == True{} : Bool}
      GL.gl.and_t(Glob.sp_all_ws(String.reverse(t)), Glob.sp_all_ws(one), al.all_rev(t, ht), Equal.trans(Bool, Bool.and(Glob.sp_ws(c), True{}), Glob.sp_ws(c), True{}, GL.gl.and_true(Glob.sp_ws(c)), hc))

# White_Space first is dropped
def al.drop_ws(w: String, +y: String, +h: {Glob.sp_all_ws(w) == True{} : Bool}) -> {GQuery.trim_start(String.append(w, y)) == GQuery.trim_start(y) : String}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hc = GL.gl.and_l(Glob.sp_ws(c), Glob.sp_all_ws(t), h)
      +ht = GL.gl.and_r(Glob.sp_ws(c), Glob.sp_all_ws(t), h)
      %Equal.sym(Bool, GQuery.ws(c), True{}, Equal.trans(Bool, GQuery.ws(c), Glob.sp_ws(c), True{}, al.ws(c), hc)) : {GQuery.trim_start.k(_, c, String.append(t, y), GQuery.trim_start(String.append(t, y))) == GQuery.trim_start(y) : String}
      al.drop_ws(t, y, ht)

# a text whose first char is no White_Space is kept
def al.keep(+c: Char, +t: String, h: {Glob.sp_ws(c) == False{} : Bool}) -> {GQuery.trim_start(SCon{c, t}) == SCon{c, t} : String}:
  %Equal.sym(Bool, GQuery.ws(c), False{}, Equal.trans(Bool, GQuery.ws(c), Glob.sp_ws(c), False{}, al.ws(c), h)) : {GQuery.trim_start.k(_, c, t, GQuery.trim_start(t)) == SCon{c, t} : String}
  {==}

def al.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      GL.gl.ft({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# c <> t reversed starts with t's last char (c for none), no White_Space
def al.Ex(s: String) -> Type:
  &e: Char -> &r: String -> ({s == SCon{e, r} : String} & {Glob.sp_ws(e) == False{} : Bool})

def al.rev_cons(+e: Char, -s: String, -r: String, +c: Char, p: {s == SCon{e, r} : String}) -> {String.append(s, SCon{c, SNil{}}) == SCon{e, String.append(r, SCon{c, SNil{}})} : String}:
  %Equal.sym(String, s, SCon{e, r}, p) : {String.append(_, SCon{c, SNil{}}) == SCon{e, String.append(r, SCon{c, SNil{}})} : String}
  {==}

def al.rev_step(+d: Char, +u: String, +c: Char, ex: al.Ex(String.reverse(SCon{d, u}))) -> al.Ex(String.reverse(SCon{c, SCon{d, u}})):
  (+e, ex1) = ex
  (r, pf) = ex1
  (eq, nw) = pf
  +one = {SCon{c, SNil{}} : String}
  (e, (String.append(r, one), (Equal.trans(String, String.reverse.go(SCon{d, u}, one), String.append(String.reverse(SCon{d, u}), one), SCon{e, String.append(r, one)}, al.rgo(SCon{d, u}, one), al.rev_cons(e, String.reverse(SCon{d, u}), r, c, eq)), nw)))

def al.rev_first(t: String, +c: Char, h: {Glob.sp_last_kept(t, c) == True{} : Bool}) -> al.Ex(String.reverse(SCon{c, t})):
  match t:
    case SNil{}:
      (c, (SNil{}, ({==}, al.not_t(Glob.sp_ws(c), h))))
    case SCon{+d, +u}:
      al.rev_step(d, u, c, al.rev_first(u, d, h))

# Trimming
# --------

def al.trim_rev(+s: String, ex: al.Ex(s)) -> {GQuery.trim_start(s) == s : String}:
  (e, ex1) = ex
  (r, pf) = ex1
  (eq, nw) = pf
  %Equal.sym(String, s, SCon{e, r}, eq) : {GQuery.trim_start(_) == _ : String}
  al.keep(e, r, nw)

# a text of White_Space trims to nothing
def al.ws_empty(w: String, +h: {Glob.sp_all_ws(w) == True{} : Bool}) -> {GQuery.trim_start(w) == SNil{} : String}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hc = GL.gl.and_l(Glob.sp_ws(c), Glob.sp_all_ws(t), h)
      +ht = GL.gl.and_r(Glob.sp_ws(c), Glob.sp_all_ws(t), h)
      %Equal.sym(Bool, GQuery.ws(c), True{}, Equal.trans(Bool, GQuery.ws(c), Glob.sp_ws(c), True{}, al.ws(c), hc)) : {GQuery.trim_start.k(_, c, t, GQuery.trim_start(t)) == SNil{} : String}
      al.ws_empty(t, ht)

# trimming w1 ++ p ++ w2 gives p: White_Space around, none at p's ends
def al.trim(+w1: String, p: String, +w2: String, +h1: {Glob.sp_all_ws(w1) == True{} : Bool}, +hp: {Glob.sp_trimmed(p) == True{} : Bool}, +h2: {Glob.sp_all_ws(w2) == True{} : Bool}) -> {GQuery.trim(String.append(w1, String.append(p, w2))) == p : String}:
  match p:
    case SNil{}:
      %Equal.sym(String, GQuery.trim_start(String.append(w1, w2)), SNil{}, Equal.trans(String, GQuery.trim_start(String.append(w1, w2)), GQuery.trim_start(w2), SNil{}, al.drop_ws(w1, w2, h1), al.ws_empty(w2, h2))) : {String.reverse(GQuery.trim_start(String.reverse(_))) == SNil{} : String}
      {==}
    case SCon{+c, +t}:
      +p = {SCon{c, t} : String}
      +hc = al.not_t(Glob.sp_ws(c), GL.gl.and_l(Bool.not(Glob.sp_ws(c)), Glob.sp_last_kept(t, c), hp))
      +hl = GL.gl.and_r(Bool.not(Glob.sp_ws(c)), Glob.sp_last_kept(t, c), hp)
      +pw = String.append(p, w2)
      +rp = String.reverse(p)
      +rw = String.reverse(w2)
      +s1 = Equal.trans(String, GQuery.trim_start(String.append(w1, pw)), GQuery.trim_start(pw), pw, al.drop_ws(w1, pw, h1), al.keep(c, String.append(t, w2), hc))
      +s3 = Equal.trans(String, GQuery.trim_start(String.append(rw, rp)), GQuery.trim_start(rp), rp, al.drop_ws(rw, rp, al.all_rev(w2, h2)), al.trim_rev(rp, al.rev_first(t, c, hl)))
      Equal.trans(String, String.reverse(GQuery.trim_start(String.reverse(GQuery.trim_start(String.append(w1, pw))))), String.reverse(GQuery.trim_start(String.reverse(pw))), p, Equal.cong(String, String, z => String.reverse(GQuery.trim_start(String.reverse(z))), GQuery.trim_start(String.append(w1, pw)), pw, s1), Equal.trans(String, String.reverse(GQuery.trim_start(String.reverse(pw))), String.reverse(GQuery.trim_start(String.append(rw, rp))), p, Equal.cong(String, String, z => String.reverse(GQuery.trim_start(z)), String.reverse(pw), String.append(rw, rp), al.rev_app(p, w2)), Equal.trans(String, String.reverse(GQuery.trim_start(String.append(rw, rp))), String.reverse(rp), p, Equal.cong(String, String, z => String.reverse(z), GQuery.trim_start(String.append(rw, rp)), rp, s3), al.rev_rev(p))))

# Verdicts
# --------

def al.wild(s: String) -> {GQuery.wild(s) == Glob.sp_wild(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          Equal.cong(Bool, Bool, z => Bool.or(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), U32.is_eq(x, 91))), z), GQuery.wild(t), Glob.sp_wild(t), al.wild(t))

def al.o() -> GItems.Opts:
  GItems.Opts{False{}, False{}}

# one text searched: its match
def al.one(+b: String, +its: List<&2, List<&2, GItems.It>>) -> {GQuery.hit_any([b], its) == GMatch.any_full(GItems.bytes(b), its) : Bool}:
  Equal.trans(Bool, GQuery.hit_any([b], its), Bool.or(GMatch.any_full(GItems.bytes(b), its), False{}), GMatch.any_full(GItems.bytes(b), its), GS.gs.af_or(GMatch.any_full(GItems.bytes(b), its), GQuery.hit_any(Nil{}, its)), GL.gl.or_false(GMatch.any_full(GItems.bytes(b), its)))

def al.g(res: Result<&2, &2, GParse.Err, GParse.Glob>, +sel: String) -> {GQuery.allow.g(res, sel) == Bool.or(Glob.sp_parsed_hit(al.o(), res, sel), Glob.sp_parsed_hit(al.o(), res, GQuery.bare(sel))) : Bool}:
  match res:
    case Fail{e}:
      {==}
    case Done{+g}:
      +its = GItems.items(al.o(), g)
      +a1 = GMatch.any_full(GItems.bytes(sel), its)
      +hb = GQuery.hit_any([GQuery.bare(sel)], its)
      Equal.trans(Bool, GQuery.hit_any([sel, GQuery.bare(sel)], its), Bool.or(a1, hb), Bool.or(a1, GMatch.any_full(GItems.bytes(GQuery.bare(sel)), its)), GS.gs.af_or(a1, hb), Equal.cong(Bool, Bool, z => Bool.or(a1, z), hb, GMatch.any_full(GItems.bytes(GQuery.bare(sel)), its), al.one(GQuery.bare(sel), its)))

def al.w(w: Bool, +sel: String, +p: String) -> {GQuery.allow.w(w, sel, p) == Glob.sp_allow.k(False{}, w, sel, p) : Bool}:
  match w:
    case True{}:
      al.g(GParse.parse(p), sel)
    case False{}:
      {==}

def al.e(e: Bool, +sel: String, +p: String) -> {GQuery.allow.e(e, sel, p) == Glob.sp_allow.k(e, Glob.sp_wild(p), sel, p) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, GQuery.allow.w(GQuery.wild(p), sel, p), GQuery.allow.w(Glob.sp_wild(p), sel, p), Glob.sp_allow.k(False{}, Glob.sp_wild(p), sel, p), Equal.cong(Bool, Bool, z => GQuery.allow.w(z, sel, p), GQuery.wild(p), Glob.sp_wild(p), al.wild(p)), al.w(Glob.sp_wild(p), sel, p))

# a list of one pattern decides as that pattern
def al.single(+sel: String, +x: String) -> {GQuery.allowed(sel, [x]) == GQuery.allow1(sel, x) : Bool}:
  Equal.trans(Bool, GQuery.allowed(sel, [x]), Bool.or(GQuery.allow1(sel, x), False{}), GQuery.allow1(sel, x), GS.gs.af_or(GQuery.allow1(sel, x), GQuery.allowed(sel, Nil{})), GL.gl.or_false(GQuery.allow1(sel, x)))
