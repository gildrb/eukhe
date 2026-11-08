# eukhe: lemmas shared by the proofs of area privacy, section ip: the
# decision the IPv4 grammar takes on the text four octets write

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S
import ./chars.bend as LIp
import ./read.bend as LRd
import ./quad.bend as LQd
import ./decide.bend as LDc

# Before the address
# ------------------

def pd4.alpha(m: Maybe<&2, Char>) -> {Ip.alpha(m) == S.mletter(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      match c:
        case Chr{x}:
          {==}

def pd4.edge4_pair(q: Maybe<&2, Char>, +p: Maybe<&2, Char>) -> {Ip.edge4((p, q)) == S.before4.of(q, p) : Bool}:
  match q:
    case None{}:
      {==}
    case Some{+c}:
      %Equal.sym(Bool, Ip.Sym.edge4(Ip.Sym.of(c)), S.k_edge4(S.kind(c)), LIp.pip.edge4_of(c)) : {Bool.and(_, Bool.not(Bool.and(Char.is_eq(c, '/'), Ip.alpha(p)))) == S.before4.of(Some{c}, p) : Bool}
      %Equal.sym(Bool, Ip.alpha(p), S.mletter(p), pd4.alpha(p)) : {Bool.and(S.k_edge4(S.kind(c)), Bool.not(Bool.and(Char.is_eq(c, '/'), _))) == S.before4.of(Some{c}, p) : Bool}
      {==}

# the last two chars of c, d, then s
def pd4.last2_cc(s: String, +c: Char, +d: Char) -> {Ip.last2(s, Some{c}, Some{d}) == (S.before_last(SCon{c, SCon{d, s}}), S.last(SCon{c, SCon{d, s}})) : Maybe<&2, Char> & Maybe<&2, Char>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+e, v}:
      pd4.last2_cc(v, d, e)

# the reader's last two chars are the spec's
def pd4.last2(s: String) -> {Ip.last2(s, None{}, None{}) == (S.before_last(s), S.last(s)) : Maybe<&2, Char> & Maybe<&2, Char>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      match t:
        case SNil{}:
          {==}
        case SCon{+d, u}:
          pd4.last2_cc(u, c, d)

def pd4.edge4(+b: String) -> {Ip.edge4(Ip.last2(b, None{}, None{})) == S.before4(b) : Bool}:
  %Equal.sym(Maybe<&2, Char> & Maybe<&2, Char>, Ip.last2(b, None{}, None{}), (S.before_last(b), S.last(b)), pd4.last2(b)) : {Ip.edge4(_) == S.before4(b) : Bool}
  pd4.edge4_pair(S.last(b), S.before_last(b))

# After the address
# -----------------

def pd4.sep(u: String) -> {Ip.after4.sep(Ip.Sym.list(u)) == S.after4.sep(u) : Bool}:
  match u:
    case SNil{}:
      {==}
    case SCon{+d, w}:
      %Equal.sym(Bool, Ip.Sym.alnum(Ip.Sym.of(d)), S.k_alnum(S.kind(d)), LIp.pip.alnum_of(d)) : {Bool.not(_) == Bool.not(S.k_alnum(S.kind(d))) : Bool}
      {==}

# what the spec asks of the chars after an IPv4: k, then u
def pd4.A4(+k: S.CKind, u: String) -> Bool:
  Bool.and(Bool.not(S.k_word(k)), Bool.or(Bool.not(S.k_sep(k)), S.after4.sep(u)))

def pd4.after4_y(y: Ip.Sym, +u: String) -> {Ip.after4(y <> Ip.Sym.list(u)) == pd4.A4(LIp.pip.kind(y), u) : Bool}:
  match y:
    case Ip.Dig{c}:
      {==}
    case Ip.Hx{c}:
      {==}
    case Ip.Col{}:
      {==}
    case Ip.Dot{}:
      pd4.sep(u)
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      pd4.sep(u)
    case Ip.Oth{}:
      {==}

def pd4.after4(t: String) -> {Ip.after4(Ip.Sym.list(t)) == S.after4(t) : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      Equal.trans(Bool, Ip.after4(Ip.Sym.of(c) <> Ip.Sym.list(u)), pd4.A4(LIp.pip.kind(Ip.Sym.of(c)), u), pd4.A4(S.kind(c), u), pd4.after4_y(Ip.Sym.of(c), u), Equal.cong(S.CKind, Bool, k => pd4.A4(k, u), LIp.pip.kind(Ip.Sym.of(c)), S.kind(c), LIp.pip.kind_of(c)))

# The decision
# ------------

def pd4.first_ok(q: Ip.Quad) -> {Ip.first_ok(q) == S.first_ok(q) : Bool}:
  match q:
    case Ip.Quad{a, b, c, d}:
      {==}

# the length the grammar answers is the length of what s writes
def pd4.len_app(+s: String, +t: String) -> {Nat.sub(List.length(&2, Ip.Sym, Ip.Sym.list(String.append(s, t))), List.length(&2, Ip.Sym, Ip.Sym.list(t))) == String.length(s) : Nat}:
  +ls = List.length(&2, Ip.Sym, Ip.Sym.list(s))
  +lt = List.length(&2, Ip.Sym, Ip.Sym.list(t))
  %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(s, t)), List.append(&2, Ip.Sym, Ip.Sym.list(s), Ip.Sym.list(t)), LRd.prd.sym_app(s, t)) : {Nat.sub(List.length(&2, Ip.Sym, _), lt) == String.length(s) : Nat}
  %Equal.sym(Nat, List.length(&2, Ip.Sym, List.append(&2, Ip.Sym, Ip.Sym.list(s), Ip.Sym.list(t))), Nat.add(ls, lt), LRd.prd.list_len_app(Ip.Sym.list(s), Ip.Sym.list(t))) : {Nat.sub(_, lt) == String.length(s) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(ls, lt), lt), ls, LRd.prd.sub_add(ls, lt)) : {_ == String.length(s) : Nat}
  LRd.prd.len_sym(s)

def pd4.len4(+q: Ip.Quad, +t: String) -> {Nat.sub(List.length(&2, Ip.Sym, Ip.Sym.list(S.quad_text(q, t))), List.length(&2, Ip.Sym, Ip.Sym.list(t))) == String.length(S.quad_text(q, "")) : Nat}:
  %LQd.pqd.qt_app(q, t) : {Nat.sub(List.length(&2, Ip.Sym, Ip.Sym.list(_)), List.length(&2, Ip.Sym, Ip.Sym.list(t))) == String.length(S.quad_text(q, "")) : Nat}
  pd4.len_app(S.quad_text(q, ""), t)

# the quad read, and what follows it
def pd4.got(+q: Ip.Quad, +t: String, +h: {S.quad_ok(q) == True{} : Bool}, +ht: {S.stops4(t) == True{} : Bool}) -> {Ip.v4.go(True{}, S.quad_text(q, t)) == S.ans(Bool.and(S.first_ok(q), S.after4(t)), String.length(S.quad_text(q, ""))) : Maybe<&2, Nat>}:
  +hs = LRd.prd.drun_end4(t, ht)
  +L = String.length(S.quad_text(q, ""))
  +n = List.length(&2, Ip.Sym, Ip.Sym.list(S.quad_text(q, t)))
  +lt = List.length(&2, Ip.Sym, Ip.Sym.list(t))
  %Equal.sym(Maybe<&2, Ip.QCut>, Ip.quad(Ip.Sym.list(S.quad_text(q, t))), Some{Ip.QCut{q, Ip.Sym.list(t)}}, LQd.pqd.quad_read(q, t, h, hs)) : {Ip.v4.got(n, _) == S.ans(Bool.and(S.first_ok(q), S.after4(t)), L) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Ip.first_ok(q), S.first_ok(q), pd4.first_ok(q)) : {Ip.ans(Bool.and(_, Ip.after4(Ip.Sym.list(t))), Nat.sub(n, lt)) == S.ans(Bool.and(S.first_ok(q), S.after4(t)), L) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Ip.after4(Ip.Sym.list(t)), S.after4(t), pd4.after4(t)) : {Ip.ans(Bool.and(S.first_ok(q), _), Nat.sub(n, lt)) == S.ans(Bool.and(S.first_ok(q), S.after4(t)), L) : Maybe<&2, Nat>}
  %Equal.sym(Nat, Nat.sub(n, lt), L, pd4.len4(q, t)) : {Ip.ans(Bool.and(S.first_ok(q), S.after4(t)), _) == S.ans(Bool.and(S.first_ok(q), S.after4(t)), L) : Maybe<&2, Nat>}
  LDc.pdc.ans(Bool.and(S.first_ok(q), S.after4(t)), L)

def pd4.go_v(v: Bool, +q: Ip.Quad, +t: String, +h: {S.quad_ok(q) == True{} : Bool}, +ht: {S.stops4(t) == True{} : Bool}) -> {Ip.v4.go(Bool.not(v), S.quad_text(q, t)) == S.ans(Bool.and(Bool.and(S.first_ok(q), S.after4(t)), Bool.not(v)), String.length(S.quad_text(q, ""))) : Maybe<&2, Nat>}:
  match v:
    case True{}:
      +X = Bool.and(S.first_ok(q), S.after4(t))
      %Equal.sym(Bool, Bool.and(X, False{}), False{}, LIp.pip.and_false(X)) : {None{} == S.ans(_, String.length(S.quad_text(q, ""))) : Maybe<&2, Nat>}
      {==}
    case False{}:
      +X = Bool.and(S.first_ok(q), S.after4(t))
      %Equal.sym(Bool, Bool.and(X, True{}), X, LIp.pip.and_true(X)) : {Ip.v4.go(True{}, S.quad_text(q, t)) == S.ans(_, String.length(S.quad_text(q, ""))) : Maybe<&2, Nat>}
      pd4.got(q, t, h, ht)

def pd4.go(g: Bool, v: Bool, +q: Ip.Quad, +t: String, +h: {S.quad_ok(q) == True{} : Bool}, +ht: {S.stops4(t) == True{} : Bool}) -> {Ip.v4.go(Bool.and(g, Bool.not(v)), S.quad_text(q, t)) == S.ans(Bool.and(Bool.and(Bool.and(S.first_ok(q), S.after4(t)), g), Bool.not(v)), String.length(S.quad_text(q, ""))) : Maybe<&2, Nat>}:
  match g:
    case False{}:
      %Equal.sym(Bool, Bool.and(Bool.and(S.first_ok(q), S.after4(t)), False{}), False{}, LIp.pip.and_false(Bool.and(S.first_ok(q), S.after4(t)))) : {None{} == S.ans(Bool.and(_, Bool.not(v)), String.length(S.quad_text(q, ""))) : Maybe<&2, Nat>}
      {==}
    case True{}:
      %Equal.sym(Bool, Bool.and(Bool.and(S.first_ok(q), S.after4(t)), True{}), Bool.and(S.first_ok(q), S.after4(t)), LIp.pip.and_true(Bool.and(S.first_ok(q), S.after4(t)))) : {Ip.v4.go(Bool.not(v), S.quad_text(q, t)) == S.ans(Bool.and(_, Bool.not(v)), String.length(S.quad_text(q, ""))) : Maybe<&2, Nat>}
      pd4.go_v(v, q, t, h, ht)

# every four octets, then t, are decided as the spec decides
def pd4.decides(+q: Ip.Quad, +before: String, +t: String, +ok: {S.quad_ok(q) == True{} : Bool}, +st: {S.stops4(t) == True{} : Bool}) -> {Ip.v4(before, S.quad_text(q, t)) == S.take4(q, before, t, Cx.vctx(before)) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Ip.edge4(Ip.last2(before, None{}, None{})), S.before4(before), pd4.edge4(before)) : {Ip.v4.go(Bool.and(_, Bool.not(Cx.vctx(before))), S.quad_text(q, t)) == S.take4(q, before, t, Cx.vctx(before)) : Maybe<&2, Nat>}
  pd4.go(S.before4(before), Cx.vctx(before), q, t, ok, st)
