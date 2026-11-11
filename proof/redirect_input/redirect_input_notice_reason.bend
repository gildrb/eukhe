# eukhe: the proof of LAW redirect_input_notice_reason
#
# PROOF: the leading whitespace w1 is trimmed whatever follows it (nr.ts1).
# What is left, r d w2, starts with no whitespace when r or d holds a char
# (r's first char is none, a `.` is none), so the first trim keeps it
# (nr.ts2); else it is all whitespace and trims to nothing. Reversed, it is
# w2 reversed (whitespace, trimmed), then d reversed (dots), then r
# reversed, which starts with no whitespace (a `.`, or r's last char); the
# dots go and r reversed, starting with no `.`, stays: reversed back it is
# r.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../bend/gateway_answer.bend as Ga
import ../../laws/redirect_input.bend as RedirectInput
import ../shape/base/chars.bend as LCh
import ./base/text.bend as LT

# whitespace in front is trimmed
def nr.ts1(w: String, +y: String, h: {RedirectInput.ri_spaces(w) == True{} : Bool}) -> {Ri.trim_start(String.append(w, y)) == Ri.trim_start(y) : String}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      %Equal.sym(Bool, RedirectInput.ri_space(c), True{}, LT.rt.and_l(RedirectInput.ri_space(c), RedirectInput.ri_spaces(t), h0)) : {Ri.trim_start.at(_, c, String.append(t, y), Ri.trim_start(String.append(t, y))) == Ri.trim_start(y) : String}
      nr.ts1(t, y, LT.rt.and_r(RedirectInput.ri_space(c), RedirectInput.ri_spaces(t), h0))

# a text that starts with no whitespace is kept
def nr.ts2(y: String, h: {RedirectInput.ri_space_first(y) == False{} : Bool}) -> {Ri.trim_start(y) == y : String}:
  match y:
    case SNil{}:
      {==}
    case SCon{+q, +qs}:
      %Equal.sym(Bool, RedirectInput.ri_space(q), False{}, h) : {Ri.trim_start.at(_, q, qs, Ri.trim_start(qs)) == SCon{q, qs} : String}
      {==}

# dots in front are dropped
def nr.d1(d: String, +y: String, h: {RedirectInput.ri_dots(d) == True{} : Bool}) -> {Ri.dots(String.append(d, y)) == Ri.dots(y) : String}:
  match d:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h0 = h
      %Equal.sym(Bool, Char.is_eq(c, '.'), True{}, LT.rt.and_l(Char.is_eq(c, '.'), RedirectInput.ri_dots(t), h0)) : {Ri.dots.at(_, c, String.append(t, y), Ri.dots(String.append(t, y))) == Ri.dots(y) : String}
      nr.d1(t, y, LT.rt.and_r(Char.is_eq(c, '.'), RedirectInput.ri_dots(t), h0))

# a text that starts with no dot is kept
def nr.d2(y: String, h: {RedirectInput.ri_dot_first(y) == False{} : Bool}) -> {Ri.dots(y) == y : String}:
  match y:
    case SNil{}:
      {==}
    case SCon{+q, +qs}:
      %Equal.sym(Bool, Char.is_eq(q, '.'), False{}, h) : {Ri.dots.at(_, q, qs, Ri.dots(qs)) == SCon{q, qs} : String}
      {==}

# reversed whitespace, reversed dots
def nr.sp_rev(s: String, +acc: String, ha: {RedirectInput.ri_spaces(acc) == True{} : Bool}, h: {RedirectInput.ri_spaces(s) == True{} : Bool}) -> {RedirectInput.ri_spaces(String.reverse.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      ha
    case SCon{+c, +t}:
      +h0 = h
      nr.sp_rev(t, SCon{c, acc}, LT.rt.and_t(RedirectInput.ri_space(c), RedirectInput.ri_spaces(acc), LT.rt.and_l(RedirectInput.ri_space(c), RedirectInput.ri_spaces(t), h0), ha), LT.rt.and_r(RedirectInput.ri_space(c), RedirectInput.ri_spaces(t), h0))

def nr.dot_rev(s: String, +acc: String, ha: {RedirectInput.ri_dots(acc) == True{} : Bool}, h: {RedirectInput.ri_dots(s) == True{} : Bool}) -> {RedirectInput.ri_dots(String.reverse.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      ha
    case SCon{+c, +t}:
      +h0 = h
      nr.dot_rev(t, SCon{c, acc}, LT.rt.and_t(Char.is_eq(c, '.'), RedirectInput.ri_dots(acc), LT.rt.and_l(Char.is_eq(c, '.'), RedirectInput.ri_dots(t), h0), ha), LT.rt.and_r(Char.is_eq(c, '.'), RedirectInput.ri_dots(t), h0))

# a `.` is no whitespace
def nr.dot_ns(c: Char, h: {Char.is_eq(c, '.') == True{} : Bool}) -> {RedirectInput.ri_space(c) == False{} : Bool}:
  match c:
    case Chr{+x}:
      %Equal.sym(U32, x, 46, LCh.shq.eq_sound(x, 46, h)) : {RedirectInput.ri_space(Chr{_}) == False{} : Bool}
      {==}

# dots that hold a char start with no whitespace
def nr.dots_nsf(d: String, h: {RedirectInput.ri_dots(d) == True{} : Bool}, ne: {String.is_empty(d) == False{} : Bool}) -> {RedirectInput.ri_space_first(d) == False{} : Bool}:
  match d:
    case SNil{}:
      LT.rt.absurd({RedirectInput.ri_space_first(SNil{}) == False{} : Bool}, ne)
    case SCon{+c, t}:
      nr.dot_ns(c, LT.rt.and_l(Char.is_eq(c, '.'), RedirectInput.ri_dots(t), h))

# the reverse of a text that holds a char holds one
def nr.rev_ne(s: String, ne: {String.is_empty(s) == False{} : Bool}) -> {String.is_empty(String.reverse(s)) == False{} : Bool}:
  match s:
    case SNil{}:
      LT.rt.absurd({String.is_empty(SNil{}) == False{} : Bool}, ne)
    case SCon{+c, +t}:
      LT.rt.rev_ne(c, t)

# a text that holds a char starts as its first part does
def nr.sf_app(x: String, -y: String, ne: {String.is_empty(x) == False{} : Bool}) -> {RedirectInput.ri_space_first(String.append(x, y)) == RedirectInput.ri_space_first(x) : Bool}:
  match x:
    case SNil{}:
      LT.rt.absurd({RedirectInput.ri_space_first(y) == RedirectInput.ri_space_first(SNil{}) : Bool}, ne)
    case SCon{c, t}:
      {==}

# reversed dots that hold a char, then anything, start with no whitespace
def nr.rdots_nsf(+d: String, +y: String, dd: {RedirectInput.ri_dots(d) == True{} : Bool}, ne: {String.is_empty(d) == False{} : Bool}) -> {RedirectInput.ri_space_first(String.append(String.reverse(d), y)) == False{} : Bool}:
  +rn = nr.rev_ne(d, ne)
  Equal.trans(Bool, RedirectInput.ri_space_first(String.append(String.reverse(d), y)), RedirectInput.ri_space_first(String.reverse(d)), False{}, nr.sf_app(String.reverse(d), y, rn), nr.dots_nsf(String.reverse(d), nr.dot_rev(d, SNil{}, {==}, dd), rn))

# the second trim and the dots, from r d w2 reversed, give r reversed
def nr.back(+r: String, +d: String, +w2: String, sp2: {RedirectInput.ri_spaces(w2) == True{} : Bool}, dd: {RedirectInput.ri_dots(d) == True{} : Bool}, tail: {RedirectInput.ri_dot_first(String.reverse(r)) == False{} : Bool}, keep1: {Ri.trim_start(String.append(r, String.append(d, w2))) == String.append(r, String.append(d, w2)) : String}, keep2: {Ri.trim_start(String.append(String.reverse(d), String.reverse(r))) == String.append(String.reverse(d), String.reverse(r)) : String}) -> {String.reverse(Ri.dots(Ri.trim_start(String.reverse(Ri.trim_start(String.append(r, String.append(d, w2))))))) == r : String}:
  +rr = String.reverse(r)
  +rd = String.reverse(d)
  %Equal.sym(String, Ri.trim_start(String.append(r, String.append(d, w2))), String.append(r, String.append(d, w2)), keep1) : {String.reverse(Ri.dots(Ri.trim_start(String.reverse(_)))) == r : String}
  %Equal.sym(String, String.reverse.go(String.append(r, String.append(d, w2)), SNil{}), String.reverse.go(String.append(d, w2), rr), LT.rt.rev_app(r, String.append(d, w2), SNil{})) : {String.reverse(Ri.dots(Ri.trim_start(_))) == r : String}
  %Equal.sym(String, String.reverse.go(String.append(d, w2), rr), String.reverse.go(w2, String.reverse.go(d, rr)), LT.rt.rev_app(d, w2, rr)) : {String.reverse(Ri.dots(Ri.trim_start(_))) == r : String}
  %Equal.sym(String, String.reverse.go(w2, String.reverse.go(d, rr)), String.append(String.reverse(w2), String.reverse.go(d, rr)), LT.rt.rev_acc(w2, String.reverse.go(d, rr))) : {String.reverse(Ri.dots(Ri.trim_start(_))) == r : String}
  %Equal.sym(String, String.reverse.go(d, rr), String.append(rd, rr), LT.rt.rev_acc(d, rr)) : {String.reverse(Ri.dots(Ri.trim_start(String.append(String.reverse(w2), _)))) == r : String}
  %Equal.sym(String, Ri.trim_start(String.append(String.reverse(w2), String.append(rd, rr))), Ri.trim_start(String.append(rd, rr)), nr.ts1(String.reverse(w2), String.append(rd, rr), nr.sp_rev(w2, SNil{}, {==}, sp2))) : {String.reverse(Ri.dots(_)) == r : String}
  %Equal.sym(String, Ri.trim_start(String.append(rd, rr)), String.append(rd, rr), keep2) : {String.reverse(Ri.dots(_)) == r : String}
  %Equal.sym(String, Ri.dots(String.append(rd, rr)), Ri.dots(rr), nr.d1(rd, rr, nr.dot_rev(d, SNil{}, {==}, dd))) : {String.reverse(_) == r : String}
  %Equal.sym(String, Ri.dots(rr), rr, nr.d2(rr, tail)) : {String.reverse(_) == r : String}
  LT.rt.rev_rev(r)

def nr.cases(r: String, d: String, +w2: String, sp2: {RedirectInput.ri_spaces(w2) == True{} : Bool}, dd: {RedirectInput.ri_dots(d) == True{} : Bool}, head: {RedirectInput.ri_space_first(r) == False{} : Bool}, tail: {RedirectInput.ri_dot_first(String.reverse(r)) == False{} : Bool}, bare: {Bool.and(String.is_empty(d), RedirectInput.ri_space_first(String.reverse(r))) == False{} : Bool}) -> {String.reverse(Ri.dots(Ri.trim_start(String.reverse(Ri.trim_start(String.append(r, String.append(d, w2))))))) == r : String}:
  match r d:
    case SCon{+q, +qs} SCon{+p, +ps}:
      +d0 = dd
      nr.back(SCon{q, qs}, SCon{p, ps}, w2, sp2, d0, tail, nr.ts2(String.append(SCon{q, qs}, String.append(SCon{p, ps}, w2)), head), nr.ts2(String.append(String.reverse(SCon{p, ps}), String.reverse(SCon{q, qs})), nr.rdots_nsf(SCon{p, ps}, String.reverse(SCon{q, qs}), d0, {==})))
    case SCon{+q, +qs} SNil{}:
      nr.back(SCon{q, qs}, SNil{}, w2, sp2, dd, tail, nr.ts2(String.append(SCon{q, qs}, w2), head), nr.ts2(String.reverse(SCon{q, qs}), bare))
    case SNil{} SCon{+p, +ps}:
      +d0 = dd
      nr.back(SNil{}, SCon{p, ps}, w2, sp2, d0, tail, nr.ts2(String.append(SCon{p, ps}, w2), nr.dots_nsf(SCon{p, ps}, d0, {==})), nr.ts2(String.append(String.reverse(SCon{p, ps}), SNil{}), nr.rdots_nsf(SCon{p, ps}, SNil{}, d0, {==})))
    case SNil{} SNil{}:
      +e = Equal.trans(String, Ri.trim_start(w2), Ri.trim_start(String.append(w2, SNil{})), SNil{}, Equal.cong(String, String, z => Ri.trim_start(z), w2, String.append(w2, SNil{}), Equal.sym(String, String.append(w2, SNil{}), w2, LT.rt.app_nil(w2))), nr.ts1(w2, SNil{}, sp2))
      %Equal.sym(String, Ri.trim_start(w2), SNil{}, e) : {String.reverse(Ri.dots(Ri.trim_start(String.reverse(_)))) == SNil{} : String}
      {==}

def nr.reason(+w1: String, +r: String, +d: String, +w2: String, sp1: {RedirectInput.ri_spaces(w1) == True{} : Bool}, sp2: {RedirectInput.ri_spaces(w2) == True{} : Bool}, dd: {RedirectInput.ri_dots(d) == True{} : Bool}, head: {RedirectInput.ri_space_first(r) == False{} : Bool}, tail: {RedirectInput.ri_dot_first(String.reverse(r)) == False{} : Bool}, bare: {Bool.and(String.is_empty(d), RedirectInput.ri_space_first(String.reverse(r))) == False{} : Bool}) -> {Ri.reason(String.append(w1, String.append(r, String.append(d, w2)))) == r : String}:
  %Equal.sym(String, Ri.trim_start(String.append(w1, String.append(r, String.append(d, w2)))), Ri.trim_start(String.append(r, String.append(d, w2))), nr.ts1(w1, String.append(r, String.append(d, w2)), sp1)) : {String.reverse(Ri.dots(Ri.trim_start(String.reverse(_)))) == r : String}
  nr.cases(r, d, w2, sp2, dd, head, tail, bare)

def RedirectInput.redirect_input_notice_reason(w1, r, d, w2, sp1, sp2, dd, head, tail, bare):
  Equal.cong(String, String, z => String.concat(["Login did not complete: ", z, ". Paste the address again, or open the login link again and sign in."]), Ri.reason(String.append(w1, String.append(r, String.append(d, w2)))), r, nr.reason(w1, r, d, w2, sp1, sp2, dd, head, tail, bare))
