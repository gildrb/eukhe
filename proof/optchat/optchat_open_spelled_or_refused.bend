# eukhe: the proof of LAW optchat_open_spelled_or_refused
#
# Every input the entry's open reads whole is exactly the laws' spelling
# of the open it read, and that open fits the wire: each decoder stage,
# given what its sub-decoder read, turns the input into the spelling of
# that part (the wire's exactness laws: Nats, Bools, and the lists of
# built nodes and view lines item by item), and the decoded Nats fit
# (the wire's decoded-fits law). Any other input opens the refused state
# and answers the malformed error.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_optchat.bend as FOc
import ../../bend/optchat/state.bend as OState
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/optchat.bend as Optchat
import ../wire/wire_nat_exact.bend as PWNatExact
import ../wire/wire_nat_decoded_fits.bend as PWNatFits
import ../wire/wire_bool_exact.bend as PWBoolExact
import ../base/bool.bend as LBool
import ./base/ffi_optchat.bend as LAF
import ./optchat_entry_spelled_or_refused.bend as PX

# The spelling, with what follows it
# ----------------------------------

def os.gots(+bs: List<&2, FOc.Got>, r: String) -> String:
  Wr.put_nat(List.length(&2, FOc.Got, bs), Optchat.oc_spell_gots.items(bs, r))

def os.lines(+vs: List<&2, FOc.Line>, r: String) -> String:
  Wr.put_nat(List.length(&2, FOc.Line, vs), Optchat.oc_spell_lines.items(vs, r))

# What each decoder's answer says about its input
# -----------------------------------------------

def os.OP(d: Wr.Dec<FOc.Open>, s: String) -> Type:
  match d:
    case Wr.Got{o, r}:
      match r:
        case SNil{}:
          {Optchat.oc_spell_open(o) == s : String} & {Optchat.oc_open_fits(o) == True{} : Bool}
        case SCon{x, t}:
          Unit
    case Wr.Bad{}:
      Unit

# a list of built nodes read (m + 1 of them), then r
def os.PG(s: String, m: Nat, d: Wr.Dec<List<&2, FOc.Got>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Optchat.oc_spell_gots.items(xs, r) : String} & ({List.length(&2, FOc.Got, xs) == 1n+m : Nat} & {Optchat.oc_gots_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def os.GS(s: String, d: Wr.Dec<List<&2, FOc.Got>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == os.gots(xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, FOc.Got, xs)) == True{} : Bool} & {Optchat.oc_gots_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def os.PL(s: String, m: Nat, d: Wr.Dec<List<&2, FOc.Line>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Optchat.oc_spell_lines.items(xs, r) : String} & ({List.length(&2, FOc.Line, xs) == 1n+m : Nat} & {Optchat.oc_lines_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def os.LS(s: String, d: Wr.Dec<List<&2, FOc.Line>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == os.lines(xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, FOc.Line, xs)) == True{} : Bool} & {Optchat.oc_lines_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

# Logic
# -----

def os.str_cong(-s: String, -a: String, -b: String, -f: String -> String, e1: {s == f(a) : String}, e2: {a == b : String}) -> {s == f(b) : String}:
  Equal.trans(String, s, f(a), f(b), e1, Equal.cong(String, String, f, a, b, e2))

# a, b, c true: a and b and c and the rest
def os.and4(+a: Bool, +b: Bool, +c: Bool, -d: Bool, +f: {Bool.and(a, Bool.and(b, c)) == True{} : Bool}, fd: {d == True{} : Bool}) -> {Bool.and(a, Bool.and(b, Bool.and(c, d))) == True{} : Bool}:
  +fa = LAF.oe.and_l(a, Bool.and(b, c), f)
  +fbc = LAF.oe.and_r(a, Bool.and(b, c), f)
  LBool.cb_and_intro(a, Bool.and(b, Bool.and(c, d)), fa, LBool.cb_and_intro(b, Bool.and(c, d), LAF.oe.and_l(b, c, fbc), LBool.cb_and_intro(c, d, LAF.oe.and_r(b, c, fbc), fd)))

def os.and3(+a: Bool, +b: Bool, -c: Bool, +f: {Bool.and(a, b) == True{} : Bool}, fc: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  LBool.cb_and_intro(a, Bool.and(b, c), LAF.oe.and_l(a, b, f), LBool.cb_and_intro(b, c, LAF.oe.and_r(a, b, f), fc))

# The built nodes
# ---------------

def os.gstep(-s: String, +l: Nat, +k: Nat, +z: Nat, +s3: String, -m: Nat, es: {s == Optchat.oc_spell_lk(l, k, Wr.put_nat(z, s3)) : String}, f: {Bool.and(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(z))) == True{} : Bool},
  d: Wr.Dec<List<&2, FOc.Got>>, ih: os.PG(s3, m, d)) -> os.PG(s, 1n+m, Wr.get_list.cons(FOc.Got, FOc.Got{l, k, z}, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (os.str_cong(s, s3, Optchat.oc_spell_gots.items(ys, r), x => Optchat.oc_spell_lk(l, k, Wr.put_nat(z, x)), es, e1), (Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, FOc.Got, ys), 1n+m, e2), os.and4(LawsBase.wire_fits(l), LawsBase.wire_fits(k), LawsBase.wire_fits(z), Optchat.oc_gots_fit(ys), f, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled built nodes that fit
def os.gloop(m: Nat, cur: Wr.Dec<FOc.Got>, +s: String, gp: PX.ox.GP(cur, s)) -> os.PG(s, m, Wr.get_list.go(~FOc.Got, ~FOc.get_got, m, cur)):
  match m cur:
    case 0n Wr.Got{x, +s3}:
      match x:
        case FOc.Got{+l, +k, +z}:
          (es, f) = gp
          (es, ({==}, os.and4(LawsBase.wire_fits(l), LawsBase.wire_fits(k), LawsBase.wire_fits(z), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k1 Wr.Got{x, +s3}:
      match x:
        case FOc.Got{+l, +k, +z}:
          (es, f) = gp
          os.gstep(s, l, k, z, s3, k1, es, f, Wr.get_list.go(~FOc.Got, ~FOc.get_got, k1, FOc.get_got(s3)), os.gloop(k1, FOc.get_got(s3), s3, PX.ox.got(s3)))
    case 1n++k1 Wr.Bad{}:
      Unit{}

def os.gconv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, FOc.Got>>, pg: os.PG(s2, m, d)) -> os.GS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pg
      (+e2, e3) = e23
      %Equal.sym(Nat, List.length(&2, FOc.Got, xs), 1n+m, e2) : {s == Wr.put_nat(_, Optchat.oc_spell_gots.items(xs, r)) : String} & ({LawsBase.wire_fits(_) == True{} : Bool} & {Optchat.oc_gots_fit(xs) == True{} : Bool})
      (os.str_cong(s, s2, Optchat.oc_spell_gots.items(xs, r), x => Wr.put_nat(1n+m, x), en, e1), (fn, e3))
    case Wr.Bad{}:
      Unit{}

def os.gtop(+s: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> os.GS(s, Wr.get_list.start(~FOc.Got, ~FOc.get_got, r)):
  match r:
    case Wr.Got{+n, +s2}:
      match n:
        case 0n:
          +h = hr
          (Wire.wire_nat_exact(s, 0n, s2, h), (Wire.wire_nat_decoded_fits(s, 0n, s2, h), {==}))
        case 1n++m:
          +h = hr
          os.gconv(s, s2, m, Wire.wire_nat_exact(s, 1n+m, s2, h), Wire.wire_nat_decoded_fits(s, 1n+m, s2, h), Wr.get_list.go(~FOc.Got, ~FOc.get_got, m, FOc.get_got(s2)), os.gloop(m, FOc.get_got(s2), s2, PX.ox.got(s2)))
    case Wr.Bad{}:
      Unit{}

# a list of built nodes decoded is spelled, and what it holds fits
def os.glist(+s: String) -> os.GS(s, Wr.get_list(~FOc.Got, ~FOc.get_got, s)):
  os.gtop(s, Wr.get_nat(s), {==})

# The view lines
# --------------

def os.lstep(-s: String, +l: Nat, +k: Nat, +s3: String, -m: Nat, es: {s == Optchat.oc_spell_lk(l, k, s3) : String}, f: {Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(k)) == True{} : Bool},
  d: Wr.Dec<List<&2, FOc.Line>>, ih: os.PL(s3, m, d)) -> os.PL(s, 1n+m, Wr.get_list.cons(FOc.Line, FOc.Line{l, k}, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (os.str_cong(s, s3, Optchat.oc_spell_lines.items(ys, r), x => Optchat.oc_spell_lk(l, k, x), es, e1), (Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, FOc.Line, ys), 1n+m, e2), os.and3(LawsBase.wire_fits(l), LawsBase.wire_fits(k), Optchat.oc_lines_fit(ys), f, e3)))
    case Wr.Bad{}:
      Unit{}

def os.lloop(m: Nat, cur: Wr.Dec<FOc.Line>, +s: String, lp: PX.ox.LP(cur, s)) -> os.PL(s, m, Wr.get_list.go(~FOc.Line, ~FOc.get_line, m, cur)):
  match m cur:
    case 0n Wr.Got{x, +s3}:
      match x:
        case FOc.Line{+l, +k}:
          (es, f) = lp
          (es, ({==}, os.and3(LawsBase.wire_fits(l), LawsBase.wire_fits(k), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k1 Wr.Got{x, +s3}:
      match x:
        case FOc.Line{+l, +k}:
          (es, f) = lp
          os.lstep(s, l, k, s3, k1, es, f, Wr.get_list.go(~FOc.Line, ~FOc.get_line, k1, FOc.get_line(s3)), os.lloop(k1, FOc.get_line(s3), s3, PX.ox.line(s3)))
    case 1n++k1 Wr.Bad{}:
      Unit{}

def os.lconv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, FOc.Line>>, pl: os.PL(s2, m, d)) -> os.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      %Equal.sym(Nat, List.length(&2, FOc.Line, xs), 1n+m, e2) : {s == Wr.put_nat(_, Optchat.oc_spell_lines.items(xs, r)) : String} & ({LawsBase.wire_fits(_) == True{} : Bool} & {Optchat.oc_lines_fit(xs) == True{} : Bool})
      (os.str_cong(s, s2, Optchat.oc_spell_lines.items(xs, r), x => Wr.put_nat(1n+m, x), en, e1), (fn, e3))
    case Wr.Bad{}:
      Unit{}

def os.ltop(+s: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> os.LS(s, Wr.get_list.start(~FOc.Line, ~FOc.get_line, r)):
  match r:
    case Wr.Got{+n, +s2}:
      match n:
        case 0n:
          +h = hr
          (Wire.wire_nat_exact(s, 0n, s2, h), (Wire.wire_nat_decoded_fits(s, 0n, s2, h), {==}))
        case 1n++m:
          +h = hr
          os.lconv(s, s2, m, Wire.wire_nat_exact(s, 1n+m, s2, h), Wire.wire_nat_decoded_fits(s, 1n+m, s2, h), Wr.get_list.go(~FOc.Line, ~FOc.get_line, m, FOc.get_line(s2)), os.lloop(m, FOc.get_line(s2), s2, PX.ox.line(s2)))
    case Wr.Bad{}:
      Unit{}

# a list of view lines decoded is spelled, and what it holds fits
def os.llist(+s: String) -> os.LS(s, Wr.get_list(~FOc.Line, ~FOc.get_line, s)):
  os.ltop(s, Wr.get_nat(s), {==})

# The open, stage by stage
# ------------------------
# Each stage reads one field of the open from what is left (s_k); its
# claim is about the whole input, spelled from the fields read so far and
# then s_k.

# the sizes ph, ceil, floor, cceil, cfloor, jobs, then x
def os.pre(a: Nat, b: Nat, c: Nat, d: Nat, e: Nat, f: Nat, x: String) -> String:
  Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, Wr.put_nat(d, Wr.put_nat(e, Wr.put_nat(f, x))))))

# every number and item of an open fits
def os.fits(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, +t: Nat, +bs: List<&2, FOc.Got>, +vs: List<&2, FOc.Line>, -sh: Bool, -m: Bool, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, fe: {LawsBase.wire_fits(e) == True{} : Bool}, ff: {LawsBase.wire_fits(f) == True{} : Bool}, ft: {LawsBase.wire_fits(t) == True{} : Bool}, flb: {LawsBase.wire_fits(List.length(&2, FOc.Got, bs)) == True{} : Bool}, flv: {LawsBase.wire_fits(List.length(&2, FOc.Line, vs)) == True{} : Bool}, fg: {Optchat.oc_gots_fit(bs) == True{} : Bool}, fv: {Optchat.oc_lines_fit(vs) == True{} : Bool}) -> {Optchat.oc_open_fits(FOc.Open{OState.Cfg{a, b, c, d, e, f}, t, bs, vs, sh, m}) == True{} : Bool}:
  +lb = List.length(&2, FOc.Got, bs)
  +lv = List.length(&2, FOc.Line, vs)
  +n9 = LBool.cb_and_intro(LawsBase.wire_fits(lv), True{}, flv, {==})
  +n8 = LBool.cb_and_intro(LawsBase.wire_fits(lb), LawsBase.wire_nats_fit([lv]), flb, n9)
  +n7 = LBool.cb_and_intro(LawsBase.wire_fits(t), LawsBase.wire_nats_fit([lb, lv]), ft, n8)
  +n6 = LBool.cb_and_intro(LawsBase.wire_fits(f), LawsBase.wire_nats_fit([t, lb, lv]), ff, n7)
  +n5 = LBool.cb_and_intro(LawsBase.wire_fits(e), LawsBase.wire_nats_fit([f, t, lb, lv]), fe, n6)
  +n4 = LBool.cb_and_intro(LawsBase.wire_fits(d), LawsBase.wire_nats_fit([e, f, t, lb, lv]), fd, n5)
  +n3 = LBool.cb_and_intro(LawsBase.wire_fits(c), LawsBase.wire_nats_fit([d, e, f, t, lb, lv]), fc, n4)
  +n2 = LBool.cb_and_intro(LawsBase.wire_fits(b), LawsBase.wire_nats_fit([c, d, e, f, t, lb, lv]), fb, n3)
  +n1 = LBool.cb_and_intro(LawsBase.wire_fits(a), LawsBase.wire_nats_fit([b, c, d, e, f, t, lb, lv]), fa, n2)
  LBool.cb_and_intro(LawsBase.wire_nats_fit([a, b, c, d, e, f, t, lb, lv]), Bool.and(Optchat.oc_gots_fit(bs), Optchat.oc_lines_fit(vs)), n1, LBool.cb_and_intro(Optchat.oc_gots_fit(bs), Optchat.oc_lines_fit(vs), fg, fv))

def os.missed(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, +t: Nat, +bs: List<&2, FOc.Got>, +vs: List<&2, FOc.Line>, +sh: Bool, +s10: String, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, fe: {LawsBase.wire_fits(e) == True{} : Bool}, ff: {LawsBase.wire_fits(f) == True{} : Bool}, ft: {LawsBase.wire_fits(t) == True{} : Bool}, flb: {LawsBase.wire_fits(List.length(&2, FOc.Got, bs)) == True{} : Bool}, flv: {LawsBase.wire_fits(List.length(&2, FOc.Line, vs)) == True{} : Bool}, fg: {Optchat.oc_gots_fit(bs) == True{} : Bool}, fv: {Optchat.oc_lines_fit(vs) == True{} : Bool}, r: Wr.Dec<Bool>, hr: {Wr.get_bool(s10) == r : Wr.Dec<Bool>}) -> os.OP(FOc.get_open.missed(OState.Cfg{a, b, c, d, e, f}, t, bs, vs, sh, r), os.pre(a, b, c, d, e, f, Wr.put_nat(t, os.gots(bs, os.lines(vs, Wr.put_bool(sh, s10)))))):
  match r:
    case Wr.Got{+m, s11}:
      match s11:
        case SNil{}:
          +h = hr
          %Equal.sym(String, s10, Wr.put_bool(m, ""), Wire.wire_bool_exact(s10, m, "", h)) : os.OP(Wr.Got{FOc.Open{OState.Cfg{a, b, c, d, e, f}, t, bs, vs, sh, m}, ""}, os.pre(a, b, c, d, e, f, Wr.put_nat(t, os.gots(bs, os.lines(vs, Wr.put_bool(sh, _))))))
          ({==}, os.fits(a, b, c, d, e, f, t, bs, vs, sh, m, fa, fb, fc, fd, fe, ff, ft, flb, flv, fg, fv))
        case SCon{x, y}:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def os.shrink(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, +t: Nat, +bs: List<&2, FOc.Got>, +vs: List<&2, FOc.Line>, +s9: String, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, fe: {LawsBase.wire_fits(e) == True{} : Bool}, ff: {LawsBase.wire_fits(f) == True{} : Bool}, ft: {LawsBase.wire_fits(t) == True{} : Bool}, flb: {LawsBase.wire_fits(List.length(&2, FOc.Got, bs)) == True{} : Bool}, flv: {LawsBase.wire_fits(List.length(&2, FOc.Line, vs)) == True{} : Bool}, fg: {Optchat.oc_gots_fit(bs) == True{} : Bool}, fv: {Optchat.oc_lines_fit(vs) == True{} : Bool}, r: Wr.Dec<Bool>, hr: {Wr.get_bool(s9) == r : Wr.Dec<Bool>}) -> os.OP(FOc.get_open.shrink(OState.Cfg{a, b, c, d, e, f}, t, bs, vs, r), os.pre(a, b, c, d, e, f, Wr.put_nat(t, os.gots(bs, os.lines(vs, s9))))):
  match r:
    case Wr.Got{+sh, +s10}:
      +h = hr
      %Equal.sym(String, s9, Wr.put_bool(sh, s10), Wire.wire_bool_exact(s9, sh, s10, h)) : os.OP(FOc.get_open.missed(OState.Cfg{a, b, c, d, e, f}, t, bs, vs, sh, Wr.get_bool(s10)), os.pre(a, b, c, d, e, f, Wr.put_nat(t, os.gots(bs, os.lines(vs, _)))))
      os.missed(a, b, c, d, e, f, t, bs, vs, sh, s10, fa, fb, fc, fd, fe, ff, ft, flb, flv, fg, fv, Wr.get_bool(s10), {==})
    case Wr.Bad{}:
      Unit{}

def os.view(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, +t: Nat, +bs: List<&2, FOc.Got>, +s8: String, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, fe: {LawsBase.wire_fits(e) == True{} : Bool}, ff: {LawsBase.wire_fits(f) == True{} : Bool}, ft: {LawsBase.wire_fits(t) == True{} : Bool}, flb: {LawsBase.wire_fits(List.length(&2, FOc.Got, bs)) == True{} : Bool}, fg: {Optchat.oc_gots_fit(bs) == True{} : Bool}, dv: Wr.Dec<List<&2, FOc.Line>>, ls: os.LS(s8, dv)) -> os.OP(FOc.get_open.view(OState.Cfg{a, b, c, d, e, f}, t, bs, dv), os.pre(a, b, c, d, e, f, Wr.put_nat(t, os.gots(bs, s8)))):
  match dv:
    case Wr.Got{+vs, +s9}:
      (e1, e23) = ls
      (flv, fv) = e23
      %Equal.sym(String, s8, os.lines(vs, s9), e1) : os.OP(FOc.get_open.shrink(OState.Cfg{a, b, c, d, e, f}, t, bs, vs, Wr.get_bool(s9)), os.pre(a, b, c, d, e, f, Wr.put_nat(t, os.gots(bs, _))))
      os.shrink(a, b, c, d, e, f, t, bs, vs, s9, fa, fb, fc, fd, fe, ff, ft, flb, flv, fg, fv, Wr.get_bool(s9), {==})
    case Wr.Bad{}:
      Unit{}

def os.built(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, +t: Nat, +s7: String, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, fe: {LawsBase.wire_fits(e) == True{} : Bool}, ff: {LawsBase.wire_fits(f) == True{} : Bool}, ft: {LawsBase.wire_fits(t) == True{} : Bool}, db: Wr.Dec<List<&2, FOc.Got>>, gs: os.GS(s7, db)) -> os.OP(FOc.get_open.built(OState.Cfg{a, b, c, d, e, f}, t, db), os.pre(a, b, c, d, e, f, Wr.put_nat(t, s7))):
  match db:
    case Wr.Got{+bs, +s8}:
      (e1, e23) = gs
      (flb, fg) = e23
      %Equal.sym(String, s7, os.gots(bs, s8), e1) : os.OP(FOc.get_open.view(OState.Cfg{a, b, c, d, e, f}, t, bs, Wr.get_list(~FOc.Line, ~FOc.get_line, s8)), os.pre(a, b, c, d, e, f, Wr.put_nat(t, _)))
      os.view(a, b, c, d, e, f, t, bs, s8, fa, fb, fc, fd, fe, ff, ft, flb, fg, Wr.get_list(~FOc.Line, ~FOc.get_line, s8), os.llist(s8))
    case Wr.Bad{}:
      Unit{}

def os.t(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, +s6: String, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, fe: {LawsBase.wire_fits(e) == True{} : Bool}, ff: {LawsBase.wire_fits(f) == True{} : Bool}, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s6) == r : Wr.Dec<Nat>}) -> os.OP(FOc.get_open.t(OState.Cfg{a, b, c, d, e, f}, r), os.pre(a, b, c, d, e, f, s6)):
  match r:
    case Wr.Got{+t, +s7}:
      +h = hr
      %Equal.sym(String, s6, Wr.put_nat(t, s7), Wire.wire_nat_exact(s6, t, s7, h)) : os.OP(FOc.get_open.built(OState.Cfg{a, b, c, d, e, f}, t, Wr.get_list(~FOc.Got, ~FOc.get_got, s7)), os.pre(a, b, c, d, e, f, _))
      os.built(a, b, c, d, e, f, t, s7, fa, fb, fc, fd, fe, ff, Wire.wire_nat_decoded_fits(s6, t, s7, h), Wr.get_list(~FOc.Got, ~FOc.get_got, s7), os.glist(s7))
    case Wr.Bad{}:
      Unit{}

def os.c5(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +s5: String, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, fe: {LawsBase.wire_fits(e) == True{} : Bool}, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s5) == r : Wr.Dec<Nat>}) -> os.OP(FOc.get_open.cfg(FOc.get_cfg.jobs(a, b, c, d, e, r)), Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, Wr.put_nat(d, Wr.put_nat(e, s5)))))):
  match r:
    case Wr.Got{+f, +s6}:
      +h = hr
      %Equal.sym(String, s5, Wr.put_nat(f, s6), Wire.wire_nat_exact(s5, f, s6, h)) : os.OP(FOc.get_open.t(OState.Cfg{a, b, c, d, e, f}, Wr.get_nat(s6)), Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, Wr.put_nat(d, Wr.put_nat(e, _))))))
      os.t(a, b, c, d, e, f, s6, fa, fb, fc, fd, fe, Wire.wire_nat_decoded_fits(s5, f, s6, h), Wr.get_nat(s6), {==})
    case Wr.Bad{}:
      Unit{}

def os.c4(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +s4: String, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fd: {LawsBase.wire_fits(d) == True{} : Bool}, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s4) == r : Wr.Dec<Nat>}) -> os.OP(FOc.get_open.cfg(FOc.get_cfg.cfloor(a, b, c, d, r)), Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, Wr.put_nat(d, s4))))):
  match r:
    case Wr.Got{+e, +s5}:
      +h = hr
      %Equal.sym(String, s4, Wr.put_nat(e, s5), Wire.wire_nat_exact(s4, e, s5, h)) : os.OP(FOc.get_open.cfg(FOc.get_cfg.jobs(a, b, c, d, e, Wr.get_nat(s5))), Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, Wr.put_nat(d, _)))))
      os.c5(a, b, c, d, e, s5, fa, fb, fc, fd, Wire.wire_nat_decoded_fits(s4, e, s5, h), Wr.get_nat(s5), {==})
    case Wr.Bad{}:
      Unit{}

def os.c3(+a: Nat, +b: Nat, +c: Nat, +s3: String, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s3) == r : Wr.Dec<Nat>}) -> os.OP(FOc.get_open.cfg(FOc.get_cfg.cceil(a, b, c, r)), Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, s3)))):
  match r:
    case Wr.Got{+d, +s4}:
      +h = hr
      %Equal.sym(String, s3, Wr.put_nat(d, s4), Wire.wire_nat_exact(s3, d, s4, h)) : os.OP(FOc.get_open.cfg(FOc.get_cfg.cfloor(a, b, c, d, Wr.get_nat(s4))), Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, _))))
      os.c4(a, b, c, d, s4, fa, fb, fc, Wire.wire_nat_decoded_fits(s3, d, s4, h), Wr.get_nat(s4), {==})
    case Wr.Bad{}:
      Unit{}

def os.c2(+a: Nat, +b: Nat, +s2: String, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s2) == r : Wr.Dec<Nat>}) -> os.OP(FOc.get_open.cfg(FOc.get_cfg.floor(a, b, r)), Wr.put_nat(a, Wr.put_nat(b, s2))):
  match r:
    case Wr.Got{+c, +s3}:
      +h = hr
      %Equal.sym(String, s2, Wr.put_nat(c, s3), Wire.wire_nat_exact(s2, c, s3, h)) : os.OP(FOc.get_open.cfg(FOc.get_cfg.cceil(a, b, c, Wr.get_nat(s3))), Wr.put_nat(a, Wr.put_nat(b, _)))
      os.c3(a, b, c, s3, fa, fb, Wire.wire_nat_decoded_fits(s2, c, s3, h), Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def os.c1(+a: Nat, +s1: String, fa: {LawsBase.wire_fits(a) == True{} : Bool}, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}) -> os.OP(FOc.get_open.cfg(FOc.get_cfg.ceil(a, r)), Wr.put_nat(a, s1)):
  match r:
    case Wr.Got{+b, +s2}:
      +h = hr
      %Equal.sym(String, s1, Wr.put_nat(b, s2), Wire.wire_nat_exact(s1, b, s2, h)) : os.OP(FOc.get_open.cfg(FOc.get_cfg.floor(a, b, Wr.get_nat(s2))), Wr.put_nat(a, _))
      os.c2(a, b, s2, fa, Wire.wire_nat_decoded_fits(s1, b, s2, h), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def os.c0(+i: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(i) == r : Wr.Dec<Nat>}) -> os.OP(FOc.get_open.cfg(FOc.get_cfg.ph(r)), i):
  match r:
    case Wr.Got{+a, +s1}:
      +h = hr
      %Equal.sym(String, i, Wr.put_nat(a, s1), Wire.wire_nat_exact(i, a, s1, h)) : os.OP(FOc.get_open.cfg(FOc.get_cfg.ceil(a, Wr.get_nat(s1))), _)
      os.c1(a, s1, Wire.wire_nat_decoded_fits(i, a, s1, h), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# The law
# -------

# an input the entry's open does not read whole opens the refused state
def os.refuse(+i: String, -d: Wr.Dec<FOc.Open>, hd: {FOc.get_open(i) == d : Wr.Dec<FOc.Open>}, k: {FOc.open.go(d) == (FOc.Refused{}, Wr.err("optchat: malformed open")) : FOc.St & String})
  -> {FOc.open(i) == (FOc.Refused{}, Wr.err("optchat: malformed open")) : FOc.St & String}:
  %Equal.sym(Wr.Dec<FOc.Open>, FOc.get_open(i), d, hd) : {FOc.open.go(_) == (FOc.Refused{}, Wr.err("optchat: malformed open")) : FOc.St & String}
  k

# an open the entry reads whole is the spelling of what it read
def os.whole(+i: String, +o: FOc.Open, hd: {FOc.get_open(i) == Wr.Got{o, ""} : Wr.Dec<FOc.Open>}) -> {Optchat.oc_spell_open(o) == i : String} & {Optchat.oc_open_fits(o) == True{} : Bool}:
  %hd : os.OP(_, i)
  os.c0(i, Wr.get_nat(i), {==})

def os.ans(+i: String, d: Wr.Dec<FOc.Open>, hd: {FOc.get_open(i) == d : Wr.Dec<FOc.Open>}) -> Optchat.oc_open_spelled(i) | {FOc.open(i) == (FOc.Refused{}, Wr.err("optchat: malformed open")) : FOc.St & String}:
  match d:
    case Wr.Got{+o, rest}:
      match rest:
        case SNil{}:
          Inl{(o, os.whole(i, o, hd))}
        case SCon{c, t}:
          Inr{os.refuse(i, Wr.Got{o, SCon{c, t}}, hd, {==})}
    case Wr.Bad{}:
      Inr{os.refuse(i, Wr.Bad{}, hd, {==})}

def Optchat.optchat_open_spelled_or_refused(i):
  os.ans(i, FOc.get_open(i), {==})
