# eukhe: the screen entry's decoders read only spelled values that fit:
# whatever a decoder of bend/ffi_screen.bend reads is the laws' spelling
# (laws/screen/interface.bend `screen_spell_*`) of what it read, then its rest, and
# fits the wire (sx.req for a request), tag by tag with the wire's
# exactness laws (an unknown tag is Bad), list by list with an item loop
# that carries the input spelled up to its item (sx.*.loop).

import Base
import ../../../bend/ffi_screen.bend as FSc
import ../../../bend/screen.bend as Sc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/screen/interface.bend as Screen
import ../../../laws/wire.bend as Wire
import ../../wire/base/spell.bend as LAWireSpell
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact

# s spelled up to a field a is s spelled up to its spelling b
def sx.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# Nat
# ---

def sx.Nat(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Wr.put_nat(x, r) : String} & {LawsBase.wire_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.nat.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.Nat(s, d):
  match d:
    case Wr.Got{+x, +r}:
      +e = ed
      (Wire.wire_nat_exact(s, x, r, e), Wire.wire_nat_decoded_fits(s, x, r, e))
    case Wr.Bad{}:
      Unit{}

def sx.nat(+s: String) -> sx.Nat(s, Wr.get_nat(s)):
  sx.nat.go(s, Wr.get_nat(s), {==})

# Block states and blocks
# -----------------------

def sx.St(s: String, d: Wr.Dec<Sc.St>) -> Type:
  match d:
    case Wr.Got{st, r}:
      {s == Screen.screen_spell_st(st, r) : String}
    case Wr.Bad{}:
      Unit

def sx.st.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.St(s, FSc.get_st.of(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s0, ed)
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def sx.st(+s: String) -> sx.St(s, FSc.get_st(s)):
  sx.st.go(s, Wr.get_nat(s), {==})

def sx.Blk(s: String, d: Wr.Dec<Sc.Blk>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Screen.screen_spell_blk(b, r) : String} & {Screen.blk_fits(b) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.blk.len(-s: String, +i: Nat, +st: Sc.St, +s2: String, pre: {s == Wr.put_nat(i, Screen.screen_spell_st(st, s2)) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> sx.Blk(s, FSc.get_blk.len(i, st, d)):
  match d:
    case Wr.Got{+l, +s3}:
      +e = ed
      (sx.step(z => Wr.put_nat(i, Screen.screen_spell_st(st, z)), s, s2, Wr.put_nat(l, s3), pre, Wire.wire_nat_exact(s2, l, s3, e)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(i), LawsBase.wire_fits(l), fi, Wire.wire_nat_decoded_fits(s2, l, s3, e)))
    case Wr.Bad{}:
      Unit{}

def sx.blk.st(-s: String, +i: Nat, +s1: String, pre: {s == Wr.put_nat(i, s1) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Sc.St>, xd: sx.St(s1, d)) -> sx.Blk(s, FSc.get_blk.st(i, d)):
  match d:
    case Wr.Got{+st, +s2}:
      sx.blk.len(s, i, st, s2, sx.step(z => Wr.put_nat(i, z), s, s1, Screen.screen_spell_st(st, s2), pre, xd), fi, Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def sx.blk.id(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.Blk(s, FSc.get_blk.id(d)):
  match d:
    case Wr.Got{+i, +s1}:
      +e = ed
      sx.blk.st(s, i, s1, Wire.wire_nat_exact(s, i, s1, e), Wire.wire_nat_decoded_fits(s, i, s1, e), FSc.get_st(s1), sx.st(s1))
    case Wr.Bad{}:
      Unit{}

def sx.blk(+s: String) -> sx.Blk(s, FSc.get_blk(s)):
  sx.blk.id(s, Wr.get_nat(s), {==})

# Lists of blocks
# ---------------

# what the item loop's answer says about its input s (m + 1 items)
def sx.blks.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Sc.Blk>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Screen.screen_spell_blks.items(xs, r) : String} & ({List.length(&2, Sc.Blk, xs) == 1n+m : Nat} & {Screen.blks_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def sx.blks.step(-s: String, +x: Sc.Blk, +s3: String, -k: Nat, ex: {s == Screen.screen_spell_blk(x, s3) : String}, fx: {Screen.blk_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Sc.Blk>>, ih: sx.blks.PL(s3, k, d)) -> sx.blks.PL(s, 1n+k, Wr.get_list.cons(Sc.Blk, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (sx.step(z => Screen.screen_spell_blk(x, z), s, s3, Screen.screen_spell_blks.items(ys, r), ex, e1), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Sc.Blk, ys), 1n+k, e2), LAWireSpell.ws_and_tt(Screen.blk_fits(x), Screen.blks_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled blocks that fit
def sx.blks.loop(m: Nat, cur: Wr.Dec<Sc.Blk>, +s: String, pc: sx.Blk(s, cur)) -> sx.blks.PL(s, m, Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(Screen.blk_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      sx.blks.step(s, x, s3, k, e, f, Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, k, FSc.get_blk(s3)), sx.blks.loop(k, FSc.get_blk(s3), s3, sx.blk(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def sx.blks.LS(s: String, d: Wr.Dec<List<&2, Sc.Blk>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Screen.screen_spell_blks(xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, Sc.Blk, xs)) == True{} : Bool} & {Screen.blks_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def sx.blks.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Sc.Blk>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == Screen.screen_spell_blks.items(xs, r) : String}, e2: {List.length(&2, Sc.Blk, xs) == 1n+m : Nat}) -> {s == Screen.screen_spell_blks(xs, r) : String}:
  %Equal.sym(Nat, List.length(&2, Sc.Blk, xs), 1n+m, e2) : {s == Wr.put_nat(_, Screen.screen_spell_blks.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def sx.blks.conv_f(-m: Nat, -xs: List<&2, Sc.Blk>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Sc.Blk, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Sc.Blk, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Sc.Blk, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def sx.blks.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Sc.Blk>>, pl: sx.blks.PL(s2, m, d)) -> sx.blks.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (sx.blks.conv_s(s, s2, m, xs, r, en, e1, e2), (sx.blks.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def sx.blks.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> sx.blks.LS(s, Wr.get_list.start(~Sc.Blk, ~FSc.get_blk, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      sx.blks.conv(s, s2, m, en, fn, Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, m, FSc.get_blk(s2)), sx.blks.loop(m, FSc.get_blk(s2), s2, sx.blk(s2)))

def sx.blks.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.blks.LS(s, Wr.get_list.start(~Sc.Blk, ~FSc.get_blk, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      sx.blks.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

def sx.blks(+s: String) -> sx.blks.LS(s, Wr.get_list(~Sc.Blk, ~FSc.get_blk, s)):
  sx.blks.top(s, Wr.get_nat(s), {==})

# Transcripts
# -----------

def sx.Tx(s: String, d: Wr.Dec<Sc.Tx>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == Screen.screen_spell_tx(t, r) : String} & {Screen.tx_fits(t) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.tx.w(-s: String, +bs: List<&2, Sc.Blk>, +n: Nat, +s2: String, pre: {s == Screen.screen_spell_blks(bs, Wr.put_nat(n, s2)) : String}, fl: {LawsBase.wire_fits(List.length(&2, Sc.Blk, bs)) == True{} : Bool}, fb: {Screen.blks_fit(bs) == True{} : Bool}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> sx.Tx(s, FSc.get_tx.w(bs, n, d)):
  match d:
    case Wr.Got{+w, +s3}:
      +e = ed
      +fw = Wire.wire_nat_decoded_fits(s2, w, s3, e)
      (sx.step(z => Screen.screen_spell_blks(bs, Wr.put_nat(n, z)), s, s2, Wr.put_nat(w, s3), pre, Wire.wire_nat_exact(s2, w, s3, e)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Sc.Blk, bs)), Bool.and(Screen.blks_fit(bs), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(w))), fl, LAWireSpell.ws_and_tt(Screen.blks_fit(bs), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(w)), fb, LAWireSpell.ws_and_tt(LawsBase.wire_fits(n), LawsBase.wire_fits(w), fn, fw))))
    case Wr.Bad{}:
      Unit{}

def sx.tx.n(-s: String, +bs: List<&2, Sc.Blk>, +s1: String, pre: {s == Screen.screen_spell_blks(bs, s1) : String}, fl: {LawsBase.wire_fits(List.length(&2, Sc.Blk, bs)) == True{} : Bool}, fb: {Screen.blks_fit(bs) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> sx.Tx(s, FSc.get_tx.n(bs, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      sx.tx.w(s, bs, n, s2, sx.step(z => Screen.screen_spell_blks(bs, z), s, s1, Wr.put_nat(n, s2), pre, Wire.wire_nat_exact(s1, n, s2, e)), fl, fb, Wire.wire_nat_decoded_fits(s1, n, s2, e), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def sx.tx.bs(+s: String, d: Wr.Dec<List<&2, Sc.Blk>>, xd: sx.blks.LS(s, d)) -> sx.Tx(s, FSc.get_tx.bs(d)):
  match d:
    case Wr.Got{+bs, +s1}:
      (e, f) = xd
      (fl, fb) = f
      sx.tx.n(s, bs, s1, e, fl, fb, Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def sx.tx(+s: String) -> sx.Tx(s, FSc.get_tx(s)):
  sx.tx.bs(s, Wr.get_list(~Sc.Blk, ~FSc.get_blk, s), sx.blks(s))

# Events
# ------

def sx.Ev(s: String, d: Wr.Dec<Sc.Ev>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == Screen.screen_spell_ev(e, r) : String} & {Screen.ev_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.ev.grow_n(-s: String, +x: Nat, +s1: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(x, s1)) : String}, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> sx.Ev(s, FSc.get_ev.n(x, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      (sx.step(z => Wr.put_nat(1n, Wr.put_nat(x, z)), s, s1, Wr.put_nat(n, s2), pre, Wire.wire_nat_exact(s1, n, s2, e)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), LawsBase.wire_fits(n), fx, Wire.wire_nat_decoded_fits(s1, n, s2, e)))
    case Wr.Bad{}:
      Unit{}

def sx.ev.grow_x(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> sx.Ev(s, FSc.get_ev.x(d)):
  match d:
    case Wr.Got{+x, +s1}:
      +e = ed
      sx.ev.grow_n(s, x, s1, sx.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(x, s1), pre, Wire.wire_nat_exact(s0, x, s1, e)), Wire.wire_nat_decoded_fits(s0, x, s1, e), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def sx.ev.fin(-s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> sx.Ev(s, FSc.get_ev.one(d)):
  match d:
    case Wr.Got{+x, +s1}:
      +e = ed
      (sx.step(z => Wr.put_nat(2n, z), s, s0, Wr.put_nat(x, s1), pre, Wire.wire_nat_exact(s0, x, s1, e)), Wire.wire_nat_decoded_fits(s0, x, s1, e))
    case Wr.Bad{}:
      Unit{}

def sx.ev.resize(-s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> sx.Ev(s, FSc.get_ev.w(d)):
  match d:
    case Wr.Got{+w, +s1}:
      +e = ed
      (sx.step(z => Wr.put_nat(4n, z), s, s0, Wr.put_nat(w, s1), pre, Wire.wire_nat_exact(s0, w, s1, e)), Wire.wire_nat_decoded_fits(s0, w, s1, e))
    case Wr.Bad{}:
      Unit{}

def sx.ev.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.Ev(s, FSc.get_ev.of(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s0, ed), {==})
        case 1n:
          sx.ev.grow_x(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n:
          sx.ev.fin(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_nat(s0), {==})
        case 3n:
          (Wire.wire_nat_exact(s, 3n, s0, ed), {==})
        case 4n:
          sx.ev.resize(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), Wr.get_nat(s0), {==})
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def sx.ev(+s: String) -> sx.Ev(s, FSc.get_ev(s)):
  sx.ev.go(s, Wr.get_nat(s), {==})

# Lists of events
# ---------------

def sx.evs.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Sc.Ev>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Screen.screen_spell_evs.items(xs, r) : String} & ({List.length(&2, Sc.Ev, xs) == 1n+m : Nat} & {Screen.evs_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def sx.evs.step(-s: String, +x: Sc.Ev, +s3: String, -k: Nat, ex: {s == Screen.screen_spell_ev(x, s3) : String}, fx: {Screen.ev_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Sc.Ev>>, ih: sx.evs.PL(s3, k, d)) -> sx.evs.PL(s, 1n+k, Wr.get_list.cons(Sc.Ev, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (sx.step(z => Screen.screen_spell_ev(x, z), s, s3, Screen.screen_spell_evs.items(ys, r), ex, e1), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Sc.Ev, ys), 1n+k, e2), LAWireSpell.ws_and_tt(Screen.ev_fits(x), Screen.evs_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def sx.evs.loop(m: Nat, cur: Wr.Dec<Sc.Ev>, +s: String, pc: sx.Ev(s, cur)) -> sx.evs.PL(s, m, Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(Screen.ev_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      sx.evs.step(s, x, s3, k, e, f, Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, k, FSc.get_ev(s3)), sx.evs.loop(k, FSc.get_ev(s3), s3, sx.ev(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def sx.evs.LS(s: String, d: Wr.Dec<List<&2, Sc.Ev>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Screen.screen_spell_evs(xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, Sc.Ev, xs)) == True{} : Bool} & {Screen.evs_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def sx.evs.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Sc.Ev>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == Screen.screen_spell_evs.items(xs, r) : String}, e2: {List.length(&2, Sc.Ev, xs) == 1n+m : Nat}) -> {s == Screen.screen_spell_evs(xs, r) : String}:
  %Equal.sym(Nat, List.length(&2, Sc.Ev, xs), 1n+m, e2) : {s == Wr.put_nat(_, Screen.screen_spell_evs.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def sx.evs.conv_f(-m: Nat, -xs: List<&2, Sc.Ev>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Sc.Ev, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Sc.Ev, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Sc.Ev, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def sx.evs.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Sc.Ev>>, pl: sx.evs.PL(s2, m, d)) -> sx.evs.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (sx.evs.conv_s(s, s2, m, xs, r, en, e1, e2), (sx.evs.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def sx.evs.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> sx.evs.LS(s, Wr.get_list.start(~Sc.Ev, ~FSc.get_ev, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      sx.evs.conv(s, s2, m, en, fn, Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, m, FSc.get_ev(s2)), sx.evs.loop(m, FSc.get_ev(s2), s2, sx.ev(s2)))

def sx.evs.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.evs.LS(s, Wr.get_list.start(~Sc.Ev, ~FSc.get_ev, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      sx.evs.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

def sx.evs(+s: String) -> sx.evs.LS(s, Wr.get_list(~Sc.Ev, ~FSc.get_ev, s)):
  sx.evs.top(s, Wr.get_nat(s), {==})

# Lists of Nats (heights)
# -----------------------

def sx.nats.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == LawsBase.wire_spell_nats.items(xs, r) : String} & ({List.length(&2, Nat, xs) == 1n+m : Nat} & {LawsBase.wire_nats_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def sx.nats.step(-s: String, +x: Nat, +s3: String, -k: Nat, ex: {s == Wr.put_nat(x, s3) : String}, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ih: sx.nats.PL(s3, k, d)) -> sx.nats.PL(s, 1n+k, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (sx.step(z => Wr.put_nat(x, z), s, s3, LawsBase.wire_spell_nats.items(ys, r), ex, e1), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Nat, ys), 1n+k, e2), LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def sx.nats.loop(m: Nat, cur: Wr.Dec<Nat>, +s: String, pc: sx.Nat(s, cur)) -> sx.nats.PL(s, m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      sx.nats.step(s, x, s3, k, e, f, Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(s3)), sx.nats.loop(k, Wr.get_nat(s3), s3, sx.nat(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def sx.nats.LS(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == LawsBase.wire_spell_nats(xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, Nat, xs)) == True{} : Bool} & {LawsBase.wire_nats_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def sx.nats.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Nat>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == LawsBase.wire_spell_nats.items(xs, r) : String}, e2: {List.length(&2, Nat, xs) == 1n+m : Nat}) -> {s == LawsBase.wire_spell_nats(xs, r) : String}:
  %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e2) : {s == Wr.put_nat(_, LawsBase.wire_spell_nats.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def sx.nats.conv_f(-m: Nat, -xs: List<&2, Nat>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Nat, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Nat, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def sx.nats.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, pl: sx.nats.PL(s2, m, d)) -> sx.nats.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (sx.nats.conv_s(s, s2, m, xs, r, en, e1, e2), (sx.nats.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def sx.nats.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> sx.nats.LS(s, Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      sx.nats.conv(s, s2, m, en, fn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s2)), sx.nats.loop(m, Wr.get_nat(s2), s2, sx.nat(s2)))

def sx.nats.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.nats.LS(s, Wr.get_list.start(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      sx.nats.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

def sx.nats(+s: String) -> sx.nats.LS(s, Wr.get_list(~Nat, ~Wr.get_nat, s)):
  sx.nats.top(s, Wr.get_nat(s), {==})

# Lists of check results
# ----------------------

def sx.Bool(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Wr.put_bool(x, r) : String}
    case Wr.Bad{}:
      Unit

def sx.bool.go(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> sx.Bool(s, d):
  match d:
    case Wr.Got{+x, +r}:
      Wire.wire_bool_exact(s, x, r, ed)
    case Wr.Bad{}:
      Unit{}

def sx.bool(+s: String) -> sx.Bool(s, Wr.get_bool(s)):
  sx.bool.go(s, Wr.get_bool(s), {==})

def sx.bools.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Screen.screen_spell_bools.items(xs, r) : String} & {List.length(&2, Bool, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def sx.bools.step(-s: String, +x: Bool, +s3: String, -k: Nat, ex: {s == Wr.put_bool(x, s3) : String}, d: Wr.Dec<List<&2, Bool>>, ih: sx.bools.PL(s3, k, d)) -> sx.bools.PL(s, 1n+k, Wr.get_list.cons(Bool, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (sx.step(z => Wr.put_bool(x, z), s, s3, Screen.screen_spell_bools.items(ys, r), ex, e1), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Bool, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

def sx.bools.loop(m: Nat, cur: Wr.Dec<Bool>, +s: String, pc: sx.Bool(s, cur)) -> sx.bools.PL(s, m, Wr.get_list.go(~Bool, ~Wr.get_bool, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (pc, {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      sx.bools.step(s, x, s3, k, pc, Wr.get_list.go(~Bool, ~Wr.get_bool, k, Wr.get_bool(s3)), sx.bools.loop(k, Wr.get_bool(s3), s3, sx.bool(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def sx.bools.LS(s: String, d: Wr.Dec<List<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Screen.screen_spell_bools(xs, r) : String} & {LawsBase.wire_fits(List.length(&2, Bool, xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.bools.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Bool>, -r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == Screen.screen_spell_bools.items(xs, r) : String}, e2: {List.length(&2, Bool, xs) == 1n+m : Nat}) -> {s == Screen.screen_spell_bools(xs, r) : String}:
  %Equal.sym(Nat, List.length(&2, Bool, xs), 1n+m, e2) : {s == Wr.put_nat(_, Screen.screen_spell_bools.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def sx.bools.conv_f(-m: Nat, -xs: List<&2, Bool>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, Bool, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Bool, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Bool, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def sx.bools.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Bool>>, pl: sx.bools.PL(s2, m, d)) -> sx.bools.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, +e2) = pl
      (sx.bools.conv_s(s, s2, m, xs, r, en, e1, e2), sx.bools.conv_f(m, xs, fn, e2))
    case Wr.Bad{}:
      Unit{}

def sx.bools.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> sx.bools.LS(s, Wr.get_list.start(~Bool, ~Wr.get_bool, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, fn)
    case 1n++m:
      sx.bools.conv(s, s2, m, en, fn, Wr.get_list.go(~Bool, ~Wr.get_bool, m, Wr.get_bool(s2)), sx.bools.loop(m, Wr.get_bool(s2), s2, sx.bool(s2)))

def sx.bools.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.bools.LS(s, Wr.get_list.start(~Bool, ~Wr.get_bool, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      sx.bools.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

def sx.bools(+s: String) -> sx.bools.LS(s, Wr.get_list(~Bool, ~Wr.get_bool, s)):
  sx.bools.top(s, Wr.get_nat(s), {==})

# Requests
# --------

# the request: its spelling, then its rest, and it fits
def sx.Req(s: String, d: Wr.Dec<FSc.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Screen.screen_spell_req(q, r) : String} & {Screen.screen_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sx.run.es(-s: String, +t: Sc.Tx, +s1: String, pre: {s == Wr.put_nat(0n, Screen.screen_spell_tx(t, s1)) : String}, ft: {Screen.tx_fits(t) == True{} : Bool}, d: Wr.Dec<List<&2, Sc.Ev>>, xd: sx.evs.LS(s1, d)) -> sx.Req(s, FSc.get_run.es(t, d)):
  match d:
    case Wr.Got{+es, +s2}:
      (e, f) = xd
      (fl, fe) = f
      (sx.step(z => Wr.put_nat(0n, Screen.screen_spell_tx(t, z)), s, s1, Screen.screen_spell_evs(es, s2), pre, e), LAWireSpell.ws_and_tt(Screen.tx_fits(t), Bool.and(LawsBase.wire_fits(List.length(&2, Sc.Ev, es)), Screen.evs_fit(es)), ft, LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Sc.Ev, es)), Screen.evs_fit(es), fl, fe)))
    case Wr.Bad{}:
      Unit{}

def sx.run(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<Sc.Tx>, xd: sx.Tx(s0, d)) -> sx.Req(s, FSc.get_run(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, ft) = xd
      sx.run.es(s, t, s1, sx.step(z => Wr.put_nat(0n, z), s, s0, Screen.screen_spell_tx(t, s1), pre, e), ft, Wr.get_list(~Sc.Ev, ~FSc.get_ev, s1), sx.evs(s1))
    case Wr.Bad{}:
      Unit{}

def sx.pace.n(-s: String, +min: Nat, +k: Nat, +p: Sc.Pace, +s4: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(min, Wr.put_nat(k, Screen.screen_spell_pace(p, s4)))) : String}, fmk: {Bool.and(LawsBase.wire_fits(min), LawsBase.wire_fits(k)) == True{} : Bool}, fp: {Screen.screen_pace_fits(p) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s4) == d : Wr.Dec<Nat>}) -> sx.Req(s, FSc.get_pacereq.n(min, k, p, d)):
  match d:
    case Wr.Got{+n, +s5}:
      +e = ed
      (sx.step(z => Wr.put_nat(1n, Wr.put_nat(min, Wr.put_nat(k, Screen.screen_spell_pace(p, z)))), s, s4, Wr.put_nat(n, s5), pre, Wire.wire_nat_exact(s4, n, s5, e)), LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(min), LawsBase.wire_fits(k)), Bool.and(Screen.screen_pace_fits(p), LawsBase.wire_fits(n)), fmk, LAWireSpell.ws_and_tt(Screen.screen_pace_fits(p), LawsBase.wire_fits(n), fp, Wire.wire_nat_decoded_fits(s4, n, s5, e))))
    case Wr.Bad{}:
      Unit{}

def sx.pace.s(-s: String, +min: Nat, +k: Nat, +r: Nat, +s3: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(min, Wr.put_nat(k, Wr.put_nat(r, s3)))) : String}, fmk: {Bool.and(LawsBase.wire_fits(min), LawsBase.wire_fits(k)) == True{} : Bool}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> sx.Req(s, FSc.get_pacereq.p(min, k, FSc.get_pace.s(r, d))):
  match d:
    case Wr.Got{+sh, +s4}:
      +e = ed
      sx.pace.n(s, min, k, Sc.Pace{r, sh}, s4, sx.step(z => Wr.put_nat(1n, Wr.put_nat(min, Wr.put_nat(k, Wr.put_nat(r, z)))), s, s3, Wr.put_nat(sh, s4), pre, Wire.wire_nat_exact(s3, sh, s4, e)), fmk, LAWireSpell.ws_and_tt(LawsBase.wire_fits(r), LawsBase.wire_fits(sh), fr, Wire.wire_nat_decoded_fits(s3, sh, s4, e)), Wr.get_nat(s4), {==})
    case Wr.Bad{}:
      Unit{}

def sx.pace.r(-s: String, +min: Nat, +k: Nat, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(min, Wr.put_nat(k, s2))) : String}, fmk: {Bool.and(LawsBase.wire_fits(min), LawsBase.wire_fits(k)) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> sx.Req(s, FSc.get_pacereq.p(min, k, FSc.get_pace.r(d))):
  match d:
    case Wr.Got{+r, +s3}:
      +e = ed
      sx.pace.s(s, min, k, r, s3, sx.step(z => Wr.put_nat(1n, Wr.put_nat(min, Wr.put_nat(k, z))), s, s2, Wr.put_nat(r, s3), pre, Wire.wire_nat_exact(s2, r, s3, e)), fmk, Wire.wire_nat_decoded_fits(s2, r, s3, e), Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def sx.pace.k(-s: String, +min: Nat, +s1: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(min, s1)) : String}, fmin: {LawsBase.wire_fits(min) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> sx.Req(s, FSc.get_pacereq.k(min, d)):
  match d:
    case Wr.Got{+k, +s2}:
      +e = ed
      sx.pace.r(s, min, k, s2, sx.step(z => Wr.put_nat(1n, Wr.put_nat(min, z)), s, s1, Wr.put_nat(k, s2), pre, Wire.wire_nat_exact(s1, k, s2, e)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(min), LawsBase.wire_fits(k), fmin, Wire.wire_nat_decoded_fits(s1, k, s2, e)), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def sx.pace.min(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> sx.Req(s, FSc.get_pacereq(d)):
  match d:
    case Wr.Got{+min, +s1}:
      +e = ed
      sx.pace.k(s, min, s1, sx.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(min, s1), pre, Wire.wire_nat_exact(s0, min, s1, e)), Wire.wire_nat_decoded_fits(s0, min, s1, e), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def sx.stack.rows(-s: String, +hs: List<&2, Nat>, +y: Nat, +s2: String, pre: {s == Wr.put_nat(2n, LawsBase.wire_spell_nats(hs, Wr.put_nat(y, s2))) : String}, fh: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)) == True{} : Bool}, fy: {LawsBase.wire_fits(y) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> sx.Req(s, FSc.get_stack.rows(hs, y, d)):
  match d:
    case Wr.Got{+rows, +s3}:
      +e = ed
      (sx.step(z => Wr.put_nat(2n, LawsBase.wire_spell_nats(hs, Wr.put_nat(y, z))), s, s2, Wr.put_nat(rows, s3), pre, Wire.wire_nat_exact(s2, rows, s3, e)), LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)), Bool.and(LawsBase.wire_fits(y), LawsBase.wire_fits(rows)), fh, LAWireSpell.ws_and_tt(LawsBase.wire_fits(y), LawsBase.wire_fits(rows), fy, Wire.wire_nat_decoded_fits(s2, rows, s3, e))))
    case Wr.Bad{}:
      Unit{}

def sx.stack.y(-s: String, +hs: List<&2, Nat>, +s1: String, pre: {s == Wr.put_nat(2n, LawsBase.wire_spell_nats(hs, s1)) : String}, fh: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> sx.Req(s, FSc.get_stack.y(hs, d)):
  match d:
    case Wr.Got{+y, +s2}:
      +e = ed
      sx.stack.rows(s, hs, y, s2, sx.step(z => Wr.put_nat(2n, LawsBase.wire_spell_nats(hs, z)), s, s1, Wr.put_nat(y, s2), pre, Wire.wire_nat_exact(s1, y, s2, e)), fh, Wire.wire_nat_decoded_fits(s1, y, s2, e), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def sx.stack(-s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<List<&2, Nat>>, xd: sx.nats.LS(s0, d)) -> sx.Req(s, FSc.get_stack(d)):
  match d:
    case Wr.Got{+hs, +s1}:
      (e, f) = xd
      (fl, fn) = f
      sx.stack.y(s, hs, s1, sx.step(z => Wr.put_nat(2n, z), s, s0, LawsBase.wire_spell_nats(hs, s1), pre, e), LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs), fl, fn), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def sx.paint(-s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, d: Wr.Dec<List<&2, Bool>>, xd: sx.bools.LS(s0, d)) -> sx.Req(s, FSc.get_paint(d)):
  match d:
    case Wr.Got{+ks, +s1}:
      (e, f) = xd
      (sx.step(z => Wr.put_nat(3n, z), s, s0, Screen.screen_spell_bools(ks, s1), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def sx.req.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sx.Req(s, FSc.get_req.of(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          sx.run(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FSc.get_tx(s0), sx.tx(s0))
        case 1n:
          sx.pace.min(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n:
          sx.stack(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_list(~Nat, ~Wr.get_nat, s0), sx.nats(s0))
        case 3n:
          sx.paint(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), Wr.get_list(~Bool, ~Wr.get_bool, s0), sx.bools(s0))
        case 4n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def sx.req(+s: String) -> sx.Req(s, FSc.get_req(s)):
  sx.req.go(s, Wr.get_nat(s), {==})
