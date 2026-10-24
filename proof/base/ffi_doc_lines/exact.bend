# eukhe: exactness of the projection decoder of bend/ffi_doc_lines.bend:
# a decoder that answers Got{v, rest} saw exactly the spelling of v
# (laws/base.bend `doc lines projection`), and every number of v fits
# the wire (used by lines_entry_exact and rows_entry_exact)

import Base
import ../../../bend/wire.bend as Wr
import ../../../bend/doc_lines.bend as Dl
import ../../../bend/ffi_doc_lines.bend as Fdl
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact

# ---- logic ----

# Unit at True, the goal G at False
def fdx_BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False: anything follows (an error reply refutes "no error")
def fdx_absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : fdx_BD(_, G)
  Unit{}

# both sides of an and hold, so it does
def fdx_and(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# ---- Nat ----

# what a Nat decoder's answer says about its input s
def fdx_pn(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a decoded Nat is spelled and fits (wire_nat_exact, wire_nat_decoded_fits)
def fdx_nat_go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> fdx_pn(s, d):
  match d:
    case Wr.Got{+n, +r}:
      (Wire.wire_nat_exact(s, n, r, ed), Wire.wire_nat_decoded_fits(s, n, r, ed))
    case Wr.Bad{}:
      Unit{}

# every Nat the decoder reads is spelled and fits
def fdx_nat(+s: String) -> fdx_pn(s, Wr.get_nat(s)):
  fdx_nat_go(s, Wr.get_nat(s), {==})

# ---- End ----

# what an ending decoder's answer says about its input s
def fdx_pe(s: String, d: Wr.Dec<Dl.End>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == LawsBase.proj_spell_end(e, r) : String}
    case Wr.Bad{}:
      Unit

# the ending tag is 0 or 1, spelled as such
def fdx_end_tag(-s: String, d: Wr.Dec<Nat>, pn: fdx_pn(s, d)) -> fdx_pe(s, Fdl.get_end.tag(d)):
  match d:
    case Wr.Got{t, r}:
      match t:
        case 0n:
          (e, f) = pn
          e
        case 1n:
          (e, f) = pn
          e
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every ending the decoder reads is spelled
def fdx_end(+s: String) -> fdx_pe(s, Fdl.get_end(s)):
  fdx_end_tag(s, Wr.get_nat(s), fdx_nat(s))

# ---- Maybe<End> ----

# what a Maybe<End> decoder's answer says about its input s
def fdx_pm(s: String, d: Wr.Dec<Maybe<&2, Dl.End>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == LawsBase.proj_spell_mend(m, r) : String}
    case Wr.Bad{}:
      Unit

# tag 1, then a spelled ending
def fdx_mend_some(-s: String, -s2: String, en: {s == Wr.put_nat(1n, s2) : String}, d: Wr.Dec<Dl.End>,
  pe: fdx_pe(s2, d)) -> fdx_pm(s, Fdl.get_mend.some(d)):
  match d:
    case Wr.Got{e, r}:
      %pe : {s == Wr.put_nat(1n, _) : String}
      en
    case Wr.Bad{}:
      Unit{}

# the Maybe tag is 0 or 1 (then an ending)
def fdx_mend_tag(-s: String, d: Wr.Dec<Nat>, pn: fdx_pn(s, d)) -> fdx_pm(s, Fdl.get_mend.tag(d)):
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          (e, f) = pn
          e
        case 1n:
          (e, f) = pn
          fdx_mend_some(s, r, e, Fdl.get_end(r), fdx_end(r))
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every Maybe<End> the decoder reads is spelled
def fdx_mend(+s: String) -> fdx_pm(s, Fdl.get_mend(s)):
  fdx_mend_tag(s, Wr.get_nat(s), fdx_nat(s))

# ---- Line ----

# what a line decoder's answer says about its input s
def fdx_pl(s: String, d: Wr.Dec<Dl.Line>) -> Type:
  match d:
    case Wr.Got{l, r}:
      match l:
        case Dl.Line{+n, en}:
          {s == Wr.put_nat(n, LawsBase.proj_spell_mend(en, r)) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a spelled length, then a spelled ending
def fdx_line_end(-s: String, -n: Nat, -s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Dl.End>>, pm: fdx_pm(s2, d))
  -> fdx_pl(s, Fdl.get_line.end(n, d)):
  match d:
    case Wr.Got{o, r}:
      (Equal.trans(String, s, Wr.put_nat(n, s2), Wr.put_nat(n, LawsBase.proj_spell_mend(o, r)), en,
        Equal.cong(String, String, z => Wr.put_nat(n, z), s2, LawsBase.proj_spell_mend(o, r), pm)), fn)
    case Wr.Bad{}:
      Unit{}

# a spelled length that fits, then the rest of the line
def fdx_line_len(-s: String, d: Wr.Dec<Nat>, pn: fdx_pn(s, d)) -> fdx_pl(s, Fdl.get_line.len(d)):
  match d:
    case Wr.Got{+n, +r}:
      (en, fn) = pn
      fdx_line_end(s, n, r, en, fn, Fdl.get_mend(r), fdx_mend(r))
    case Wr.Bad{}:
      Unit{}

# every line the decoder reads is spelled and its length fits
def fdx_line(+s: String) -> fdx_pl(s, Fdl.get_line(s)):
  fdx_line_len(s, Wr.get_nat(s), fdx_nat(s))

# ---- List<Line> ----

# the spellings of the lines xs, then rest
def fdx_lines_items(xs: List<&2, Dl.Line>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      LawsBase.proj_spell_line(x, fdx_lines_items(t, rest))

# the list encoder's loop: the count and the items
def fdx_lines_go(xs: List<&2, Dl.Line>, -rest: String) -> {Wr.put_list.go(~Dl.Line, ~LawsBase.proj_spell_line, xs, rest) == (List.length(&2, Dl.Line, xs), fdx_lines_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Line, ~LawsBase.proj_spell_line, t, rest), (List.length(&2, Dl.Line, t), fdx_lines_items(t, rest)), fdx_lines_go(t, rest)) : {Wr.put_list.step(~Dl.Line, ~LawsBase.proj_spell_line, x, _) == (1n+List.length(&2, Dl.Line, t), LawsBase.proj_spell_line(x, fdx_lines_items(t, rest))) : Nat & String}
      {==}

# a list of lines is its count, then its items
def fdx_lines_put(+xs: List<&2, Dl.Line>, -rest: String) -> {Wr.put_list(~Dl.Line, ~LawsBase.proj_spell_line, xs, rest) == Wr.put_nat(List.length(&2, Dl.Line, xs), fdx_lines_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Line, ~LawsBase.proj_spell_line, xs, rest), (List.length(&2, Dl.Line, xs), fdx_lines_items(xs, rest)), fdx_lines_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Dl.Line, xs), fdx_lines_items(xs, rest)) : String}
  {==}

# what the item loop's answer says about its input s (m + 1 items)
def fdx_pll(s: String, m: Nat, d: Wr.Dec<List<&2, Dl.Line>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == fdx_lines_items(xs, r) : String} & ({List.length(&2, Dl.Line, xs) == 1n+m : Nat} & {LawsBase.proj_lines_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

# one more spelled line before the rest of the loop
def fdx_lines_step(-s: String, x: Dl.Line, -s3: String, -k: Nat, d: Wr.Dec<List<&2, Dl.Line>>,
  ih: fdx_pll(s3, k, d), px: fdx_pl(s, Wr.Got{x, s3})) -> fdx_pll(s, 1n+k, Wr.get_list.cons(Dl.Line, x, d)):
  match x:
    case Dl.Line{+n, +en}:
      match d:
        case Wr.Got{+ys, +r}:
          (e1, (e2, e3)) = ih
          (ex, fx) = px
          (Equal.trans(String, s, Wr.put_nat(n, LawsBase.proj_spell_mend(en, s3)), Wr.put_nat(n, LawsBase.proj_spell_mend(en, fdx_lines_items(ys, r))), ex,
              Equal.cong(String, String, z => Wr.put_nat(n, LawsBase.proj_spell_mend(en, z)), s3, fdx_lines_items(ys, r), e1)),
            (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Dl.Line, ys), 1n+k, e2),
              fdx_and(LawsBase.wire_fits(n), LawsBase.proj_lines_fit(ys), fx, e3)))
        case Wr.Bad{}:
          Unit{}

# the item loop accepts only spelled lines that fit
def fdx_lines_loop(m: Nat, cur: Wr.Dec<Dl.Line>, +s: String, pc: fdx_pl(s, cur)) ->
  fdx_pll(s, m, Wr.get_list.go(~Dl.Line, ~Fdl.get_line, m, cur)):
  match m cur:
    case 0n Wr.Got{x, s3}:
      match x:
        case Dl.Line{+n, en}:
          (ex, fx) = pc
          (ex, ({==}, fdx_and(LawsBase.wire_fits(n), True{}, fx, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      fdx_lines_step(s, x, s3, k, Wr.get_list.go(~Dl.Line, ~Fdl.get_line, k, Fdl.get_line(s3)),
        fdx_lines_loop(k, Fdl.get_line(s3), s3, fdx_line(s3)), pc)
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list-of-lines decoder's answer says about its input s
def fdx_pls(s: String, d: Wr.Dec<List<&2, Dl.Line>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Dl.Line, ~LawsBase.proj_spell_line, xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Dl.Line, xs)), LawsBase.proj_lines_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# the count spelled before the items is the list's length
def fdx_lines_eq(-s: String, -s2: String, -m: Nat, +xs: List<&2, Dl.Line>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == fdx_lines_items(xs, r) : String},
  e2: {List.length(&2, Dl.Line, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Dl.Line, ~LawsBase.proj_spell_line, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Dl.Line, ~LawsBase.proj_spell_line, xs, r), Wr.put_nat(List.length(&2, Dl.Line, xs), fdx_lines_items(xs, r)), fdx_lines_put(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Dl.Line, xs), 1n+m, e2) : {s == Wr.put_nat(_, fdx_lines_items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

# m + 1 spelled items after their count: a spelled list that fits
def fdx_lines_conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Dl.Line>>, pl: fdx_pll(s2, m, d)) -> fdx_pls(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (fdx_lines_eq(s, s2, m, xs, r, en, e1, e2),
        fdx_and(LawsBase.wire_fits(List.length(&2, Dl.Line, xs)), LawsBase.proj_lines_fit(xs),
          Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Dl.Line, xs)), LawsBase.wire_fits(1n+m), True{},
            Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, Dl.Line, xs), 1n+m, e2), fn), e3))
    case Wr.Bad{}:
      Unit{}

# the count 0 is the empty list; else the item loop runs
def fdx_lines_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> fdx_pls(s, Wr.get_list.start(~Dl.Line, ~Fdl.get_line, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      fdx_lines_conv(s, s2, m, en, fn, Wr.get_list.go(~Dl.Line, ~Fdl.get_line, m, Fdl.get_line(s2)),
        fdx_lines_loop(m, Fdl.get_line(s2), s2, fdx_line(s2)))

# a list starts with a spelled count that fits
def fdx_lines_top(+s: String, d: Wr.Dec<Nat>, pn: fdx_pn(s, d)) -> fdx_pls(s, Wr.get_list.start(~Dl.Line, ~Fdl.get_line, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (en, fn) = pn
      fdx_lines_nat(s, n, s2, en, fn)
    case Wr.Bad{}:
      Unit{}

# every list of lines the decoder reads is spelled and fits
def fdx_lines(+s: String) -> fdx_pls(s, Wr.get_list(~Dl.Line, ~Fdl.get_line, s)):
  fdx_lines_top(s, Wr.get_nat(s), fdx_nat(s))

# ---- Proj ----

# what a projection decoder's answer says about its input s
def fdx_pp(s: String, d: Wr.Dec<Dl.Proj>) -> Type:
  match d:
    case Wr.Got{+p, r}:
      {s == LawsBase.proj_spell(p, r) : String} & {LawsBase.proj_fits(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a spelled BOM flag, then spelled lines
def fdx_proj_lines(-s: String, -b: Bool, -s2: String, eb: {s == Wr.put_bool(b, s2) : String},
  d: Wr.Dec<List<&2, Dl.Line>>, pl: fdx_pls(s2, d)) -> fdx_pp(s, Fdl.get_proj.lines(b, d)):
  match d:
    case Wr.Got{+ls, +r}:
      (e1, f1) = pl
      (Equal.trans(String, s, Wr.put_bool(b, s2), Wr.put_bool(b, Wr.put_list(~Dl.Line, ~LawsBase.proj_spell_line, ls, r)), eb,
        Equal.cong(String, String, z => Wr.put_bool(b, z), s2, Wr.put_list(~Dl.Line, ~LawsBase.proj_spell_line, ls, r), e1)), f1)
    case Wr.Bad{}:
      Unit{}

# a spelled BOM flag (wire_bool_exact), then the lines
def fdx_proj_bom(+s: String, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> fdx_pp(s, Fdl.get_proj.bom(d)):
  match d:
    case Wr.Got{+b, +r}:
      fdx_proj_lines(s, b, r, Wire.wire_bool_exact(s, b, r, ed), Wr.get_list(~Dl.Line, ~Fdl.get_line, r), fdx_lines(r))
    case Wr.Bad{}:
      Unit{}

# every projection the decoder reads is spelled and fits
def fdx_proj(+s: String) -> fdx_pp(s, Fdl.get_proj(s)):
  fdx_proj_bom(s, Wr.get_bool(s), {==})
