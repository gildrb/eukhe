# eukhe: exactness of the request decoders of bend/ffi_doc_seen.bend: a
# decoder that answers Got{v, rest} saw exactly the laws' spelling of v
# (laws/doc_seen.bend seen.spell_*) followed by rest, and every number of
# v fits the wire (used by the entry laws of doc_seen)

import Base
import ../../../bend/doc_seen.bend as Ds
import ../../../bend/ffi_doc_seen.bend as Fds
import ../../../bend/wire.bend as Wr
import ../../../laws/doc_seen.bend as DocSeen
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/base/spell.bend as LAWireSpell

# ---- Nat ----

# what a Nat decoder's answer says about its input s
def fsx_pn(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fsx_nat_go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> fsx_pn(s, d):
  match d:
    case Wr.Got{+n, +r}:
      (Wire.wire_nat_exact(s, n, r, ed), Wire.wire_nat_decoded_fits(s, n, r, ed))
    case Wr.Bad{}:
      Unit{}

# every Nat the decoder reads is spelled and fits
def fsx_nat(+s: String) -> fsx_pn(s, Wr.get_nat(s)):
  fsx_nat_go(s, Wr.get_nat(s), {==})

# ---- Iv ----

# what a seen run decoder's answer says about its input s
def fsx_pi(s: String, d: Wr.Dec<Ds.Iv>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == DocSeen.seen.spell_iv(x, r) : String} & {DocSeen.seen.IvFit(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a spelled lo that fits, then a spelled hi that fits
def fsx_iv_hi(-s: String, -lo: Nat, -s2: String, el: {s == Wr.put_nat(lo, s2) : String},
  fl: {LawsBase.wire_fits(lo) == True{} : Bool}, d: Wr.Dec<Nat>, pn: fsx_pn(s2, d)) -> fsx_pi(s, Fds.get_iv.hi(lo, d)):
  match d:
    case Wr.Got{+hi, +r}:
      (eh, fh) = pn
      (Equal.trans(String, s, Wr.put_nat(lo, s2), Wr.put_nat(lo, Wr.put_nat(hi, r)), el,
        Equal.cong(String, String, z => Wr.put_nat(lo, z), s2, Wr.put_nat(hi, r), eh)),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(lo), LawsBase.wire_fits(hi), fl, fh))
    case Wr.Bad{}:
      Unit{}

def fsx_iv_lo(-s: String, d: Wr.Dec<Nat>, pn: fsx_pn(s, d)) -> fsx_pi(s, Fds.get_iv.lo(d)):
  match d:
    case Wr.Got{+lo, +s2}:
      (el, fl) = pn
      fsx_iv_hi(s, lo, s2, el, fl, Wr.get_nat(s2), fsx_nat(s2))
    case Wr.Bad{}:
      Unit{}

# every seen run the decoder reads is spelled and fits
def fsx_iv(+s: String) -> fsx_pi(s, Fds.get_iv(s)):
  fsx_iv_lo(s, Wr.get_nat(s), fsx_nat(s))

# ---- Maybe<Nat> ----

# what a Maybe<Nat> decoder's answer says about its input s
def fsx_pm(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == DocSeen.seen.spell_mnat(m, r) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# tag 1, then a spelled Nat that fits
def fsx_mnat_some(-s: String, -s2: String, e1: {s == Wr.put_nat(1n, s2) : String}, d: Wr.Dec<Nat>,
  pn: fsx_pn(s2, d)) -> fsx_pm(s, Fds.get_mnat.some(d)):
  match d:
    case Wr.Got{+x, +r}:
      (ex, fx) = pn
      (Equal.trans(String, s, Wr.put_nat(1n, s2), Wr.put_nat(1n, Wr.put_nat(x, r)), e1,
        Equal.cong(String, String, z => Wr.put_nat(1n, z), s2, Wr.put_nat(x, r), ex)), fx)
    case Wr.Bad{}:
      Unit{}

# the tag is 0 (none) or 1 (then a Nat)
def fsx_mnat_tag(-s: String, d: Wr.Dec<Nat>, pn: fsx_pn(s, d)) -> fsx_pm(s, Fds.get_mnat.tag(d)):
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          (e, f) = pn
          (e, {==})
        case 1n:
          (e, f) = pn
          fsx_mnat_some(s, r, e, Wr.get_nat(r), fsx_nat(r))
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every Maybe<Nat> the decoder reads is spelled and fits
def fsx_mnat(+s: String) -> fsx_pm(s, Fds.get_mnat(s)):
  fsx_mnat_tag(s, Wr.get_nat(s), fsx_nat(s))

# ---- At ----

# what an anchor decoder's answer says about its input s
def fsx_pa(s: String, d: Wr.Dec<Ds.At>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == DocSeen.seen.spell_at(x, r) : String} & {DocSeen.seen.AtFit(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a line that fits and a width that fits: the anchor fits
def fsx_at_fit(-n: Nat, m: Maybe<&2, Nat>, fn: {LawsBase.wire_fits(n) == True{} : Bool},
  fm: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {DocSeen.seen.AtFit(Ds.At{n, m}) == True{} : Bool}:
  match m:
    case None{}:
      fn
    case Some{x}:
      LAWireSpell.ws_and_tt(LawsBase.wire_fits(n), LawsBase.wire_fits(x), fn, fm)

# a spelled line, then a spelled width
def fsx_at_w(-s: String, -n: Nat, -s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Nat>>, pm: fsx_pm(s2, d)) -> fsx_pa(s, Fds.get_at.w(n, d)):
  match d:
    case Wr.Got{+m, +r}:
      (em, fm) = pm
      (Equal.trans(String, s, Wr.put_nat(n, s2), Wr.put_nat(n, DocSeen.seen.spell_mnat(m, r)), en,
        Equal.cong(String, String, z => Wr.put_nat(n, z), s2, DocSeen.seen.spell_mnat(m, r), em)),
        fsx_at_fit(n, m, fn, fm))
    case Wr.Bad{}:
      Unit{}

def fsx_at_n(-s: String, d: Wr.Dec<Nat>, pn: fsx_pn(s, d)) -> fsx_pa(s, Fds.get_at.n(d)):
  match d:
    case Wr.Got{+n, +s2}:
      (en, fn) = pn
      fsx_at_w(s, n, s2, en, fn, Fds.get_mnat(s2), fsx_mnat(s2))
    case Wr.Bad{}:
      Unit{}

# every anchor the decoder reads is spelled and fits
def fsx_at(+s: String) -> fsx_pa(s, Fds.get_at(s)):
  fsx_at_n(s, Wr.get_nat(s), fsx_nat(s))

# ---- List<Iv> ----

def fsx_ivs_items(xs: List<&2, Ds.Iv>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocSeen.seen.spell_iv(x, fsx_ivs_items(t, rest))

def fsx_ivs_go(xs: List<&2, Ds.Iv>, -rest: String) -> {Wr.put_list.go(~Ds.Iv, ~DocSeen.seen.spell_iv, xs, rest) == (List.length(&2, Ds.Iv, xs), fsx_ivs_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ds.Iv, ~DocSeen.seen.spell_iv, t, rest), (List.length(&2, Ds.Iv, t), fsx_ivs_items(t, rest)), fsx_ivs_go(t, rest)) : {Wr.put_list.step(~Ds.Iv, ~DocSeen.seen.spell_iv, x, _) == (1n+List.length(&2, Ds.Iv, t), DocSeen.seen.spell_iv(x, fsx_ivs_items(t, rest))) : Nat & String}
      {==}

def fsx_ivs_put(+xs: List<&2, Ds.Iv>, -rest: String) -> {Wr.put_list(~Ds.Iv, ~DocSeen.seen.spell_iv, xs, rest) == Wr.put_nat(List.length(&2, Ds.Iv, xs), fsx_ivs_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Ds.Iv, ~DocSeen.seen.spell_iv, xs, rest), (List.length(&2, Ds.Iv, xs), fsx_ivs_items(xs, rest)), fsx_ivs_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Ds.Iv, xs), fsx_ivs_items(xs, rest)) : String}
  {==}

# what the item loop's answer says about its input s (m + 1 items)
def fsx_ivs_pll(s: String, m: Nat, d: Wr.Dec<List<&2, Ds.Iv>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == fsx_ivs_items(xs, r) : String} & ({List.length(&2, Ds.Iv, xs) == 1n+m : Nat} & {DocSeen.seen.IvsFit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def fsx_ivs_step(-s: String, +x: Ds.Iv, -s3: String, -k: Nat, d: Wr.Dec<List<&2, Ds.Iv>>,
  ih: fsx_ivs_pll(s3, k, d), px: fsx_pi(s, Wr.Got{x, s3})) -> fsx_ivs_pll(s, 1n+k, Wr.get_list.cons(Ds.Iv, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, (e2, e3)) = ih
      (ex, fx) = px
      (Equal.trans(String, s, DocSeen.seen.spell_iv(x, s3), DocSeen.seen.spell_iv(x, fsx_ivs_items(ys, r)), ex,
          Equal.cong(String, String, z => DocSeen.seen.spell_iv(x, z), s3, fsx_ivs_items(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Ds.Iv, ys), 1n+k, e2),
          LAWireSpell.ws_and_tt(DocSeen.seen.IvFit(x), DocSeen.seen.IvsFit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def fsx_ivs_loop(m: Nat, cur: Wr.Dec<Ds.Iv>, +s: String, pc: fsx_pi(s, cur)) ->
  fsx_ivs_pll(s, m, Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, s3}:
      (ex, fx) = pc
      (ex, ({==}, LAWireSpell.ws_and_tt(DocSeen.seen.IvFit(x), True{}, fx, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      fsx_ivs_step(s, x, s3, k, Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, k, Fds.get_iv(s3)),
        fsx_ivs_loop(k, Fds.get_iv(s3), s3, fsx_iv(s3)), pc)
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list-of-runs decoder's answer says about its input s
def fsx_pivs(s: String, d: Wr.Dec<List<&2, Ds.Iv>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == DocSeen.seen.spell_seen(xs, r) : String} & {DocSeen.seen.SeenFits(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fsx_ivs_eq(-s: String, -s2: String, -m: Nat, +xs: List<&2, Ds.Iv>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == fsx_ivs_items(xs, r) : String},
  e2: {List.length(&2, Ds.Iv, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Ds.Iv, ~DocSeen.seen.spell_iv, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Ds.Iv, ~DocSeen.seen.spell_iv, xs, r), Wr.put_nat(List.length(&2, Ds.Iv, xs), fsx_ivs_items(xs, r)), fsx_ivs_put(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Ds.Iv, xs), 1n+m, e2) : {s == Wr.put_nat(_, fsx_ivs_items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def fsx_ivs_conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Ds.Iv>>, pl: fsx_ivs_pll(s2, m, d)) -> fsx_pivs(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (+e2, e3)) = pl
      (fsx_ivs_eq(s, s2, m, xs, r, en, e1, e2),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Ds.Iv, xs)), DocSeen.seen.IvsFit(xs),
          Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Ds.Iv, xs)), LawsBase.wire_fits(1n+m), True{},
            Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, Ds.Iv, xs), 1n+m, e2), fn), e3))
    case Wr.Bad{}:
      Unit{}

def fsx_ivs_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> fsx_pivs(s, Wr.get_list.start(~Ds.Iv, ~Fds.get_iv, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      fsx_ivs_conv(s, s2, m, en, fn, Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, m, Fds.get_iv(s2)),
        fsx_ivs_loop(m, Fds.get_iv(s2), s2, fsx_iv(s2)))

def fsx_ivs_top(+s: String, d: Wr.Dec<Nat>, pn: fsx_pn(s, d)) -> fsx_pivs(s, Wr.get_list.start(~Ds.Iv, ~Fds.get_iv, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (en, fn) = pn
      fsx_ivs_nat(s, n, s2, en, fn)
    case Wr.Bad{}:
      Unit{}

# every list of seen runs the decoder reads is spelled and fits
def fsx_ivs(+s: String) -> fsx_pivs(s, Wr.get_list(~Ds.Iv, ~Fds.get_iv, s)):
  fsx_ivs_top(s, Wr.get_nat(s), fsx_nat(s))

# ---- List<At> ----

def fsx_ats_items(xs: List<&2, Ds.At>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocSeen.seen.spell_at(x, fsx_ats_items(t, rest))

def fsx_ats_go(xs: List<&2, Ds.At>, -rest: String) -> {Wr.put_list.go(~Ds.At, ~DocSeen.seen.spell_at, xs, rest) == (List.length(&2, Ds.At, xs), fsx_ats_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ds.At, ~DocSeen.seen.spell_at, t, rest), (List.length(&2, Ds.At, t), fsx_ats_items(t, rest)), fsx_ats_go(t, rest)) : {Wr.put_list.step(~Ds.At, ~DocSeen.seen.spell_at, x, _) == (1n+List.length(&2, Ds.At, t), DocSeen.seen.spell_at(x, fsx_ats_items(t, rest))) : Nat & String}
      {==}

def fsx_ats_put(+xs: List<&2, Ds.At>, -rest: String) -> {Wr.put_list(~Ds.At, ~DocSeen.seen.spell_at, xs, rest) == Wr.put_nat(List.length(&2, Ds.At, xs), fsx_ats_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Ds.At, ~DocSeen.seen.spell_at, xs, rest), (List.length(&2, Ds.At, xs), fsx_ats_items(xs, rest)), fsx_ats_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Ds.At, xs), fsx_ats_items(xs, rest)) : String}
  {==}

def fsx_ats_pll(s: String, m: Nat, d: Wr.Dec<List<&2, Ds.At>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == fsx_ats_items(xs, r) : String} & ({List.length(&2, Ds.At, xs) == 1n+m : Nat} & {DocSeen.seen.AtsFit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def fsx_ats_step(-s: String, +x: Ds.At, -s3: String, -k: Nat, d: Wr.Dec<List<&2, Ds.At>>,
  ih: fsx_ats_pll(s3, k, d), px: fsx_pa(s, Wr.Got{x, s3})) -> fsx_ats_pll(s, 1n+k, Wr.get_list.cons(Ds.At, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, (e2, e3)) = ih
      (ex, fx) = px
      (Equal.trans(String, s, DocSeen.seen.spell_at(x, s3), DocSeen.seen.spell_at(x, fsx_ats_items(ys, r)), ex,
          Equal.cong(String, String, z => DocSeen.seen.spell_at(x, z), s3, fsx_ats_items(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Ds.At, ys), 1n+k, e2),
          LAWireSpell.ws_and_tt(DocSeen.seen.AtFit(x), DocSeen.seen.AtsFit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def fsx_ats_loop(m: Nat, cur: Wr.Dec<Ds.At>, +s: String, pc: fsx_pa(s, cur)) ->
  fsx_ats_pll(s, m, Wr.get_list.go(~Ds.At, ~Fds.get_at, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, s3}:
      (ex, fx) = pc
      (ex, ({==}, LAWireSpell.ws_and_tt(DocSeen.seen.AtFit(x), True{}, fx, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      fsx_ats_step(s, x, s3, k, Wr.get_list.go(~Ds.At, ~Fds.get_at, k, Fds.get_at(s3)),
        fsx_ats_loop(k, Fds.get_at(s3), s3, fsx_at(s3)), pc)
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list-of-anchors decoder's answer says about its input s
def fsx_pats(s: String, d: Wr.Dec<List<&2, Ds.At>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == DocSeen.seen.spell_ats(xs, r) : String} & {DocSeen.seen.AnchorsFit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fsx_ats_eq(-s: String, -s2: String, -m: Nat, +xs: List<&2, Ds.At>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == fsx_ats_items(xs, r) : String},
  e2: {List.length(&2, Ds.At, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Ds.At, ~DocSeen.seen.spell_at, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Ds.At, ~DocSeen.seen.spell_at, xs, r), Wr.put_nat(List.length(&2, Ds.At, xs), fsx_ats_items(xs, r)), fsx_ats_put(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Ds.At, xs), 1n+m, e2) : {s == Wr.put_nat(_, fsx_ats_items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def fsx_ats_conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Ds.At>>, pl: fsx_ats_pll(s2, m, d)) -> fsx_pats(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (+e2, e3)) = pl
      (fsx_ats_eq(s, s2, m, xs, r, en, e1, e2),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Ds.At, xs)), DocSeen.seen.AtsFit(xs),
          Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Ds.At, xs)), LawsBase.wire_fits(1n+m), True{},
            Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, Ds.At, xs), 1n+m, e2), fn), e3))
    case Wr.Bad{}:
      Unit{}

def fsx_ats_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> fsx_pats(s, Wr.get_list.start(~Ds.At, ~Fds.get_at, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      fsx_ats_conv(s, s2, m, en, fn, Wr.get_list.go(~Ds.At, ~Fds.get_at, m, Fds.get_at(s2)),
        fsx_ats_loop(m, Fds.get_at(s2), s2, fsx_at(s2)))

def fsx_ats_top(+s: String, d: Wr.Dec<Nat>, pn: fsx_pn(s, d)) -> fsx_pats(s, Wr.get_list.start(~Ds.At, ~Fds.get_at, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (en, fn) = pn
      fsx_ats_nat(s, n, s2, en, fn)
    case Wr.Bad{}:
      Unit{}

# every list of anchors the decoder reads is spelled and fits
def fsx_ats(+s: String) -> fsx_pats(s, Wr.get_list(~Ds.At, ~Fds.get_at, s)):
  fsx_ats_top(s, Wr.get_nat(s), fsx_nat(s))
