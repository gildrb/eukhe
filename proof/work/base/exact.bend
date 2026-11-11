# eukhe: lemmas of area work: the stepper's decoder answers Got only for
# the laws' spelling of what it read before the rest, every number within
# the wire (wire_nat_exact, wire_nat_decoded_fits), stage by stage: a
# block (wre.blk), a list of blocks (wre.blks), an entry (wre.ent), a list
# of entries (wre.ents), the view's place (wre.at), an event (wre.ev).

import Base
import ../../../bend/ffi_work.bend as FW
import ../../../bend/progress.bend as Pr
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/work.bend as Work
import ../../wire/base/spell.bend as LAWireSpell
import ../base.bend as LWork

# A block
# -------

def wre.BP(s: String, d: Wr.Dec<Pr.Blk>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Work.wk_spell_blk(b, r) : String} & {Work.wk_blk_fits(b) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def wre.call_fp(-s: String, +k: Nat, +s2: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(k, s2)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> wre.BP(s, FW.get_blk.call.fp(k, d)):
  match d:
    case Wr.Got{+f, +s3}:
      +e = ed
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(k, s2)), Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(f, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(k, z)), s2, Wr.put_nat(f, s3), Wire.wire_nat_exact(s2, f, s3, e))),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(k), LawsBase.wire_fits(f), fk, Wire.wire_nat_decoded_fits(s2, f, s3, e)))
    case Wr.Bad{}:
      Unit{}

def wre.call(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> wre.BP(s, FW.get_blk.call(d)):
  match d:
    case Wr.Got{+k, +s2}:
      +e = ed
      wre.call_fp(s, k, s2,
        Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_nat(k, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_nat(k, s2), Wire.wire_nat_exact(s1, k, s2, e))),
        Wire.wire_nat_decoded_fits(s1, k, s2, e), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def wre.res_fp(-s: String, +k: Nat, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(k, s2)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> wre.BP(s, FW.get_blk.res.fp(k, d)):
  match d:
    case Wr.Got{+f, +s3}:
      +e = ed
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(k, s2)), Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(f, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(k, z)), s2, Wr.put_nat(f, s3), Wire.wire_nat_exact(s2, f, s3, e))),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(k), LawsBase.wire_fits(f), fk, Wire.wire_nat_decoded_fits(s2, f, s3, e)))
    case Wr.Bad{}:
      Unit{}

def wre.res(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> wre.BP(s, FW.get_blk.res(d)):
  match d:
    case Wr.Got{+k, +s2}:
      +e = ed
      wre.res_fp(s, k, s2,
        Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(k, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(k, s2), Wire.wire_nat_exact(s1, k, s2, e))),
        Wire.wire_nat_decoded_fits(s1, k, s2, e), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def wre.blk_tag(-s: String, n: Nat, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}) -> wre.BP(s, FW.get_blk.tag(n, s1)):
  match n:
    case 0n:
      wre.call(s, s1, pre, Wr.get_nat(s1), {==})
    case 1n:
      wre.res(s, s1, pre, Wr.get_nat(s1), {==})
    case 2n:
      (pre, {==})
    case 3n:
      (pre, {==})
    case 4n:
      (pre, {==})
    case 5n:
      (pre, {==})
    case 6n+q:
      Unit{}

def wre.blk_go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wre.BP(s, FW.get_blk.go(d)):
  match d:
    case Wr.Got{+n, +s1}:
      wre.blk_tag(s, n, s1, Wire.wire_nat_exact(s, n, s1, ed))
    case Wr.Bad{}:
      Unit{}

# a decoded block is spelled, and its numbers fit
def wre.blk(+s: String) -> wre.BP(s, FW.get_blk(s)):
  wre.blk_go(s, Wr.get_nat(s), {==})

# A list of blocks
# ----------------

# what the item loop's answer says about its input s (m + 1 blocks)
def wre.bPL(s: String, m: Nat, d: Wr.Dec<List<&2, Pr.Blk>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == LWork.wk.b.items(xs, r) : String} & ({List.length(&2, Pr.Blk, xs) == 1n+m : Nat} & {Work.wk_blks_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def wre.b_step(-s: String, +x: Pr.Blk, +s3: String, -k: Nat, ex: {s == Work.wk_spell_blk(x, s3) : String}, fx: {Work.wk_blk_fits(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Pr.Blk>>, ih: wre.bPL(s3, k, d)) -> wre.bPL(s, 1n+k, Wr.get_list.cons(Pr.Blk, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, Work.wk_spell_blk(x, s3), Work.wk_spell_blk(x, LWork.wk.b.items(ys, r)), ex,
          Equal.cong(String, String, z => Work.wk_spell_blk(x, z), s3, LWork.wk.b.items(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Pr.Blk, ys), 1n+k, e2), LAWireSpell.ws_and_tt(Work.wk_blk_fits(x), Work.wk_blks_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled blocks that fit
def wre.b_loop(m: Nat, cur: Wr.Dec<Pr.Blk>, +s: String, pc: wre.BP(s, cur)) -> wre.bPL(s, m, Wr.get_list.go(~Pr.Blk, ~FW.get_blk, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(Work.wk_blk_fits(x), Work.wk_blks_fit(Nil{}), f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      wre.b_step(s, x, s3, k, e, f, Wr.get_list.go(~Pr.Blk, ~FW.get_blk, k, FW.get_blk(s3)),
        wre.b_loop(k, FW.get_blk(s3), s3, wre.blk(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def wre.bLS(s: String, d: Wr.Dec<List<&2, Pr.Blk>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Pr.Blk, ~Work.wk_spell_blk, xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, Pr.Blk, xs)) == True{} : Bool} & {Work.wk_blks_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def wre.b_conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Pr.Blk>, +r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == LWork.wk.b.items(xs, r) : String},
  e2: {List.length(&2, Pr.Blk, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Pr.Blk, ~Work.wk_spell_blk, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Pr.Blk, ~Work.wk_spell_blk, xs, r), Wr.put_nat(List.length(&2, Pr.Blk, xs), LWork.wk.b.items(xs, r)), LWork.wk.b.put_list(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Pr.Blk, xs), 1n+m, e2) : {s == Wr.put_nat(_, LWork.wk.b.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def wre.b_conv_f(-m: Nat, -xs: List<&2, Pr.Blk>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e2: {List.length(&2, Pr.Blk, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Pr.Blk, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Pr.Blk, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def wre.b_conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Pr.Blk>>, pl: wre.bPL(s2, m, d)) -> wre.bLS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (wre.b_conv_s(s, s2, m, xs, r, en, e1, e2), (wre.b_conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def wre.b_nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  wre.bLS(s, Wr.get_list.start(~Pr.Blk, ~FW.get_blk, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      wre.b_conv(s, s2, m, en, fn, Wr.get_list.go(~Pr.Blk, ~FW.get_blk, m, FW.get_blk(s2)),
        wre.b_loop(m, FW.get_blk(s2), s2, wre.blk(s2)))

def wre.b_top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  wre.bLS(s, Wr.get_list.start(~Pr.Blk, ~FW.get_blk, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      wre.b_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a decoded list of blocks is spelled, its count and blocks within the wire
def wre.blks(+s: String) -> wre.bLS(s, Wr.get_list(~Pr.Blk, ~FW.get_blk, s)):
  wre.b_top(s, Wr.get_nat(s), {==})

# An entry
# --------

def wre.EP(s: String, d: Wr.Dec<Pr.Ent>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == Work.wk_spell_ent(e, r) : String} & {Work.wk_ent_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def wre.ent_bs(-s: String, +i: Nat, +s1: String, pre: {s == Wr.put_nat(i, s1) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<List<&2, Pr.Blk>>, ls: wre.bLS(s1, d)) -> wre.EP(s, FW.get_ent.bs(i, d)):
  match d:
    case Wr.Got{+bs, +s2}:
      (e1, f23) = ls
      (f2, f3) = f23
      (Equal.trans(String, s, Wr.put_nat(i, s1), Wr.put_nat(i, Wr.put_list(~Pr.Blk, ~Work.wk_spell_blk, bs, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(i, z), s1, Wr.put_list(~Pr.Blk, ~Work.wk_spell_blk, bs, s2), e1)),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(List.length(&2, Pr.Blk, bs)), Work.wk_blks_fit(bs)), fi,
          LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Pr.Blk, bs)), Work.wk_blks_fit(bs), f2, f3)))
    case Wr.Bad{}:
      Unit{}

def wre.ent_go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wre.EP(s, FW.get_ent.go(d)):
  match d:
    case Wr.Got{+i, +s1}:
      +e = ed
      wre.ent_bs(s, i, s1, Wire.wire_nat_exact(s, i, s1, e), Wire.wire_nat_decoded_fits(s, i, s1, e), Wr.get_list(~Pr.Blk, ~FW.get_blk, s1), wre.blks(s1))
    case Wr.Bad{}:
      Unit{}

# a decoded entry is spelled, and its numbers fit
def wre.ent(+s: String) -> wre.EP(s, FW.get_ent(s)):
  wre.ent_go(s, Wr.get_nat(s), {==})

# A list of entries
# -----------------

def wre.ePL(s: String, m: Nat, d: Wr.Dec<List<&2, Pr.Ent>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == LWork.wk.e.items(xs, r) : String} & ({List.length(&2, Pr.Ent, xs) == 1n+m : Nat} & {Work.wk_ents_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def wre.e_step(-s: String, +x: Pr.Ent, +s3: String, -k: Nat, ex: {s == Work.wk_spell_ent(x, s3) : String}, fx: {Work.wk_ent_fits(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Pr.Ent>>, ih: wre.ePL(s3, k, d)) -> wre.ePL(s, 1n+k, Wr.get_list.cons(Pr.Ent, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, Work.wk_spell_ent(x, s3), Work.wk_spell_ent(x, LWork.wk.e.items(ys, r)), ex,
          Equal.cong(String, String, z => Work.wk_spell_ent(x, z), s3, LWork.wk.e.items(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Pr.Ent, ys), 1n+k, e2), LAWireSpell.ws_and_tt(Work.wk_ent_fits(x), Work.wk_ents_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def wre.e_loop(m: Nat, cur: Wr.Dec<Pr.Ent>, +s: String, pc: wre.EP(s, cur)) -> wre.ePL(s, m, Wr.get_list.go(~Pr.Ent, ~FW.get_ent, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(Work.wk_ent_fits(x), Work.wk_ents_fit(Nil{}), f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      wre.e_step(s, x, s3, k, e, f, Wr.get_list.go(~Pr.Ent, ~FW.get_ent, k, FW.get_ent(s3)),
        wre.e_loop(k, FW.get_ent(s3), s3, wre.ent(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def wre.eLS(s: String, d: Wr.Dec<List<&2, Pr.Ent>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, Pr.Ent, xs)) == True{} : Bool} & {Work.wk_ents_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def wre.e_conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Pr.Ent>, +r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == LWork.wk.e.items(xs, r) : String},
  e2: {List.length(&2, Pr.Ent, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, xs, r), Wr.put_nat(List.length(&2, Pr.Ent, xs), LWork.wk.e.items(xs, r)), LWork.wk.e.put_list(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Pr.Ent, xs), 1n+m, e2) : {s == Wr.put_nat(_, LWork.wk.e.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def wre.e_conv_f(-m: Nat, -xs: List<&2, Pr.Ent>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e2: {List.length(&2, Pr.Ent, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Pr.Ent, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Pr.Ent, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def wre.e_conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Pr.Ent>>, pl: wre.ePL(s2, m, d)) -> wre.eLS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (wre.e_conv_s(s, s2, m, xs, r, en, e1, e2), (wre.e_conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def wre.e_nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  wre.eLS(s, Wr.get_list.start(~Pr.Ent, ~FW.get_ent, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      wre.e_conv(s, s2, m, en, fn, Wr.get_list.go(~Pr.Ent, ~FW.get_ent, m, FW.get_ent(s2)),
        wre.e_loop(m, FW.get_ent(s2), s2, wre.ent(s2)))

def wre.e_top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  wre.eLS(s, Wr.get_list.start(~Pr.Ent, ~FW.get_ent, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      wre.e_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a decoded list of entries is spelled, its count and entries within the
# wire
def wre.ents(+s: String) -> wre.eLS(s, Wr.get_list(~Pr.Ent, ~FW.get_ent, s)):
  wre.e_top(s, Wr.get_nat(s), {==})

# The view's place
# ----------------

def wre.AP(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Work.wk_spell_at(m, r) : String} & {LawsBase.core_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def wre.at_some(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> wre.AP(s, FW.get_at.some(d)):
  match d:
    case Wr.Got{+x, +s2}:
      +e = ed
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(x, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(x, s2), Wire.wire_nat_exact(s1, x, s2, e))),
        Wire.wire_nat_decoded_fits(s1, x, s2, e))
    case Wr.Bad{}:
      Unit{}

def wre.at_tag(-s: String, n: Nat, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}) -> wre.AP(s, FW.get_at.tag(n, s1)):
  match n:
    case 0n:
      (pre, {==})
    case 1n:
      wre.at_some(s, s1, pre, Wr.get_nat(s1), {==})
    case 2n+q:
      Unit{}

def wre.at_go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wre.AP(s, FW.get_at.go(d)):
  match d:
    case Wr.Got{+n, +s1}:
      wre.at_tag(s, n, s1, Wire.wire_nat_exact(s, n, s1, ed))
    case Wr.Bad{}:
      Unit{}

# a decoded place is spelled, and fits
def wre.at(+s: String) -> wre.AP(s, FW.get_at(s)):
  wre.at_go(s, Wr.get_nat(s), {==})

# An event
# --------

def wre.VP(s: String, d: Wr.Dec<Pr.Ev>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == Work.wk_spell_ev(e, r) : String} & {Work.wk_ev_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def wre.ev_view(-s: String, +at: Maybe<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(0n, Work.wk_spell_at(at, s2)) : String}, fa: {LawsBase.core_mfits(at) == True{} : Bool}, d: Wr.Dec<List<&2, Pr.Ent>>, ls: wre.eLS(s2, d)) -> wre.VP(s, FW.get_ev.view(at, d)):
  match d:
    case Wr.Got{+es, +s3}:
      (e1, f23) = ls
      (f2, f3) = f23
      (Equal.trans(String, s, Wr.put_nat(0n, Work.wk_spell_at(at, s2)), Wr.put_nat(0n, Work.wk_spell_at(at, Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, es, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, Work.wk_spell_at(at, z)), s2, Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, es, s3), e1)),
        LAWireSpell.ws_and_tt(LawsBase.core_mfits(at), Bool.and(LawsBase.wire_fits(List.length(&2, Pr.Ent, es)), Work.wk_ents_fit(es)), fa,
          LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Pr.Ent, es)), Work.wk_ents_fit(es), f2, f3)))
    case Wr.Bad{}:
      Unit{}

def wre.ev_at(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Maybe<&2, Nat>>, ap: wre.AP(s1, d)) -> wre.VP(s, FW.get_ev.at(d)):
  match d:
    case Wr.Got{+at, +s2}:
      (e1, fa) = ap
      wre.ev_view(s, at, s2,
        Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Work.wk_spell_at(at, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Work.wk_spell_at(at, s2), e1)),
        fa, Wr.get_list(~Pr.Ent, ~FW.get_ent, s2), wre.ents(s2))
    case Wr.Bad{}:
      Unit{}

def wre.ev_page(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Pr.Ent>>, ls: wre.eLS(s1, d)) -> wre.VP(s, FW.get_ev.page(d)):
  match d:
    case Wr.Got{+es, +s2}:
      (e1, f23) = ls
      (f2, f3) = f23
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, es, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_list(~Pr.Ent, ~Work.wk_spell_ent, es, s2), e1)),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Pr.Ent, es)), Work.wk_ents_fit(es), f2, f3))
    case Wr.Bad{}:
      Unit{}

def wre.ev_note(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> wre.VP(s, FW.get_ev.note(d)):
  match d:
    case Wr.Got{+x, +s2}:
      +e = ed
      (Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_nat(x, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_nat(x, s2), Wire.wire_nat_exact(s1, x, s2, e))),
        Wire.wire_nat_decoded_fits(s1, x, s2, e))
    case Wr.Bad{}:
      Unit{}

def wre.ev_tag(-s: String, n: Nat, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}) -> wre.VP(s, FW.get_ev.tag(n, s1)):
  match n:
    case 0n:
      wre.ev_at(s, s1, pre, FW.get_at(s1), wre.at(s1))
    case 1n:
      wre.ev_page(s, s1, pre, Wr.get_list(~Pr.Ent, ~FW.get_ent, s1), wre.ents(s1))
    case 2n:
      wre.ev_note(s, s1, pre, Wr.get_nat(s1), {==})
    case 3n+q:
      Unit{}

def wre.ev_go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wre.VP(s, FW.get_ev.go(d)):
  match d:
    case Wr.Got{+n, +s1}:
      wre.ev_tag(s, n, s1, Wire.wire_nat_exact(s, n, s1, ed))
    case Wr.Bad{}:
      Unit{}

# a decoded event is spelled, and its numbers fit
def wre.ev(+s: String) -> wre.VP(s, FW.get_ev(s)):
  wre.ev_go(s, Wr.get_nat(s), {==})
