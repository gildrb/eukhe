# eukhe: the proof of LAW rebase_invalid_first
#
# PROOF: the rule is the spec's (rr.refines). Edits the spec's S1 check
# finds bad are refused as Invalid at that edit; otherwise the answer is
# the edits (a head that is the base) or what landing them gives: no step
# of a context fails as Invalid (iv.step, through the contexts iv.go and
# the edits iv.all), and the crossing check refuses only as Crossed
# (iv.crossed).

import Base
import ../../bend/rebase.bend as R
import ../../spec/harness/rebase.bend as RbSpec
import ../../laws/rebase.bend as Rebase
import ./base.bend as LR
import ./base/refines.bend as LRR

# a landing that fails as Invalid
def iv.inv(l: R.Land) -> Bool:
  match l:
    case R.Lands{f}:
      False{}
    case R.Fails{w}:
      match w:
        case R.Invalid{i}:
          True{}
        case R.Moved{i}:
          False{}
        case R.Ambiguous{i}:
          False{}
        case R.Crossed{i}:
          False{}
        case R.TooLarge{}:
          False{}

def iv.pick(q: Bool, f: R.Edit, -next: Unit -> R.Land, ih: {iv.inv(next(Unit{})) == False{} : Bool}) -> {iv.inv(RbSpec.step.pick(q, f, next)) == False{} : Bool}:
  match q:
    case True{}:
      {==}
    case False{}:
      ih

def iv.base(cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +bl: Nat, f: R.Edit, -next: Unit -> R.Land, ih: {iv.inv(next(Unit{})) == False{} : Bool}) -> {iv.inv(RbSpec.step.base(cb, la, ha, wl, bl, f, next)) == False{} : Bool}:
  match cb:
    case Nil{}:
      ih
    case Con{+x, more}:
      match more:
        case Nil{}:
          iv.pick(RbSpec.sits(la, ha, x, wl, bl), f, next, ih)
        case Con{y, rest}:
          ih

def iv.one(q: Bool, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +bl: Nat, f: R.Edit, +i: Nat, -next: Unit -> R.Land, ih: {iv.inv(next(Unit{})) == False{} : Bool}) -> {iv.inv(RbSpec.step.one(q, cb, la, ha, wl, bl, f, i, next)) == False{} : Bool}:
  match q:
    case True{}:
      iv.base(cb, la, ha, wl, bl, f, next, ih)
    case False{}:
      {==}

# one context's verdict fails as Invalid only if the next context does
def iv.step(ch: List<&2, Nat>, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +hl: Nat, +bl: Nat, +off: Nat, +len: Nat, ls: List<&2, Nat>, +i: Nat, -next: Unit -> R.Land, ih: {iv.inv(next(Unit{})) == False{} : Bool}) -> {iv.inv(RbSpec.step(ch, cb, la, ha, wl, hl, bl, off, len, ls, i, next)) == False{} : Bool}:
  match ch:
    case Nil{}:
      {==}
    case Con{+j, more}:
      match more:
        case Nil{}:
          iv.one(RbSpec.sits(la, ha, j, wl, hl), cb, la, ha, wl, bl, R.Edit{Nat.add(j, off), Nat.add(Nat.add(j, off), len), ls}, i, next, ih)
        case Con{y, rest}:
          ih

def iv.win(w: R.Win, +b: List<&2, Nat>, +h: List<&2, Nat>, ls: List<&2, Nat>, +i: Nat, -next: Unit -> R.Land, ih: {iv.inv(next(Unit{})) == False{} : Bool}) -> {iv.inv(RbSpec.step.win(w, b, h, ls, i, next)) == False{} : Bool}:
  match w:
    case R.Win{+la, +lw, +ha, +off, +len}:
      iv.step(RbSpec.copies(h, lw), RbSpec.copies(b, lw), la, ha, List.length(&2, Nat, lw), List.length(&2, Nat, h), List.length(&2, Nat, b), off, len, ls, i, next, ih)

def iv.go(fuel: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +ls: List<&2, Nat>, +k: Nat, +i: Nat) -> {iv.inv(RbSpec.land.go(fuel, b, h, s, t, ls, k, i)) == False{} : Bool}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      iv.win(RbSpec.window(b, s, t, k), b, h, ls, i, u => RbSpec.land.go(p, b, h, s, t, ls, 1n+k, i), iv.go(p, b, h, s, t, ls, 1n+k, i))

def iv.land(+b: List<&2, Nat>, +h: List<&2, Nat>, e: R.Edit, +i: Nat) -> {iv.inv(RbSpec.land(b, h, e, i)) == False{} : Bool}:
  match e:
    case R.Edit{+s, +t, +ls}:
      iv.go(Nat.sub(1n+RbSpec.ctx(), RbSpec.first(s, t)), b, h, s, t, ls, RbSpec.first(s, t), i)

def iv.all.of(l: R.Land, r: R.Outcome, hl: {iv.inv(l) == False{} : Bool}, hr: {Rebase.rb_invalid(r) == None{} : Maybe<&2, Nat>}) -> {Rebase.rb_invalid(RbSpec.land_all.of(l, r)) == None{} : Maybe<&2, Nat>}:
  match l:
    case R.Lands{f}:
      match r:
        case R.Rebased{fs}:
          {==}
        case R.Conflict{w}:
          hr
    case R.Fails{w}:
      match w:
        case R.Invalid{k}:
          LR.rb.absurd({Rebase.rb_invalid(R.Conflict{R.Invalid{k}}) == None{} : Maybe<&2, Nat>}, hl)
        case R.Moved{k}:
          {==}
        case R.Ambiguous{k}:
          {==}
        case R.Crossed{k}:
          {==}
        case R.TooLarge{}:
          {==}

# landing the edits never refuses them as Invalid
def iv.all(es: List<&2, R.Edit>, +b: List<&2, Nat>, +h: List<&2, Nat>, +i: Nat) -> {Rebase.rb_invalid(RbSpec.land_all(es, b, h, i)) == None{} : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      iv.all.of(RbSpec.land(b, h, e, i), RbSpec.land_all(rest, b, h, 1n+i), iv.land(b, h, e, i), iv.all(rest, b, h, 1n+i))

def iv.cr(c: Maybe<&2, Nat>, fs: List<&2, R.Edit>) -> {Rebase.rb_invalid(RbSpec.crossed.of(c, fs)) == None{} : Maybe<&2, Nat>}:
  match c:
    case None{}:
      {==}
    case Some{i}:
      {==}

# the crossing check refuses only as Crossed
def iv.crossed(o: R.Outcome, +m: Nat, ho: {Rebase.rb_invalid(o) == None{} : Maybe<&2, Nat>}) -> {Rebase.rb_invalid(RbSpec.crossed(o, m)) == None{} : Maybe<&2, Nat>}:
  match o:
    case R.Rebased{+fs}:
      iv.cr(RbSpec.bad(fs, m), fs)
    case R.Conflict{w}:
      ho

def iv.of(c: Maybe<&2, Nat>, q: Bool, +b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> {Rebase.rb_invalid(RbSpec.rebase.of(c, q, b, h, es)) == c : Maybe<&2, Nat>}:
  match c:
    case Some{i}:
      {==}
    case None{}:
      match q:
        case True{}:
          {==}
        case False{}:
          iv.crossed(RbSpec.land_all(es, b, h, 0n), List.length(&2, Nat, h), iv.all(es, b, h, 0n))

def Rebase.rebase_invalid_first(b, h, es):
  %Equal.sym(R.Outcome, R.rebase(b, h, es), RbSpec.rebase(b, h, es), LRR.rr.refines(b, h, es)) : {Rebase.rb_invalid(_) == RbSpec.bad(es, List.length(&2, Nat, b)) : Maybe<&2, Nat>}
  iv.of(RbSpec.bad(es, List.length(&2, Nat, b)), RbSpec.same(b, h), b, h, es)
