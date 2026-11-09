# eukhe: the proof of LAW rebase_ambiguous_refused
#
# PROOF: the rule is the spec's (rr.refines); the edit is valid and
# the head differs, so the edit tries its contexts: at each the head holds
# two copies or more, so the step goes on (ra.step, ra.win), and past the
# last context the edit is Ambiguous (ra.go, by induction on the fuel).

import Base
import ../../bend/rebase.bend as R
import ../../spec/harness/rebase.bend as RbSpec
import ../../laws/rebase.bend as Rebase
import ./base.bend as LR
import ./base/refines.bend as LRR

def ra.step(ch: List<&2, Nat>, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +hl: Nat, +bl: Nat, +off: Nat, +len: Nat, ls: List<&2, Nat>, +i: Nat, -next: Unit -> R.Land, tw: {RbSpec.two(ch) == True{} : Bool}, e: {next(Unit{}) == R.Fails{R.Ambiguous{i}} : R.Land}) -> {RbSpec.step(ch, cb, la, ha, wl, hl, bl, off, len, ls, i, next) == R.Fails{R.Ambiguous{i}} : R.Land}:
  match ch:
    case Nil{}:
      LR.rb.absurdF({RbSpec.step(Nil{}, cb, la, ha, wl, hl, bl, off, len, ls, i, next) == R.Fails{R.Ambiguous{i}} : R.Land}, tw)
    case Con{+j, more}:
      match more:
        case Nil{}:
          LR.rb.absurdF({RbSpec.step([j], cb, la, ha, wl, hl, bl, off, len, ls, i, next) == R.Fails{R.Ambiguous{i}} : R.Land}, tw)
        case Con{k, rest}:
          e

def ra.win(w: R.Win, +b: List<&2, Nat>, +h: List<&2, Nat>, ls: List<&2, Nat>, +i: Nat, -next: Unit -> R.Land, tw: {RbSpec.two(RbSpec.copies(h, RbSpec.lines(w))) == True{} : Bool}, e: {next(Unit{}) == R.Fails{R.Ambiguous{i}} : R.Land}) -> {RbSpec.step.win(w, b, h, ls, i, next) == R.Fails{R.Ambiguous{i}} : R.Land}:
  match w:
    case R.Win{+la, +lw, +ha, +off, +len}:
      ra.step(RbSpec.copies(h, lw), RbSpec.copies(b, lw), la, ha, List.length(&2, Nat, lw), List.length(&2, Nat, h), List.length(&2, Nat, b), off, len, ls, i, next, tw, e)

def ra.go(fuel: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +ls: List<&2, Nat>, +k: Nat, +i: Nat, many: {RbSpec.many.go(fuel, b, h, s, t, k) == True{} : Bool}) -> {RbSpec.land.go(fuel, b, h, s, t, ls, k, i) == R.Fails{R.Ambiguous{i}} : R.Land}:
  match fuel:
    case 0n:
      {==}
    case 1n++p:
      +m = many
      +tw = LR.rb.and_l(RbSpec.two(RbSpec.copies(h, RbSpec.lines(RbSpec.window(b, s, t, k)))), RbSpec.many.go(p, b, h, s, t, 1n+k), m)
      +more = LR.rb.and_r(RbSpec.two(RbSpec.copies(h, RbSpec.lines(RbSpec.window(b, s, t, k)))), RbSpec.many.go(p, b, h, s, t, 1n+k), m)
      ra.win(RbSpec.window(b, s, t, k), b, h, ls, i, u => RbSpec.land.go(p, b, h, s, t, ls, 1n+k, i), tw, ra.go(p, b, h, s, t, ls, 1n+k, i, more))

def ra.land(e: R.Edit, +b: List<&2, Nat>, +h: List<&2, Nat>, +i: Nat, many: {RbSpec.many(b, h, e) == True{} : Bool}) -> {RbSpec.land(b, h, e, i) == R.Fails{R.Ambiguous{i}} : R.Land}:
  match e:
    case R.Edit{+s, +t, +ls}:
      ra.go(Nat.sub(1n+RbSpec.ctx(), RbSpec.first(s, t)), b, h, s, t, ls, RbSpec.first(s, t), i, many)

def Rebase.rebase_ambiguous_refused(b, h, e, ok, stale, many):
  +l = {[e] : List<&2, R.Edit>}
  +n = List.length(&2, Nat, b)
  %Equal.sym(R.Outcome, R.rebase(b, h, l), RbSpec.rebase(b, h, l), LRR.rr.refines(b, h, l)) : {_ == R.Conflict{R.Ambiguous{0n}} : R.Outcome}
  %Equal.sym(Maybe<&2, Nat>, RbSpec.bad(l, n), None{}, LR.rb.none_true(RbSpec.bad(l, n), ok)) : {RbSpec.rebase.of(_, RbSpec.same(b, h), b, h, l) == R.Conflict{R.Ambiguous{0n}} : R.Outcome}
  %Equal.sym(Bool, RbSpec.same(b, h), False{}, stale) : {RbSpec.rebase.of(None{}, _, b, h, l) == R.Conflict{R.Ambiguous{0n}} : R.Outcome}
  %Equal.sym(R.Land, RbSpec.land(b, h, e, 0n), R.Fails{R.Ambiguous{0n}}, ra.land(e, b, h, 0n, many)) : {RbSpec.crossed(RbSpec.land_all.of(_, R.Rebased{Nil{}}), List.length(&2, Nat, h)) == R.Conflict{R.Ambiguous{0n}} : R.Outcome}
  {==}
