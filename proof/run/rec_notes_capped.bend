# eukhe: the proof of LAW rec_notes_capped

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

# Every recovery stops at its cap
# -------------------------------
# Each lemma takes a cap test u with its equation e, as a match needs a
# parameter.

def cap_long(+rc: Rn.RCfg, u: Bool, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, e: {Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)) == u : Bool}, ok: {Rn.Rk.capped(rc, k, row) == True{} : Bool}) -> {Rn.Rec.capped(rc, Rn.Dec.r(Rn.rec.long(u, Rn.Rk.longs(k, row), same, last, Rn.Rec{k, row, same, last}))) == True{} : Bool}:
  match u:
    case True{}:
      e
    case False{}:
      ok

def cap_leak(+rc: Rn.RCfg, u: Bool, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, e: {Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)) == u : Bool}, ok: {Rn.Rk.capped(rc, k, row) == True{} : Bool}) -> {Rn.Rec.capped(rc, Rn.Dec.r(Rn.rec.leak(u, Rn.Rk.leaks(k, row), same, last, Rn.Rec{k, row, same, last}))) == True{} : Bool}:
  match u:
    case True{}:
      e
    case False{}:
      ok

def cap_ran(+rc: Rn.RCfg, fresh: Bool, u: Bool, kept: Bool, +m: Nat, +h: Nat, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, e: {Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)) == u : Bool}, ok: {Rn.Rk.capped(rc, k, row) == True{} : Bool}) -> {Rn.Rec.capped(rc, Rn.Dec.r(Rn.rec.ran(fresh, u, kept, m, h, Rn.Rk.loops(k, row), same, last, Rn.Rec{k, row, same, last}))) == True{} : Bool}:
  match fresh u:
    case True{} u:
      {==}
    case False{} True{}:
      e
    case False{} False{}:
      ok

def cap_out(+rc: Rn.RCfg, o: Rn.Out, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, ok: {Rn.Rk.capped(rc, k, row) == True{} : Bool}) -> {Rn.Rec.capped(rc, Rn.Dec.r(Rn.rec.go(rc, o, k, row, same, last))) == True{} : Bool}:
  match o:
    case Rn.Long{}:
      cap_long(rc, Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)), k, row, same, last, {==}, ok)
    case Rn.Leak{rebuilt, +h, kept}:
      match rebuilt:
        case True{}:
          cap_ran(rc, Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)), Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), kept, Rn.again(same, last, h), h, k, row, same, last, {==}, ok)
        case False{}:
          cap_leak(rc, Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)), k, row, same, last, {==}, ok)
    case Rn.Ran{+h, kept}:
      cap_ran(rc, Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)), Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), kept, Rn.again(same, last, h), h, k, row, same, last, {==}, ok)
    case Rn.Noted{}:
      {==}
    case Rn.Said{}:
      ok
    case Rn.Answer{}:
      {==}
    case Rn.Other{}:
      ok

def cap_step(+rc: Rn.RCfg, o: Rn.Out, r: Rn.Rec, ok: {Rn.Rec.capped(rc, r) == True{} : Bool}) -> {Rn.Rec.capped(rc, Rn.Dec.r(Rn.Rec.step(rc, o, r))) == True{} : Bool}:
  match r:
    case Rn.Rec{k, row, same, last}:
      cap_out(rc, o, k, row, same, last, ok)

def cap_go(os: List<&2, Rn.Out>, +rc: Rn.RCfg, +r: Rn.Rec, ok: {Rn.Rec.capped(rc, r) == True{} : Bool}) -> {Rn.Rec.capped(rc, Rn.Rec.go(os, rc, r)) == True{} : Bool}:
  match os:
    case Nil{}:
      ok
    case +o <> rest:
      cap_go(rest, rc, Rn.Dec.r(Rn.Rec.step(rc, o, r)), cap_step(rc, o, r, ok))

def notes_capped(+rc: Rn.RCfg, +os: List<&2, Rn.Out>) -> {Rn.Rec.capped(rc, Rn.Rec.run(rc, os)) == True{} : Bool}:
  cap_go(os, rc, Rn.Rec.init(), {==})

def Laws.rec_notes_capped(rc, os):
  notes_capped(rc, os)
