# eukhe: the proof of LAW search_walk_runs: by induction on the walk, for any
# reply before it and any count of files left to meet; each file steps as
# search_met_answers' chain says, and the entry's place in the walk is not in
# the reply

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

# both sides of an and that holds hold
def swr.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def swr.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LADocSearch.dsb.tf({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, e))

# one file met: the stepper's walk and reply, as the rules give them
def swr.step(+p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat, +t: Nat, +maxb: Nat, +f: Sr.Form, h: {DocSearch.ds_fits(DocSearch.ds_met(f)) == True{} : Bool}) -> {(FDs.Walk{p, s, k, Sr.left(Sr.Ent{0n, f}, p, rem), Sr.seen(Sr.Ent{0n, f}, rem, n), Nat.sub(t, 1n), maxb}, DocSearch.ds_spell(DocSearch.ds_said(Sr.out(Sr.Ent{0n, f}, p, s, k, rem, n), Sr.kept(Sr.Ent{0n, f}, p, rem)))) == FDs.step(FDs.Walk{p, s, k, rem, n, t, maxb}, DocSearch.ds_spell(DocSearch.ds_met(f))) : FDs.St & String}:
  +w = {FDs.Walk{p, s, k, rem, n, t, maxb} : FDs.St}
  +e = {Sr.Ent{0n, f} : Sr.Ent}
  +o = Sr.out(e, p, s, k, rem, n)
  +kp = Sr.kept(e, p, rem)
  +w2 = {FDs.Walk{p, s, k, Sr.left(e, p, rem), Sr.seen(e, rem, n), Nat.sub(t, 1n), maxb} : FDs.St}
  +xs = {DocSearch.ds_met(f) : List<&2, Nat>}
  %LADocSearch.dsb.read(xs, h) : {(w2, DocSearch.ds_spell(DocSearch.ds_said(o, kp))) == FDs.step.got(w, _) : FDs.St & String}
  %LADocSearch.dsb.met(f) : {(w2, DocSearch.ds_spell(DocSearch.ds_said(o, kp))) == FDs.step.ev(w, _) : FDs.St & String}
  %LADocSearch.dsb.said(o, kp) : {(w2, DocSearch.ds_spell(_)) == FDs.step.ev(w, Some{FDs.Met{f}}) : FDs.St & String}
  {==}

# the replies to an entry and to the rest of the walk do not hold its place
# in the walk
def swr.place(f: Sr.Form, +rem: Nat, -i: Nat, +rest: List<&2, Sr.Ent>, +p: Nat, +s: Nat, +k: Nat, +n: Nat, +said: String) -> {said <> DocSearch.ds_spell(DocSearch.ds_said(Sr.out(Sr.Ent{i, f}, p, s, k, rem, n), Sr.kept(Sr.Ent{i, f}, p, rem))) <> DocSearch.ds_trace(Sr.run(rest, p, s, k, Sr.left(Sr.Ent{i, f}, p, rem), Sr.seen(Sr.Ent{i, f}, rem, n)), Sr.keeps(rest, p, Sr.left(Sr.Ent{i, f}, p, rem))) == said <> DocSearch.ds_spell(DocSearch.ds_said(Sr.out(Sr.Ent{0n, f}, p, s, k, rem, n), Sr.kept(Sr.Ent{0n, f}, p, rem))) <> DocSearch.ds_trace(Sr.run(rest, p, s, k, Sr.left(Sr.Ent{0n, f}, p, rem), Sr.seen(Sr.Ent{0n, f}, rem, n)), Sr.keeps(rest, p, Sr.left(Sr.Ent{0n, f}, p, rem))) : List<&2, String>}:
  match f:
    case Sr.Opened{h, big}:
      match rem:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case Sr.Skip{why}:
      {==}

# the walk from any state, after any reply, turned around
def swr.go(es: List<&2, Sr.Ent>, +p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat, +t: Nat, +maxb: Nat, +said: String, +h: {DocSearch.ds_walk_fits(es) == True{} : Bool}) -> {said <> DocSearch.ds_trace(Sr.run(es, p, s, k, rem, n), Sr.keeps(es, p, rem)) == DocSearch.ds_drive(es, (FDs.Walk{p, s, k, rem, n, t, maxb}, said)) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Sr.Ent{+i, +f}:
          +e0 = {Sr.Ent{0n, f} : Sr.Ent}
          +ei = {Sr.Ent{i, f} : Sr.Ent}
          +l0 = Sr.left(e0, p, rem)
          +sn0 = Sr.seen(e0, rem, n)
          +kp0 = Sr.kept(e0, p, rem)
          +sp0 = DocSearch.ds_spell(DocSearch.ds_said(Sr.out(e0, p, s, k, rem, n), kp0))
          +fits = DocSearch.ds_fits(DocSearch.ds_met(f))
          +more = DocSearch.ds_walk_fits(rest)
          +ri = {said <> DocSearch.ds_trace(Sr.run(ei <> rest, p, s, k, rem, n), Sr.keeps(ei <> rest, p, rem)) : List<&2, String>}
          %swr.step(p, s, k, rem, n, t, maxb, f, swr.and_l(fits, more, h)) : {ri == said <> DocSearch.ds_drive(rest, _) : List<&2, String>}
          %swr.go(rest, p, s, k, l0, sn0, Nat.sub(t, 1n), maxb, sp0, swr.and_r(fits, more, h)) : {ri == said <> _ : List<&2, String>}
          swr.place(f, rem, i, rest, p, s, k, n, said)

def DocSearch.search_walk_runs(es, p, s, k, rem, n, t, maxb, h):
  Equal.sym(List<&2, String>, "" <> DocSearch.ds_trace(Sr.run(es, p, s, k, rem, n), Sr.keeps(es, p, rem)), DocSearch.ds_drive(es, (FDs.Walk{p, s, k, rem, n, t, maxb}, "")), swr.go(es, p, s, k, rem, n, t, maxb, "", h))
