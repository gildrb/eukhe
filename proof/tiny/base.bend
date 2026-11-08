# eukhe: lemmas the proofs of area tiny share

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/base.bend as LawsBase

# ---- tiny ----

# proof_tiny: the S9 laws of the tiny-model model in
# bend/tiny.bend.
#
# A pick scans its chain with the test of the head as a parameter: a hit
# gives the head, which is in the chain and available; a miss moves on
# to the rest, so the first available model wins and a chain with none
# available ends in Unavailable. Every event's need lists exactly one
# outcome and an exit none, so the outcomes count the needs. A worker's
# tag after one event is the tag of that need (a join keeps a worker of
# the same tag) or none after an exit, which carries the last tag along
# the events.

# Logic
# -----

def tiny.pn.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def tiny.pn.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : tiny.pn.BD(_, A, Unit)
  Unit{}

def tiny.pn.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      tiny.pn.absurdF({False{} == True{} : Bool}, h)

def tiny.pn.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      tiny.pn.absurdF({b == True{} : Bool}, h)

def pn.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      tiny.pn.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# Numbers
# -------

def pn.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pn.eq_refl(p)

# One process's election
# ----------------------
# The code compares two tags char by char exactly as the spec's
# text_same does (te.same), so each choice on a pong is the spec's.

def te.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : tiny.pn.BD(_, Unit, G)
  Unit{}

def te.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# the code's tag comparison is the spec's
def te.same(a: String, b: String) -> {Tn.same(a, b) == LawsBase.text_same(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, v}:
      {==}
    case SCon{x, u} SNil{}:
      {==}
    case SCon{x, u} SCon{y, v}:
      %te.same(u, v) : {Bool.and(Char.is_eq(x, y), Tn.same(u, v)) == Bool.and(Char.is_eq(x, y), _) : Bool}
      {==}
