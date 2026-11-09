# eukhe: the proof of LAW path_real_chain_within
#
# PROOF: in a chain of K links, the first link at /i+1 (i < K) is the one
# to /i (pch.find_some), and /0 holds none (pch.find_none); so from /i with
# at least i links left, each link is followed to the next one, one link
# fewer each time, and /0 ends it without a loop (pch.walk, by induction
# on i).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./base/lemmas.bend as LAE
import ../base/logic/logic.bend as LLogicLogic

def pch.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      pch.le_refl(k)

def pch.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

# 1 + a <= b gives a <= b
def pch.le_pred(a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a:
    case 0n:
      pch.le0(b)
    case 1n+i:
      match b:
        case 0n:
          h
        case 1n+k:
          pch.le_pred(i, k, h)

# i <= k and k is not i: 1 + i <= k
def pch.le_ne(i: Nat, k: Nat, h: {Nat.is_le(i, k) == True{} : Bool}, ne: {Nat.is_eq(k, i) == False{} : Bool}) -> {Nat.is_le(1n+i, k) == True{} : Bool}:
  match i:
    case 0n:
      match k:
        case 0n:
          LLogicLogic.pp.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, ne)
        case 1n+j:
          pch.le0(j)
    case 1n+a:
      match k:
        case 0n:
          h
        case 1n+j:
          pch.le_ne(a, j, h, ne)

# no link of a chain sits at /0
def pch.find_none(k: Nat) -> {Pp.link.find(PathPolicy.pp_chain(k), [0n]) == None{} : Maybe<&2, Pp.Link>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      pch.find_none(j)

# the head of a chain of 1 + k links, by the test b of k against i
def pch.fs_at(b: Bool, +k: Nat, +i: Nat, eb: {Nat.is_eq(k, i) == b : Bool}, le: {Nat.is_le(1n+i, 1n+k) == True{} : Bool}, ih: {Nat.is_le(1n+i, k) == True{} : Bool} -> {Pp.link.find(PathPolicy.pp_chain(k), [1n+i]) == Some{Pp.Link{[1n+i], True{}, [Tl.Name{i}]}} : Maybe<&2, Pp.Link>}) -> {Pp.link.pick(Bool.and(b, True{}), Pp.Link{[1n+k], True{}, [Tl.Name{k}]}, Pp.link.find(PathPolicy.pp_chain(k), [1n+i])) == Some{Pp.Link{[1n+i], True{}, [Tl.Name{i}]}} : Maybe<&2, Pp.Link>}:
  match b:
    case True{}:
      +e = LAE.pp.eq_true(k, i, eb)
      Equal.cong(Nat, Maybe<&2, Pp.Link>, z => Some{Pp.Link{[1n+z], True{}, [Tl.Name{z}]}}, k, i, e)
    case False{}:
      ih(pch.le_ne(i, k, le, eb))

# the first link of a chain of k links at /1+i (i < k) is the one to /i
def pch.find_some(k: Nat, +i: Nat) -> {Nat.is_le(1n+i, k) == True{} : Bool} -> {Pp.link.find(PathPolicy.pp_chain(k), [1n+i]) == Some{Pp.Link{[1n+i], True{}, [Tl.Name{i}]}} : Maybe<&2, Pp.Link>}:
  match k:
    case 0n:
      h => LA.pp.absurdF({Pp.link.find(Nil{}, [1n+i]) == Some{Pp.Link{[1n+i], True{}, [Tl.Name{i}]}} : Maybe<&2, Pp.Link>}, h)
    case 1n++j:
      h => pch.fs_at(Nat.is_eq(j, i), j, i, {==}, h, pch.find_some(j, i))

# from /i, with f >= i links left, a chain of K >= i links ends at /0
def pch.walk(i: Nat, f: Nat, +K: Nat, +iK: {Nat.is_le(i, K) == True{} : Bool}, fi: {Nat.is_le(i, f) == True{} : Bool}) -> {Pp.go(f, [Tl.Name{i}], PathPolicy.pp_chain(K), Nil{}, False{}, Pp.link.find(PathPolicy.pp_chain(K), [i])) == Pp.Res{[0n], False{}} : Pp.Res}:
  match i:
    case 0n:
      match f:
        case 0n:
          %Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(PathPolicy.pp_chain(K), [0n]), None{}, pch.find_none(K)) : {Pp.go(0n, [Tl.Name{0n}], PathPolicy.pp_chain(K), Nil{}, False{}, _) == Pp.Res{[0n], False{}} : Pp.Res}
          {==}
        case 1n+g:
          %Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(PathPolicy.pp_chain(K), [0n]), None{}, pch.find_none(K)) : {Pp.go(1n+g, [Tl.Name{0n}], PathPolicy.pp_chain(K), Nil{}, False{}, _) == Pp.Res{[0n], False{}} : Pp.Res}
          {==}
    case 1n++a:
      match f:
        case 0n:
          LA.pp.absurdF({Pp.go(0n, [Tl.Name{1n+a}], PathPolicy.pp_chain(K), Nil{}, False{}, Pp.link.find(PathPolicy.pp_chain(K), [1n+a])) == Pp.Res{[0n], False{}} : Pp.Res}, fi)
        case 1n+g:
          +ea = Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(PathPolicy.pp_chain(K), [1n+a]), Some{Pp.Link{[1n+a], True{}, [Tl.Name{a}]}}, pch.find_some(K, a)(iK))
          %ea : {Pp.go(1n+g, [Tl.Name{1n+a}], PathPolicy.pp_chain(K), Nil{}, False{}, _) == Pp.Res{[0n], False{}} : Pp.Res}
          pch.walk(a, g, K, pch.le_pred(a, K, iK), fi)

def PathPolicy.path_real_chain_within(k, le):
  pch.walk(k, 40n, k, pch.le_refl(k), le)
