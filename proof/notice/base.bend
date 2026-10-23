# eukhe: lemmas the proofs of area notice share

import Base
import ../../bend/notice.bend as No

# ---- notice ----

# proof_notice: the restore notice laws of LAWS.bend section supervisor (D1).
#
# - notice_shown_once: each stored notice is in one of two states: not
#   in the record and never shown, or in the record and shown once
#   (`pn.ok`). A restore adds a notice in the first state, and an offer
#   (`No.show`) moves a notice to the second state (`pn.show_shown`).
#   So no notice shows more than once.
# - notice_per_restore: an attach offers every stored notice, so after
#   it each one showed exactly once (`pn.full`), and the view stores one
#   notice for each restore (`pn.len_go`).

# Logic
# -----

def notice.pn.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def notice.pn.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : notice.pn.BD(_, A, Unit)
  Unit{}

def notice.pn.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      notice.pn.absurdF({False{} == True{} : Bool}, h)

def notice.pn.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      notice.pn.absurdF({b == True{} : Bool}, h)

def notice.pn.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      notice.pn.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

# The two states of a notice
# --------------------------

def pn.zero(c: Nat) -> Bool:
  match c:
    case 0n:
      True{}
    case 1n+p:
      False{}

def pn.one(c: Nat) -> Bool:
  match c:
    case 0n:
      False{}
    case 1n+p:
      pn.zero(p)

# not in the record and never shown, or in the record and shown once
def pn.ok(n: No.N) -> Bool:
  match n:
    case No.N{s, c}:
      match s:
        case True{}:
          pn.one(c)
        case False{}:
          pn.zero(c)

def pn.all_ok(ns: List<&2, No.N>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case n <> t:
      Bool.and(pn.ok(n), pn.all_ok(t))

# an offer leaves a notice in the record, shown once
def pn.show_shown(n: No.N, h: {pn.ok(n) == True{} : Bool}) -> {No.show(n) == No.N{True{}, 1n} : No.N}:
  match n:
    case No.N{s, c}:
      match s:
        case True{}:
          match c:
            case 0n:
              notice.pn.absurdF({No.show(No.N{True{}, 0n}) == No.N{True{}, 1n} : No.N}, h)
            case 1n+p:
              match p:
                case 0n:
                  {==}
                case 1n+q:
                  notice.pn.absurdF({No.show(No.N{True{}, 2n+q}) == No.N{True{}, 1n} : No.N}, h)
        case False{}:
          match c:
            case 0n:
              {==}
            case 1n+p:
              notice.pn.absurdF({No.show(No.N{False{}, 1n+p}) == No.N{True{}, 1n} : No.N}, h)

def pn.ok_show(+n: No.N, h: {pn.ok(n) == True{} : Bool}) -> {pn.ok(No.show(n)) == True{} : Bool}:
  %Equal.sym(No.N, No.show(n), No.N{True{}, 1n}, pn.show_shown(n, h)) : {pn.ok(_) == True{} : Bool}
  {==}

# Every event keeps the two states
# --------------------------------

def pn.ok_rebuild(ns: List<&2, No.N>, +h: {pn.all_ok(ns) == True{} : Bool}) -> {pn.all_ok(No.rebuild(ns)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +t:
      notice.pn.and_t(pn.ok(No.show(n)), pn.all_ok(No.rebuild(t)), pn.ok_show(n, notice.pn.and_l(pn.ok(n), pn.all_ok(t), h)), pn.ok_rebuild(t, notice.pn.and_r(pn.ok(n), pn.all_ok(t), h)))

def pn.ok_live_at(t: List<&2, No.N>, +n: No.N, hn: {pn.ok(n) == True{} : Bool}, +ht: {pn.all_ok(t) == True{} : Bool}) -> {pn.all_ok(No.live.at(t, n)) == True{} : Bool}:
  match t:
    case Nil{}:
      notice.pn.and_t(pn.ok(No.show(n)), True{}, pn.ok_show(n, hn), {==})
    case +m <> +u:
      notice.pn.and_t(pn.ok(n), pn.all_ok(No.live.at(u, m)), hn, pn.ok_live_at(u, m, notice.pn.and_l(pn.ok(m), pn.all_ok(u), ht), notice.pn.and_r(pn.ok(m), pn.all_ok(u), ht)))

def pn.ok_live(ns: List<&2, No.N>, +h: {pn.all_ok(ns) == True{} : Bool}) -> {pn.all_ok(No.live(ns)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +t:
      pn.ok_live_at(t, n, notice.pn.and_l(pn.ok(n), pn.all_ok(t), h), notice.pn.and_r(pn.ok(n), pn.all_ok(t), h))

def pn.ok_append(ns: List<&2, No.N>, +x: No.N, +h: {pn.all_ok(ns) == True{} : Bool}, hx: {pn.ok(x) == True{} : Bool}) -> {pn.all_ok(List.append(&2, No.N, ns, [x])) == True{} : Bool}:
  match ns:
    case Nil{}:
      notice.pn.and_t(pn.ok(x), True{}, hx, {==})
    case +n <> +t:
      notice.pn.and_t(pn.ok(n), pn.all_ok(List.append(&2, No.N, t, [x])), notice.pn.and_l(pn.ok(n), pn.all_ok(t), h), pn.ok_append(t, x, notice.pn.and_r(pn.ok(n), pn.all_ok(t), h), hx))

def pn.ok_step(+ns: List<&2, No.N>, e: No.Ev, h: {pn.all_ok(ns) == True{} : Bool}) -> {pn.all_ok(No.step(ns, e)) == True{} : Bool}:
  match e:
    case No.Restore{}:
      pn.ok_append(ns, No.N{False{}, 0n}, h, {==})
    case No.Live{}:
      pn.ok_live(ns, h)
    case No.Reconnect{}:
      pn.ok_rebuild(ns, h)

def pn.ok_go(evs: List<&2, No.Ev>, +ns: List<&2, No.N>, h: {pn.all_ok(ns) == True{} : Bool}) -> {pn.all_ok(No.go(evs, ns)) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case +e <> +rest:
      pn.ok_go(rest, No.step(ns, e), pn.ok_step(ns, e, h))
