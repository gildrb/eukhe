# proof_notice: the restore notice laws of laws/supervisor.bend (D1).
#
# - notice_shown_once: each stored notice is in one of two states: not
#   in the record and never shown, or in the record and shown once
#   (`pn.ok`). A restore adds a notice in the first state, and an offer
#   (`No.show`) moves a notice to the second state (`pn.show_shown`).
#   So no notice shows more than once.
# - notice_per_restore: an attach offers every stored notice, so after
#   it each one showed exactly once (`pn.full`), and the view stores one
#   notice for each restore (`pn.len_go`).

import Base
import ./notice.bend as No

# Logic
# -----

def pn.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pn.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pn.BD(_, A, Unit)
  Unit{}

def pn.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pn.absurdF({False{} == True{} : Bool}, h)

def pn.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pn.absurdF({b == True{} : Bool}, h)

def pn.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      pn.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

# Numbers
# -------

def pn.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pn.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def pn.add_succ_r(a: Nat, +m: Nat) -> {Nat.add(a, 1n+m) == 1n+Nat.add(a, m) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pn.add_succ_r(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

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
              pn.absurdF({No.show(No.N{True{}, 0n}) == No.N{True{}, 1n} : No.N}, h)
            case 1n+p:
              match p:
                case 0n:
                  {==}
                case 1n+q:
                  pn.absurdF({No.show(No.N{True{}, 2n+q}) == No.N{True{}, 1n} : No.N}, h)
        case False{}:
          match c:
            case 0n:
              {==}
            case 1n+p:
              pn.absurdF({No.show(No.N{False{}, 1n+p}) == No.N{True{}, 1n} : No.N}, h)

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
      pn.and_t(pn.ok(No.show(n)), pn.all_ok(No.rebuild(t)), pn.ok_show(n, pn.and_l(pn.ok(n), pn.all_ok(t), h)), pn.ok_rebuild(t, pn.and_r(pn.ok(n), pn.all_ok(t), h)))

def pn.ok_live_at(t: List<&2, No.N>, +n: No.N, hn: {pn.ok(n) == True{} : Bool}, +ht: {pn.all_ok(t) == True{} : Bool}) -> {pn.all_ok(No.live.at(t, n)) == True{} : Bool}:
  match t:
    case Nil{}:
      pn.and_t(pn.ok(No.show(n)), True{}, pn.ok_show(n, hn), {==})
    case +m <> +u:
      pn.and_t(pn.ok(n), pn.all_ok(No.live.at(u, m)), hn, pn.ok_live_at(u, m, pn.and_l(pn.ok(m), pn.all_ok(u), ht), pn.and_r(pn.ok(m), pn.all_ok(u), ht)))

def pn.ok_live(ns: List<&2, No.N>, +h: {pn.all_ok(ns) == True{} : Bool}) -> {pn.all_ok(No.live(ns)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +t:
      pn.ok_live_at(t, n, pn.and_l(pn.ok(n), pn.all_ok(t), h), pn.and_r(pn.ok(n), pn.all_ok(t), h))

def pn.ok_append(ns: List<&2, No.N>, +x: No.N, +h: {pn.all_ok(ns) == True{} : Bool}, hx: {pn.ok(x) == True{} : Bool}) -> {pn.all_ok(List.append(&2, No.N, ns, [x])) == True{} : Bool}:
  match ns:
    case Nil{}:
      pn.and_t(pn.ok(x), True{}, hx, {==})
    case +n <> +t:
      pn.and_t(pn.ok(n), pn.all_ok(List.append(&2, No.N, t, [x])), pn.and_l(pn.ok(n), pn.all_ok(t), h), pn.ok_append(t, x, pn.and_r(pn.ok(n), pn.all_ok(t), h), hx))

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

# notice_shown_once
# -----------------

def pn.amo(s: Bool, c: Nat, h: {pn.ok(No.N{s, c}) == True{} : Bool}) -> {No.at_most_one(c) == True{} : Bool}:
  match s c:
    case True{} 0n:
      {==}
    case True{} 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          pn.absurdF({No.at_most_one(2n+q) == True{} : Bool}, h)
    case False{} 0n:
      {==}
    case False{} 1n+p:
      pn.absurdF({No.at_most_one(1n+p) == True{} : Bool}, h)

def pn.once_of_ok(ns: List<&2, No.N>, +h: {pn.all_ok(ns) == True{} : Bool}) -> {No.once(ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      match n:
        case No.N{+s, +c}:
          pn.and_t(No.at_most_one(c), No.once(t), pn.amo(s, c, pn.and_l(pn.ok(No.N{s, c}), pn.all_ok(t), h)), pn.once_of_ok(t, pn.and_r(pn.ok(No.N{s, c}), pn.all_ok(t), h)))

def pn.notice_shown_once(+evs: List<&2, No.Ev>) -> {No.once(No.run(evs)) == True{} : Bool}:
  pn.once_of_ok(No.run(evs), pn.ok_go(evs, Nil{}, {==}))

# notice_per_restore
# ------------------

def pn.len_snoc(ns: List<&2, No.N>, +x: No.N) -> {List.length(&2, No.N, List.append(&2, No.N, ns, [x])) == 1n+List.length(&2, No.N, ns) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      %pn.len_snoc(t, x) : {1n+List.length(&2, No.N, List.append(&2, No.N, t, [x])) == 1n+_ : Nat}
      {==}

def pn.len_live_at(t: List<&2, No.N>, n: No.N) -> {List.length(&2, No.N, No.live.at(t, n)) == 1n+List.length(&2, No.N, t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case +m <> +u:
      %pn.len_live_at(u, m) : {1n+List.length(&2, No.N, No.live.at(u, m)) == 1n+_ : Nat}
      {==}

def pn.len_live(ns: List<&2, No.N>) -> {List.length(&2, No.N, No.live(ns)) == List.length(&2, No.N, ns) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case n <> t:
      pn.len_live_at(t, n)

def pn.len_rebuild(ns: List<&2, No.N>) -> {List.length(&2, No.N, No.rebuild(ns)) == List.length(&2, No.N, ns) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      %pn.len_rebuild(t) : {1n+List.length(&2, No.N, No.rebuild(t)) == 1n+_ : Nat}
      {==}

# the view stores one notice for each restore
def pn.len_go(evs: List<&2, No.Ev>, +ns: List<&2, No.N>) -> {List.length(&2, No.N, No.go(evs, ns)) == Nat.add(No.restores(evs), List.length(&2, No.N, ns)) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case No.Restore{}:
          +r = No.restores(rest)
          +l = List.length(&2, No.N, ns)
          +app = List.append(&2, No.N, ns, [No.N{False{}, 0n}])
          %Equal.sym(Nat, List.length(&2, No.N, No.go(rest, app)), Nat.add(r, List.length(&2, No.N, app)), pn.len_go(rest, app)) : {_ == 1n+Nat.add(r, l) : Nat}
          %Equal.sym(Nat, List.length(&2, No.N, app), 1n+l, pn.len_snoc(ns, No.N{False{}, 0n})) : {Nat.add(r, _) == 1n+Nat.add(r, l) : Nat}
          pn.add_succ_r(r, l)
        case No.Live{}:
          +r = No.restores(rest)
          %Equal.sym(Nat, List.length(&2, No.N, No.go(rest, No.live(ns))), Nat.add(r, List.length(&2, No.N, No.live(ns))), pn.len_go(rest, No.live(ns))) : {_ == Nat.add(r, List.length(&2, No.N, ns)) : Nat}
          %pn.len_live(ns) : {Nat.add(r, List.length(&2, No.N, No.live(ns))) == Nat.add(r, _) : Nat}
          {==}
        case No.Reconnect{}:
          +r = No.restores(rest)
          %Equal.sym(Nat, List.length(&2, No.N, No.go(rest, No.rebuild(ns))), Nat.add(r, List.length(&2, No.N, No.rebuild(ns))), pn.len_go(rest, No.rebuild(ns))) : {_ == Nat.add(r, List.length(&2, No.N, ns)) : Nat}
          %pn.len_rebuild(ns) : {Nat.add(r, List.length(&2, No.N, No.rebuild(ns))) == Nat.add(r, _) : Nat}
          {==}

# after an attach, each stored notice showed once
def pn.full(ns: List<&2, No.N>, +h: {pn.all_ok(ns) == True{} : Bool}) -> {No.total(No.rebuild(ns)) == List.length(&2, No.N, ns) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +t:
      %Equal.sym(No.N, No.show(n), No.N{True{}, 1n}, pn.show_shown(n, pn.and_l(pn.ok(n), pn.all_ok(t), h))) : {No.total(_ <> No.rebuild(t)) == 1n+List.length(&2, No.N, t) : Nat}
      %pn.full(t, pn.and_r(pn.ok(n), pn.all_ok(t), h)) : {1n+No.total(No.rebuild(t)) == 1n+_ : Nat}
      {==}

# the events, then the last event an attach
def pn.go_snoc(evs: List<&2, No.Ev>, +ns: List<&2, No.N>, +e: No.Ev) -> {No.go(List.append(&2, No.Ev, evs, [e]), ns) == No.step(No.go(evs, ns), e) : List<&2, No.N>}:
  match evs:
    case Nil{}:
      {==}
    case +h <> +t:
      pn.go_snoc(t, No.step(ns, h), e)

def pn.notice_per_restore(+evs: List<&2, No.Ev>) -> {No.total(No.run(List.append(&2, No.Ev, evs, [No.Reconnect{}]))) == No.restores(evs) : Nat}:
  +g = No.go(evs, Nil{})
  %Equal.sym(List<&2, No.N>, No.go(List.append(&2, No.Ev, evs, [No.Reconnect{}]), Nil{}), No.step(g, No.Reconnect{}), pn.go_snoc(evs, Nil{}, No.Reconnect{})) : {No.total(_) == No.restores(evs) : Nat}
  %Equal.sym(Nat, No.total(No.rebuild(g)), List.length(&2, No.N, g), pn.full(g, pn.ok_go(evs, Nil{}, {==}))) : {_ == No.restores(evs) : Nat}
  Equal.trans(Nat, List.length(&2, No.N, g), Nat.add(No.restores(evs), 0n), No.restores(evs), pn.len_go(evs, Nil{}), pn.add_zero(No.restores(evs)))
