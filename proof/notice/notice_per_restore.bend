# eukhe: the proof of LAW notice_per_restore

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice
import ./base.bend as LA

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
def pn.full(ns: List<&2, No.N>, +h: {LA.pn.all_ok(ns) == True{} : Bool}) -> {No.total(No.rebuild(ns)) == List.length(&2, No.N, ns) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +t:
      %Equal.sym(No.N, No.show(n), No.N{True{}, 1n}, LA.pn.show_shown(n, LA.notice.pn.and_l(LA.pn.ok(n), LA.pn.all_ok(t), h))) : {No.total(_ <> No.rebuild(t)) == 1n+List.length(&2, No.N, t) : Nat}
      %pn.full(t, LA.notice.pn.and_r(LA.pn.ok(n), LA.pn.all_ok(t), h)) : {1n+No.total(No.rebuild(t)) == 1n+_ : Nat}
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
  %Equal.sym(Nat, No.total(No.rebuild(g)), List.length(&2, No.N, g), pn.full(g, LA.pn.ok_go(evs, Nil{}, {==}))) : {_ == No.restores(evs) : Nat}
  Equal.trans(Nat, List.length(&2, No.N, g), Nat.add(No.restores(evs), 0n), No.restores(evs), pn.len_go(evs, Nil{}), pn.add_zero(No.restores(evs)))

def Notice.notice_per_restore(evs):
  pn.notice_per_restore(evs)
