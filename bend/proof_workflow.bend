# proof_workflow: the WF laws (laws/workflow.bend) of the dynamic
# workflow scheduler model in bend/workflow.bend.
#
# Taking and giving a unit move it between the two counters of a pool,
# so the pool's size stays; the counters laws go by induction on the
# events. The cache laws read the hit; the results law goes by
# induction on the items before the failed one.

import Base
import ./workflow.bend as W

def pw.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pw.add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def pw.take_size(p: W.Pool) -> {W.size(W.take(p)) == W.size(p) : Nat}:
  match p:
    case W.Pool{t, l}:
      match l:
        case 0n:
          {==}
        case 1n+m:
          pw.add_succ(t, m)

def pw.give_size(p: W.Pool) -> {W.size(W.give(p)) == W.size(p) : Nat}:
  match p:
    case W.Pool{t, l}:
      match t:
        case 0n:
          {==}
        case 1n+s:
          Equal.sym(Nat, 1n+Nat.add(s, l), Nat.add(s, 1n+l), pw.add_succ(s, l))

def pw.step_size(e: W.Ev, p: W.Pool) -> {W.size(W.step(e, p)) == W.size(p) : Nat}:
  match e:
    case W.Ask{}:
      pw.take_size(p)
    case W.Settle{}:
      pw.give_size(p)

def pw.run_size(es: List<&2, W.Ev>, +p: W.Pool) -> {W.size(W.run(es, p)) == W.size(p) : Nat}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      Equal.trans(Nat, W.size(W.run(rest, W.step(e, p))), W.size(W.step(e, p)), W.size(p), pw.run_size(rest, W.step(e, p)), pw.step_size(e, p))

def pw.spawns_size(n: Nat, +p: W.Pool) -> {W.size(W.spawns(n, p)) == W.size(p) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      Equal.trans(Nat, W.size(W.spawns(m, W.take(p))), W.size(W.take(p)), W.size(p), pw.spawns_size(m, W.take(p)), pw.take_size(p))

def pw.cached(+k: Nat, cache: List<&2, Nat>, hit: {W.member(k, cache) == True{} : Bool}) -> {W.cost(k, cache) == 0n : Nat}:
  %Equal.sym(Bool, W.member(k, cache), True{}, hit) : {W.cost.go(_) == 0n : Nat}
  {==}

def pw.empty(keys: List<&2, Nat>) -> {W.resumed([], keys) == List.length(&2, Nat, keys) : Nat}:
  match keys:
    case Nil{}:
      {==}
    case k <> +rest:
      %pw.empty(rest) : {1n+W.resumed([], rest) == 1n+_ : Nat}
      {==}

def pw.spares(xs: List<&2, W.Out>, +ys: List<&2, W.Out>) -> {W.results(W.cat(xs, W.Failed{} <> ys)) == W.rcat(W.results(xs), None{} <> W.results(ys)) : List<&2, Maybe<&2, Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %pw.spares(rest, ys) : {W.result(x) <> W.results(W.cat(rest, W.Failed{} <> ys)) == W.result(x) <> _ : List<&2, Maybe<&2, Nat>>}
      {==}
