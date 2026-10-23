# eukhe: the proof of LAW log_only_commits

import Base
import ../../bend/log.bend as Lg
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pl.take0(-A: Data, xs: List<&2, A>) -> {Nil{} == List.take(&2, A, xs, 0n) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

# the head x before a cut of the commits
def pl.head_take(x: Nat, c: List<&2, Nat>, rest: List<&2, List<&2, Nat>>, n: Nat) -> {LA.pl.head(x, List.take(&2, List<&2, Nat>, c <> rest, n)) == List.take(&2, List<&2, Nat>, (x <> c) <> rest, n) : List<&2, List<&2, Nat>>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def pl.head_pair(+x: Nat, +cs: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, -K: List<&2, List<&2, Nat>>, r: &n: Nat -> {K == List.take(&2, List<&2, Nat>, cs <> rest, n) : List<&2, List<&2, Nat>>}) -> &n: Nat -> {LA.pl.head(x, K) == List.take(&2, List<&2, Nat>, (x <> cs) <> rest, n) : List<&2, List<&2, Nat>>}:
  match r:
    case (+m, e):
      (m, (%Equal.sym(List<&2, List<&2, Nat>>, K, List.take(&2, List<&2, Nat>, cs <> rest, m), e) : {LA.pl.head(x, _) == List.take(&2, List<&2, Nat>, (x <> cs) <> rest, m) : List<&2, List<&2, Nat>>}; pl.head_take(x, cs, rest, m)))

# a torn line is a prefix of the commits from it
def pl.keep_take(k: Nat, c: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>) -> &n: Nat -> {LA.log.pl.keep(k, c) == List.take(&2, List<&2, Nat>, c <> rest, n) : List<&2, List<&2, Nat>>}:
  match k:
    case 0n:
      (0n, {==})
    case 1n+j:
      match c:
        case Nil{}:
          (1n, (%pl.take0(List<&2, Nat>, rest) : {[Nil{}] == Nil{} <> _ : List<&2, List<&2, Nat>>}; {==}))
        case +x <> +cs:
          pl.head_pair(x, cs, rest, LA.log.pl.keep(j, cs), pl.keep_take(j, cs, rest))

# Only a prefix of the commits
# ---------------------------

def pl.ml1_torn(+l: List<&2, List<&2, Nat>>, +c: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +k: Nat, r: &n: Nat -> {LA.log.pl.keep(k, c) == List.take(&2, List<&2, Nat>, c <> rest, n) : List<&2, List<&2, Nat>>}) -> &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, c <> rest, n)) == Lg.recover(List.append(&2, Nat, Lg.render(l), List.take(&2, Nat, Lg.line(c), k))) : List<&2, List<&2, Nat>>}:
  match r:
    case (+n, e):
      (n, (%LA.pl.recover_render(l, List.take(&2, Nat, Lg.line(c), k)) : {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, c <> rest, n)) == _ : List<&2, List<&2, Nat>>}; %LA.pl.torn(k, c) : {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, c <> rest, n)) == List.append(&2, List<&2, Nat>, l, _) : List<&2, List<&2, Nat>>}; %e : {List.append(&2, List<&2, Nat>, l, _) == List.append(&2, List<&2, Nat>, l, LA.log.pl.keep(k, c)) : List<&2, List<&2, Nat>>}; {==}))

def pl.ml1_step(+l: List<&2, List<&2, Nat>>, +c: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, -f: List<&2, List<&2, Nat>>, r: &n: Nat -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, [c]), List.take(&2, List<&2, Nat>, rest, n)) == f : List<&2, List<&2, Nat>>}) -> &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, c <> rest, n)) == f : List<&2, List<&2, Nat>>}:
  match r:
    case (+n, e):
      (1n+n, Equal.trans(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, l, c <> List.take(&2, List<&2, Nat>, rest, n)), List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, [c]), List.take(&2, List<&2, Nat>, rest, n)), f, LA.pl.assoc(List<&2, Nat>, l, [c], List.take(&2, List<&2, Nat>, rest, n)), e))

def pl.ml1(cs: List<&2, List<&2, Nat>>, +p: Nat, +k: Nat, +de: Bool, +fe: Bool, +l: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>) -> &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, cs, n)) == LA.pl.fin(k, Lg.more(cs, p, Lg.St{de, fe, l, None{}, a})) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      (0n, LA.pl.recover_render(l, Nil{}))
    case +c <> +rest:
      match p:
        case 0n:
          (0n, LA.pl.recover_render(l, Nil{}))
        case 1n+p1:
          match p1:
            case 0n:
              pl.ml1_torn(l, c, rest, k, pl.keep_take(k, c, rest))
            case 1n+p2:
              +l2 = List.append(&2, List<&2, Nat>, l, [c])
              +a2 = List.append(&2, List<&2, Nat>, a, [c])
              pl.ml1_step(l, c, rest, LA.pl.fin(k, Lg.more(rest, p2, Lg.St{de, fe, l2, None{}, a2})), pl.ml1(rest, p2, k, de, fe, l2, a2))

def pl.f1(cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat, +fe: Bool, +l: List<&2, List<&2, Nat>>) -> &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, cs, n)) == LA.pl.fin(k, Lg.first(cs, q, Lg.St{True{}, fe, l, None{}, Nil{}})) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      (0n, LA.pl.recover_render(l, Nil{}))
    case +c <> +rest:
      match q:
        case 0n:
          (0n, LA.pl.recover_render(l, Nil{}))
        case 1n+q1:
          match q1:
            case 0n:
              pl.ml1_torn(l, c, rest, k, pl.keep_take(k, c, rest))
            case 1n+q2:
              match q2:
                case 0n:
                  +l2 = List.append(&2, List<&2, Nat>, l, [c])
                  (1n, (%pl.take0(List<&2, Nat>, rest) : {List.append(&2, List<&2, Nat>, l, c <> _) == Lg.recover(List.append(&2, Nat, Lg.render(l2), Nil{})) : List<&2, List<&2, Nat>>}; LA.pl.rl(l2)))
                case 1n+q3:
                  +l2 = List.append(&2, List<&2, Nat>, l, [c])
                  pl.ml1_step(l, c, rest, LA.pl.fin(k, Lg.more(rest, q3, Lg.St{True{}, True{}, l2, None{}, [c]})), pl.ml1(rest, q3, k, True{}, True{}, l2, [c]))

# The laws
# --------

def pl.oc_lift(-l0: List<&2, List<&2, Nat>>, -cs: List<&2, List<&2, Nat>>, -f: List<&2, List<&2, Nat>>, -d: List<&2, List<&2, Nat>>, r: &n: Nat -> {List.append(&2, List<&2, Nat>, l0, List.take(&2, List<&2, Nat>, cs, n)) == f : List<&2, List<&2, Nat>>}, s: {f == d : List<&2, List<&2, Nat>>}) -> &n: Nat -> {d == List.append(&2, List<&2, Nat>, l0, List.take(&2, List<&2, Nat>, cs, n)) : List<&2, List<&2, Nat>>}:
  match r:
    case (+n, e):
      (n, Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, l0, List.take(&2, List<&2, Nat>, cs, n)), d, Equal.trans(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, l0, List.take(&2, List<&2, Nat>, cs, n)), f, d, e, s)))

# an absent file, a crash that drops the entries
def pl.only_drop(cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat) -> &n: Nat -> {Lg.Disk.log(Lg.crash(k, True{}, Lg.first(cs, q, Lg.St{True{}, False{}, Nil{}, None{}, Nil{}}))) == List.take(&2, List<&2, Nat>, cs, n) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      (0n, {==})
    case +c <> +rest:
      match q:
        case 0n:
          (0n, {==})
        case 1n+q1:
          match q1:
            case 0n:
              (0n, {==})
            case 1n+q2:
              match q2:
                case 0n:
                  (0n, {==})
                case 1n+q3:
                  +m = Lg.more(rest, q3, Lg.St{True{}, True{}, [c], None{}, [c]})
                  pl.oc_lift(Nil{}, c <> rest, LA.pl.fin(k, m), Lg.Disk.log(Lg.crash(k, True{}, m)), pl.ml1_step(Nil{}, c, rest, LA.pl.fin(k, m), pl.ml1(rest, q3, k, True{}, True{}, [c], [c])), LA.pl.surv(k, True{}, m, LA.pl.mt(True{}, rest, q3, [c], [c])))

# the law log_only_commits
def pl.only(d: Lg.Disk, e: Lg.Epoch) -> &n: Nat -> {Lg.Disk.log(Lg.after(d, e)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), List.take(&2, List<&2, Nat>, Lg.Epoch.cs(e), n)) : List<&2, List<&2, Nat>>}:
  match d:
    case Lg.Absent{}:
      match e:
        case Lg.Epoch{+cs, +p, +k, drop}:
          match p:
            case 0n:
              match drop:
                case True{}:
                  (0n, pl.take0(List<&2, Nat>, cs))
                case False{}:
                  (0n, pl.take0(List<&2, Nat>, cs))
            case 1n+q:
              match drop:
                case True{}:
                  pl.only_drop(cs, q, k)
                case False{}:
                  +m = Lg.first(cs, q, Lg.St{True{}, False{}, Nil{}, None{}, Nil{}})
                  pl.oc_lift(Nil{}, cs, LA.pl.fin(k, m), Lg.Disk.log(Lg.crash(k, False{}, m)), pl.f1(cs, q, k, False{}, Nil{}), LA.pl.surv(k, False{}, m, {==}))
    case Lg.Present{+b}:
      match e:
        case Lg.Epoch{+cs, +p, +k, +drop}:
          match p:
            case 0n:
              +r = Lg.recover(b)
              +s = {Lg.St{True{}, True{}, r, None{}, Nil{}} : Lg.St}
              pl.oc_lift(r, cs, LA.pl.fin(k, s), Lg.Disk.log(Lg.crash(k, drop, s)), (0n, (%pl.take0(List<&2, Nat>, cs) : {List.append(&2, List<&2, Nat>, r, _) == LA.pl.fin(k, s) : List<&2, List<&2, Nat>>}; LA.pl.recover_render(r, Nil{}))), LA.pl.surv(k, drop, s, LA.pl.kt(drop)))
            case 1n+q:
              +r = Lg.recover(b)
              +m = Lg.first(cs, q, Lg.St{True{}, True{}, r, None{}, Nil{}})
              pl.oc_lift(r, cs, LA.pl.fin(k, m), Lg.Disk.log(Lg.crash(k, drop, m)), pl.f1(cs, q, k, True{}, r), LA.pl.surv(k, drop, m, LA.pl.ft(drop, cs, q, r)))

def Laws.log_only_commits(d, e):
  pl.only(d, e)
