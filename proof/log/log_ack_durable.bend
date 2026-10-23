# eukhe: the proof of LAW log_ack_durable

import Base
import ../../bend/log.bend as Lg
import ../../LAWS.bend as Laws
import ./base.bend as LA

# The acknowledged commits are kept
# ---------------------------------

def pl.ml2(cs: List<&2, List<&2, Nat>>, +p: Nat, +k: Nat, +de: Bool, +fe: Bool, +l0: List<&2, List<&2, Nat>>, +l: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>, h: {l == List.append(&2, List<&2, Nat>, l0, a) : List<&2, List<&2, Nat>>}) -> &r: List<&2, List<&2, Nat>> -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l0, Lg.St.acked(Lg.more(cs, p, Lg.St{de, fe, l, None{}, a}))), r) == LA.pl.fin(k, Lg.more(cs, p, Lg.St{de, fe, l, None{}, a})) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      +la = List.append(&2, List<&2, Nat>, l0, a)
      (Nil{}, (%LA.pl.recover_render(l, Nil{}) : {List.append(&2, List<&2, Nat>, la, Nil{}) == _ : List<&2, List<&2, Nat>>}; %h : {List.append(&2, List<&2, Nat>, _, Nil{}) == List.append(&2, List<&2, Nat>, l, Nil{}) : List<&2, List<&2, Nat>>}; {==}))
    case +c <> +rest:
      match p:
        case 0n:
          +la = List.append(&2, List<&2, Nat>, l0, a)
          (Nil{}, (%LA.pl.recover_render(l, Nil{}) : {List.append(&2, List<&2, Nat>, la, Nil{}) == _ : List<&2, List<&2, Nat>>}; %h : {List.append(&2, List<&2, Nat>, _, Nil{}) == List.append(&2, List<&2, Nat>, l, Nil{}) : List<&2, List<&2, Nat>>}; {==}))
        case 1n+p1:
          match p1:
            case 0n:
              +la = List.append(&2, List<&2, Nat>, l0, a)
              (LA.log.pl.keep(k, c), (%LA.pl.recover_render(l, List.take(&2, Nat, Lg.line(c), k)) : {List.append(&2, List<&2, Nat>, la, LA.log.pl.keep(k, c)) == _ : List<&2, List<&2, Nat>>}; %LA.pl.torn(k, c) : {List.append(&2, List<&2, Nat>, la, LA.log.pl.keep(k, c)) == List.append(&2, List<&2, Nat>, l, _) : List<&2, List<&2, Nat>>}; %h : {List.append(&2, List<&2, Nat>, _, LA.log.pl.keep(k, c)) == List.append(&2, List<&2, Nat>, l, LA.log.pl.keep(k, c)) : List<&2, List<&2, Nat>>}; {==}))
            case 1n+p2:
              +la = List.append(&2, List<&2, Nat>, l0, a)
              +a2 = List.append(&2, List<&2, Nat>, a, [c])
              pl.ml2(rest, p2, k, de, fe, l0, List.append(&2, List<&2, Nat>, l, [c]), a2, (%Equal.sym(List<&2, List<&2, Nat>>, l, la, h) : {List.append(&2, List<&2, Nat>, _, [c]) == List.append(&2, List<&2, Nat>, l0, a2) : List<&2, List<&2, Nat>>}; Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, l0, a2), List.append(&2, List<&2, Nat>, la, [c]), LA.pl.assoc(List<&2, Nat>, l0, a, [c]))))

def pl.fa(cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat, +fe: Bool, +l: List<&2, List<&2, Nat>>) -> &r: List<&2, List<&2, Nat>> -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, Lg.St.acked(Lg.first(cs, q, Lg.St{True{}, fe, l, None{}, Nil{}}))), r) == LA.pl.fin(k, Lg.first(cs, q, Lg.St{True{}, fe, l, None{}, Nil{}})) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      pl.ml2(Nil{}, 0n, k, True{}, fe, l, l, Nil{}, LA.pl.app_nil(List<&2, Nat>, l))
    case +c <> +rest:
      match q:
        case 0n:
          pl.ml2(Nil{}, 0n, k, True{}, fe, l, l, Nil{}, LA.pl.app_nil(List<&2, Nat>, l))
        case 1n+q1:
          match q1:
            case 0n:
              pl.ml2([c], 1n, k, True{}, fe, l, l, Nil{}, LA.pl.app_nil(List<&2, Nat>, l))
            case 1n+q2:
              match q2:
                case 0n:
                  +l2 = List.append(&2, List<&2, Nat>, l, [c])
                  ([c], (%LA.pl.app_nil(List<&2, Nat>, l) : {List.append(&2, List<&2, Nat>, _, [c]) == Lg.recover(List.append(&2, Nat, Lg.render(l2), Nil{})) : List<&2, List<&2, Nat>>}; LA.pl.rl(l2)))
                case 1n+q3:
                  +l2 = List.append(&2, List<&2, Nat>, l, [c])
                  pl.ml2(rest, q3, k, True{}, True{}, l, l2, [c], {==})

def pl.ad_lift(-l0: List<&2, List<&2, Nat>>, -a: List<&2, List<&2, Nat>>, -f: List<&2, List<&2, Nat>>, -d: List<&2, List<&2, Nat>>, r: &x: List<&2, List<&2, Nat>> -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l0, a), x) == f : List<&2, List<&2, Nat>>}, s: {f == d : List<&2, List<&2, Nat>>}) -> &x: List<&2, List<&2, Nat>> -> {d == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l0, a), x) : List<&2, List<&2, Nat>>}:
  match r:
    case (+x, e):
      (x, Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l0, a), x), d, Equal.trans(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l0, a), x), f, d, e, s)))

def pl.ack_drop(cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat) -> &r: List<&2, List<&2, Nat>> -> {Lg.Disk.log(Lg.crash(k, True{}, Lg.first(cs, q, Lg.St{True{}, False{}, Nil{}, None{}, Nil{}}))) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, Nil{}, Lg.St.acked(Lg.first(cs, q, Lg.St{True{}, False{}, Nil{}, None{}, Nil{}}))), r) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      (Nil{}, {==})
    case +c <> +rest:
      match q:
        case 0n:
          (Nil{}, {==})
        case 1n+q1:
          match q1:
            case 0n:
              (Nil{}, {==})
            case 1n+q2:
              match q2:
                case 0n:
                  (Nil{}, {==})
                case 1n+q3:
                  +m = Lg.more(rest, q3, Lg.St{True{}, True{}, [c], None{}, [c]})
                  pl.ad_lift(Nil{}, Lg.St.acked(m), LA.pl.fin(k, m), Lg.Disk.log(Lg.crash(k, True{}, m)), pl.ml2(rest, q3, k, True{}, True{}, Nil{}, [c], [c], {==}), LA.pl.surv(k, True{}, m, LA.pl.mt(True{}, rest, q3, [c], [c])))

# the law log_ack_durable
def pl.ack(d: Lg.Disk, e: Lg.Epoch) -> &x: List<&2, List<&2, Nat>> -> {Lg.Disk.log(Lg.after(d, e)) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Lg.acked(d, e)), x) : List<&2, List<&2, Nat>>}:
  match d:
    case Lg.Absent{}:
      match e:
        case Lg.Epoch{+cs, +p, +k, drop}:
          match p:
            case 0n:
              match drop:
                case True{}:
                  (Nil{}, {==})
                case False{}:
                  (Nil{}, {==})
            case 1n+q:
              match drop:
                case True{}:
                  pl.ack_drop(cs, q, k)
                case False{}:
                  +m = Lg.first(cs, q, Lg.St{True{}, False{}, Nil{}, None{}, Nil{}})
                  pl.ad_lift(Nil{}, Lg.St.acked(m), LA.pl.fin(k, m), Lg.Disk.log(Lg.crash(k, False{}, m)), pl.fa(cs, q, k, False{}, Nil{}), LA.pl.surv(k, False{}, m, {==}))
    case Lg.Present{+b}:
      match e:
        case Lg.Epoch{+cs, +p, +k, +drop}:
          match p:
            case 0n:
              +r = Lg.recover(b)
              +s = {Lg.St{True{}, True{}, r, None{}, Nil{}} : Lg.St}
              pl.ad_lift(r, Nil{}, LA.pl.fin(k, s), Lg.Disk.log(Lg.crash(k, drop, s)), pl.ml2(Nil{}, 0n, k, True{}, True{}, r, r, Nil{}, LA.pl.app_nil(List<&2, Nat>, r)), LA.pl.surv(k, drop, s, LA.pl.kt(drop)))
            case 1n+q:
              +r = Lg.recover(b)
              +m = Lg.first(cs, q, Lg.St{True{}, True{}, r, None{}, Nil{}})
              pl.ad_lift(r, Lg.St.acked(m), LA.pl.fin(k, m), Lg.Disk.log(Lg.crash(k, drop, m)), pl.fa(cs, q, k, True{}, r), LA.pl.surv(k, drop, m, LA.pl.ft(drop, cs, q, r)))

def Laws.log_ack_durable(d, e):
  pl.ack(d, e)
