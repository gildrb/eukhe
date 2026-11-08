# eukhe: the proof of LAW dir_step_no_verdict_defers

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

# one more Defer after the verdicts changes no decision
def pn.pad(s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +r: Bool, +st: Bool) -> {Dr.decide.go(s, List.append(&2, Dr.Verdict, vs, [Dr.Defer{}]), r, st) == Dr.decide.go(s, vs, r, st) : Dr.Dec}:
  match s:
    case Nil{}:
      {==}
    case +l <> +rest:
      match vs:
        case Nil{}:
          {==}
        case v <> +vr:
          match v:
            case Dr.Defer{}:
              Equal.cong(Dr.Dec, Dr.Dec, d => Dr.under(l, d), Dr.decide.go(rest, List.append(&2, Dr.Verdict, vr, [Dr.Defer{}]), r, st), Dr.decide.go(rest, vr, r, st), pn.pad(rest, vr, r, st))
            case Dr.Again{}:
              {==}
            case Dr.Yield{}:
              {==}
            case Dr.Stack{p}:
              {==}
            case Dr.Leave{}:
              pn.pad(rest, vr, r, st)
            case Dr.Abort{}:
              {==}
            case Dr.Lead{}:
              Equal.cong(Dr.Dec, Dr.Dec, d => Dr.lead(st, l, d), Dr.decide.go(rest, List.append(&2, Dr.Verdict, vr, [Dr.Defer{}]), r, st), Dr.decide.go(rest, vr, r, st), pn.pad(rest, vr, r, st))

# a continue reads its verdicts only through the kept stack
def pn.on_same(n: Nat, +t: List<&2, Dr.Layer>, +s: List<&2, Dr.Layer>, +vs1: List<&2, Dr.Verdict>, +vs2: List<&2, Dr.Verdict>, +cap: Nat, ek: {Dr.kept(s, vs1, cap) == Dr.kept(s, vs2, cap) : List<&2, Dr.Layer>}) -> {Dr.go.on(n, t, s, vs1, cap) == Dr.go.on(n, t, s, vs2, cap) : Dr.Loop}:
  match n:
    case 0n:
      Equal.cong(List<&2, Dr.Layer>, Dr.Loop, k => Dr.Loop{0n, k, Some{Dr.Hand{}}}, Dr.kept(s, vs1, cap), Dr.kept(s, vs2, cap), ek)
    case 1n+m:
      {==}

# a settle reads its verdicts only through the kept stack
def pn.settle_same(d: Dr.Dec, +n: Nat, +s: List<&2, Dr.Layer>, +vs1: List<&2, Dr.Verdict>, +vs2: List<&2, Dr.Verdict>, +cap: Nat, ek: {Dr.kept(s, vs1, cap) == Dr.kept(s, vs2, cap) : List<&2, Dr.Layer>}) -> {Dr.settle(d, n, s, vs1, cap) == Dr.settle(d, n, s, vs2, cap) : Dr.Loop}:
  match d:
    case Dr.Dec{o, +t}:
      match o:
        case Dr.Cont{}:
          pn.on_same(n, t, s, vs1, vs2, cap, ek)
        case Dr.Hand{}:
          Equal.cong(List<&2, Dr.Layer>, Dr.Loop, k => Dr.Loop{n, k, Some{Dr.Hand{}}}, Dr.kept(s, vs1, cap), Dr.kept(s, vs2, cap), ek)
        case Dr.Failed{}:
          Equal.cong(List<&2, Dr.Layer>, Dr.Loop, k => Dr.Loop{n, k, Some{Dr.Failed{}}}, Dr.kept(s, vs1, cap), Dr.kept(s, vs2, cap), ek)

def pn.go(l: Dr.Loop, +cap: Nat, +vs: List<&2, Dr.Verdict>) -> {Dr.tick(cap, l, vs) == Dr.tick(cap, l, List.append(&2, Dr.Verdict, vs, [Dr.Defer{}])) : Dr.Loop}:
  match l:
    case Dr.Loop{+n, +s, e}:
      match e:
        case None{}:
          +vs2 = List.append(&2, Dr.Verdict, vs, [Dr.Defer{}])
          +R = Nat.is_lt(List.length(&2, Dr.Layer, s), cap)
          +D2 = Dr.decide.go(s, vs2, R, False{})
          +ek = Equal.sym(List<&2, Dr.Layer>, Dr.kept(s, vs2, cap), Dr.kept(s, vs, cap), Equal.cong(Dr.Dec, List<&2, Dr.Layer>, x => Dr.Dec.stack(x), Dr.decide.go(s, vs2, R, True{}), Dr.decide.go(s, vs, R, True{}), pn.pad(s, vs, R, True{})))
          +e1 = Equal.cong(Dr.Dec, Dr.Loop, x => Dr.settle(x, n, s, vs, cap), Dr.decide.go(s, vs, R, False{}), D2, Equal.sym(Dr.Dec, D2, Dr.decide.go(s, vs, R, False{}), pn.pad(s, vs, R, False{})))
          Equal.trans(Dr.Loop, Dr.settle(Dr.decide.go(s, vs, R, False{}), n, s, vs, cap), Dr.settle(D2, n, s, vs, cap), Dr.settle(D2, n, s, vs2, cap), e1, pn.settle_same(D2, n, s, vs, vs2, cap, ek))
        case Some{x}:
          {==}

def Director.dir_step_no_verdict_defers(cap, l, vs):
  pn.go(l, cap, vs)
