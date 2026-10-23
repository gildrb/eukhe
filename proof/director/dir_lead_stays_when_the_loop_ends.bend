# eukhe: the proof of LAW dir_lead_stays_when_the_loop_ends

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ../base.bend as L
import ./base.bend as LA

# a Lead that stays is a Defer, whatever the decision does with leads
def pd.defer_as(s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +r: Bool, +x: Bool) -> {Dr.decide.go(s, vs, r, True{}) == Dr.decide.go(s, Director.dir_leads(vs, Dr.Defer{}), r, x) : Dr.Dec}:
  match s:
    case Nil{}:
      {==}
    case +l <> +rest:
      match vs:
        case Nil{}:
          Equal.cong(Dr.Dec, Dr.Dec, d => Dr.under(l, d), Dr.decide.go(rest, Nil{}, r, True{}), Dr.decide.go(rest, Nil{}, r, x), pd.defer_as(rest, Nil{}, r, x))
        case v <> +vr:
          match v:
            case Dr.Defer{}:
              Equal.cong(Dr.Dec, Dr.Dec, d => Dr.under(l, d), Dr.decide.go(rest, vr, r, True{}), Dr.decide.go(rest, Director.dir_leads(vr, Dr.Defer{}), r, x), pd.defer_as(rest, vr, r, x))
            case Dr.Again{}:
              {==}
            case Dr.Yield{}:
              {==}
            case Dr.Stack{n}:
              {==}
            case Dr.Leave{}:
              pd.defer_as(rest, vr, r, x)
            case Dr.Abort{}:
              {==}
            case Dr.Lead{}:
              Equal.cong(Dr.Dec, Dr.Dec, d => Dr.under(l, d), Dr.decide.go(rest, vr, r, True{}), Dr.decide.go(rest, Director.dir_leads(vr, Dr.Defer{}), r, x), pd.defer_as(rest, vr, r, x))

def pd.out_under(+l: Dr.Layer, d: Dr.Dec) -> {Dr.Dec.out(Dr.under(l, d)) == Dr.Dec.out(d) : Dr.Out}:
  match d:
    case Dr.Dec{o, s}:
      {==}

def pd.out_under2(+l: Dr.Layer, +a: Dr.Dec, +b: Dr.Dec, ih: {Dr.Dec.out(a) == Dr.Dec.out(b) : Dr.Out}) -> {Dr.Dec.out(Dr.under(l, a)) == Dr.Dec.out(Dr.under(l, b)) : Dr.Out}:
  Equal.trans(Dr.Out, Dr.Dec.out(Dr.under(l, a)), Dr.Dec.out(a), Dr.Dec.out(Dr.under(l, b)), pd.out_under(l, a), Equal.trans(Dr.Out, Dr.Dec.out(a), Dr.Dec.out(b), Dr.Dec.out(Dr.under(l, b)), ih, Equal.sym(Dr.Out, Dr.Dec.out(Dr.under(l, b)), Dr.Dec.out(b), pd.out_under(l, b))))

# whether a layer that leads stays or leaves, the outcome is the same
def pd.out_stay(s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +r: Bool) -> {Dr.Dec.out(Dr.decide.go(s, vs, r, True{})) == Dr.Dec.out(Dr.decide.go(s, vs, r, False{})) : Dr.Out}:
  match s:
    case Nil{}:
      {==}
    case +l <> +rest:
      match vs:
        case Nil{}:
          pd.out_under2(l, Dr.decide.go(rest, Nil{}, r, True{}), Dr.decide.go(rest, Nil{}, r, False{}), pd.out_stay(rest, Nil{}, r))
        case v <> +vr:
          match v:
            case Dr.Defer{}:
              pd.out_under2(l, Dr.decide.go(rest, vr, r, True{}), Dr.decide.go(rest, vr, r, False{}), pd.out_stay(rest, vr, r))
            case Dr.Again{}:
              {==}
            case Dr.Yield{}:
              {==}
            case Dr.Stack{n}:
              {==}
            case Dr.Leave{}:
              pd.out_stay(rest, vr, r)
            case Dr.Abort{}:
              {==}
            case Dr.Lead{}:
              Equal.trans(Dr.Out, Dr.Dec.out(Dr.under(l, Dr.decide.go(rest, vr, r, True{}))), Dr.Dec.out(Dr.decide.go(rest, vr, r, True{})), Dr.Dec.out(Dr.decide.go(rest, vr, r, False{})), pd.out_under(l, Dr.decide.go(rest, vr, r, True{})), pd.out_stay(rest, vr, r))

# a continue that ends reads only the kept stack
def pd.goon_end(n: Nat, +t1: List<&2, Dr.Layer>, +t2: List<&2, Dr.Layer>, +s: List<&2, Dr.Layer>, +vs1: List<&2, Dr.Verdict>, +vs2: List<&2, Dr.Verdict>, +vs3: List<&2, Dr.Verdict>, +cap: Nat, ek: {Dr.kept(s, vs1, cap) == Dr.kept(s, vs2, cap) : List<&2, Dr.Layer>}, ends: {Dr.ended(Dr.go.on(n, t1, s, vs3, cap)) == True{} : Bool}) -> {Dr.go.on(n, t1, s, vs1, cap) == Dr.go.on(n, t2, s, vs2, cap) : Dr.Loop}:
  match n:
    case 0n:
      Equal.cong(List<&2, Dr.Layer>, Dr.Loop, k => Dr.Loop{0n, k, Some{Dr.Hand{}}}, Dr.kept(s, vs1, cap), Dr.kept(s, vs2, cap), ek)
    case 1n+m:
      L.tree.pt.absurdF({Dr.go.on(1n+m, t1, s, vs1, cap) == Dr.go.on(1n+m, t2, s, vs2, cap) : Dr.Loop}, ends)

# a settle that ends reads only the outcome and the kept stack
def pd.settle_end1(o1: Dr.Out, +t1: List<&2, Dr.Layer>, d2: Dr.Dec, +n: Nat, +s: List<&2, Dr.Layer>, +vs1: List<&2, Dr.Verdict>, +vs2: List<&2, Dr.Verdict>, +vs3: List<&2, Dr.Verdict>, +cap: Nat, eo: {Dr.Dec.out(Dr.Dec{o1, t1}) == Dr.Dec.out(d2) : Dr.Out}, +ek: {Dr.kept(s, vs1, cap) == Dr.kept(s, vs2, cap) : List<&2, Dr.Layer>}, ends: {Dr.ended(Dr.settle(Dr.Dec{o1, t1}, n, s, vs3, cap)) == True{} : Bool}) -> {Dr.settle(Dr.Dec{o1, t1}, n, s, vs1, cap) == Dr.settle(d2, n, s, vs2, cap) : Dr.Loop}:
  match o1:
    case Dr.Cont{}:
      match d2:
        case Dr.Dec{o2, +t2}:
          match o2:
            case Dr.Cont{}:
              pd.goon_end(n, t1, t2, s, vs1, vs2, vs3, cap, ek, ends)
            case Dr.Hand{}:
              LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Cont{}, t1}, n, s, vs1, cap) == Dr.settle(Dr.Dec{Dr.Hand{}, t2}, n, s, vs2, cap) : Dr.Loop}, Dr.Cont{}, Dr.Hand{}, eo, {==})
            case Dr.Failed{}:
              LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Cont{}, t1}, n, s, vs1, cap) == Dr.settle(Dr.Dec{Dr.Failed{}, t2}, n, s, vs2, cap) : Dr.Loop}, Dr.Cont{}, Dr.Failed{}, eo, {==})
    case Dr.Hand{}:
      match d2:
        case Dr.Dec{o2, +t2}:
          match o2:
            case Dr.Cont{}:
              LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Hand{}, t1}, n, s, vs1, cap) == Dr.settle(Dr.Dec{Dr.Cont{}, t2}, n, s, vs2, cap) : Dr.Loop}, Dr.Hand{}, Dr.Cont{}, eo, {==})
            case Dr.Hand{}:
              Equal.cong(List<&2, Dr.Layer>, Dr.Loop, k => Dr.Loop{n, k, Some{Dr.Hand{}}}, Dr.kept(s, vs1, cap), Dr.kept(s, vs2, cap), ek)
            case Dr.Failed{}:
              LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Hand{}, t1}, n, s, vs1, cap) == Dr.settle(Dr.Dec{Dr.Failed{}, t2}, n, s, vs2, cap) : Dr.Loop}, Dr.Hand{}, Dr.Failed{}, eo, {==})
    case Dr.Failed{}:
      match d2:
        case Dr.Dec{o2, +t2}:
          match o2:
            case Dr.Cont{}:
              LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Failed{}, t1}, n, s, vs1, cap) == Dr.settle(Dr.Dec{Dr.Cont{}, t2}, n, s, vs2, cap) : Dr.Loop}, Dr.Failed{}, Dr.Cont{}, eo, {==})
            case Dr.Hand{}:
              LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Failed{}, t1}, n, s, vs1, cap) == Dr.settle(Dr.Dec{Dr.Hand{}, t2}, n, s, vs2, cap) : Dr.Loop}, Dr.Failed{}, Dr.Hand{}, eo, {==})
            case Dr.Failed{}:
              Equal.cong(List<&2, Dr.Layer>, Dr.Loop, k => Dr.Loop{n, k, Some{Dr.Failed{}}}, Dr.kept(s, vs1, cap), Dr.kept(s, vs2, cap), ek)

def pd.settle_end(d1: Dr.Dec, d2: Dr.Dec, +n: Nat, +s: List<&2, Dr.Layer>, +vs1: List<&2, Dr.Verdict>, +vs2: List<&2, Dr.Verdict>, +vs3: List<&2, Dr.Verdict>, +cap: Nat, eo: {Dr.Dec.out(d1) == Dr.Dec.out(d2) : Dr.Out}, +ek: {Dr.kept(s, vs1, cap) == Dr.kept(s, vs2, cap) : List<&2, Dr.Layer>}, ends: {Dr.ended(Dr.settle(d1, n, s, vs3, cap)) == True{} : Bool}) -> {Dr.settle(d1, n, s, vs1, cap) == Dr.settle(d2, n, s, vs2, cap) : Dr.Loop}:
  match d1:
    case Dr.Dec{o1, +t1}:
      pd.settle_end1(o1, t1, d2, n, s, vs1, vs2, vs3, cap, eo, ek, ends)

# an ended settle stays ended for an equal decision
def pd.ends_eq(-d1: Dr.Dec, -d2: Dr.Dec, e: {d1 == d2 : Dr.Dec}, +n: Nat, +s: List<&2, Dr.Layer>, +vs: List<&2, Dr.Verdict>, +cap: Nat, h: {Dr.ended(Dr.settle(d2, n, s, vs, cap)) == True{} : Bool}) -> {Dr.ended(Dr.settle(d1, n, s, vs, cap)) == True{} : Bool}:
  %Equal.sym(Dr.Dec, d1, d2, e) : {Dr.ended(Dr.settle(_, n, s, vs, cap)) == True{} : Bool}
  h

def Director.dir_lead_stays_when_the_loop_ends(cap, l, vs, L.ends):
  match l:
    case Dr.Loop{+n, +s, e}:
      match e:
        case None{}:
          +L = Director.dir_leads(vs, Dr.Leave{})
          +Df = Director.dir_leads(vs, Dr.Defer{})
          +r = Nat.is_lt(List.length(&2, Dr.Layer, s), cap)
          +D = Dr.decide.go(s, vs, r, False{})
          +E = Dr.decide.go(s, vs, r, True{})
          +eo = Equal.trans(Dr.Out, Dr.Dec.out(D), Dr.Dec.out(E), Dr.Dec.out(Dr.decide.go(s, Df, r, False{})), Equal.sym(Dr.Out, Dr.Dec.out(E), Dr.Dec.out(D), pd.out_stay(s, vs, r)), Equal.cong(Dr.Dec, Dr.Out, d => Dr.Dec.out(d), E, Dr.decide.go(s, Df, r, False{}), pd.defer_as(s, vs, r, False{})))
          +ek = Equal.cong(Dr.Dec, List<&2, Dr.Layer>, d => Dr.Dec.stack(d), E, Dr.decide.go(s, Df, r, True{}), pd.defer_as(s, vs, r, True{}))
          +ends2 = pd.ends_eq(D, Dr.decide.go(s, L, r, False{}), LA.pd.leave_as(s, vs, r, False{}), n, s, L, cap, L.ends)
          pd.settle_end(Dr.decide(s, vs, cap), Dr.decide(s, Df, cap), n, s, vs, Df, L, cap, eo, ek, ends2)
        case Some{x}:
          {==}
