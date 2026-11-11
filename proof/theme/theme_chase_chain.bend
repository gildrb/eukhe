# eukhe: the proof of LAW theme_chase_chain
# The chase is the walk over the variable list (CT.pt.chase_walk). Along
# the chain p the walk takes one step per variable of p: each value names
# the next variable, met for the first time (p repeats none), so the walk
# goes on to its value (cc.next); at the end the walk stops where the
# laws' th.last decides, with that decision (cc.last). There is fuel for
# the whole chain: p is no longer than the variables.

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../laws/theme.bend as Theme
import ./base.bend as LA
import ./theme_chase_chain/trees.bend as CT

def cc.ungot(m: Maybe<&2, TChase.Got>) -> TChase.Got:
  match m:
    case None{}:
      TChase.Hit{TFile.Dflt{}}
    case Some{x}:
      x

def cc.unjson(m: Maybe<&2, TFile.Json>) -> TFile.Json:
  match m:
    case None{}:
      TFile.JOther{""}
    case Some{x}:
      x

def cc.stop(-x: TChase.Got, -g: TChase.Got, h: {Some{x} == Some{g} : Maybe<&2, TChase.Got>}) -> {TChase.Stop{x} == TChase.Stop{g} : TChase.Step}:
  Equal.cong(Maybe<&2, TChase.Got>, TChase.Step, m => TChase.Stop{cc.ungot(m)}, Some{x}, Some{g}, h)

# The end of the chain
# --------------------
# Where th.last decides, the walk's step stops with that decision.

def cc.at(looped: Bool, m: Maybe<&2, TFile.Json>, +seen: List<&2, Nat>, +s: String, +i: Nat, -g: TChase.Got, h: {Theme.th.last.at(looped, m, s) == Some{g} : Maybe<&2, TChase.Got>}) -> {CT.cr.ref(looped, m, seen, s, i) == TChase.Stop{g} : TChase.Step}:
  match looped:
    case True{}:
      cc.stop(TChase.Miss{TFile.Circular{s}}, g, h)
    case False{}:
      match m:
        case None{}:
          cc.stop(TChase.Miss{TFile.NotFound{s}}, g, h)
        case Some{x}:
          LA.pt.none_some(TChase.Got, g, {CT.cr.ref(False{}, Some{x}, seen, s, i) == TChase.Stop{g} : TChase.Step}, h)

def cc.ref(+vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, +s: String, at: Maybe<&2, Nat>, -g: TChase.Got, h: {Theme.th.last.ref(vars, seen, s, at) == Some{g} : Maybe<&2, TChase.Got>}) -> {CT.cr.name(vars, seen, s, at) == TChase.Stop{g} : TChase.Step}:
  match at:
    case None{}:
      cc.stop(TChase.Miss{TFile.NotFound{s}}, g, h)
    case Some{+i}:
      cc.at(Theme.th.mem(seen, i), Theme.th.var(vars, i), seen, s, i, g, h)

def cc.sym(sharp: Bool, +vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, +c: Char, +rest: String, at: Maybe<&2, Nat>, -g: TChase.Got, h: {Theme.th.last.str(Bool.not(sharp), vars, seen, SCon{c, rest}, at) == Some{g} : Maybe<&2, TChase.Got>}) -> {CT.cr.text.c(sharp, vars, seen, SCon{c, rest}, at) == TChase.Stop{g} : TChase.Step}:
  match sharp:
    case True{}:
      cc.stop(Theme.th.hex(Co.hex(SCon{c, rest}), SCon{c, rest}), g, h)
    case False{}:
      cc.ref(vars, seen, SCon{c, rest}, at, g, h)

def cc.str(+vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, s: String, at: Maybe<&2, Nat>, -g: TChase.Got, h: {Theme.th.last.str(Theme.th.refers(s), vars, seen, s, at) == Some{g} : Maybe<&2, TChase.Got>}) -> {CT.cr.text(vars, seen, s, at) == TChase.Stop{g} : TChase.Step}:
  match s:
    case SNil{}:
      cc.stop(TChase.Hit{TFile.Dflt{}}, g, h)
    case SCon{+c, +rest}:
      cc.sym(Char.is_eq(c, '#'), vars, seen, c, rest, at, g, h)

def cc.last(+vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, j: TFile.Json, -g: TChase.Got, h: {Theme.th.last(vars, seen, j) == Some{g} : Maybe<&2, TChase.Got>}) -> {CT.cr.next(vars, seen, j) == TChase.Stop{g} : TChase.Step}:
  match j:
    case TFile.JStr{+s, at}:
      cc.str(vars, seen, s, at, g, h)
    case TFile.JNum{+t}:
      cc.stop(Theme.th.num(Co.num(t), t), g, h)
    case TFile.JOther{t}:
      cc.stop(TChase.Miss{TFile.BadValue{t}}, g, h)

# A step along the chain
# ----------------------
# A value that names variable i, met for the first time, goes on to i's
# value.

def cc.eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.themes.pt.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LA.themes.pt.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, cc.eq(p, q, h))

def cc.go(looped: Bool, m: Maybe<&2, TFile.Json>, +seen: List<&2, Nat>, s: String, +i: Nat, -v: TFile.Json, hl: {looped == False{} : Bool}, hm: {m == Some{v} : Maybe<&2, TFile.Json>}) -> {CT.cr.ref(looped, m, seen, s, i) == TChase.Go{i <> seen, v} : TChase.Step}:
  match looped:
    case True{}:
      LA.themes.pt.absurdT({CT.cr.ref(True{}, m, seen, s, i) == TChase.Go{i <> seen, v} : TChase.Step}, hl)
    case False{}:
      match m:
        case None{}:
          LA.pt.none_some(TFile.Json, v, {CT.cr.ref(False{}, None{}, seen, s, i) == TChase.Go{i <> seen, v} : TChase.Step}, hm)
        case Some{x}:
          Equal.cong(Maybe<&2, TFile.Json>, TChase.Step, y => TChase.Go{i <> seen, cc.unjson(y)}, Some{x}, Some{v}, hm)

def cc.at_next(same: Bool, +vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, +s: String, +k: Nat, +i: Nat, -v: TFile.Json, hn: {Theme.th.next.at(same, vars, i) == Some{v} : Maybe<&2, TFile.Json>}, hs: {Nat.is_eq(k, i) == same : Bool}, hf: {Theme.th.mem(seen, i) == False{} : Bool}) -> {CT.cr.name(vars, seen, s, Some{k}) == TChase.Go{i <> seen, v} : TChase.Step}:
  match same:
    case True{}:
      %Equal.sym(Nat, k, i, cc.eq(k, i, hs)) : {CT.cr.ref(Theme.th.mem(seen, _), Theme.th.var(vars, _), seen, s, _) == TChase.Go{i <> seen, v} : TChase.Step}
      cc.go(Theme.th.mem(seen, i), Theme.th.var(vars, i), seen, s, i, v, hf, hn)
    case False{}:
      LA.pt.none_some(TFile.Json, v, {CT.cr.name(vars, seen, s, Some{k}) == TChase.Go{i <> seen, v} : TChase.Step}, hn)

def cc.sym_next(sharp: Bool, +vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, +c: Char, +rest: String, at: Maybe<&2, Nat>, +i: Nat, -v: TFile.Json, hn: {Theme.th.next.str(Bool.not(sharp), vars, at, i) == Some{v} : Maybe<&2, TFile.Json>}, hf: {Theme.th.mem(seen, i) == False{} : Bool}) -> {CT.cr.text.c(sharp, vars, seen, SCon{c, rest}, at) == TChase.Go{i <> seen, v} : TChase.Step}:
  match sharp:
    case True{}:
      LA.pt.none_some(TFile.Json, v, {CT.cr.text.c(True{}, vars, seen, SCon{c, rest}, at) == TChase.Go{i <> seen, v} : TChase.Step}, hn)
    case False{}:
      match at:
        case None{}:
          LA.pt.none_some(TFile.Json, v, {CT.cr.text.c(False{}, vars, seen, SCon{c, rest}, None{}) == TChase.Go{i <> seen, v} : TChase.Step}, hn)
        case Some{+k}:
          cc.at_next(Nat.is_eq(k, i), vars, seen, SCon{c, rest}, k, i, v, hn, {==}, hf)

def cc.str_next(+vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, s: String, at: Maybe<&2, Nat>, +i: Nat, -v: TFile.Json, hn: {Theme.th.next.str(Theme.th.refers(s), vars, at, i) == Some{v} : Maybe<&2, TFile.Json>}, hf: {Theme.th.mem(seen, i) == False{} : Bool}) -> {CT.cr.text(vars, seen, s, at) == TChase.Go{i <> seen, v} : TChase.Step}:
  match s:
    case SNil{}:
      LA.pt.none_some(TFile.Json, v, {CT.cr.text(vars, seen, SNil{}, at) == TChase.Go{i <> seen, v} : TChase.Step}, hn)
    case SCon{+c, +rest}:
      cc.sym_next(Char.is_eq(c, '#'), vars, seen, c, rest, at, i, v, hn, hf)

def cc.next(+vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, j: TFile.Json, +i: Nat, -v: TFile.Json, hn: {Theme.th.next(vars, j, i) == Some{v} : Maybe<&2, TFile.Json>}, hf: {Theme.th.mem(seen, i) == False{} : Bool}) -> {CT.cr.next(vars, seen, j) == TChase.Go{i <> seen, v} : TChase.Step}:
  match j:
    case TFile.JStr{s, at}:
      cc.str_next(vars, seen, s, at, i, v, hn, hf)
    case TFile.JNum{t}:
      LA.pt.none_some(TFile.Json, v, {CT.cr.next(vars, seen, TFile.JNum{t}) == TChase.Go{i <> seen, v} : TChase.Step}, hn)
    case TFile.JOther{t}:
      LA.pt.none_some(TFile.Json, v, {CT.cr.next(vars, seen, TFile.JOther{t}) == TChase.Go{i <> seen, v} : TChase.Step}, hn)

# The walk along the chain
# ------------------------

def cc.follow_stop(f: Nat, +vars: List<&2, TFile.Var>, g: TChase.Got) -> {CT.cr.follow(f, vars, TChase.Stop{g}) == g : TChase.Got}:
  match f:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cc.if_rest(m: Maybe<&2, TFile.Json>, -r: Maybe<&2, TChase.Got>, -g: TChase.Got, h: {Theme.th.chain.if(m, r) == Some{g} : Maybe<&2, TChase.Got>}) -> {r == Some{g} : Maybe<&2, TChase.Got>}:
  match m:
    case None{}:
      LA.pt.none_some(TChase.Got, g, {r == Some{g} : Maybe<&2, TChase.Got>}, h)
    case Some{x}:
      h

def cc.if_some(m: Maybe<&2, TFile.Json>, -r: Maybe<&2, TChase.Got>, -g: TChase.Got, h: {Theme.th.chain.if(m, r) == Some{g} : Maybe<&2, TChase.Got>}) -> {m == Some{Theme.th.or.json(m)} : Maybe<&2, TFile.Json>}:
  match m:
    case None{}:
      LA.pt.none_some(TChase.Got, g, {None{} == Some{Theme.th.or.json(None{})} : Maybe<&2, TFile.Json>}, h)
    case Some{x}:
      {==}

def cc.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, False{}, True{}, h)
    case False{}:
      {==}

# a chain that decides at its end, with no variable met twice and fuel
# for each of its variables, is the walk's answer
def cc.walk(p: List<&2, Nat>, f: Nat, +vars: List<&2, TFile.Var>, +seen: List<&2, Nat>, +j: TFile.Json, +g: TChase.Got, +hd: {Theme.th.fresh(p, seen) == True{} : Bool}, hn: {Nat.is_le(List.length(&2, Nat, p), f) == True{} : Bool}, +he: {Theme.th.chain(p, vars, seen, j) == Some{g} : Maybe<&2, TChase.Got>})
  -> {CT.cr.follow(1n+f, vars, TChase.Go{seen, j}) == g : TChase.Got}:
  match p:
    case Nil{}:
      %Equal.sym(TChase.Step, CT.cr.next(vars, seen, j), TChase.Stop{g}, cc.last(vars, seen, j, g, he)) : {CT.cr.follow(f, vars, _) == g : TChase.Got}
      cc.follow_stop(f, vars, g)
    case Con{+i, +rest}:
      match f:
        case 0n:
          LA.themes.pt.absurdF({CT.cr.follow(1n+0n, vars, TChase.Go{seen, j}) == g : TChase.Got}, hn)
        case 1n+f2:
          +m = Theme.th.next(vars, j, i)
          +v = Theme.th.or.json(m)
          +r = Theme.th.chain(rest, vars, i <> seen, v)
          +hf = cc.not_t(Theme.th.mem(seen, i), LA.themes.pt.and_l(Bool.not(Theme.th.mem(seen, i)), Theme.th.fresh(rest, i <> seen), hd))
          +hd2 = LA.themes.pt.and_r(Bool.not(Theme.th.mem(seen, i)), Theme.th.fresh(rest, i <> seen), hd)
          +hr = cc.if_rest(m, r, g, he)
          +hv = cc.if_some(m, r, g, he)
          %Equal.sym(TChase.Step, CT.cr.next(vars, seen, j), TChase.Go{i <> seen, v}, cc.next(vars, seen, j, i, v, hv, hf)) : {CT.cr.follow(1n+f2, vars, _) == g : TChase.Got}
          cc.walk(rest, f2, vars, i <> seen, v, g, hd2, hn, hr)

def Theme.theme_chase_chain(vars, j, p, g, d, n, e):
  Equal.trans(TChase.Got, TChase.chase(vars, j), CT.cr.follow(1n+List.length(&2, TFile.Var, vars), vars, TChase.Go{Nil{}, j}), g, CT.pt.chase_walk(vars, j), cc.walk(p, List.length(&2, TFile.Var, vars), vars, Nil{}, j, g, d, n, e))
