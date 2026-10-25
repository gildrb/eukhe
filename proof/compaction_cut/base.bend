# eukhe: lemmas of the model proofs of area compaction_cut
#
# The walk back: from a contribution at or after the start the code keeps
# the tokens of the contributions after it, so it stops where the spec's
# suffix total reaches the limit (cc.reach_ge); before the start it only
# passes the answer on (cc.reach_any). The candidates: the code carries
# the calls of the last assistant answer, the spec finds them in every
# message before (cc.step_calls), and the code's look ahead is the spec's
# scan of the messages after (cc.ahead). The cut and the summarizer's
# answer: the code's functions against the spec's, one by one.

import Base
import ../../bend/context_order.bend as Co
import ../../bend/compaction_cut.bend as Cc
import ../../laws/context_order.bend as ContextOrder
import ../../laws/compaction_cut.bend as CompactionCut
import ../context_order/base.bend as LACo

# ---- logic ----

def cc.app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(List<&2, A>, List<&2, A>, z => x <> z, List.append(&2, A, t, Nil{}), t, cc.app_nil(A, t))

def cc.lt_s(j: Nat, s: Nat, h: {Nat.is_lt(j, s) == False{} : Bool}) -> {Nat.is_lt(1n+j, s) == False{} : Bool}:
  match j s:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LACo.co.tf({Nat.is_lt(1n, 1n+q) == False{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cc.lt_s(p, q, h)

# ---- the summarizer's answer ----

def cc.fail_call(calls: Bool) -> {Cc.failed.call(calls) == CompactionCut.fail_text(calls) : Cc.Outcome}:
  match calls:
    case True{}:
      {==}
    case False{}:
      {==}

def cc.summary(s: Co.Stop, calls: Bool, text: Bool, err: Maybe<&2, String>) -> {Cc.summary(s, calls, text, err) == CompactionCut.summary_spec(s, calls, text, err) : Cc.Outcome}:
  match s:
    case Co.SPending{}:
      cc.fail_call(calls)
    case Co.SStop{}:
      match calls:
        case True{}:
          {==}
        case False{}:
          match text:
            case True{}:
              {==}
            case False{}:
              {==}
    case Co.SLength{}:
      {==}
    case Co.SToolUse{}:
      cc.fail_call(calls)
    case Co.SError{}:
      match err:
        case None{}:
          {==}
        case Some{e}:
          {==}
    case Co.SAborted{}:
      match err:
        case None{}:
          {==}
        case Some{e}:
          {==}
    case Co.SDeferred{}:
      cc.fail_call(calls)

# ---- the look ahead ----

def cc.has(xs: List<&2, Nat>, +c: Nat) -> {Cc.has(xs, c) == CompactionCut.member(xs, c) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(x, c), z), Cc.has(t, c), CompactionCut.member(t, c), cc.has(t, c))

def cc.res(b: Bool, -x: Bool, -y: Bool, e: {x == y : Bool}) -> {Bool.and(Bool.not(b), x) == CompactionCut.clear.res(b, y) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def cc.res2(+calls: List<&2, Nat>, +d: Nat, -x: Bool, -y: Bool, e: {x == y : Bool}) -> {Bool.and(Bool.not(Cc.has(calls, d)), x) == CompactionCut.clear.res(CompactionCut.member(calls, d), y) : Bool}:
  %cc.has(calls, d) : {Bool.and(Bool.not(Cc.has(calls, d)), x) == CompactionCut.clear.res(_, y) : Bool}
  cc.res(Cc.has(calls, d), x, y, e)

def cc.last(ms: List<&2, Co.Msg>, +calls: List<&2, Nat>) -> {Cc.ahead.last(ms, calls) == CompactionCut.clear(ms, calls) : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, +u}:
      match m:
        case Co.MUser{}:
          cc.last(u, calls)
        case Co.MSystem{}:
          cc.last(u, calls)
        case Co.MAsst{s, cs}:
          {==}
        case Co.MRes{+d}:
          cc.res2(calls, d, Cc.ahead.last(u, calls), CompactionCut.clear(u, calls), cc.last(u, calls))

# the code's look ahead is the spec's scan of ms, then the messages of cs
def cc.ahead(cs: List<&2, Cc.Contrib>, +ms: List<&2, Co.Msg>, +calls: List<&2, Nat>) -> {Cc.ahead(cs, ms, calls) == CompactionCut.clear(List.append(&2, Co.Msg, ms, CompactionCut.flat(cs)), calls) : Bool}:
  match cs:
    case Nil{}:
      %Equal.sym(List<&2, Co.Msg>, List.append(&2, Co.Msg, ms, Nil{}), ms, cc.app_nil(Co.Msg, ms)) : {Cc.ahead.last(ms, calls) == CompactionCut.clear(_, calls) : Bool}
      cc.last(ms, calls)
    case Con{c, +t}:
      match c:
        case Cc.Contrib{+tok, +ms2}:
          match ms:
            case Nil{}:
              cc.ahead(t, ms2, calls)
            case Con{m, +u}:
              match m:
                case Co.MUser{}:
                  cc.ahead(Cc.Contrib{tok, ms2} <> t, u, calls)
                case Co.MSystem{}:
                  cc.ahead(Cc.Contrib{tok, ms2} <> t, u, calls)
                case Co.MAsst{s, xs}:
                  {==}
                case Co.MRes{+d}:
                  cc.res2(calls, d, Cc.ahead(Cc.Contrib{tok, ms2} <> t, u, calls), CompactionCut.clear(List.append(&2, Co.Msg, u, CompactionCut.flat(Cc.Contrib{tok, ms2} <> t)), calls), cc.ahead(Cc.Contrib{tok, ms2} <> t, u, calls))

def cc.user(calls: List<&2, Nat>, +u: List<&2, Co.Msg>, +t: List<&2, Cc.Contrib>) -> {Cc.cand.user(calls, u, t) == CompactionCut.user_spec(calls, Co.MUser{} <> List.append(&2, Co.Msg, u, CompactionCut.flat(t))) : Bool}:
  match calls:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      cc.ahead(t, u, x <> xs)

# the code's candidate test is the spec's
def cc.cand(ms: List<&2, Co.Msg>, +pre: List<&2, Cc.Contrib>, -tok: Nat, +t: List<&2, Cc.Contrib>) -> {Cc.cand(ms, CompactionCut.calls_before(pre), t) == CompactionCut.cand_spec(pre, Cc.Contrib{tok, ms} <> t) : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, +u}:
      match m:
        case Co.MUser{}:
          cc.user(CompactionCut.calls_before(pre), u, t)
        case Co.MSystem{}:
          {==}
        case Co.MAsst{s, xs}:
          {==}
        case Co.MRes{c}:
          {==}

# ---- the calls of the last assistant answer ----

def cc.cor(r: Maybe<&2, List<&2, Nat>>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match r:
    case None{}:
      acc
    case Some{x}:
      x

def cc.lor(r: Maybe<&2, List<&2, Nat>>, q: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match r:
    case None{}:
      q
    case Some{x}:
      Some{x}

def cc.lp.other(r: Maybe<&2, List<&2, Nat>>, -acc: List<&2, Nat>, m: Co.Msg, e: {CompactionCut.last_spec.pick(None{}, m) == None{} : Maybe<&2, List<&2, Nat>>}) -> {cc.cor(r, acc) == cc.cor(CompactionCut.last_spec.pick(r, m), acc) : List<&2, Nat>}:
  match r:
    case None{}:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, CompactionCut.last_spec.pick(None{}, m), None{}, e) : {acc == cc.cor(_, acc) : List<&2, Nat>}
      {==}
    case Some{x}:
      {==}

def cc.lp.asst(r: Maybe<&2, List<&2, Nat>>, -s: Co.Stop, -cs: List<&2, Nat>, -acc: List<&2, Nat>) -> {cc.cor(r, cs) == cc.cor(CompactionCut.last_spec.pick(r, Co.MAsst{s, cs}), acc) : List<&2, Nat>}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      {==}

# the code's tail fold finds the spec's last assistant answer
def cc.lastc(ms: List<&2, Co.Msg>, +acc: List<&2, Nat>) -> {Cc.last_calls(ms, acc) == cc.cor(CompactionCut.last_spec(ms), acc) : List<&2, Nat>}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, +u}:
      match m:
        case Co.MUser{}:
          %cc.lp.other(CompactionCut.last_spec(u), acc, Co.MUser{}, {==}) : {Cc.last_calls(u, acc) == _ : List<&2, Nat>}
          cc.lastc(u, acc)
        case Co.MSystem{}:
          %cc.lp.other(CompactionCut.last_spec(u), acc, Co.MSystem{}, {==}) : {Cc.last_calls(u, acc) == _ : List<&2, Nat>}
          cc.lastc(u, acc)
        case Co.MAsst{+s, +cs}:
          %cc.lp.asst(CompactionCut.last_spec(u), s, cs, acc) : {Cc.last_calls(u, cs) == _ : List<&2, Nat>}
          cc.lastc(u, cs)
        case Co.MRes{+c}:
          %cc.lp.other(CompactionCut.last_spec(u), acc, Co.MRes{c}, {==}) : {Cc.last_calls(u, acc) == _ : List<&2, Nat>}
          cc.lastc(u, acc)

def cc.flat_app(xs: List<&2, Cc.Contrib>, +ys: List<&2, Cc.Contrib>) -> {CompactionCut.flat(List.append(&2, Cc.Contrib, xs, ys)) == List.append(&2, Co.Msg, CompactionCut.flat(xs), CompactionCut.flat(ys)) : List<&2, Co.Msg>}:
  match xs:
    case Nil{}:
      {==}
    case Con{c, +t}:
      match c:
        case Cc.Contrib{tok, +ms}:
          Equal.trans(List<&2, Co.Msg>, List.append(&2, Co.Msg, ms, CompactionCut.flat(List.append(&2, Cc.Contrib, t, ys))), List.append(&2, Co.Msg, ms, List.append(&2, Co.Msg, CompactionCut.flat(t), CompactionCut.flat(ys))), List.append(&2, Co.Msg, List.append(&2, Co.Msg, ms, CompactionCut.flat(t)), CompactionCut.flat(ys)), Equal.cong(List<&2, Co.Msg>, List<&2, Co.Msg>, z => List.append(&2, Co.Msg, ms, z), CompactionCut.flat(List.append(&2, Cc.Contrib, t, ys)), List.append(&2, Co.Msg, CompactionCut.flat(t), CompactionCut.flat(ys)), cc.flat_app(t, ys)), Equal.sym(List<&2, Co.Msg>, List.append(&2, Co.Msg, List.append(&2, Co.Msg, ms, CompactionCut.flat(t)), CompactionCut.flat(ys)), List.append(&2, Co.Msg, ms, List.append(&2, Co.Msg, CompactionCut.flat(t), CompactionCut.flat(ys))), LACo.co.app_assoc(Co.Msg, ms, CompactionCut.flat(t), CompactionCut.flat(ys))))

def cc.lor_none(r: Maybe<&2, List<&2, Nat>>) -> {r == cc.lor(r, None{}) : Maybe<&2, List<&2, Nat>>}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      {==}

def cc.lp.lor(r: Maybe<&2, List<&2, Nat>>, -q: Maybe<&2, List<&2, Nat>>, -m: Co.Msg) -> {CompactionCut.last_spec.pick(cc.lor(r, q), m) == cc.lor(r, CompactionCut.last_spec.pick(q, m)) : Maybe<&2, List<&2, Nat>>}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      {==}

# the last assistant answer of xs ++ ys is that of ys, else that of xs
def cc.ls_app(xs: List<&2, Co.Msg>, +ys: List<&2, Co.Msg>) -> {CompactionCut.last_spec(List.append(&2, Co.Msg, xs, ys)) == cc.lor(CompactionCut.last_spec(ys), CompactionCut.last_spec(xs)) : Maybe<&2, List<&2, Nat>>}:
  match xs:
    case Nil{}:
      cc.lor_none(CompactionCut.last_spec(ys))
    case Con{+m, +t}:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, CompactionCut.last_spec(List.append(&2, Co.Msg, t, ys)), cc.lor(CompactionCut.last_spec(ys), CompactionCut.last_spec(t)), cc.ls_app(t, ys)) : {CompactionCut.last_spec.pick(_, m) == cc.lor(CompactionCut.last_spec(ys), CompactionCut.last_spec.pick(CompactionCut.last_spec(t), m)) : Maybe<&2, List<&2, Nat>>}
      cc.lp.lor(CompactionCut.last_spec(ys), CompactionCut.last_spec(t), m)

def cc.cor_co(r: Maybe<&2, List<&2, Nat>>, -q: Maybe<&2, List<&2, Nat>>) -> {cc.cor(r, CompactionCut.calls_of(q)) == CompactionCut.calls_of(cc.lor(r, q)) : List<&2, Nat>}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      {==}

# the calls the code carries past a contribution are the spec's for the
# contributions before it and it
def cc.step_calls(+pre: List<&2, Cc.Contrib>, +tok: Nat, +ms: List<&2, Co.Msg>) -> {Cc.last_calls(ms, CompactionCut.calls_before(pre)) == CompactionCut.calls_before(List.append(&2, Cc.Contrib, pre, [Cc.Contrib{tok, ms}])) : List<&2, Nat>}:
  +fp = CompactionCut.flat(pre)
  +a1 = cc.cor(CompactionCut.last_spec(ms), CompactionCut.calls_of(CompactionCut.last_spec(fp)))
  +a2 = CompactionCut.calls_of(cc.lor(CompactionCut.last_spec(ms), CompactionCut.last_spec(fp)))
  +a3 = CompactionCut.calls_of(CompactionCut.last_spec(List.append(&2, Co.Msg, fp, ms)))
  +a4 = CompactionCut.calls_of(CompactionCut.last_spec(List.append(&2, Co.Msg, fp, List.append(&2, Co.Msg, ms, Nil{}))))
  +e1 = cc.lastc(ms, CompactionCut.calls_of(CompactionCut.last_spec(fp)))
  +e2 = cc.cor_co(CompactionCut.last_spec(ms), CompactionCut.last_spec(fp))
  +e3 = Equal.cong(Maybe<&2, List<&2, Nat>>, List<&2, Nat>, z => CompactionCut.calls_of(z), cc.lor(CompactionCut.last_spec(ms), CompactionCut.last_spec(fp)), CompactionCut.last_spec(List.append(&2, Co.Msg, fp, ms)), Equal.sym(Maybe<&2, List<&2, Nat>>, CompactionCut.last_spec(List.append(&2, Co.Msg, fp, ms)), cc.lor(CompactionCut.last_spec(ms), CompactionCut.last_spec(fp)), cc.ls_app(fp, ms)))
  +e4 = Equal.cong(List<&2, Co.Msg>, List<&2, Nat>, z => CompactionCut.calls_of(CompactionCut.last_spec(List.append(&2, Co.Msg, fp, z))), ms, List.append(&2, Co.Msg, ms, Nil{}), Equal.sym(List<&2, Co.Msg>, List.append(&2, Co.Msg, ms, Nil{}), ms, cc.app_nil(Co.Msg, ms)))
  +e5 = Equal.cong(List<&2, Co.Msg>, List<&2, Nat>, z => CompactionCut.calls_of(CompactionCut.last_spec(z)), List.append(&2, Co.Msg, fp, List.append(&2, Co.Msg, ms, Nil{})), CompactionCut.flat(List.append(&2, Cc.Contrib, pre, [Cc.Contrib{tok, ms}])), Equal.sym(List<&2, Co.Msg>, CompactionCut.flat(List.append(&2, Cc.Contrib, pre, [Cc.Contrib{tok, ms}])), List.append(&2, Co.Msg, fp, List.append(&2, Co.Msg, ms, Nil{})), cc.flat_app(pre, [Cc.Contrib{tok, ms}])))
  Equal.trans(List<&2, Nat>, Cc.last_calls(ms, CompactionCut.calls_before(pre)), a1, CompactionCut.calls_before(List.append(&2, Cc.Contrib, pre, [Cc.Contrib{tok, ms}])), e1, Equal.trans(List<&2, Nat>, a1, a2, CompactionCut.calls_before(List.append(&2, Cc.Contrib, pre, [Cc.Contrib{tok, ms}])), e2, Equal.trans(List<&2, Nat>, a2, a3, CompactionCut.calls_before(List.append(&2, Cc.Contrib, pre, [Cc.Contrib{tok, ms}])), e3, Equal.trans(List<&2, Nat>, a3, a4, CompactionCut.calls_before(List.append(&2, Cc.Contrib, pre, [Cc.Contrib{tok, ms}])), e4, e5))))

def cc.one(b: Bool, -i: Nat, -xs: List<&2, Nat>) -> {Cc.cands.one(b, i, xs) == CompactionCut.cands_spec.one(b, i, xs) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's candidates are the spec's
def cc.cands(t: List<&2, Cc.Contrib>, +pre: List<&2, Cc.Contrib>, +i: Nat, +start: Nat) -> {Cc.cands.go(t, i, start, CompactionCut.calls_before(pre)) == CompactionCut.cands_spec.go(t, pre, i, start) : List<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{c, +u}:
      match c:
        case Cc.Contrib{+tok, +ms}:
          +x = Bool.and(Bool.not(Nat.is_lt(i, start)), Cc.cand(ms, CompactionCut.calls_before(pre), u))
          %cc.cand(ms, pre, tok, u) : {Cc.cands.one(x, i, Cc.cands.go(u, 1n+i, start, Cc.last_calls(ms, CompactionCut.calls_before(pre)))) == CompactionCut.cands_spec.one(Bool.and(Bool.not(Nat.is_lt(i, start)), _), i, CompactionCut.cands_spec.go(u, List.append(&2, Cc.Contrib, pre, [Cc.Contrib{tok, ms}]), 1n+i, start)) : List<&2, Nat>}
          %cc.cands(u, List.append(&2, Cc.Contrib, pre, [Cc.Contrib{tok, ms}]), 1n+i, start) : {Cc.cands.one(x, i, Cc.cands.go(u, 1n+i, start, Cc.last_calls(ms, CompactionCut.calls_before(pre)))) == CompactionCut.cands_spec.one(x, i, _) : List<&2, Nat>}
          %cc.step_calls(pre, tok, ms) : {Cc.cands.one(x, i, Cc.cands.go(u, 1n+i, start, Cc.last_calls(ms, CompactionCut.calls_before(pre)))) == CompactionCut.cands_spec.one(x, i, Cc.cands.go(u, 1n+i, start, _)) : List<&2, Nat>}
          cc.one(x, i, Cc.cands.go(u, 1n+i, start, Cc.last_calls(ms, CompactionCut.calls_before(pre))))

# ---- the walk back ----

def cc.wsp(r: Maybe<&2, Nat>, n: Nat) -> Cc.Walk:
  match r:
    case None{}:
      Cc.Kept{n}
    case Some{a}:
      Cc.Reached{a}

def cc.rb(b: Bool, -m: Nat, -j: Nat) -> {Cc.reach.pick(b, m, j) == cc.wsp(CompactionCut.reach_spec.pick(None{}, Bool.not(b), j), m) : Cc.Walk}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cc.rstep(r: Maybe<&2, Nat>, +n: Nat, +tok: Nat, +j: Nat, +k: Nat) -> {Cc.reach.step(cc.wsp(r, n), tok, False{}, j, k) == cc.wsp(CompactionCut.reach_spec.pick(r, Bool.not(Nat.is_lt(Nat.add(n, tok), k)), j), Nat.add(n, tok)) : Cc.Walk}:
  match r:
    case None{}:
      cc.rb(Nat.is_lt(Nat.add(n, tok), k), Nat.add(n, tok), j)
    case Some{a}:
      {==}

# from a contribution at or after the start, the code's walk is the
# spec's, keeping the tokens of every contribution walked
def cc.reach_ge(t: List<&2, Cc.Contrib>, +j: Nat, +start: Nat, +k: Nat, +h: {Nat.is_lt(j, start) == False{} : Bool}) -> {Cc.reach.go(t, j, start, k) == cc.wsp(CompactionCut.reach_spec.go(t, j, start, k), CompactionCut.total(t)) : Cc.Walk}:
  match t:
    case Nil{}:
      {==}
    case Con{c, +u}:
      match c:
        case Cc.Contrib{+tok, +ms}:
          +r = CompactionCut.reach_spec.go(u, 1n+j, start, k)
          %Equal.sym(Cc.Walk, Cc.reach.go(u, 1n+j, start, k), cc.wsp(r, CompactionCut.total(u)), cc.reach_ge(u, 1n+j, start, k, cc.lt_s(j, start, h))) : {Cc.reach.step(_, tok, Nat.is_lt(j, start), j, k) == cc.wsp(CompactionCut.reach_spec.pick(r, Bool.and(Bool.not(Nat.is_lt(j, start)), Bool.not(Nat.is_lt(Nat.add(CompactionCut.total(u), tok), k))), j), Nat.add(CompactionCut.total(u), tok)) : Cc.Walk}
          %Equal.sym(Bool, Nat.is_lt(j, start), False{}, h) : {Cc.reach.step(cc.wsp(r, CompactionCut.total(u)), tok, _, j, k) == cc.wsp(CompactionCut.reach_spec.pick(r, Bool.and(Bool.not(_), Bool.not(Nat.is_lt(Nat.add(CompactionCut.total(u), tok), k))), j), Nat.add(CompactionCut.total(u), tok)) : Cc.Walk}
          cc.rstep(r, CompactionCut.total(u), tok, j, k)

def cc.of(r: Maybe<&2, Nat>, -n: Nat) -> {Cc.reach.of(cc.wsp(r, n)) == r : Maybe<&2, Nat>}:
  match r:
    case None{}:
      {==}
    case Some{a}:
      {==}

def cc.skip(w: Cc.Walk, -tok: Nat, -j: Nat, -k: Nat) -> {Cc.reach.of(Cc.reach.step(w, tok, True{}, j, k)) == Cc.reach.of(w) : Maybe<&2, Nat>}:
  match w:
    case Cc.Reached{a}:
      {==}
    case Cc.Kept{n}:
      {==}

def cc.pf(r: Maybe<&2, Nat>, -j: Nat) -> {r == CompactionCut.reach_spec.pick(r, False{}, j) : Maybe<&2, Nat>}:
  match r:
    case None{}:
      {==}
    case Some{a}:
      {==}

def cc.ra.at(b: Bool, +tok: Nat, +ms: List<&2, Co.Msg>, +u: List<&2, Cc.Contrib>, +j: Nat, +start: Nat, +k: Nat, e: {Nat.is_lt(j, start) == b : Bool}, ih: {Cc.reach.of(Cc.reach.go(u, 1n+j, start, k)) == CompactionCut.reach_spec.go(u, 1n+j, start, k) : Maybe<&2, Nat>}) -> {Cc.reach.of(Cc.reach.go(Cc.Contrib{tok, ms} <> u, j, start, k)) == CompactionCut.reach_spec.go(Cc.Contrib{tok, ms} <> u, j, start, k) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      +w = Cc.reach.go(u, 1n+j, start, k)
      +r = CompactionCut.reach_spec.go(u, 1n+j, start, k)
      %Equal.sym(Bool, Nat.is_lt(j, start), True{}, e) : {Cc.reach.of(Cc.reach.step(w, tok, _, j, k)) == CompactionCut.reach_spec.pick(r, Bool.and(Bool.not(_), Bool.not(Nat.is_lt(Nat.add(CompactionCut.total(u), tok), k))), j) : Maybe<&2, Nat>}
      Equal.trans(Maybe<&2, Nat>, Cc.reach.of(Cc.reach.step(w, tok, True{}, j, k)), Cc.reach.of(w), CompactionCut.reach_spec.pick(r, False{}, j), cc.skip(w, tok, j, k), Equal.trans(Maybe<&2, Nat>, Cc.reach.of(w), r, CompactionCut.reach_spec.pick(r, False{}, j), ih, cc.pf(r, j)))
    case False{}:
      +t = {Cc.Contrib{tok, ms} <> u : List<&2, Cc.Contrib>}
      Equal.trans(Maybe<&2, Nat>, Cc.reach.of(Cc.reach.go(t, j, start, k)), Cc.reach.of(cc.wsp(CompactionCut.reach_spec.go(t, j, start, k), CompactionCut.total(t))), CompactionCut.reach_spec.go(t, j, start, k), Equal.cong(Cc.Walk, Maybe<&2, Nat>, z => Cc.reach.of(z), Cc.reach.go(t, j, start, k), cc.wsp(CompactionCut.reach_spec.go(t, j, start, k), CompactionCut.total(t)), cc.reach_ge(t, j, start, k, e)), cc.of(CompactionCut.reach_spec.go(t, j, start, k), CompactionCut.total(t)))

# from any contribution, where the code's walk stops is the spec's
def cc.reach_any(t: List<&2, Cc.Contrib>, +j: Nat, +start: Nat, +k: Nat) -> {Cc.reach.of(Cc.reach.go(t, j, start, k)) == CompactionCut.reach_spec.go(t, j, start, k) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{c, +u}:
      match c:
        case Cc.Contrib{+tok, +ms}:
          cc.ra.at(Nat.is_lt(j, start), tok, ms, u, j, start, k, {==}, cc.reach_any(u, 1n+j, start, k))

def cc.reach(+start: Nat, lim: Cc.Limit, +cs: List<&2, Cc.Contrib>) -> {Cc.reach(start, lim, cs) == CompactionCut.reach_spec(start, lim, cs) : Maybe<&2, Nat>}:
  match lim:
    case Cc.Never{}:
      {==}
    case Cc.Below{+k}:
      cc.reach_any(cs, 0n, start, k)

# ---- the cut ----

def cc.fp(b: Bool, -x: Nat, -rest: Maybe<&2, Nat>) -> {Cc.first_at.pick(Bool.not(b), x, rest) == CompactionCut.at_or_after.pick(b, x, rest) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cc.first(xs: List<&2, Nat>, +r: Nat) -> {Cc.first_at(xs, r) == CompactionCut.at_or_after(xs, r) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cc.first(t, r) : {Cc.first_at.pick(Bool.not(Nat.is_lt(x, r)), x, Cc.first_at(t, r)) == CompactionCut.at_or_after.pick(Nat.is_lt(x, r), x, _) : Maybe<&2, Nat>}
      cc.fp(Nat.is_lt(x, r), x, Cc.first_at(t, r))

def cc.mor(r: Maybe<&2, Nat>, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match r:
    case None{}:
      acc
    case Some{y}:
      Some{y}

def cc.fin(r: Maybe<&2, Nat>, -x: Nat, -acc: Maybe<&2, Nat>) -> {cc.mor(r, Some{x}) == cc.mor(CompactionCut.final.pick(r, x), acc) : Maybe<&2, Nat>}:
  match r:
    case None{}:
      {==}
    case Some{y}:
      {==}

def cc.lastof(xs: List<&2, Nat>, +acc: Maybe<&2, Nat>) -> {Cc.last_of.go(xs, acc) == cc.mor(CompactionCut.final(xs), acc) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cc.fin(CompactionCut.final(t), x, acc) : {Cc.last_of.go(t, Some{x}) == _ : Maybe<&2, Nat>}
      cc.lastof(t, Some{x})

def cc.mor_none(r: Maybe<&2, Nat>) -> {cc.mor(r, None{}) == r : Maybe<&2, Nat>}:
  match r:
    case None{}:
      {==}
    case Some{y}:
      {==}

def cc.pco(m: Maybe<&2, Nat>, +xs: List<&2, Nat>) -> {Cc.pick_cut.or(m, xs) == CompactionCut.chosen_spec.or(m, xs) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      Equal.trans(Maybe<&2, Nat>, Cc.last_of.go(xs, None{}), cc.mor(CompactionCut.final(xs), None{}), CompactionCut.final(xs), cc.lastof(xs, None{}), cc.mor_none(CompactionCut.final(xs)))
    case Some{x}:
      {==}

def cc.pick_cut(+xs: List<&2, Nat>, +r: Nat) -> {Cc.pick_cut(xs, r) == CompactionCut.chosen_spec(xs, r) : Maybe<&2, Nat>}:
  %cc.first(xs, r) : {Cc.pick_cut.or(Cc.first_at(xs, r), xs) == CompactionCut.chosen_spec.or(_, xs) : Maybe<&2, Nat>}
  cc.pco(Cc.first_at(xs, r), xs)

def cc.fa(b: Bool, ms: List<&2, Co.Msg>, -rest: Bool) -> {Bool.or(Bool.and(b, Cc.nonempty(ms)), rest) == CompactionCut.filled_spec.at(b, ms, rest) : Bool}:
  match b:
    case True{}:
      match ms:
        case Nil{}:
          {==}
        case Con{m, t}:
          {==}
    case False{}:
      {==}

def cc.filled(cs: List<&2, Cc.Contrib>, +i: Nat, +start: Nat, +x: Nat) -> {Cc.filled(cs, i, start, x) == CompactionCut.filled_spec(cs, i, start, x) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{c, +t}:
      match c:
        case Cc.Contrib{tok, +ms}:
          +b = Bool.and(Bool.not(Nat.is_lt(i, start)), Nat.is_lt(i, x))
          %cc.filled(t, 1n+i, start, x) : {Bool.or(Bool.and(b, Cc.nonempty(ms)), Cc.filled(t, 1n+i, start, x)) == CompactionCut.filled_spec.at(b, ms, _) : Bool}
          cc.fa(b, ms, Cc.filled(t, 1n+i, start, x))

def cc.keep(b: Bool, -x: Nat) -> {Cc.cut.keep(b, x) == CompactionCut.cut_spec.keep(b, x) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cc.cut_at(m: Maybe<&2, Nat>, +start: Nat, +cs: List<&2, Cc.Contrib>) -> {Cc.cut.at(m, start, cs) == CompactionCut.cut_spec.at(m, start, cs) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %cc.filled(cs, 0n, start, x) : {Cc.cut.keep(Cc.filled(cs, 0n, start, x), x) == CompactionCut.cut_spec.keep(_, x) : Maybe<&2, Nat>}
      cc.keep(Cc.filled(cs, 0n, start, x), x)

def cc.cut_from(r: Maybe<&2, Nat>, +start: Nat, +cs: List<&2, Cc.Contrib>) -> {Cc.cut.from(r, start, cs) == CompactionCut.cut_spec.from(r, start, cs) : Maybe<&2, Nat>}:
  match r:
    case None{}:
      {==}
    case Some{+a}:
      %cc.cands(cs, [], 0n, start) : {Cc.cut.at(Cc.pick_cut(Cc.cands(start, cs), a), start, cs) == CompactionCut.cut_spec.at(CompactionCut.chosen_spec(_, a), start, cs) : Maybe<&2, Nat>}
      %cc.pick_cut(Cc.cands(start, cs), a) : {Cc.cut.at(Cc.pick_cut(Cc.cands(start, cs), a), start, cs) == CompactionCut.cut_spec.at(_, start, cs) : Maybe<&2, Nat>}
      cc.cut_at(Cc.pick_cut(Cc.cands(start, cs), a), start, cs)
