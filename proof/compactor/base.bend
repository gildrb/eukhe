# eukhe: lemmas the proofs of area compactor share

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/state.bend as OState
import ../base/bool.bend as LBool
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../base/optchat.bend as LOptchat

def pc.lt_succ_of_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      LLogicLogic.pc.absurd_ft({Nat.is_lt(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.lt_succ_of_le(p, q, e)

def pc.le_succ_of_lt(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      LLogicLogic.pc.lt_zero({Nat.is_le(1n+p, 0n) == True{} : Bool}, p, e)
    case 0n 1n+q:
      LNat.compactor.pc.le_zero(q)
    case 1n+p 1n+q:
      pc.le_succ_of_lt(p, q, e)

def pc.lt_add_l(c: Nat, -x: Nat, -y: Nat, e: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+p:
      pc.lt_add_l(p, x, y, e)

def pc.le_add_l(c: Nat, -x: Nat, -y: Nat, e: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+p:
      pc.le_add_l(p, x, y, e)

def pc.and_true(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LLogicLogic.pc.absurd_ft({False{} == True{} : Bool}, ea)

def pc.lt_self(+x: Nat) -> {Nat.is_lt(x, 1n+x) == True{} : Bool}:
  pc.lt_succ_of_le(x, x, LNat.compactor.pc.le_refl(x))

# an outcome that counts lowers a pending line's weight
def pc.after_falls(n: Nat, o: C.Outcome, +m: Nat, lands: {C.Outcome.lands(o) == True{} : Bool}) -> {Nat.is_lt(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{n}, o)), m), Nat.add(1n+n, m)) == True{} : Bool}:
  match n o:
    case +p C.Built{}:
      pc.lt_succ_of_le(m, Nat.add(p, m), LNat.compactor.pc.le_add(p, m))
    case 0n C.Failed{}:
      pc.lt_self(m)
    case 1n+p C.Failed{}:
      pc.lt_self(Nat.add(p, m))
    case p C.Disk{}:
      LLogicLogic.pc.absurd_ft({Nat.is_lt(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Disk{})), m), Nat.add(1n+p, m)) == True{} : Bool}, lands)
    case p C.Stopped{}:
      LLogicLogic.pc.absurd_ft({Nat.is_lt(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Stopped{})), m), Nat.add(1n+p, m)) == True{} : Bool}, lands)

# and no outcome raises it
def pc.after_holds(n: Nat, o: C.Outcome, +m: Nat) -> {Nat.is_le(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{n}, o)), m), Nat.add(1n+n, m)) == True{} : Bool}:
  match n o:
    case +p C.Built{}:
      LNat.pc.lt_to_le(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Built{})), m), Nat.add(1n+p, m), pc.after_falls(p, C.Built{}, m, {==}))
    case +p C.Failed{}:
      LNat.pc.lt_to_le(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Failed{})), m), Nat.add(1n+p, m), pc.after_falls(p, C.Failed{}, m, {==}))
    case 0n C.Disk{}:
      LNat.compactor.pc.le_refl(1n+m)
    case 1n+p C.Disk{}:
      LNat.compactor.pc.le_refl(Nat.add(2n+p, m))
    case 0n C.Stopped{}:
      LNat.compactor.pc.le_refl(1n+m)
    case 1n+p C.Stopped{}:
      LNat.compactor.pc.le_refl(Nat.add(2n+p, m))

def pc.settle_falls(ps: List<&2, C.Pend>, k: Nat, o: C.Outcome, due: {C.pending_at(ps, k) == True{} : Bool}, lands: {C.Outcome.lands(o) == True{} : Bool}) -> {Nat.is_lt(C.measure(C.hit(ps, k, o)), C.measure(ps)) == True{} : Bool}:
  match ps k:
    case Nil{} j:
      LLogicLogic.pc.absurd_ft({Nat.is_lt(0n, 0n) == True{} : Bool}, due)
    case C.Made{} <> rest 0n:
      LLogicLogic.pc.absurd_ft({Nat.is_lt(C.measure(rest), C.measure(rest)) == True{} : Bool}, due)
    case C.Owed{n} <> rest 0n:
      pc.after_falls(n, o, C.measure(rest), lands)
    case p <> rest 1n+j:
      pc.lt_add_l(C.Pend.weight(p), C.measure(C.hit(rest, j, o)), C.measure(rest), pc.settle_falls(rest, j, o, due, lands))

def pc.settle_holds(ps: List<&2, C.Pend>, k: Nat, +o: C.Outcome) -> {Nat.is_le(C.measure(C.hit(ps, k, o)), C.measure(ps)) == True{} : Bool}:
  match ps k:
    case Nil{} j:
      {==}
    case C.Made{} <> rest 0n:
      LNat.compactor.pc.le_refl(C.measure(rest))
    case C.Owed{+n} <> rest 0n:
      pc.after_holds(n, o, C.measure(rest))
    case +p <> rest 1n+j:
      pc.le_add_l(C.Pend.weight(p), C.measure(C.hit(rest, j, o)), C.measure(rest), pc.settle_holds(rest, j, o))

def pc.bounded_step(b: Bool, +h: Nat, +x: Nat, +m1: Nat, +m0: Nat, +ih: {Nat.is_le(Nat.add(h, x), m1) == True{} : Bool}, holds: {Nat.is_le(m1, m0) == True{} : Bool}, falls: {b == True{} : Bool} -> {Nat.is_lt(m1, m0) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(OBits.bit(b, 0n), h), x), m0) == True{} : Bool}:
  match b:
    case False{}:
      LNat.compactor.pc.le_trans(Nat.add(h, x), m1, m0, ih, holds)
    case True{}:
      pc.le_succ_of_lt(Nat.add(h, x), m0, LNat.pc.le_lt_trans(Nat.add(h, x), m1, m0, ih, falls({==})))

def pc.settle_bounded(es: List<&2, C.End>, +ps: List<&2, C.Pend>) -> {Nat.is_le(Nat.add(C.hits(es, ps), C.measure(C.run(es, ps))), C.measure(ps)) == True{} : Bool}:
  match es:
    case Nil{}:
      LNat.compactor.pc.le_refl(C.measure(ps))
    case C.End{+k, +o} <> +rest:
      +next = C.hit(ps, k, o)
      +due = C.pending_at(ps, k)
      +lands = C.Outcome.lands(o)
      pc.bounded_step(Bool.and(due, lands), C.hits(rest, next), C.measure(C.run(rest, next)), C.measure(next), C.measure(ps), pc.settle_bounded(rest, next), pc.settle_holds(ps, k, o), +both => pc.settle_falls(ps, k, o, LLogicBool.pf.and_l(due, lands, both), LLogicBool.pf.and_r(due, lands, both)))

# (H2) Need first
# ---------------

def pc.needed_cons(+info: OInfo.Info, +h: ONode.Node, +v: List<&2, ONode.Node>, ns: List<&2, ONode.Node>, +e: {C.needed(info, v, ns) == True{} : Bool}) -> {C.needed(info, h <> v, ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> rest:
      +a = Bool.and(ONode.Nodes.has(v, n), Bool.not(OInfo.Info.built(info, n)))
      +ea = LLogicBool.pf.and_l(a, C.needed(info, v, rest), e)
      pc.and_true(Bool.and(Bool.or(ONode.Node.eq(h, n), ONode.Nodes.has(v, n)), Bool.not(OInfo.Info.built(info, n))), C.needed(info, h <> v, rest), pc.and_true(Bool.or(ONode.Node.eq(h, n), ONode.Nodes.has(v, n)), Bool.not(OInfo.Info.built(info, n)), LBool.pf.or_r(ONode.Node.eq(h, n), ONode.Nodes.has(v, n), LLogicBool.pf.and_l(ONode.Nodes.has(v, n), Bool.not(OInfo.Info.built(info, n)), ea)), LLogicBool.pf.and_r(ONode.Nodes.has(v, n), Bool.not(OInfo.Info.built(info, n)), ea)), pc.needed_cons(info, h, v, rest, LLogicBool.pf.and_r(a, C.needed(info, v, rest), e)))

def pc.emit_ok(stop: Bool, b: Bool, free: Bool, +info: OInfo.Info, +h: ONode.Node, +rest: List<&2, ONode.Node>, +rec: List<&2, ONode.Node>, eb: {b == OInfo.Info.built(info, h) : Bool}, +ih: {C.needed(info, rest, rec) == True{} : Bool}) -> {C.needed(info, h <> rest, OQueue.cand.emit(stop, b, free, h, rec)) == True{} : Bool}:
  match stop b free:
    case True{} y z:
      {==}
    case False{} True{} z:
      pc.needed_cons(info, h, rest, rec, ih)
    case False{} False{} True{}:
      %eb : {Bool.and(Bool.and(Bool.or(ONode.Node.eq(h, h), ONode.Nodes.has(rest, h)), Bool.not(_)), C.needed(info, h <> rest, rec)) == True{} : Bool}
      %LOptchat.pf.node_eq_refl(h) : {Bool.and(Bool.and(Bool.or(_, ONode.Nodes.has(rest, h)), True{}), C.needed(info, h <> rest, rec)) == True{} : Bool}
      pc.needed_cons(info, h, rest, rec, ih)
    case False{} False{} False{}:
      pc.needed_cons(info, h, rest, rec, ih)

def pc.cand_ok(v: List<&2, ONode.Node>, +info: OInfo.Info, +busy: List<&2, ONode.Node>, +jobs: Nat, +unb: Nat, room: Nat) -> {C.needed(info, v, OQueue.cand.view(v, info, busy, jobs, unb, room)) == True{} : Bool}:
  match v room:
    case Nil{} r:
      {==}
    case h <> rest 0n:
      {==}
    case +h <> +rest 1n+r:
      +unb2 = Nat.add(unb, OBits.bit(Bool.not(OInfo.Info.built(info, h)), 0n))
      +room2 = Nat.sub(1n+r, OBits.bit(Bool.and(Bool.not(OInfo.Info.built(info, h)), Bool.not(ONode.Nodes.has(busy, h))), 0n))
      pc.emit_ok(Nat.is_ge(unb, jobs), OInfo.Info.built(info, h), Bool.not(ONode.Nodes.has(busy, h)), info, h, rest, OQueue.cand.view(rest, info, busy, jobs, unb2, room2), {==}, pc.cand_ok(rest, info, busy, jobs, unb2, room2))

def pc.need_first(+cfg: OState.Cfg, +s: OState.St) -> {C.needed(OState.St.info(s), OState.St.view(s), OQueue.cands.need(cfg, s)) == True{} : Bool}:
  pc.cand_ok(OState.St.view(s), OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), 0n, Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))))

# (H1) A line after the replies it asked again on
# -----------------------------------------------
# Over replies the line asks again after (Compactor.asks), line.go takes
# one more call per reply, keeps each as the best reply, and goes on with
# the rest from the last of them (lp.go); the best reply it holds then
# is past the node and its length is its bytes (lp.Lk, lp.lk).

# a text's Text.len is its bytes
def lp.len(t: List<&2, C.W>) -> {C.Text.len(t) == Compactor.bytes(t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case c <> rest:
      match c:
        case C.W1{}:
          %lp.len(rest) : {1n+C.Text.len(rest) == 1n+_ : Nat}
          {==}
        case C.W2{}:
          %lp.len(rest) : {2n+C.Text.len(rest) == 2n+_ : Nat}
          {==}
        case C.W3{}:
          %lp.len(rest) : {3n+C.Text.len(rest) == 3n+_ : Nat}
          {==}
        case C.W4{}:
          %lp.len(rest) : {4n+C.Text.len(rest) == 4n+_ : Nat}
          {==}

# the best reply a line holds: its length is its bytes, past the node
def lp.Lk(node: Nat, b: Maybe<&2, List<&2, C.W>>, bl: Nat) -> Type:
  match b:
    case None{}:
      Unit
    case Some{a}:
      +n = Compactor.bytes(a)
      {bl == n : Nat} & {Nat.is_lt(node, n) == True{} : Bool}

# the best reply's length after the replies ps
def lp.bl(ps: List<&2, C.Reply>, bl: Nat) -> Nat:
  match ps:
    case Nil{}:
      bl
    case r <> rest:
      match r:
        case C.Erred{}:
          lp.bl(rest, bl)
        case C.Says{ws}:
          lp.bl(rest, C.Text.len(ws))

# k more calls
def lp.plus(x: C.Line, k: Nat) -> C.Line:
  match x:
    case C.Line{c, l}:
      C.Line{Nat.add(k, c), l}

def lp.plus_zero(x: C.Line) -> {x == lp.plus(x, 0n) : C.Line}:
  match x:
    case C.Line{c, l}:
      {==}

def lp.more_plus(x: C.Line, -k: Nat) -> {C.Line.more(lp.plus(x, k)) == lp.plus(x, 1n+k) : C.Line}:
  match x:
    case C.Line{c, l}:
      {==}

def lp.add_one(k: Nat) -> {Nat.add(k, 1n) == 1n+k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %lp.add_one(p) : {1n+Nat.add(p, 1n) == 1n+_ : Nat}
      {==}

def lp.add_zero(k: Nat) -> {Nat.add(k, 0n) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %lp.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# a line that ends at its next call, after k calls before it
def lp.plus_one(x: C.Line, +l: Maybe<&2, List<&2, C.W>>, +k: Nat, e: {x == C.Line{1n, l} : C.Line}) -> {lp.plus(x, k) == C.Line{1n+k, l} : C.Line}:
  %Equal.sym(C.Line, x, C.Line{1n, l}, e) : {lp.plus(_, k) == C.Line{1n+k, l} : C.Line}
  %lp.add_one(k) : {C.Line{Nat.add(k, 1n), l} == C.Line{_, l} : C.Line}
  {==}

# a reply past the node, shorter than the best: the line asks again
def lp.next(fit: Bool, less: Bool, -ws: List<&2, C.W>, -node: Nat, -b: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>, -rec: C.Line, ef: {fit == False{} : Bool}, el: {less == True{} : Bool}) -> {C.line.next(fit, less, ws, node, b, input, rec) == C.Line.more(rec) : C.Line}:
  match fit less:
    case True{} y:
      LLogicLogic.pc.absurd_tf({C.line.next(True{}, y, ws, node, b, input, rec) == C.Line.more(rec) : C.Line}, ef)
    case False{} False{}:
      LLogicLogic.pc.absurd_ft({C.line.next(False{}, False{}, ws, node, b, input, rec) == C.Line.more(rec) : C.Line}, el)
    case False{} True{}:
      {==}

# a text past the node does not fit it
def lp.over(+node: Nat, +t: List<&2, C.W>, e: {Nat.is_lt(node, Compactor.bytes(t)) == True{} : Bool}) -> {Nat.is_le(C.Text.len(t), node) == False{} : Bool}:
  %Equal.sym(Nat, C.Text.len(t), Compactor.bytes(t), lp.len(t)) : {Nat.is_le(_, node) == False{} : Bool}
  LNat.pc.lt_not_le(node, Compactor.bytes(t), e)

# a reply below the best reply is shorter than it
def lp.less(-node: Nat, b: Maybe<&2, List<&2, C.W>>, +bl: Nat, +t: List<&2, C.W>, lk: lp.Lk(node, b, bl), e: {Compactor.below(b, Compactor.bytes(t)) == True{} : Bool}) -> {C.shorter(C.Text.len(t), b, bl) == True{} : Bool}:
  match b:
    case None{}:
      {==}
    case Some{+a}:
      (eb, eo) = lk
      %Equal.sym(Nat, bl, Compactor.bytes(a), eb) : {Nat.is_lt(C.Text.len(t), _) == True{} : Bool}
      %Equal.sym(Nat, C.Text.len(t), Compactor.bytes(t), lp.len(t)) : {Nat.is_lt(_, Compactor.bytes(a)) == True{} : Bool}
      e

# no reply past the node is empty
def lp.empty(-G: Type, +node: Nat, +b: Maybe<&2, List<&2, C.W>>, -more: List<&2, C.Reply>, go: {Compactor.asks(C.Says{Nil{}} <> more, node, b) == True{} : Bool}) -> G:
  +e1 = LLogicBool.wr_and_l(Bool.and(Nat.is_lt(node, 0n), Compactor.below(b, 0n)), Compactor.asks(more, node, Some{Nil{}}), go)
  +e2 = LLogicBool.wr_and_l(Nat.is_lt(node, 0n), Compactor.below(b, 0n), e1)
  LLogicLogic.pc.absurd_ft(G, Equal.trans(Bool, False{}, Nat.is_lt(node, 0n), True{}, LNat.pu.lt_zero_f(node), e2))

def lp.go(ps: List<&2, C.Reply>, +T: Nat, +node: Nat, +b: Maybe<&2, List<&2, C.W>>, +bl: Nat, +rest: List<&2, C.Reply>, +input: List<&2, C.W>, lk: lp.Lk(node, b, bl), +go: {Compactor.asks(ps, node, b) == True{} : Bool}) -> {C.line.go(Nat.add(List.length(&2, C.Reply, ps), T), node, b, bl, List.append(&2, C.Reply, ps, rest), input) == lp.plus(C.line.go(T, node, Compactor.last_said(ps, b), lp.bl(ps, bl), rest, input), List.length(&2, C.Reply, ps)) : C.Line}:
  match ps:
    case Nil{}:
      lp.plus_zero(C.line.go(T, node, b, bl, rest, input))
    case r <> +more:
      match r:
        case C.Erred{}:
          LLogicLogic.pc.absurd_ft({C.line.go(Nat.add(1n+List.length(&2, C.Reply, more), T), node, b, bl, C.Erred{} <> List.append(&2, C.Reply, more, rest), input) == lp.plus(C.line.go(T, node, Compactor.last_said(more, b), lp.bl(more, bl), rest, input), 1n+List.length(&2, C.Reply, more)) : C.Line}, go)
        case C.Says{ws}:
          match ws:
            case Nil{}:
              lp.empty({C.line.go(Nat.add(1n+List.length(&2, C.Reply, more), T), node, b, bl, C.Says{Nil{}} <> List.append(&2, C.Reply, more, rest), input) == lp.plus(C.line.go(T, node, Compactor.last_said(more, Some{Nil{}}), lp.bl(more, C.Text.len(Nil{})), rest, input), 1n+List.length(&2, C.Reply, more)) : C.Line}, node, b, more, go)
            case +w <> +t:
              +k = List.length(&2, C.Reply, more)
              +n = Compactor.bytes(w <> t)
              +g1 = LLogicBool.wr_and_l(Bool.and(Nat.is_lt(node, n), Compactor.below(b, n)), Compactor.asks(more, node, Some{w <> t}), go)
              +eo = LLogicBool.wr_and_l(Nat.is_lt(node, n), Compactor.below(b, n), g1)
              +eb = LLogicBool.wr_and_r(Nat.is_lt(node, n), Compactor.below(b, n), g1)
              +ga = LLogicBool.wr_and_r(Bool.and(Nat.is_lt(node, n), Compactor.below(b, n)), Compactor.asks(more, node, Some{w <> t}), go)
              +X = C.line.go(T, node, Compactor.last_said(more, Some{w <> t}), lp.bl(more, C.Text.len(w <> t)), rest, input)
              +rec = C.line.go(Nat.add(k, T), node, Some{w <> t}, C.Text.len(w <> t), List.append(&2, C.Reply, more, rest), input)
              +ih = lp.go(more, T, node, Some{w <> t}, C.Text.len(w <> t), rest, input, (lp.len(w <> t), eo), ga)
              Equal.trans(C.Line, C.line.next(Nat.is_le(C.Text.len(w <> t), node), C.shorter(C.Text.len(w <> t), b, bl), w <> t, node, b, input, rec), C.Line.more(rec), lp.plus(X, 1n+k),
                lp.next(Nat.is_le(C.Text.len(w <> t), node), C.shorter(C.Text.len(w <> t), b, bl), w <> t, node, b, input, rec, lp.over(node, w <> t, eo), lp.less(node, b, bl, w <> t, lk, eb)),
                Equal.trans(C.Line, C.Line.more(rec), C.Line.more(lp.plus(X, k)), lp.plus(X, 1n+k), Equal.cong(C.Line, C.Line, z => C.Line.more(z), rec, lp.plus(X, k), ih), lp.more_plus(X, k)))

# after the replies, the best reply the line holds is still past the
# node, its length its bytes
def lp.lk(ps: List<&2, C.Reply>, +node: Nat, +b: Maybe<&2, List<&2, C.W>>, +bl: Nat, lk: lp.Lk(node, b, bl), +go: {Compactor.asks(ps, node, b) == True{} : Bool}) -> lp.Lk(node, Compactor.last_said(ps, b), lp.bl(ps, bl)):
  match ps:
    case Nil{}:
      lk
    case r <> +more:
      match r:
        case C.Erred{}:
          LLogicLogic.pc.absurd_ft(lp.Lk(node, Compactor.last_said(more, b), lp.bl(more, bl)), go)
        case C.Says{ws}:
          match ws:
            case Nil{}:
              lp.empty(lp.Lk(node, Compactor.last_said(more, Some{Nil{}}), lp.bl(more, C.Text.len(Nil{}))), node, b, more, go)
            case +w <> +t:
              +n = Compactor.bytes(w <> t)
              +g1 = LLogicBool.wr_and_l(Bool.and(Nat.is_lt(node, n), Compactor.below(b, n)), Compactor.asks(more, node, Some{w <> t}), go)
              +eo = LLogicBool.wr_and_l(Nat.is_lt(node, n), Compactor.below(b, n), g1)
              +ga = LLogicBool.wr_and_r(Bool.and(Nat.is_lt(node, n), Compactor.below(b, n)), Compactor.asks(more, node, Some{w <> t}), go)
              lp.lk(more, node, Some{w <> t}, C.Text.len(w <> t), (lp.len(w <> t), eo), ga)

# a line with no tries left after the replies ends with the best one, else
# the input, cut
def lp.end(+node: Nat, b: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>) -> {C.line.end(node, b, input) == C.cut(Compactor.or_input(b, input), node) : List<&2, C.W>}:
  match b:
    case None{}:
      {==}
    case Some{a}:
      {==}
