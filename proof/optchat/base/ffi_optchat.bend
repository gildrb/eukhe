# eukhe: lemmas the proofs of area optchat share: the stepper entry
# bend/ffi_optchat.bend
#
# The entry spells nodes as the laws do (oe.nodes); a wait answers the
# laws' held nodes (oe.held); each whole request runs as the laws' model
# asks (oe.serve). The entry reads every input as the laws' reader does
# (oe.read), and the laws' reader reads every spelled request that fits
# the wire back (oe.spelled).

import Base
import ../../../bend/wire.bend as Wr
import ../../../bend/ffi_optchat.bend as FOc
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/state.bend as OState
import ../../../bend/optchat/step.bend as OStep
import ../../../bend/optchat/queue.bend as OQueue
import ../../../bend/optchat/ctx.bend as OCtx
import ../../../laws/optchat.bend as Optchat
import ../../../laws/base.bend as LawsBase
import ../../base/wire.bend as LWire
import ../../base/logic/bool.bend as LLogicBool

# Logic
# -----

def oe.MD(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def oe.none_some(-A: Data, -G: Type, -r: A, h: {None{} == Some{r} : Maybe<&2, A>}) -> G:
  %h : oe.MD(A, _, G)
  Unit{}

def oe.get(-A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def oe.some_inj(-A: Data, +a: A, +b: A, h: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => oe.get(A, m, a), Some{a}, Some{b}, h)

def oe.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  LLogicBool.wr_and_l(a, b, e)

def oe.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  LLogicBool.wr_and_r(a, b, e)

# The replies
# -----------

def oe.node(n: ONode.Node, -rest: String) -> {Optchat.oc_spell_node(n, rest) == FOc.put_node(n, rest) : String}:
  match n:
    case ONode.Node{l, i}:
      {==}

def oe.items(ns: List<&2, ONode.Node>, -rest: String) -> {Wr.put_list.go(~ONode.Node, ~FOc.put_node, ns, rest) == (List.length(&2, ONode.Node, ns), Optchat.oc_spell_nodes.items(ns, rest)) : Nat & String}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~ONode.Node, ~FOc.put_node, t, rest), (List.length(&2, ONode.Node, t), Optchat.oc_spell_nodes.items(t, rest)), oe.items(t, rest)) : {Wr.put_list.step(~ONode.Node, ~FOc.put_node, n, _) == (1n+List.length(&2, ONode.Node, t), Optchat.oc_spell_node(n, Optchat.oc_spell_nodes.items(t, rest))) : Nat & String}
      %oe.node(n, Optchat.oc_spell_nodes.items(t, rest)) : {(1n+List.length(&2, ONode.Node, t), _) == (1n+List.length(&2, ONode.Node, t), Optchat.oc_spell_node(n, Optchat.oc_spell_nodes.items(t, rest))) : Nat & String}
      {==}

# the entry spells nodes as the laws do
def oe.nodes(+ns: List<&2, ONode.Node>, -rest: String) -> {FOc.put_nodes(ns, rest) == Optchat.oc_spell_nodes(ns, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~ONode.Node, ~FOc.put_node, ns, rest), (List.length(&2, ONode.Node, ns), Optchat.oc_spell_nodes.items(ns, rest)), oe.items(ns, rest)) : {Wr.put_list.fin(_) == Optchat.oc_spell_nodes(ns, rest) : String}
  {==}

def oe.keep(k: Bool, -h: ONode.Node, -t: List<&2, ONode.Node>) -> {ONode.Nodes.keep(k, h, t) == Optchat.oc_held.pick(k, h, t) : List<&2, ONode.Node>}:
  match k:
    case True{}:
      {==}
    case False{}:
      {==}

def oe.held_go(+info: OInfo.Info, +v: List<&2, ONode.Node>, bs: List<&2, ONode.Node>) -> {OQueue.busy.held(info, v, bs) == Optchat.oc_held(info, v, bs) : List<&2, ONode.Node>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      +k = Bool.not(Bool.and(ONode.Nodes.has(v, b), Bool.not(OInfo.Info.built(info, b))))
      %oe.held_go(info, v, rest) : {ONode.Nodes.keep(k, b, OQueue.busy.held(info, v, rest)) == Optchat.oc_held.pick(k, b, _) : List<&2, ONode.Node>}
      oe.keep(k, b, OQueue.busy.held(info, v, rest))

# a wait answers the laws' held nodes
def oe.held(s: OState.St) -> {Optchat.oc_held(OState.St.info(s), OState.St.view(s), OState.St.busy(s)) == OQueue.St.held(s) : List<&2, ONode.Node>}:
  match s:
    case OState.St{t, +info, +view, shrink, cview, ready, busy}:
      Equal.sym(List<&2, ONode.Node>, OQueue.busy.held(info, view, busy), Optchat.oc_held(info, view, busy), oe.held_go(info, view, busy))

# a batch's reply, as the laws spell it
def oe.answer(grow: Bool, +merged: List<&2, ONode.Node>, +s: OState.St) -> {FOc.msg.answer(grow, merged, s) == Optchat.oc_spell_batch(grow, merged, s) : String}:
  match grow:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(String, FOc.put_nodes(OState.St.view(s), Wr.put_bool(OState.St.shrink(s), "")), Optchat.oc_spell_nodes(OState.St.view(s), Wr.put_bool(OState.St.shrink(s), "")), oe.nodes(OState.St.view(s), Wr.put_bool(OState.St.shrink(s), ""))) : {Wr.put_nat(1n, FOc.put_nodes(merged, _)) == Optchat.oc_spell_batch(True{}, merged, s) : String}
      %Equal.sym(String, FOc.put_nodes(merged, Optchat.oc_spell_nodes(OState.St.view(s), Wr.put_bool(OState.St.shrink(s), ""))), Optchat.oc_spell_nodes(merged, Optchat.oc_spell_nodes(OState.St.view(s), Wr.put_bool(OState.St.shrink(s), ""))), oe.nodes(merged, Optchat.oc_spell_nodes(OState.St.view(s), Wr.put_bool(OState.St.shrink(s), "")))) : {Wr.put_nat(1n, _) == Optchat.oc_spell_batch(True{}, merged, s) : String}
      {==}

def oe.msg(+grow: Bool, r: OState.St & List<&2, ONode.Node>, +cfg: OState.Cfg) -> {FOc.msg.reply(grow, r, cfg) == (FOc.Live{cfg, Pair.fst(OState.St, List<&2, ONode.Node>, r)}, Optchat.oc_spell_batch(grow, Pair.snd(OState.St, List<&2, ONode.Node>, r), Pair.fst(OState.St, List<&2, ONode.Node>, r))) : FOc.St & String}:
  (s, merged) = r
  +s1 = s
  +m1 = merged
  Equal.cong(String, FOc.St & String, x => (FOc.Live{cfg, s1}, x), FOc.msg.answer(grow, m1, s1), Optchat.oc_spell_batch(grow, m1, s1), oe.answer(grow, m1, s1))

def oe.done(+cfg: OState.Cfg, r: OState.St & List<&2, ONode.Node>) -> {FOc.done(cfg, r) == (FOc.Live{cfg, Pair.fst(OState.St, List<&2, ONode.Node>, r)}, Wr.put_nat(0n, "")) : FOc.St & String}:
  (s, merged) = r
  {==}

def oe.query(+cfg: OState.Cfg, +s: OState.St, +ns: List<&2, ONode.Node>) -> {(FOc.Live{cfg, s}, FOc.put_nodes(ns, "")) == (FOc.Live{cfg, s}, Optchat.oc_spell_nodes(ns, "")) : FOc.St & String}:
  Equal.cong(String, FOc.St & String, x => (FOc.Live{cfg, s}, x), FOc.put_nodes(ns, ""), Optchat.oc_spell_nodes(ns, ""), oe.nodes(ns, ""))

# a whole request runs as the laws' model asks
def oe.serve(+cfg: OState.Cfg, +s: OState.St, q: FOc.Q) -> {FOc.serve(cfg, s, q) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, q)}, Optchat.oc_reply(cfg, s, q)) : FOc.St & String}:
  match q:
    case FOc.QMsg{}:
      oe.msg(OStep.St.batch(cfg, s), OStep.msg(cfg, s), cfg)
    case FOc.QBuilt{+l, +k, +z}:
      oe.done(cfg, OStep.step(cfg, s, OState.Build{Optchat.oc_node(l, k), z}))
    case FOc.QStart{+l, +k}:
      oe.done(cfg, OStep.step(cfg, s, OState.Start{Optchat.oc_node(l, k)}))
    case FOc.QFree{+l, +k}:
      oe.done(cfg, OStep.step(cfg, s, OState.Free{Optchat.oc_node(l, k)}))
    case FOc.QWait{}:
      %oe.held(s) : {(FOc.Live{cfg, OQueue.St.wait(s)}, FOc.put_nodes(_, "")) == (FOc.Live{cfg, OQueue.St.wait(s)}, Optchat.oc_spell_nodes(Optchat.oc_held(OState.St.info(s), OState.St.view(s), OState.St.busy(s)), "")) : FOc.St & String}
      oe.query(cfg, OQueue.St.wait(s), Optchat.oc_held(OState.St.info(s), OState.St.view(s), OState.St.busy(s)))
    case FOc.QCands{}:
      oe.query(cfg, s, OQueue.cands(cfg, s))
    case FOc.QNeed{}:
      oe.query(cfg, s, OQueue.cands.need(cfg, s))
    case FOc.QCtx{+l, +k}:
      oe.query(cfg, s, OCtx.ctx(s, Optchat.oc_node(l, k)))
    case FOc.QBusy{}:
      {==}

# The entry reads as the laws' reader
# ------------------------------------

def oe.k(l: Nat, r: Wr.Dec<Nat>) -> {Optchat.oc_read.k(l, r) == FOc.get_line.k(l, r) : Wr.Dec<FOc.Line>}:
  match r:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def oe.l(r: Wr.Dec<Nat>) -> {Optchat.oc_read.l(r) == FOc.get_line.l(r) : Wr.Dec<FOc.Line>}:
  match r:
    case Wr.Got{l, s}:
      oe.k(l, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# turned around: rewrites the laws' read into the entry's
def oe.line(+s: String) -> {FOc.get_line(s) == Optchat.oc_read.line(s) : Wr.Dec<FOc.Line>}:
  Equal.sym(Wr.Dec<FOc.Line>, Optchat.oc_read.line(s), FOc.get_line(s), oe.l(Wr.get_nat(s)))

def oe.size(n: FOc.Line, r: Wr.Dec<Nat>) -> {Optchat.oc_read.size(n, r) == FOc.get_got.size(n, r) : Wr.Dec<FOc.Got>}:
  match n r:
    case FOc.Line{l, k} Wr.Got{z, s}:
      {==}
    case FOc.Line{l, k} Wr.Bad{}:
      {==}

def oe.got_node(r: Wr.Dec<FOc.Line>) -> {Optchat.oc_read.got.node(r) == FOc.get_got.node(r) : Wr.Dec<FOc.Got>}:
  match r:
    case Wr.Got{n, s}:
      oe.size(n, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def oe.got_eq(+s: String) -> {Optchat.oc_read.got(s) == FOc.get_got(s) : Wr.Dec<FOc.Got>}:
  %oe.line(s) : {Optchat.oc_read.got.node(_) == FOc.get_got(s) : Wr.Dec<FOc.Got>}
  oe.got_node(FOc.get_line(s))

# turned around: rewrites the laws' read into the entry's
def oe.got(+s: String) -> {FOc.get_got(s) == Optchat.oc_read.got(s) : Wr.Dec<FOc.Got>}:
  Equal.sym(Wr.Dec<FOc.Got>, Optchat.oc_read.got(s), FOc.get_got(s), oe.got_eq(s))

def oe.built(r: Wr.Dec<FOc.Got>) -> {Optchat.oc_read.built(r) == FOc.get_ev.built(r) : Wr.Dec<FOc.Q>}:
  match r:
    case Wr.Got{g, s}:
      match g:
        case FOc.Got{l, k, z}:
          {==}
    case Wr.Bad{}:
      {==}

def oe.start(r: Wr.Dec<FOc.Line>) -> {Optchat.oc_read.start(r) == FOc.get_ev.start(r) : Wr.Dec<FOc.Q>}:
  match r:
    case Wr.Got{n, s}:
      match n:
        case FOc.Line{l, k}:
          {==}
    case Wr.Bad{}:
      {==}

def oe.free(r: Wr.Dec<FOc.Line>) -> {Optchat.oc_read.free(r) == FOc.get_ev.free(r) : Wr.Dec<FOc.Q>}:
  match r:
    case Wr.Got{n, s}:
      match n:
        case FOc.Line{l, k}:
          {==}
    case Wr.Bad{}:
      {==}

def oe.ctx(r: Wr.Dec<FOc.Line>) -> {Optchat.oc_read.ctx(r) == FOc.get_ev.ctx(r) : Wr.Dec<FOc.Q>}:
  match r:
    case Wr.Got{n, s}:
      match n:
        case FOc.Line{l, k}:
          {==}
    case Wr.Bad{}:
      {==}

def oe.tag(n: Nat, +s: String) -> {Optchat.oc_read.tag(n, s) == FOc.get_ev.tag(n, s) : Wr.Dec<FOc.Q>}:
  match n:
    case 0n:
      {==}
    case 1n:
      %oe.got(s) : {Optchat.oc_read.built(_) == FOc.get_ev.built(FOc.get_got(s)) : Wr.Dec<FOc.Q>}
      oe.built(FOc.get_got(s))
    case 2n:
      %oe.line(s) : {Optchat.oc_read.start(_) == FOc.get_ev.start(FOc.get_line(s)) : Wr.Dec<FOc.Q>}
      oe.start(FOc.get_line(s))
    case 3n:
      %oe.line(s) : {Optchat.oc_read.free(_) == FOc.get_ev.free(FOc.get_line(s)) : Wr.Dec<FOc.Q>}
      oe.free(FOc.get_line(s))
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      %oe.line(s) : {Optchat.oc_read.ctx(_) == FOc.get_ev.ctx(FOc.get_line(s)) : Wr.Dec<FOc.Q>}
      oe.ctx(FOc.get_line(s))
    case 8n:
      {==}
    case 9n+p:
      {==}

# the entry reads every request as the laws' reader does
def oe.read(r: Wr.Dec<Nat>) -> {Optchat.oc_read.go(r) == FOc.get_ev.go(r) : Wr.Dec<FOc.Q>}:
  match r:
    case Wr.Got{n, s}:
      oe.tag(n, s)
    case Wr.Bad{}:
      {==}

# A whole request
# ---------------

# a request the laws' reader reads whole runs as the model asks
def oe.whole(+cfg: OState.Cfg, +s: OState.St, d: Wr.Dec<FOc.Q>, +q: FOc.Q, got: {Optchat.oc_read.whole(d) == Some{q} : Maybe<&2, FOc.Q>}) -> {FOc.step.ev(cfg, s, d) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, q)}, Optchat.oc_reply(cfg, s, q)) : FOc.St & String}:
  match d:
    case Wr.Got{+x, rest}:
      match rest:
        case SNil{}:
          %oe.some_inj(FOc.Q, x, q, got) : {FOc.serve(cfg, s, x) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, _)}, Optchat.oc_reply(cfg, s, _)) : FOc.St & String}
          oe.serve(cfg, s, x)
        case SCon{h, t}:
          oe.none_some(FOc.Q, {(FOc.Live{cfg, s}, FOc.fail()) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, q)}, Optchat.oc_reply(cfg, s, q)) : FOc.St & String}, q, got)
    case Wr.Bad{}:
      oe.none_some(FOc.Q, {(FOc.Live{cfg, s}, FOc.fail()) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, q)}, Optchat.oc_reply(cfg, s, q)) : FOc.St & String}, q, got)

# a request the laws' reader does not read whole keeps the chat
def oe.no(+cfg: OState.Cfg, +s: OState.St, d: Wr.Dec<FOc.Q>, no: {Optchat.oc_read.whole(d) == None{} : Maybe<&2, FOc.Q>}) -> {FOc.step.ev(cfg, s, d) == (FOc.Live{cfg, s}, SCon{'E', SCon{' ', "optchat: malformed event"}}) : FOc.St & String}:
  match d:
    case Wr.Got{x, rest}:
      match rest:
        case SNil{}:
          oe.none_some(FOc.Q, {FOc.step.end(True{}, cfg, s, x) == (FOc.Live{cfg, s}, SCon{'E', SCon{' ', "optchat: malformed event"}}) : FOc.St & String}, x, Equal.sym(Maybe<&2, FOc.Q>, Some{x}, None{}, no))
        case SCon{h, t}:
          {==}
    case Wr.Bad{}:
      {==}

# Spelled requests read back
# --------------------------

# a node that fits reads back
def oe.lk(+l: Nat, +k: Nat, +rest: String, fl: {LawsBase.wire_fits(l) == True{} : Bool}, fk: {LawsBase.wire_fits(k) == True{} : Bool}) -> {Wr.Got{FOc.Line{l, k}, rest} == Optchat.oc_read.line(Optchat.oc_spell_lk(l, k, rest)) : Wr.Dec<FOc.Line>}:
  %LWire.pc.nat(l, Wr.put_nat(k, rest), fl) : {Wr.Got{FOc.Line{l, k}, rest} == Optchat.oc_read.l(_) : Wr.Dec<FOc.Line>}
  %LWire.pc.nat(k, rest, fk) : {Wr.Got{FOc.Line{l, k}, rest} == Optchat.oc_read.k(l, _) : Wr.Dec<FOc.Line>}
  {==}

# a built node that fits reads back
def oe.lkz(+l: Nat, +k: Nat, +z: Nat, +rest: String, +f: {Bool.and(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(z))) == True{} : Bool}) -> {Wr.Got{FOc.Got{l, k, z}, rest} == Optchat.oc_read.got(Optchat.oc_spell_lk(l, k, Wr.put_nat(z, rest))) : Wr.Dec<FOc.Got>}:
  +fkz = oe.and_r(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(z)), f)
  %oe.lk(l, k, Wr.put_nat(z, rest), oe.and_l(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(z)), f), oe.and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(z), fkz)) : {Wr.Got{FOc.Got{l, k, z}, rest} == Optchat.oc_read.got.node(_) : Wr.Dec<FOc.Got>}
  %LWire.pc.nat(z, rest, oe.and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(z), fkz)) : {Wr.Got{FOc.Got{l, k, z}, rest} == Optchat.oc_read.size(FOc.Line{l, k}, _) : Wr.Dec<FOc.Got>}
  {==}

def oe.lk_and(+l: Nat, +k: Nat, +rest: String, +f: {Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(k)) == True{} : Bool}) -> {Wr.Got{FOc.Line{l, k}, rest} == Optchat.oc_read.line(Optchat.oc_spell_lk(l, k, rest)) : Wr.Dec<FOc.Line>}:
  oe.lk(l, k, rest, oe.and_l(LawsBase.wire_fits(l), LawsBase.wire_fits(k), f), oe.and_r(LawsBase.wire_fits(l), LawsBase.wire_fits(k), f))

# every request that fits the wire, spelled, reads back whole
def oe.spelled(q: FOc.Q, +fits: {Optchat.oc_fits(q) == True{} : Bool}) -> {Optchat.oc_read(Optchat.oc_spell(q)) == Some{q} : Maybe<&2, FOc.Q>}:
  match q:
    case FOc.QMsg{}:
      {==}
    case FOc.QBuilt{+l, +k, +z}:
      %oe.lkz(l, k, z, "", fits) : {Optchat.oc_read.whole(Optchat.oc_read.built(_)) == Some{FOc.QBuilt{l, k, z}} : Maybe<&2, FOc.Q>}
      {==}
    case FOc.QStart{+l, +k}:
      %oe.lk_and(l, k, "", fits) : {Optchat.oc_read.whole(Optchat.oc_read.start(_)) == Some{FOc.QStart{l, k}} : Maybe<&2, FOc.Q>}
      {==}
    case FOc.QFree{+l, +k}:
      %oe.lk_and(l, k, "", fits) : {Optchat.oc_read.whole(Optchat.oc_read.free(_)) == Some{FOc.QFree{l, k}} : Maybe<&2, FOc.Q>}
      {==}
    case FOc.QWait{}:
      {==}
    case FOc.QCands{}:
      {==}
    case FOc.QNeed{}:
      {==}
    case FOc.QCtx{+l, +k}:
      %oe.lk_and(l, k, "", fits) : {Optchat.oc_read.whole(Optchat.oc_read.ctx(_)) == Some{FOc.QCtx{l, k}} : Maybe<&2, FOc.Q>}
      {==}
    case FOc.QBusy{}:
      {==}

# a request that fits the wire, spelled, runs as the model asks
def oe.answers(+cfg: OState.Cfg, +s: OState.St, +q: FOc.Q, +fits: {Optchat.oc_fits(q) == True{} : Bool}) -> {FOc.step(FOc.Live{cfg, s}, Optchat.oc_spell(q)) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, q)}, Optchat.oc_reply(cfg, s, q)) : FOc.St & String}:
  %oe.read(Wr.get_nat(Optchat.oc_spell(q))) : {FOc.step.ev(cfg, s, _) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, q)}, Optchat.oc_reply(cfg, s, q)) : FOc.St & String}
  oe.whole(cfg, s, Optchat.oc_read.go(Wr.get_nat(Optchat.oc_spell(q))), q, oe.spelled(q, fits))
