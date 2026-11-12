# eukhe: lemmas the proofs of area optchat share: the stepper entry
# bend/ffi_optchat.bend
#
# The entry spells nodes as the laws do (oe.nodes); each whole request
# runs as the laws' model asks (oe.serve); the entry reads every spelled
# request that fits the wire back whole (oe.spelled), so it answers it as
# the model does (oe.answers).

import Base
import ../../../bend/wire.bend as Wr
import ../../../bend/ffi_optchat.bend as FOc
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/state.bend as OState
import ../../../bend/optchat/step.bend as OStep
import ../../../bend/optchat/queue.bend as OQueue
import ../../../bend/optchat/ctx.bend as OCtx
import ../../../spec/memory/optchat.bend as S
import ../../../laws/optchat.bend as Optchat
import ../../../laws/base.bend as LawsBase
import ../../base/wire.bend as LWire
import ../../base/logic/bool.bend as LLogicBool
import ./batch.bend as LB

# Logic
# -----

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
      %LB.ob.batch(cfg, s) : {FOc.serve(cfg, s, FOc.QMsg{}) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, FOc.QMsg{})}, Optchat.oc_spell_batch(_, Pair.snd(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, OState.Msg{})), Pair.fst(OState.St, List<&2, ONode.Node>, OStep.step(cfg, s, OState.Msg{})))) : FOc.St & String}
      oe.msg(OStep.St.batch(cfg, s), OStep.msg(cfg, s), cfg)
    case FOc.QBuilt{+l, +k, +z}:
      oe.done(cfg, OStep.step(cfg, s, OState.Build{Optchat.oc_node(l, k), z}))
    case FOc.QStart{+l, +k}:
      oe.done(cfg, OStep.step(cfg, s, OState.Start{Optchat.oc_node(l, k)}))
    case FOc.QFree{+l, +k}:
      oe.done(cfg, OStep.step(cfg, s, OState.Free{Optchat.oc_node(l, k)}))
    case FOc.QWait{}:
      oe.query(cfg, OQueue.St.wait(s), OQueue.St.held(s))
    case FOc.QCands{+d}:
      oe.query(cfg, s, OQueue.cands.due(cfg, s, d))
    case FOc.QNeed{+d}:
      oe.query(cfg, s, OQueue.cands.need.due(cfg, s, d))
    case FOc.QCtx{+l, +k}:
      oe.query(cfg, s, OCtx.ctx(s, Optchat.oc_node(l, k)))
    case FOc.QBusy{}:
      {==}

# Spelled requests read back
# --------------------------

# a node that fits reads back
def oe.lk(+l: Nat, +k: Nat, +rest: String, fl: {LawsBase.wire_fits(l) == True{} : Bool}, fk: {LawsBase.wire_fits(k) == True{} : Bool}) -> {Wr.Got{FOc.Line{l, k}, rest} == FOc.get_line(Optchat.oc_spell_lk(l, k, rest)) : Wr.Dec<FOc.Line>}:
  %LWire.pc.nat(l, Wr.put_nat(k, rest), fl) : {Wr.Got{FOc.Line{l, k}, rest} == FOc.get_line.l(_) : Wr.Dec<FOc.Line>}
  %LWire.pc.nat(k, rest, fk) : {Wr.Got{FOc.Line{l, k}, rest} == FOc.get_line.k(l, _) : Wr.Dec<FOc.Line>}
  {==}

# a built node that fits reads back
def oe.lkz(+l: Nat, +k: Nat, +z: Nat, +rest: String, +f: {Bool.and(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(z))) == True{} : Bool}) -> {Wr.Got{FOc.Got{l, k, z}, rest} == FOc.get_got(Optchat.oc_spell_lk(l, k, Wr.put_nat(z, rest))) : Wr.Dec<FOc.Got>}:
  +fkz = oe.and_r(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(z)), f)
  %oe.lk(l, k, Wr.put_nat(z, rest), oe.and_l(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(z)), f), oe.and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(z), fkz)) : {Wr.Got{FOc.Got{l, k, z}, rest} == FOc.get_got.node(_) : Wr.Dec<FOc.Got>}
  %LWire.pc.nat(z, rest, oe.and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(z), fkz)) : {Wr.Got{FOc.Got{l, k, z}, rest} == FOc.get_got.size(FOc.Line{l, k}, _) : Wr.Dec<FOc.Got>}
  {==}

def oe.lk_and(+l: Nat, +k: Nat, +rest: String, +f: {Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(k)) == True{} : Bool}) -> {Wr.Got{FOc.Line{l, k}, rest} == FOc.get_line(Optchat.oc_spell_lk(l, k, rest)) : Wr.Dec<FOc.Line>}:
  oe.lk(l, k, rest, oe.and_l(LawsBase.wire_fits(l), LawsBase.wire_fits(k), f), oe.and_r(LawsBase.wire_fits(l), LawsBase.wire_fits(k), f))

# every request that fits the wire, spelled, reads back whole
def oe.spelled(q: FOc.Q, +fits: {Optchat.oc_fits(q) == True{} : Bool}) -> {FOc.get_ev(Optchat.oc_spell(q)) == Wr.Got{q, ""} : Wr.Dec<FOc.Q>}:
  match q:
    case FOc.QMsg{}:
      {==}
    case FOc.QBuilt{+l, +k, +z}:
      %oe.lkz(l, k, z, "", fits) : {FOc.get_ev.built(_) == Wr.Got{FOc.QBuilt{l, k, z}, ""} : Wr.Dec<FOc.Q>}
      {==}
    case FOc.QStart{+l, +k}:
      %oe.lk_and(l, k, "", fits) : {FOc.get_ev.start(_) == Wr.Got{FOc.QStart{l, k}, ""} : Wr.Dec<FOc.Q>}
      {==}
    case FOc.QFree{+l, +k}:
      %oe.lk_and(l, k, "", fits) : {FOc.get_ev.free(_) == Wr.Got{FOc.QFree{l, k}, ""} : Wr.Dec<FOc.Q>}
      {==}
    case FOc.QWait{}:
      {==}
    case FOc.QCands{+d}:
      %LWire.pc.nat(d, "", fits) : {FOc.get_ev.due(True{}, _) == Wr.Got{FOc.QCands{d}, ""} : Wr.Dec<FOc.Q>}
      {==}
    case FOc.QNeed{+d}:
      %LWire.pc.nat(d, "", fits) : {FOc.get_ev.due(False{}, _) == Wr.Got{FOc.QNeed{d}, ""} : Wr.Dec<FOc.Q>}
      {==}
    case FOc.QCtx{+l, +k}:
      %oe.lk_and(l, k, "", fits) : {FOc.get_ev.ctx(_) == Wr.Got{FOc.QCtx{l, k}, ""} : Wr.Dec<FOc.Q>}
      {==}
    case FOc.QBusy{}:
      {==}

# a request that fits the wire, spelled, runs as the model asks
def oe.answers(+cfg: OState.Cfg, +s: OState.St, +q: FOc.Q, +fits: {Optchat.oc_fits(q) == True{} : Bool}) -> {FOc.step(FOc.Live{cfg, s}, Optchat.oc_spell(q)) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, q)}, Optchat.oc_reply(cfg, s, q)) : FOc.St & String}:
  %Equal.sym(Wr.Dec<FOc.Q>, FOc.get_ev(Optchat.oc_spell(q)), Wr.Got{q, ""}, oe.spelled(q, fits)) : {FOc.step.ev(cfg, s, _) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, q)}, Optchat.oc_reply(cfg, s, q)) : FOc.St & String}
  oe.serve(cfg, s, q)
