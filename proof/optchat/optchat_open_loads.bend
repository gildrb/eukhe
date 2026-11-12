# eukhe: the proof of LAW optchat_open_loads
# A spelled open that fits the wire opens the model's open (LAO.oo.opened).
# Its T is the open's in canonical bits (LAB.ob.val_of, LAB.ob.canon_of);
# its sizes are filed one built node after another into the map, so a
# node reads the last copy's size (ol.info: a set reads back at its key,
# LQ.oq.lv, and two wire indices name one key exactly when they are equal,
# ol.bs_of); no call runs. With no missed batch the view and shrink are
# the open's; with one, the view is the open's fitted down to floor
# (LAC.ch.fit) and shrink is the size test; the compaction view is the
# view fitted down to cfloor (LAC.ch.fitted).

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_optchat.bend as FOc
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/state.bend as OState
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat.bend as Optchat
import ../base/nat.bend as LNat
import ./base/step.bend as LA
import ./base/bits.bend as LAB
import ./base/batch.bend as LB
import ./base/queries.bend as LQ
import ./base/counts.bend as LCs
import ./base/chain.bend as LAC
import ./base/open.bend as LAO

# The sizes
# ---------

def ol.or(m: Maybe<&2, Nat>, d: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      d
    case Some{x}:
      Some{x}

def ol.or_none(m: Maybe<&2, Nat>) -> {ol.or(m, None{}) == m : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def ol.bs_refl(x: List<&2, Bool>) -> {S.bits_same(x, x) == True{} : Bool}:
  match x:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case True{}:
          ol.bs_refl(t)
        case False{}:
          ol.bs_refl(t)

def ol.eq_t(+a: Nat, -b: Nat, ab: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %ab : {Nat.is_eq(a, _) == True{} : Bool}
  LNat.child.pc.eq_refl(a)

def ol.bs_ne(r: Bool, +a: Nat, +b: Nat, er: {S.bits_same(OBits.Bits.of(a), OBits.Bits.of(b)) == r : Bool}, eq: {Nat.is_eq(a, b) == False{} : Bool}) -> {S.bits_same(OBits.Bits.of(a), OBits.Bits.of(b)) == False{} : Bool}:
  match r:
    case False{}:
      er
    case True{}:
      +ob = LCs.cs.bits_eq(OBits.Bits.of(a), OBits.Bits.of(b), er)
      +ab = Equal.trans(Nat, a, OBits.Bits.val(OBits.Bits.of(a)), b, Equal.sym(Nat, OBits.Bits.val(OBits.Bits.of(a)), a, LAB.ob.val_of(a)), Equal.trans(Nat, OBits.Bits.val(OBits.Bits.of(a)), OBits.Bits.val(OBits.Bits.of(b)), b, Equal.cong(List<&2, Bool>, Nat, q => OBits.Bits.val(q), OBits.Bits.of(a), OBits.Bits.of(b), ob), LAB.ob.val_of(b)))
      +tt = ol.eq_t(a, b, ab)
      LA.cover.absurd({S.bits_same(OBits.Bits.of(a), OBits.Bits.of(b)) == False{} : Bool}, Equal.trans(Bool, False{}, Nat.is_eq(a, b), True{}, Equal.sym(Bool, Nat.is_eq(a, b), False{}, eq), tt))

def ol.bs_at(q: Bool, +a: Nat, +b: Nat, eq: {Nat.is_eq(a, b) == q : Bool}) -> {S.bits_same(OBits.Bits.of(a), OBits.Bits.of(b)) == q : Bool}:
  match q:
    case True{}:
      +ab = LA.cover.eq_of_is_eq(a, b, eq)
      %ab : {S.bits_same(OBits.Bits.of(a), OBits.Bits.of(_)) == True{} : Bool}
      ol.bs_refl(OBits.Bits.of(a))
    case False{}:
      ol.bs_ne(S.bits_same(OBits.Bits.of(a), OBits.Bits.of(b)), a, b, {==}, eq)

# two wire indices name one key exactly when they are equal
def ol.bs_of(+a: Nat, +b: Nat) -> {S.bits_same(OBits.Bits.of(a), OBits.Bits.of(b)) == Nat.is_eq(a, b) : Bool}:
  ol.bs_at(Nat.is_eq(a, b), a, b, {==})

def ol.combine(later: Maybe<&2, Nat>, h: Bool, +z: Nat, -g: Maybe<&2, Nat>) -> {ol.or(later, S.info_pick(h, z, g)) == ol.or(Optchat.oc_size.pick(later, h, z), g) : Maybe<&2, Nat>}:
  match later:
    case Some{x}:
      {==}
    case None{}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}

def ol.info_go(bs: List<&2, FOc.Got>, +ts: List<&2, OInfo.Trie>, +l: Nat, +k: Nat) -> {OInfo.Info.get(Optchat.oc_info(bs, OInfo.Lvls{ts}), Optchat.oc_node(l, k)) == ol.or(Optchat.oc_size(bs, l, k), OInfo.Lvls.get(l, ts, OBits.Bits.of(k))) : Maybe<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case FOc.Got{+l2, +k2, +z} <> +rest:
      +later = Optchat.oc_size(rest, l, k)
      +g = OInfo.Lvls.get(l, ts, OBits.Bits.of(k))
      +ts2 = OInfo.Lvls.set(l2, ts, OBits.Bits.of(k2), z)
      Equal.trans(Maybe<&2, Nat>, OInfo.Info.get(Optchat.oc_info(rest, OInfo.Lvls{ts2}), Optchat.oc_node(l, k)), ol.or(later, OInfo.Lvls.get(l, ts2, OBits.Bits.of(k))), ol.or(Optchat.oc_size.pick(later, Bool.and(Nat.is_eq(l2, l), Nat.is_eq(k2, k)), z), g),
        ol.info_go(rest, ts2, l, k),
        Equal.trans(Maybe<&2, Nat>, ol.or(later, OInfo.Lvls.get(l, ts2, OBits.Bits.of(k))), ol.or(later, S.info_pick(Bool.and(Nat.is_eq(l2, l), S.bits_same(OBits.Bits.of(k2), OBits.Bits.of(k))), z, g)), ol.or(Optchat.oc_size.pick(later, Bool.and(Nat.is_eq(l2, l), Nat.is_eq(k2, k)), z), g),
          Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>, q => ol.or(later, q), OInfo.Lvls.get(l, ts2, OBits.Bits.of(k)), S.info_pick(Bool.and(Nat.is_eq(l2, l), S.bits_same(OBits.Bits.of(k2), OBits.Bits.of(k))), z, g), LQ.oq.lv(l2, ts, l, OBits.Bits.of(k2), OBits.Bits.of(k), z)),
          Equal.trans(Maybe<&2, Nat>, ol.or(later, S.info_pick(Bool.and(Nat.is_eq(l2, l), S.bits_same(OBits.Bits.of(k2), OBits.Bits.of(k))), z, g)), ol.or(later, S.info_pick(Bool.and(Nat.is_eq(l2, l), Nat.is_eq(k2, k)), z, g)), ol.or(Optchat.oc_size.pick(later, Bool.and(Nat.is_eq(l2, l), Nat.is_eq(k2, k)), z), g),
            Equal.cong(Bool, Maybe<&2, Nat>, q => ol.or(later, S.info_pick(Bool.and(Nat.is_eq(l2, l), q), z, g)), S.bits_same(OBits.Bits.of(k2), OBits.Bits.of(k)), Nat.is_eq(k2, k), ol.bs_of(k2, k)),
            ol.combine(later, Bool.and(Nat.is_eq(l2, l), Nat.is_eq(k2, k)), z, g))))

# a node of an opened chat has the size the last copy of it gives
def ol.info(+bs: List<&2, FOc.Got>, +l: Nat, +k: Nat) -> {OInfo.Info.get(Optchat.oc_info(bs, OInfo.Info.empty()), Optchat.oc_node(l, k)) == Optchat.oc_size(bs, l, k) : Maybe<&2, Nat>}:
  +m = Optchat.oc_size(bs, l, k)
  Equal.trans(Maybe<&2, Nat>, OInfo.Info.get(Optchat.oc_info(bs, OInfo.Info.empty()), Optchat.oc_node(l, k)), ol.or(m, OInfo.Lvls.get(l, Nil{}, OBits.Bits.of(k))), m, ol.info_go(bs, Nil{}, l, k),
    Equal.trans(Maybe<&2, Nat>, ol.or(m, OInfo.Lvls.get(l, Nil{}, OBits.Bits.of(k))), ol.or(m, None{}), m, Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>, q => ol.or(m, q), OInfo.Lvls.get(l, Nil{}, OBits.Bits.of(k)), None{}, LQ.oq.lg_nil(l, OBits.Bits.of(k))), ol.or_none(m)))

# The open
# --------

def ol.Q(+o: FOc.Open, -res: FOc.St & String, +l: Nat, +k: Nat) -> Type:
  Optchat.oc_loaded(o, Optchat.oc_state(res), l, k) & Optchat.oc_opened(o, Optchat.oc_state(res), Optchat.oc_reply_of(res))

def ol.missed(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: Nat, +bs: List<&2, FOc.Got>, +vs: List<&2, FOc.Line>, +sh: Bool, +l: Nat, +k: Nat,
  ch: S.Chain(OFit.Last{}, OBits.Bits.of(t), Optchat.oc_info(bs, OInfo.Info.empty()), OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), Optchat.oc_lines(vs), Pair.fst(List<&2, ONode.Node>, List<&2, ONode.Node>, r), Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r)))
  -> ol.Q(FOc.Open{cfg, t, bs, vs, sh, True{}}, LAO.oo.m.missed(r, cfg, OBits.Bits.of(t), Optchat.oc_info(bs, OInfo.Info.empty()), LAO.oo.m.ready(bs, Optchat.oc_info(bs, OInfo.Info.empty()), Nil{})), l, k):
  (merged, v0) = r
  +mg = merged
  +nv = v0
  +info = Optchat.oc_info(bs, OInfo.Info.empty())
  +sk = Equal.cong(Nat, Bool, q => Nat.is_gt(q, OState.Cfg.floor(cfg)), OFit.view_size(OState.Cfg.ph(cfg), info, nv), S.vsize(OState.Cfg.ph(cfg), info, nv), LB.ob.vsize(OState.Cfg.ph(cfg), info, nv))
  (({==}, (LAB.ob.val_of(t), (LAB.ob.canon_of(t), (ol.info(bs, l, k), {==})))), ((mg, (ch, (sk, {==}))), LAC.ch.fitted(OFit.Last{}, OBits.Bits.of(t), OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, nv)))

def ol.open_m(m: Bool, +cfg: OState.Cfg, +t: Nat, +bs: List<&2, FOc.Got>, +vs: List<&2, FOc.Line>, +sh: Bool, +l: Nat, +k: Nat) -> ol.Q(FOc.Open{cfg, t, bs, vs, sh, m}, LAO.oo.m.open(FOc.Open{cfg, t, bs, vs, sh, m}), l, k):
  match m:
    case False{}:
      (({==}, (LAB.ob.val_of(t), (LAB.ob.canon_of(t), (ol.info(bs, l, k), {==})))), (({==}, ({==}, {==})), LAC.ch.fitted(OFit.Last{}, OBits.Bits.of(t), OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), Optchat.oc_info(bs, OInfo.Info.empty()), Optchat.oc_lines(vs))))
    case True{}:
      ol.missed(OFit.fit(OFit.Last{}, OBits.Bits.of(t), OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), Optchat.oc_info(bs, OInfo.Info.empty()), Optchat.oc_lines(vs)), cfg, t, bs, vs, sh, l, k, LAC.ch.fit(OFit.Last{}, OBits.Bits.of(t), OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), Optchat.oc_info(bs, OInfo.Info.empty()), Optchat.oc_lines(vs)))

def ol.open(o: FOc.Open, +l: Nat, +k: Nat) -> ol.Q(o, LAO.oo.m.open(o), l, k):
  match o:
    case FOc.Open{+cfg, +t, +bs, +vs, +sh, m}:
      ol.open_m(m, cfg, t, bs, vs, sh, l, k)

def Optchat.optchat_open_loads(o, l, k, fits):
  %Equal.sym(FOc.St & String, FOc.open(Optchat.oc_spell_open(o)), LAO.oo.m.open(o), LAO.oo.opened(o, fits)) : Optchat.oc_loaded(o, Optchat.oc_state(_), l, k) & Optchat.oc_opened(o, Optchat.oc_state(_), Optchat.oc_reply_of(_))
  ol.open(o, l, k)
