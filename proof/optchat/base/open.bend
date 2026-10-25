# eukhe: lemmas the proofs of area optchat share: the open of a loaded
# chat (FOc.open, OOpen.open)
#
# The entry's open runs the laws' open (oo.run: the built nodes' sizes,
# the ready merges and the view converted as the laws convert them, a
# missed batch answered as the laws spell it). The entry reads every open
# as the laws' reader does (oo.read), and the laws' reader reads every
# spelled open that fits the wire back (oo.spelled), so a spelled open
# opens the laws' open (oo.opened). The laws' open is live, with the
# open's sizes (oo.live), holds the ready merges its built nodes note
# (oo.holds), and, from a view that tiles the chat, both its views tile
# it (oo.covers).

import Base
import ../../../bend/wire.bend as Wr
import ../../../bend/ffi_optchat.bend as FOc
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/state.bend as OState
import ../../../bend/optchat/fit.bend as OFit
import ../../../bend/optchat/step.bend as OStep
import ../../../bend/optchat/open.bend as OOpen
import ../../../laws/optchat.bend as Optchat
import ../../../laws/base.bend as LawsBase
import ../../base/wire.bend as LWire
import ../../base/wire_dec.bend as LWireDec
import ../../base/logic/logic.bend as LLogicLogic
import ../../../bend/spec.bend as S
import ./step.bend as LAS
import ./bits.bend as LAB
import ./ffi_optchat.bend as LAF

# The open runs the laws' open
# ----------------------------

def oo.lines(vs: List<&2, FOc.Line>) -> {Optchat.oc_lines(vs) == FOc.lines(vs) : List<&2, ONode.Node>}:
  match vs:
    case Nil{}:
      {==}
    case FOc.Line{+l, +k} <> rest:
      Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, x => Optchat.oc_node(l, k) <> x, Optchat.oc_lines(rest), FOc.lines(rest), oo.lines(rest))

def oo.info(bs: List<&2, FOc.Got>, info: OInfo.Info) -> {Optchat.oc_info(bs, info) == OOpen.info.of(FOc.gots(bs), info) : OInfo.Info}:
  match bs:
    case Nil{}:
      {==}
    case FOc.Got{+l, +k, +z} <> rest:
      oo.info(rest, OInfo.Info.set(info, Optchat.oc_node(l, k), z))

def oo.ready(bs: List<&2, FOc.Got>, +info: OInfo.Info, rs: List<&2, ONode.Node>) -> {Optchat.oc_ready(bs, info, rs) == OOpen.ready.of(FOc.gots(bs), info, rs) : List<&2, ONode.Node>}:
  match bs:
    case Nil{}:
      {==}
    case FOc.Got{+l, +k, z} <> rest:
      oo.ready(rest, info, OStep.ready.note(info, Optchat.oc_node(l, k), rs))

def oo.batch(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +ready: List<&2, ONode.Node>) -> {FOc.open.reply(cfg, OOpen.open.batch(r, cfg, t, info, ready)) == Optchat.oc_open_missed(r, cfg, t, info, ready) : FOc.St & String}:
  (merged, view0) = r
  +m = merged
  +v = view0
  +s = Optchat.oc_open_at(cfg, t, info, v, Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, v), OState.Cfg.floor(cfg)), ready)
  Equal.cong(String, FOc.St & String, x => (FOc.Live{cfg, s}, x), FOc.msg.answer(True{}, m, s), Optchat.oc_spell_batch(True{}, m, s), LAF.oe.answer(True{}, m, s))

def oo.go(missed: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, shrink: Bool, +ready: List<&2, ONode.Node>) -> {FOc.open.reply(cfg, OOpen.open.go(missed, cfg, t, info, view, shrink, ready)) == Optchat.oc_open_go(missed, cfg, t, info, view, shrink, ready) : FOc.St & String}:
  match missed:
    case False{}:
      {==}
    case True{}:
      oo.batch(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, ready)

# the entry's open runs the laws' open
def oo.run(o: FOc.Open) -> {FOc.open.run(o) == Optchat.oc_open_model(o) : FOc.St & String}:
  match o:
    case FOc.Open{+cfg, +t, +bs, +vs, sh, m}:
      %oo.info(bs, OInfo.Info.empty()) : {FOc.open.reply(cfg, OOpen.open.go(m, cfg, OBits.Bits.of(t), _, FOc.lines(vs), sh, OOpen.ready.of(FOc.gots(bs), _, Nil{}))) == Optchat.oc_open_model(FOc.Open{cfg, t, bs, vs, sh, m}) : FOc.St & String}
      %oo.lines(vs) : {FOc.open.reply(cfg, OOpen.open.go(m, cfg, OBits.Bits.of(t), Optchat.oc_info(bs, OInfo.Info.empty()), _, sh, OOpen.ready.of(FOc.gots(bs), Optchat.oc_info(bs, OInfo.Info.empty()), Nil{}))) == Optchat.oc_open_model(FOc.Open{cfg, t, bs, vs, sh, m}) : FOc.St & String}
      %oo.ready(bs, Optchat.oc_info(bs, OInfo.Info.empty()), Nil{}) : {FOc.open.reply(cfg, OOpen.open.go(m, cfg, OBits.Bits.of(t), Optchat.oc_info(bs, OInfo.Info.empty()), Optchat.oc_lines(vs), sh, _)) == Optchat.oc_open_model(FOc.Open{cfg, t, bs, vs, sh, m}) : FOc.St & String}
      oo.go(m, cfg, OBits.Bits.of(t), Optchat.oc_info(bs, OInfo.Info.empty()), Optchat.oc_lines(vs), sh, Optchat.oc_ready(bs, Optchat.oc_info(bs, OInfo.Info.empty()), Nil{}))

# The entry reads an open as the laws' reader
# --------------------------------------------

def oo.list_got(n: Nat, cur: Wr.Dec<FOc.Got>) -> {Wr.get_list.go(~FOc.Got, ~Optchat.oc_read.got, n, cur) == Wr.get_list.go(~FOc.Got, ~FOc.get_got, n, cur) : Wr.Dec<List<&2, FOc.Got>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %LAF.oe.got(s) : {Wr.get_list.cons(FOc.Got, x, Wr.get_list.go(~FOc.Got, ~Optchat.oc_read.got, m, _)) == Wr.get_list.cons(FOc.Got, x, Wr.get_list.go(~FOc.Got, ~FOc.get_got, m, FOc.get_got(s))) : Wr.Dec<List<&2, FOc.Got>>}
          Equal.cong(Wr.Dec<List<&2, FOc.Got>>, Wr.Dec<List<&2, FOc.Got>>, d => Wr.get_list.cons(FOc.Got, x, d), Wr.get_list.go(~FOc.Got, ~Optchat.oc_read.got, m, FOc.get_got(s)), Wr.get_list.go(~FOc.Got, ~FOc.get_got, m, FOc.get_got(s)), oo.list_got(m, FOc.get_got(s)))
        case Wr.Bad{}:
          {==}

def oo.gots(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~FOc.Got, ~Optchat.oc_read.got, r) == Wr.get_list.start(~FOc.Got, ~FOc.get_got, r) : Wr.Dec<List<&2, FOc.Got>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %LAF.oe.got(s) : {Wr.get_list.go(~FOc.Got, ~Optchat.oc_read.got, m, _) == Wr.get_list.go(~FOc.Got, ~FOc.get_got, m, FOc.get_got(s)) : Wr.Dec<List<&2, FOc.Got>>}
          oo.list_got(m, FOc.get_got(s))
    case Wr.Bad{}:
      {==}

def oo.list_line(n: Nat, cur: Wr.Dec<FOc.Line>) -> {Wr.get_list.go(~FOc.Line, ~Optchat.oc_read.line, n, cur) == Wr.get_list.go(~FOc.Line, ~FOc.get_line, n, cur) : Wr.Dec<List<&2, FOc.Line>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %LAF.oe.line(s) : {Wr.get_list.cons(FOc.Line, x, Wr.get_list.go(~FOc.Line, ~Optchat.oc_read.line, m, _)) == Wr.get_list.cons(FOc.Line, x, Wr.get_list.go(~FOc.Line, ~FOc.get_line, m, FOc.get_line(s))) : Wr.Dec<List<&2, FOc.Line>>}
          Equal.cong(Wr.Dec<List<&2, FOc.Line>>, Wr.Dec<List<&2, FOc.Line>>, d => Wr.get_list.cons(FOc.Line, x, d), Wr.get_list.go(~FOc.Line, ~Optchat.oc_read.line, m, FOc.get_line(s)), Wr.get_list.go(~FOc.Line, ~FOc.get_line, m, FOc.get_line(s)), oo.list_line(m, FOc.get_line(s)))
        case Wr.Bad{}:
          {==}

def oo.lines_read(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~FOc.Line, ~Optchat.oc_read.line, r) == Wr.get_list.start(~FOc.Line, ~FOc.get_line, r) : Wr.Dec<List<&2, FOc.Line>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %LAF.oe.line(s) : {Wr.get_list.go(~FOc.Line, ~Optchat.oc_read.line, m, _) == Wr.get_list.go(~FOc.Line, ~FOc.get_line, m, FOc.get_line(s)) : Wr.Dec<List<&2, FOc.Line>>}
          oo.list_line(m, FOc.get_line(s))
    case Wr.Bad{}:
      {==}

def oo.missed(c: OState.Cfg, t: Nat, bs: List<&2, FOc.Got>, vs: List<&2, FOc.Line>, sh: Bool, r: Wr.Dec<Bool>) -> {Optchat.oc_read_open.missed(c, t, bs, vs, sh, r) == FOc.get_open.missed(c, t, bs, vs, sh, r) : Wr.Dec<FOc.Open>}:
  match r:
    case Wr.Got{m, s}:
      {==}
    case Wr.Bad{}:
      {==}

def oo.shrink(c: OState.Cfg, t: Nat, bs: List<&2, FOc.Got>, vs: List<&2, FOc.Line>, r: Wr.Dec<Bool>) -> {Optchat.oc_read_open.shrink(c, t, bs, vs, r) == FOc.get_open.shrink(c, t, bs, vs, r) : Wr.Dec<FOc.Open>}:
  match r:
    case Wr.Got{sh, s}:
      oo.missed(c, t, bs, vs, sh, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def oo.view(c: OState.Cfg, t: Nat, bs: List<&2, FOc.Got>, r: Wr.Dec<List<&2, FOc.Line>>) -> {Optchat.oc_read_open.view(c, t, bs, r) == FOc.get_open.view(c, t, bs, r) : Wr.Dec<FOc.Open>}:
  match r:
    case Wr.Got{vs, s}:
      oo.shrink(c, t, bs, vs, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def oo.built(+c: OState.Cfg, +t: Nat, r: Wr.Dec<List<&2, FOc.Got>>) -> {Optchat.oc_read_open.built(c, t, r) == FOc.get_open.built(c, t, r) : Wr.Dec<FOc.Open>}:
  match r:
    case Wr.Got{+bs, +s}:
      %Equal.sym(Wr.Dec<List<&2, FOc.Line>>, Wr.get_list(~FOc.Line, ~Optchat.oc_read.line, s), Wr.get_list(~FOc.Line, ~FOc.get_line, s), oo.lines_read(Wr.get_nat(s))) : {Optchat.oc_read_open.view(c, t, bs, _) == FOc.get_open.view(c, t, bs, Wr.get_list(~FOc.Line, ~FOc.get_line, s)) : Wr.Dec<FOc.Open>}
      oo.view(c, t, bs, Wr.get_list(~FOc.Line, ~FOc.get_line, s))
    case Wr.Bad{}:
      {==}

def oo.t(+c: OState.Cfg, r: Wr.Dec<Nat>) -> {Optchat.oc_read_open.t(c, r) == FOc.get_open.t(c, r) : Wr.Dec<FOc.Open>}:
  match r:
    case Wr.Got{+t, +s}:
      %Equal.sym(Wr.Dec<List<&2, FOc.Got>>, Wr.get_list(~FOc.Got, ~Optchat.oc_read.got, s), Wr.get_list(~FOc.Got, ~FOc.get_got, s), oo.gots(Wr.get_nat(s))) : {Optchat.oc_read_open.built(c, t, _) == FOc.get_open.built(c, t, Wr.get_list(~FOc.Got, ~FOc.get_got, s)) : Wr.Dec<FOc.Open>}
      oo.built(c, t, Wr.get_list(~FOc.Got, ~FOc.get_got, s))
    case Wr.Bad{}:
      {==}

def oo.cfg_open(r: Wr.Dec<OState.Cfg>) -> {Optchat.oc_read_open.cfg(r) == FOc.get_open.cfg(r) : Wr.Dec<FOc.Open>}:
  match r:
    case Wr.Got{c, s}:
      oo.t(c, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def oo.jobs(a: Nat, b: Nat, c: Nat, d: Nat, e: Nat, r: Wr.Dec<Nat>) -> {Optchat.oc_read_cfg.jobs(a, b, c, d, e, r) == FOc.get_cfg.jobs(a, b, c, d, e, r) : Wr.Dec<OState.Cfg>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def oo.cfloor(a: Nat, b: Nat, c: Nat, d: Nat, r: Wr.Dec<Nat>) -> {Optchat.oc_read_cfg.cfloor(a, b, c, d, r) == FOc.get_cfg.cfloor(a, b, c, d, r) : Wr.Dec<OState.Cfg>}:
  match r:
    case Wr.Got{e, s}:
      oo.jobs(a, b, c, d, e, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def oo.cceil(a: Nat, b: Nat, c: Nat, r: Wr.Dec<Nat>) -> {Optchat.oc_read_cfg.cceil(a, b, c, r) == FOc.get_cfg.cceil(a, b, c, r) : Wr.Dec<OState.Cfg>}:
  match r:
    case Wr.Got{d, s}:
      oo.cfloor(a, b, c, d, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def oo.floor(a: Nat, b: Nat, r: Wr.Dec<Nat>) -> {Optchat.oc_read_cfg.floor(a, b, r) == FOc.get_cfg.floor(a, b, r) : Wr.Dec<OState.Cfg>}:
  match r:
    case Wr.Got{c, s}:
      oo.cceil(a, b, c, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def oo.ceil(a: Nat, r: Wr.Dec<Nat>) -> {Optchat.oc_read_cfg.ceil(a, r) == FOc.get_cfg.ceil(a, r) : Wr.Dec<OState.Cfg>}:
  match r:
    case Wr.Got{b, s}:
      oo.floor(a, b, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def oo.ph(r: Wr.Dec<Nat>) -> {Optchat.oc_read_cfg.ph(r) == FOc.get_cfg.ph(r) : Wr.Dec<OState.Cfg>}:
  match r:
    case Wr.Got{a, s}:
      oo.ceil(a, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# the entry reads every open as the laws' reader does (turned around:
# rewrites the entry's read into the laws')
def oo.read(+s: String) -> {Optchat.oc_read_open.cfg(Optchat.oc_read_cfg.ph(Wr.get_nat(s))) == FOc.get_open(s) : Wr.Dec<FOc.Open>}:
  %Equal.sym(Wr.Dec<OState.Cfg>, Optchat.oc_read_cfg.ph(Wr.get_nat(s)), FOc.get_cfg.ph(Wr.get_nat(s)), oo.ph(Wr.get_nat(s))) : {Optchat.oc_read_open.cfg(_) == FOc.get_open(s) : Wr.Dec<FOc.Open>}
  oo.cfg_open(FOc.get_cfg.ph(Wr.get_nat(s)))

# an open the laws' reader reads whole runs the laws' open
def oo.whole(d: Wr.Dec<FOc.Open>, +o: FOc.Open, got: {Optchat.oc_read_open.whole(d) == Some{o} : Maybe<&2, FOc.Open>}) -> {FOc.open.go(d) == Optchat.oc_open_model(o) : FOc.St & String}:
  match d:
    case Wr.Got{+x, rest}:
      match rest:
        case SNil{}:
          %LAF.oe.some_inj(FOc.Open, x, o, got) : {FOc.open.run(x) == Optchat.oc_open_model(_) : FOc.St & String}
          oo.run(x)
        case SCon{h, t}:
          LAF.oe.none_some(FOc.Open, {(FOc.Refused{}, Wr.err("optchat: malformed open")) == Optchat.oc_open_model(o) : FOc.St & String}, o, got)
    case Wr.Bad{}:
      LAF.oe.none_some(FOc.Open, {(FOc.Refused{}, Wr.err("optchat: malformed open")) == Optchat.oc_open_model(o) : FOc.St & String}, o, got)

# an open the laws' reader does not read whole is refused
def oo.no(d: Wr.Dec<FOc.Open>, no: {Optchat.oc_read_open.whole(d) == None{} : Maybe<&2, FOc.Open>}) -> {FOc.open.go(d) == (FOc.Refused{}, SCon{'E', SCon{' ', "optchat: malformed open"}}) : FOc.St & String}:
  match d:
    case Wr.Got{x, rest}:
      match rest:
        case SNil{}:
          LAF.oe.none_some(FOc.Open, {FOc.open.end(True{}, x) == (FOc.Refused{}, SCon{'E', SCon{' ', "optchat: malformed open"}}) : FOc.St & String}, x, Equal.sym(Maybe<&2, FOc.Open>, Some{x}, None{}, no))
        case SCon{h, t}:
          {==}
    case Wr.Bad{}:
      {==}

# Spelled opens read back
# -----------------------

def oo.and3(a: Bool, b: Bool, c: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}, ec: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  match a:
    case False{}:
      LLogicLogic.pf.absurd_ft({Bool.and(False{}, Bool.and(b, c)) == True{} : Bool}, ea)
    case True{}:
      match b:
        case False{}:
          LLogicLogic.pf.absurd_ft({Bool.and(True{}, Bool.and(False{}, c)) == True{} : Bool}, eb)
        case True{}:
          ec

def oo.and2(a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case False{}:
      LLogicLogic.pf.absurd_ft({Bool.and(False{}, b) == True{} : Bool}, ea)
    case True{}:
      eb

# the fits of a built node
def oo.got_head(+l: Nat, +k: Nat, +z: Nat, -t: List<&2, FOc.Got>, +f: {Optchat.oc_gots_fit(FOc.Got{l, k, z} <> t) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(z))) == True{} : Bool}:
  +fr = LAF.oe.and_r(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(z), Optchat.oc_gots_fit(t))), f)
  +fzr = LAF.oe.and_r(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(z), Optchat.oc_gots_fit(t)), fr)
  oo.and3(LawsBase.wire_fits(l), LawsBase.wire_fits(k), LawsBase.wire_fits(z), LAF.oe.and_l(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(z), Optchat.oc_gots_fit(t))), f), LAF.oe.and_l(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(z), Optchat.oc_gots_fit(t)), fr), LAF.oe.and_l(LawsBase.wire_fits(z), Optchat.oc_gots_fit(t), fzr))

# the fits of the nodes after it
def oo.got_tail(+l: Nat, +k: Nat, +z: Nat, -t: List<&2, FOc.Got>, f: {Optchat.oc_gots_fit(FOc.Got{l, k, z} <> t) == True{} : Bool}) -> {Optchat.oc_gots_fit(t) == True{} : Bool}:
  +fr = LAF.oe.and_r(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(z), Optchat.oc_gots_fit(t))), f)
  +fzr = LAF.oe.and_r(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(z), Optchat.oc_gots_fit(t)), fr)
  LAF.oe.and_r(LawsBase.wire_fits(z), Optchat.oc_gots_fit(t), fzr)

def oo.gots_go(t: List<&2, FOc.Got>, x: FOc.Got, +rest: String, +f: {Optchat.oc_gots_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~FOc.Got, ~Optchat.oc_read.got, List.length(&2, FOc.Got, t), Optchat.oc_read.got(Optchat.oc_spell_gots.items(x <> t, rest))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, FOc.Got>>}:
  match t x:
    case Nil{} FOc.Got{+l, +k, +z}:
      %LAF.oe.lkz(l, k, z, rest, oo.got_head(l, k, z, Nil{}, f)) : {Wr.get_list.go(~FOc.Got, ~Optchat.oc_read.got, 0n, _) == Wr.Got{[FOc.Got{l, k, z}], rest} : Wr.Dec<List<&2, FOc.Got>>}
      {==}
    case +y <> +u FOc.Got{+l, +k, +z}:
      %LAF.oe.lkz(l, k, z, Optchat.oc_spell_gots.items(y <> u, rest), oo.got_head(l, k, z, y <> u, f)) : {Wr.get_list.go(~FOc.Got, ~Optchat.oc_read.got, 1n+List.length(&2, FOc.Got, u), _) == Wr.Got{FOc.Got{l, k, z} <> y <> u, rest} : Wr.Dec<List<&2, FOc.Got>>}
      %Equal.sym(Wr.Dec<List<&2, FOc.Got>>, Wr.get_list.go(~FOc.Got, ~Optchat.oc_read.got, List.length(&2, FOc.Got, u), Optchat.oc_read.got(Optchat.oc_spell_gots.items(y <> u, rest))), Wr.Got{y <> u, rest}, oo.gots_go(u, y, rest, oo.got_tail(l, k, z, y <> u, f))) : {Wr.get_list.cons(FOc.Got, FOc.Got{l, k, z}, _) == Wr.Got{FOc.Got{l, k, z} <> y <> u, rest} : Wr.Dec<List<&2, FOc.Got>>}
      {==}

# a list of built nodes that fits reads back
def oo.gots_rt(bs: List<&2, FOc.Got>, +rest: String, fc: {LawsBase.wire_fits(List.length(&2, FOc.Got, bs)) == True{} : Bool}, f: {Optchat.oc_gots_fit(bs) == True{} : Bool}) -> {Wr.Got{bs, rest} == Wr.get_list(~FOc.Got, ~Optchat.oc_read.got, Wr.put_nat(List.length(&2, FOc.Got, bs), Optchat.oc_spell_gots.items(bs, rest))) : Wr.Dec<List<&2, FOc.Got>>}:
  match bs:
    case Nil{}:
      %LWire.pc.nat(0n, rest, fc) : {Wr.Got{Nil{}, rest} == Wr.get_list.start(~FOc.Got, ~Optchat.oc_read.got, _) : Wr.Dec<List<&2, FOc.Got>>}
      {==}
    case +x <> +t:
      %LWire.pc.nat(1n+List.length(&2, FOc.Got, t), Optchat.oc_spell_gots.items(x <> t, rest), fc) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~FOc.Got, ~Optchat.oc_read.got, _) : Wr.Dec<List<&2, FOc.Got>>}
      Equal.sym(Wr.Dec<List<&2, FOc.Got>>, Wr.get_list.go(~FOc.Got, ~Optchat.oc_read.got, List.length(&2, FOc.Got, t), Optchat.oc_read.got(Optchat.oc_spell_gots.items(x <> t, rest))), Wr.Got{x <> t, rest}, oo.gots_go(t, x, rest, f))

def oo.line_head(+l: Nat, +k: Nat, -t: List<&2, FOc.Line>, +f: {Optchat.oc_lines_fit(FOc.Line{l, k} <> t) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(k)) == True{} : Bool}:
  +fr = LAF.oe.and_r(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), Optchat.oc_lines_fit(t)), f)
  oo.and2(LawsBase.wire_fits(l), LawsBase.wire_fits(k), LAF.oe.and_l(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), Optchat.oc_lines_fit(t)), f), LAF.oe.and_l(LawsBase.wire_fits(k), Optchat.oc_lines_fit(t), fr))

def oo.line_tail(+l: Nat, +k: Nat, -t: List<&2, FOc.Line>, f: {Optchat.oc_lines_fit(FOc.Line{l, k} <> t) == True{} : Bool}) -> {Optchat.oc_lines_fit(t) == True{} : Bool}:
  +fr = LAF.oe.and_r(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), Optchat.oc_lines_fit(t)), f)
  LAF.oe.and_r(LawsBase.wire_fits(k), Optchat.oc_lines_fit(t), fr)

def oo.lines_go(t: List<&2, FOc.Line>, x: FOc.Line, +rest: String, +f: {Optchat.oc_lines_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~FOc.Line, ~Optchat.oc_read.line, List.length(&2, FOc.Line, t), Optchat.oc_read.line(Optchat.oc_spell_lines.items(x <> t, rest))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, FOc.Line>>}:
  match t x:
    case Nil{} FOc.Line{+l, +k}:
      %LAF.oe.lk_and(l, k, rest, oo.line_head(l, k, Nil{}, f)) : {Wr.get_list.go(~FOc.Line, ~Optchat.oc_read.line, 0n, _) == Wr.Got{[FOc.Line{l, k}], rest} : Wr.Dec<List<&2, FOc.Line>>}
      {==}
    case +y <> +u FOc.Line{+l, +k}:
      %LAF.oe.lk_and(l, k, Optchat.oc_spell_lines.items(y <> u, rest), oo.line_head(l, k, y <> u, f)) : {Wr.get_list.go(~FOc.Line, ~Optchat.oc_read.line, 1n+List.length(&2, FOc.Line, u), _) == Wr.Got{FOc.Line{l, k} <> y <> u, rest} : Wr.Dec<List<&2, FOc.Line>>}
      %Equal.sym(Wr.Dec<List<&2, FOc.Line>>, Wr.get_list.go(~FOc.Line, ~Optchat.oc_read.line, List.length(&2, FOc.Line, u), Optchat.oc_read.line(Optchat.oc_spell_lines.items(y <> u, rest))), Wr.Got{y <> u, rest}, oo.lines_go(u, y, rest, oo.line_tail(l, k, y <> u, f))) : {Wr.get_list.cons(FOc.Line, FOc.Line{l, k}, _) == Wr.Got{FOc.Line{l, k} <> y <> u, rest} : Wr.Dec<List<&2, FOc.Line>>}
      {==}

# a list of view lines that fits reads back
def oo.lines_rt(vs: List<&2, FOc.Line>, +rest: String, fc: {LawsBase.wire_fits(List.length(&2, FOc.Line, vs)) == True{} : Bool}, f: {Optchat.oc_lines_fit(vs) == True{} : Bool}) -> {Wr.Got{vs, rest} == Wr.get_list(~FOc.Line, ~Optchat.oc_read.line, Wr.put_nat(List.length(&2, FOc.Line, vs), Optchat.oc_spell_lines.items(vs, rest))) : Wr.Dec<List<&2, FOc.Line>>}:
  match vs:
    case Nil{}:
      %LWire.pc.nat(0n, rest, fc) : {Wr.Got{Nil{}, rest} == Wr.get_list.start(~FOc.Line, ~Optchat.oc_read.line, _) : Wr.Dec<List<&2, FOc.Line>>}
      {==}
    case +x <> +t:
      %LWire.pc.nat(1n+List.length(&2, FOc.Line, t), Optchat.oc_spell_lines.items(x <> t, rest), fc) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~FOc.Line, ~Optchat.oc_read.line, _) : Wr.Dec<List<&2, FOc.Line>>}
      Equal.sym(Wr.Dec<List<&2, FOc.Line>>, Wr.get_list.go(~FOc.Line, ~Optchat.oc_read.line, List.length(&2, FOc.Line, t), Optchat.oc_read.line(Optchat.oc_spell_lines.items(x <> t, rest))), Wr.Got{x <> t, rest}, oo.lines_go(t, x, rest, f))

# the head of a list of Nats that fit fits
def oo.nf_head(+x: Nat, -t: List<&2, Nat>, f: {LawsBase.wire_nats_fit(x <> t) == True{} : Bool}) -> {LawsBase.wire_fits(x) == True{} : Bool}:
  LAF.oe.and_l(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(t), f)

# and so does its tail
def oo.nf_tail(+x: Nat, -t: List<&2, Nat>, f: {LawsBase.wire_nats_fit(x <> t) == True{} : Bool}) -> {LawsBase.wire_nats_fit(t) == True{} : Bool}:
  LAF.oe.and_r(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(t), f)

# every open that fits the wire, spelled, reads back whole
def oo.spelled(o: FOc.Open, +fits: {Optchat.oc_open_fits(o) == True{} : Bool}) -> {Optchat.oc_read_open(Optchat.oc_spell_open(o)) == Some{o} : Maybe<&2, FOc.Open>}:
  match o:
    case FOc.Open{c, +t, +bs, +vs, +sh, +m}:
      match c:
        case OState.Cfg{+ph, +ce, +fl, +cc, +cf, +j}:
          +lb = List.length(&2, FOc.Got, bs)
          +lv = List.length(&2, FOc.Line, vs)
          +R6 = Wr.put_bool(sh, Wr.put_bool(m, ""))
          +R5 = Wr.put_nat(lv, Optchat.oc_spell_lines.items(vs, R6))
          +R4 = Optchat.oc_spell_gots.items(bs, R5)
          +R3 = Wr.put_nat(lb, R4)
          +R2 = Wr.put_nat(t, R3)
          +R1 = Wr.put_nat(j, R2)
          +R0 = Wr.put_nat(cf, R1)
          +Rc = Wr.put_nat(cc, R0)
          +Rf = Wr.put_nat(fl, Rc)
          +Re = Wr.put_nat(ce, Rf)
          +cfg = {OState.Cfg{ph, ce, fl, cc, cf, j} : OState.Cfg}
          +o1 = {FOc.Open{cfg, t, bs, vs, sh, m} : FOc.Open}
          +fn = LAF.oe.and_l(LawsBase.wire_nats_fit([ph, ce, fl, cc, cf, j, t, lb, lv]), Bool.and(Optchat.oc_gots_fit(bs), Optchat.oc_lines_fit(vs)), fits)
          +fgl = LAF.oe.and_r(LawsBase.wire_nats_fit([ph, ce, fl, cc, cf, j, t, lb, lv]), Bool.and(Optchat.oc_gots_fit(bs), Optchat.oc_lines_fit(vs)), fits)
          +n1 = oo.nf_tail(ph, [ce, fl, cc, cf, j, t, lb, lv], fn)
          +n2 = oo.nf_tail(ce, [fl, cc, cf, j, t, lb, lv], n1)
          +n3 = oo.nf_tail(fl, [cc, cf, j, t, lb, lv], n2)
          +n4 = oo.nf_tail(cc, [cf, j, t, lb, lv], n3)
          +n5 = oo.nf_tail(cf, [j, t, lb, lv], n4)
          +n6 = oo.nf_tail(j, [t, lb, lv], n5)
          +n7 = oo.nf_tail(t, [lb, lv], n6)
          +n8 = oo.nf_tail(lb, [lv], n7)
          f0 = oo.nf_head(ph, [ce, fl, cc, cf, j, t, lb, lv], fn)
          f1 = oo.nf_head(ce, [fl, cc, cf, j, t, lb, lv], n1)
          f2 = oo.nf_head(fl, [cc, cf, j, t, lb, lv], n2)
          f3 = oo.nf_head(cc, [cf, j, t, lb, lv], n3)
          f4 = oo.nf_head(cf, [j, t, lb, lv], n4)
          f5 = oo.nf_head(j, [t, lb, lv], n5)
          f6 = oo.nf_head(t, [lb, lv], n6)
          f7 = oo.nf_head(lb, [lv], n7)
          f8 = oo.nf_head(lv, [], n8)
          %LWire.pc.nat(ph, Re, f0) : {Optchat.oc_read_open.whole(Optchat.oc_read_open.cfg(Optchat.oc_read_cfg.ph(_))) == Some{o1} : Maybe<&2, FOc.Open>}
          %LWire.pc.nat(ce, Rf, f1) : {Optchat.oc_read_open.whole(Optchat.oc_read_open.cfg(Optchat.oc_read_cfg.ceil(ph, _))) == Some{o1} : Maybe<&2, FOc.Open>}
          %LWire.pc.nat(fl, Rc, f2) : {Optchat.oc_read_open.whole(Optchat.oc_read_open.cfg(Optchat.oc_read_cfg.floor(ph, ce, _))) == Some{o1} : Maybe<&2, FOc.Open>}
          %LWire.pc.nat(cc, R0, f3) : {Optchat.oc_read_open.whole(Optchat.oc_read_open.cfg(Optchat.oc_read_cfg.cceil(ph, ce, fl, _))) == Some{o1} : Maybe<&2, FOc.Open>}
          %LWire.pc.nat(cf, R1, f4) : {Optchat.oc_read_open.whole(Optchat.oc_read_open.cfg(Optchat.oc_read_cfg.cfloor(ph, ce, fl, cc, _))) == Some{o1} : Maybe<&2, FOc.Open>}
          %LWire.pc.nat(j, R2, f5) : {Optchat.oc_read_open.whole(Optchat.oc_read_open.cfg(Optchat.oc_read_cfg.jobs(ph, ce, fl, cc, cf, _))) == Some{o1} : Maybe<&2, FOc.Open>}
          %LWire.pc.nat(t, R3, f6) : {Optchat.oc_read_open.whole(Optchat.oc_read_open.t(cfg, _)) == Some{o1} : Maybe<&2, FOc.Open>}
          %oo.gots_rt(bs, R5, f7, LAF.oe.and_l(Optchat.oc_gots_fit(bs), Optchat.oc_lines_fit(vs), fgl)) : {Optchat.oc_read_open.whole(Optchat.oc_read_open.built(cfg, t, _)) == Some{o1} : Maybe<&2, FOc.Open>}
          %oo.lines_rt(vs, R6, f8, LAF.oe.and_r(Optchat.oc_gots_fit(bs), Optchat.oc_lines_fit(vs), fgl)) : {Optchat.oc_read_open.whole(Optchat.oc_read_open.view(cfg, t, bs, _)) == Some{o1} : Maybe<&2, FOc.Open>}
          %LWireDec.dcw.bool_back(sh, Wr.put_bool(m, "")) : {Optchat.oc_read_open.whole(Optchat.oc_read_open.shrink(cfg, t, bs, vs, _)) == Some{o1} : Maybe<&2, FOc.Open>}
          %LWireDec.dcw.bool_back(m, "") : {Optchat.oc_read_open.whole(Optchat.oc_read_open.missed(cfg, t, bs, vs, sh, _)) == Some{o1} : Maybe<&2, FOc.Open>}
          {==}

# an open that fits the wire, spelled, opens the laws' open
def oo.opened(+o: FOc.Open, fits: {Optchat.oc_open_fits(o) == True{} : Bool}) -> {FOc.open(Optchat.oc_spell_open(o)) == Optchat.oc_open_model(o) : FOc.St & String}:
  %oo.read(Optchat.oc_spell_open(o)) : {FOc.open.go(_) == Optchat.oc_open_model(o) : FOc.St & String}
  oo.whole(Optchat.oc_read_open.cfg(Optchat.oc_read_cfg.ph(Wr.get_nat(Optchat.oc_spell_open(o)))), o, oo.spelled(o, fits))

# The opened chat
# ---------------

def oo.live_missed(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, ready: List<&2, ONode.Node>) -> {FOc.Live{cfg, Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_missed(r, cfg, t, info, ready)))} == Optchat.oc_state(Optchat.oc_open_missed(r, cfg, t, info, ready)) : FOc.St}:
  (merged, view0) = r
  {==}

def oo.live_go(missed: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, shrink: Bool, ready: List<&2, ONode.Node>) -> {FOc.Live{cfg, Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_go(missed, cfg, t, info, view, shrink, ready)))} == Optchat.oc_state(Optchat.oc_open_go(missed, cfg, t, info, view, shrink, ready)) : FOc.St}:
  match missed:
    case False{}:
      {==}
    case True{}:
      oo.live_missed(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, ready)

# the laws' open is live, with the open's sizes
def oo.live(o: FOc.Open) -> {FOc.Live{Optchat.oc_cfg(o), Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_model(o)))} == Optchat.oc_state(Optchat.oc_open_model(o)) : FOc.St}:
  match o:
    case FOc.Open{+cfg, t, +bs, vs, sh, m}:
      oo.live_go(m, cfg, OBits.Bits.of(t), Optchat.oc_info(bs, OInfo.Info.empty()), Optchat.oc_lines(vs), sh, Optchat.oc_ready(bs, Optchat.oc_info(bs, OInfo.Info.empty()), Nil{}))

def oo.holds_missed(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +ready: List<&2, ONode.Node>) -> {OState.St.ready(Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_missed(r, cfg, t, info, ready)))) == ready : List<&2, ONode.Node>}:
  (merged, view0) = r
  {==}

def oo.holds_go(missed: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, shrink: Bool, +ready: List<&2, ONode.Node>) -> {OState.St.ready(Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_go(missed, cfg, t, info, view, shrink, ready)))) == ready : List<&2, ONode.Node>}:
  match missed:
    case False{}:
      {==}
    case True{}:
      oo.holds_missed(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, ready)

# the laws' open holds the ready merges its built nodes note
def oo.holds(o: FOc.Open) -> {OState.St.ready(Optchat.oc_chat(Optchat.oc_state(Optchat.oc_open_model(o)))) == Optchat.oc_ready(Optchat.oc_built(o), Optchat.oc_info(Optchat.oc_built(o), OInfo.Info.empty()), Nil{}) : List<&2, ONode.Node>}:
  match o:
    case FOc.Open{+cfg, t, +bs, vs, sh, m}:
      oo.holds_go(m, cfg, OBits.Bits.of(t), Optchat.oc_info(bs, OInfo.Info.empty()), Optchat.oc_lines(vs), sh, Optchat.oc_ready(bs, Optchat.oc_info(bs, OInfo.Info.empty()), Nil{}))

# lines that the laws' tiling check passes tile, as nodes
def oo.tiles(vs: List<&2, FOc.Line>, +s: Nat, +e: Nat, +h: {Optchat.oc_tiles(vs, s, e) == True{} : Bool}) -> S.Tiles(s, Optchat.oc_lines(vs), e):
  match vs:
    case Nil{}:
      LAS.cover.eq_of_is_eq(s, e, h)
    case FOc.Line{+l, +k} <> +rest:
      +go = Optchat.oc_tiles(rest, Nat.add(s, OBits.pow2(l)), e)
      +hs = LAS.cover.and_l(Nat.is_eq(OBits.shl(l, k), s), go, h)
      %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.of(k)), k, LAB.ob.val_of(k)) : {OBits.shl(l, _) == s : Nat} & S.Tiles(Nat.add(s, OBits.pow2(l)), Optchat.oc_lines(rest), e)
      (LAS.cover.eq_of_is_eq(OBits.shl(l, k), s, hs), oo.tiles(rest, Nat.add(s, OBits.pow2(l)), e, LAS.cover.and_r(Nat.is_eq(OBits.shl(l, k), s), go, h)))

def oo.covers_two(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, shrink: Bool, ready: List<&2, ONode.Node>, tvs: S.Tiles(0n, view, OBits.Bits.val(t)) & S.Tiles(0n, view, OBits.Bits.val(t))) -> Optchat.oc_covers(FOc.Live{cfg, Optchat.oc_open_at(cfg, t, info, view, shrink, ready)}):
  (a, b) = tvs
  (a, LAS.cover.fit_view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, view, 0n, OBits.Bits.val(t), b))

def oo.covers_at(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, shrink: Bool, ready: List<&2, ONode.Node>, tv: S.Tiles(0n, view, OBits.Bits.val(t))) -> Optchat.oc_covers(FOc.Live{cfg, Optchat.oc_open_at(cfg, t, info, view, shrink, ready)}):
  oo.covers_two(cfg, t, info, view, shrink, ready, LAS.cover.dup(view, 0n, OBits.Bits.val(t), tv))

def oo.covers_missed(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, ready: List<&2, ONode.Node>, tv: S.Tiles(0n, Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r), OBits.Bits.val(t))) -> Optchat.oc_covers(Optchat.oc_state(Optchat.oc_open_missed(r, cfg, t, info, ready))):
  (merged, view0) = r
  +view = view0
  oo.covers_at(cfg, t, info, view, Nat.is_gt(OFit.view_size(OState.Cfg.ph(cfg), info, view), OState.Cfg.floor(cfg)), ready, tv)

def oo.covers_go(missed: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, shrink: Bool, ready: List<&2, ONode.Node>, tv: S.Tiles(0n, view, OBits.Bits.val(t))) -> Optchat.oc_covers(Optchat.oc_state(Optchat.oc_open_go(missed, cfg, t, info, view, shrink, ready))):
  match missed:
    case False{}:
      oo.covers_at(cfg, t, info, view, shrink, ready, tv)
    case True{}:
      oo.covers_missed(OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, ready, LAS.cover.fit_view(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view, 0n, OBits.Bits.val(t), tv))

def oo.tiles_t(vs: List<&2, FOc.Line>, +t: Nat, h: {Optchat.oc_tiles(vs, 0n, t) == True{} : Bool}) -> S.Tiles(0n, Optchat.oc_lines(vs), OBits.Bits.val(OBits.Bits.of(t))):
  %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.of(t)), t, LAB.ob.val_of(t)) : S.Tiles(0n, Optchat.oc_lines(vs), _)
  oo.tiles(vs, 0n, t, h)

# from a view that tiles the chat, both views of the laws' open tile it
def oo.covers(o: FOc.Open, tiles: {Optchat.oc_tiles(Optchat.oc_view(o), 0n, Optchat.oc_t(o)) == True{} : Bool}) -> Optchat.oc_covers(Optchat.oc_state(Optchat.oc_open_model(o))):
  match o:
    case FOc.Open{+cfg, +t, +bs, +vs, sh, m}:
      oo.covers_go(m, cfg, OBits.Bits.of(t), Optchat.oc_info(bs, OInfo.Info.empty()), Optchat.oc_lines(vs), sh, Optchat.oc_ready(bs, Optchat.oc_info(bs, OInfo.Info.empty()), Nil{}), oo.tiles_t(vs, t, tiles))
