# eukhe: the proof of LAW optchat_entry_spelled_or_refused
#
# Every input the entry reads whole as a request q is exactly the laws'
# spelling of q, and q fits the wire: each decoder stage, given what its
# sub-decoder read, turns the input into the spelling of that part (the
# wire's exactness laws), and the decoded Nats fit (the wire's
# decoded-fits laws). Any other input keeps the chat and answers the
# malformed error.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_optchat.bend as FOc
import ../../bend/optchat/state.bend as OState
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/optchat.bend as Optchat
import ../wire/wire_nat_exact.bend as PWNatExact
import ../wire/wire_nat_decoded_fits.bend as PWNatFits
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LWireDec

# What each decoder's answer says about its input
# -----------------------------------------------

# a node l, k read, then r
def ox.LP(d: Wr.Dec<FOc.Line>, s: String) -> Type:
  match d:
    case Wr.Got{x, r}:
      match x:
        case FOc.Line{l, k}:
          {s == Optchat.oc_spell_lk(l, k, r) : String} & {Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(k)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a built node l, k, z read, then r
def ox.GP(d: Wr.Dec<FOc.Got>, s: String) -> Type:
  match d:
    case Wr.Got{x, r}:
      match x:
        case FOc.Got{l, k, z}:
          {s == Optchat.oc_spell_lk(l, k, Wr.put_nat(z, r)) : String} & {Bool.and(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(z))) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a request read whole: the input is its spelling, and it fits
def ox.CQ(d: Wr.Dec<FOc.Q>, i: String) -> Type:
  match d:
    case Wr.Got{q, r}:
      match r:
        case SNil{}:
          {Optchat.oc_spell(q) == i : String} & {Optchat.oc_fits(q) == True{} : Bool}
        case SCon{c, t}:
          Unit
    case Wr.Bad{}:
      Unit

# A node
# ------

def ox.lk(-s: String, +l: Nat, +s1: String, es: {s == Wr.put_nat(l, s1) : String}, fl: {LawsBase.wire_fits(l) == True{} : Bool}, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}) -> ox.LP(FOc.get_line.k(l, r), s):
  match r:
    case Wr.Got{+k, +s2}:
      +h = hr
      (LWireDec.dcw.after(s, l, s1, Wr.put_nat(k, s2), es, Wire.wire_nat_exact(s1, k, s2, h)), LBool.cb_and_intro(LawsBase.wire_fits(l), LawsBase.wire_fits(k), fl, Wire.wire_nat_decoded_fits(s1, k, s2, h)))
    case Wr.Bad{}:
      Unit{}

def ox.line.at(+s: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> ox.LP(FOc.get_line.l(r), s):
  match r:
    case Wr.Got{+l, +s1}:
      +h = hr
      ox.lk(s, l, s1, Wire.wire_nat_exact(s, l, s1, h), Wire.wire_nat_decoded_fits(s, l, s1, h), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# a node decoded is spelled, and it fits
def ox.line(+s: String) -> ox.LP(FOc.get_line(s), s):
  ox.line.at(s, Wr.get_nat(s), {==})

# A built node
# ------------

def ox.and3(+a: Bool, +b: Bool, -c: Bool, ab: {Bool.and(a, b) == True{} : Bool}, ec: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  match a:
    case True{}:
      LBool.cb_and_intro(b, c, ab, ec)
    case False{}:
      ab

def ox.size(-s: String, +l: Nat, +k: Nat, +s1: String, es: {s == Optchat.oc_spell_lk(l, k, s1) : String}, f: {Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(k)) == True{} : Bool}, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}) -> ox.GP(FOc.get_got.size(FOc.Line{l, k}, r), s):
  match r:
    case Wr.Got{+z, +s2}:
      +h = hr
      (Equal.trans(String, s, Optchat.oc_spell_lk(l, k, s1), Optchat.oc_spell_lk(l, k, Wr.put_nat(z, s2)), es, Equal.cong(String, String, x => Optchat.oc_spell_lk(l, k, x), s1, Wr.put_nat(z, s2), Wire.wire_nat_exact(s1, z, s2, h))), ox.and3(LawsBase.wire_fits(l), LawsBase.wire_fits(k), LawsBase.wire_fits(z), f, Wire.wire_nat_decoded_fits(s1, z, s2, h)))
    case Wr.Bad{}:
      Unit{}

def ox.got.node(-s: String, d: Wr.Dec<FOc.Line>, lp: ox.LP(d, s)) -> ox.GP(FOc.get_got.node(d), s):
  match d:
    case Wr.Got{x, +s1}:
      match x:
        case FOc.Line{+l, +k}:
          (es, f) = lp
          ox.size(s, l, k, s1, es, f, Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# a built node decoded is spelled, and it fits
def ox.got(+s: String) -> ox.GP(FOc.get_got(s), s):
  ox.got.node(s, FOc.get_line(s), ox.line(s))

# The requests
# ------------

def ox.qbuilt(-i: String, +s1: String, ei: {i == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<FOc.Got>, gp: ox.GP(d, s1)) -> ox.CQ(FOc.get_ev.built(d), i):
  match d:
    case Wr.Got{x, r}:
      match x:
        case FOc.Got{+l, +k, +z}:
          match r:
            case SNil{}:
              (es, f) = gp
              (Equal.sym(String, i, Wr.put_nat(1n, Optchat.oc_spell_lk(l, k, Wr.put_nat(z, ""))), LWireDec.dcw.after(i, 1n, s1, Optchat.oc_spell_lk(l, k, Wr.put_nat(z, "")), ei, es)), f)
            case SCon{c, t}:
              Unit{}
    case Wr.Bad{}:
      Unit{}

def ox.qstart(-i: String, +s1: String, ei: {i == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<FOc.Line>, lp: ox.LP(d, s1)) -> ox.CQ(FOc.get_ev.start(d), i):
  match d:
    case Wr.Got{x, r}:
      match x:
        case FOc.Line{+l, +k}:
          match r:
            case SNil{}:
              (es, f) = lp
              (Equal.sym(String, i, Wr.put_nat(2n, Optchat.oc_spell_lk(l, k, "")), LWireDec.dcw.after(i, 2n, s1, Optchat.oc_spell_lk(l, k, ""), ei, es)), f)
            case SCon{c, t}:
              Unit{}
    case Wr.Bad{}:
      Unit{}

def ox.qfree(-i: String, +s1: String, ei: {i == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<FOc.Line>, lp: ox.LP(d, s1)) -> ox.CQ(FOc.get_ev.free(d), i):
  match d:
    case Wr.Got{x, r}:
      match x:
        case FOc.Line{+l, +k}:
          match r:
            case SNil{}:
              (es, f) = lp
              (Equal.sym(String, i, Wr.put_nat(3n, Optchat.oc_spell_lk(l, k, "")), LWireDec.dcw.after(i, 3n, s1, Optchat.oc_spell_lk(l, k, ""), ei, es)), f)
            case SCon{c, t}:
              Unit{}
    case Wr.Bad{}:
      Unit{}

def ox.qctx(-i: String, +s1: String, ei: {i == Wr.put_nat(7n, s1) : String}, d: Wr.Dec<FOc.Line>, lp: ox.LP(d, s1)) -> ox.CQ(FOc.get_ev.ctx(d), i):
  match d:
    case Wr.Got{x, r}:
      match x:
        case FOc.Line{+l, +k}:
          match r:
            case SNil{}:
              (es, f) = lp
              (Equal.sym(String, i, Wr.put_nat(7n, Optchat.oc_spell_lk(l, k, "")), LWireDec.dcw.after(i, 7n, s1, Optchat.oc_spell_lk(l, k, ""), ei, es)), f)
            case SCon{c, t}:
              Unit{}
    case Wr.Bad{}:
      Unit{}

# a due mark: the queries of tag 5 (cands) and 6 (a waiting turn's)
def ox.qcands(-i: String, +s1: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}, ei: {i == Wr.put_nat(5n, s1) : String}) -> ox.CQ(FOc.get_ev.due(True{}, r), i):
  match r:
    case Wr.Got{+d, s2}:
      match s2:
        case SNil{}:
          +h = hr
          (Equal.sym(String, i, Wr.put_nat(5n, Wr.put_nat(d, "")), LWireDec.dcw.after(i, 5n, s1, Wr.put_nat(d, ""), ei, Wire.wire_nat_exact(s1, d, "", h))), Wire.wire_nat_decoded_fits(s1, d, "", h))
        case SCon{x, t}:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ox.qneed(-i: String, +s1: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}, ei: {i == Wr.put_nat(6n, s1) : String}) -> ox.CQ(FOc.get_ev.due(False{}, r), i):
  match r:
    case Wr.Got{+d, s2}:
      match s2:
        case SNil{}:
          +h = hr
          (Equal.sym(String, i, Wr.put_nat(6n, Wr.put_nat(d, "")), LWireDec.dcw.after(i, 6n, s1, Wr.put_nat(d, ""), ei, Wire.wire_nat_exact(s1, d, "", h))), Wire.wire_nat_decoded_fits(s1, d, "", h))
        case SCon{x, t}:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ox.qbare(+n: Nat, -i: String, +s1: String, ei: {i == Wr.put_nat(n, s1) : String}, +q: FOc.Q, es: {Optchat.oc_spell(q) == Wr.put_nat(n, "") : String}, fq: {Optchat.oc_fits(q) == True{} : Bool}) -> ox.CQ(Wr.Got{q, s1}, i):
  match s1:
    case SNil{}:
      (Equal.trans(String, Optchat.oc_spell(q), Wr.put_nat(n, ""), i, es, Equal.sym(String, i, Wr.put_nat(n, ""), ei)), fq)
    case SCon{c, t}:
      Unit{}

def ox.q0(+i: String, r: Wr.Dec<Nat>, +hr: {Wr.get_nat(i) == r : Wr.Dec<Nat>}) -> ox.CQ(FOc.get_ev.go(r), i):
  match r:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          ox.qbare(0n, i, s1, Wire.wire_nat_exact(i, 0n, s1, hr), FOc.QMsg{}, {==}, {==})
        case 1n:
          ox.qbuilt(i, s1, Wire.wire_nat_exact(i, 1n, s1, hr), FOc.get_got(s1), ox.got(s1))
        case 2n:
          ox.qstart(i, s1, Wire.wire_nat_exact(i, 2n, s1, hr), FOc.get_line(s1), ox.line(s1))
        case 3n:
          ox.qfree(i, s1, Wire.wire_nat_exact(i, 3n, s1, hr), FOc.get_line(s1), ox.line(s1))
        case 4n:
          ox.qbare(4n, i, s1, Wire.wire_nat_exact(i, 4n, s1, hr), FOc.QWait{}, {==}, {==})
        case 5n:
          ox.qcands(i, s1, Wr.get_nat(s1), {==}, Wire.wire_nat_exact(i, 5n, s1, hr))
        case 6n:
          ox.qneed(i, s1, Wr.get_nat(s1), {==}, Wire.wire_nat_exact(i, 6n, s1, hr))
        case 7n:
          ox.qctx(i, s1, Wire.wire_nat_exact(i, 7n, s1, hr), FOc.get_line(s1), ox.line(s1))
        case 8n:
          ox.qbare(8n, i, s1, Wire.wire_nat_exact(i, 8n, s1, hr), FOc.QBusy{}, {==}, {==})
        case 9n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# The law
# -------

# an input the entry does not read whole keeps the chat
def ox.keep(+cfg: OState.Cfg, +s: OState.St, +i: String, -d: Wr.Dec<FOc.Q>, hd: {FOc.get_ev(i) == d : Wr.Dec<FOc.Q>}, k: {FOc.step.ev(cfg, s, d) == (FOc.Live{cfg, s}, FOc.fail()) : FOc.St & String})
  -> {FOc.step(FOc.Live{cfg, s}, i) == (FOc.Live{cfg, s}, Wr.err("optchat: malformed event")) : FOc.St & String}:
  %Equal.sym(Wr.Dec<FOc.Q>, FOc.get_ev(i), d, hd) : {FOc.step.ev(cfg, s, _) == (FOc.Live{cfg, s}, Wr.err("optchat: malformed event")) : FOc.St & String}
  k

# an input the entry reads whole is the spelling of what it read
def ox.got_whole(+i: String, +q: FOc.Q, hd: {FOc.get_ev(i) == Wr.Got{q, ""} : Wr.Dec<FOc.Q>}) -> {Optchat.oc_spell(q) == i : String} & {Optchat.oc_fits(q) == True{} : Bool}:
  %hd : ox.CQ(_, i)
  ox.q0(i, Wr.get_nat(i), {==})

def ox.ans(+cfg: OState.Cfg, +s: OState.St, +i: String, d: Wr.Dec<FOc.Q>, hd: {FOc.get_ev(i) == d : Wr.Dec<FOc.Q>}) -> Optchat.oc_spelled(i) | {FOc.step(FOc.Live{cfg, s}, i) == (FOc.Live{cfg, s}, Wr.err("optchat: malformed event")) : FOc.St & String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          Inl{(q, ox.got_whole(i, q, hd))}
        case SCon{c, t}:
          Inr{ox.keep(cfg, s, i, Wr.Got{q, SCon{c, t}}, hd, {==})}
    case Wr.Bad{}:
      Inr{ox.keep(cfg, s, i, Wr.Bad{}, hd, {==})}

def Optchat.optchat_entry_spelled_or_refused(cfg, s, i):
  ox.ans(cfg, s, i, FOc.get_ev(i), {==})
