# eukhe: the proof of LAW notice_ffi_exact

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ../../laws/wire.bend as Wire
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire
import ../base/logic/wire.bend as LLogicWire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_str_exact.bend as PWireStrExact
import ./base.bend as LA

# Each decoder layer that answers Got gives the prefix of the spec's
# spelling and a value that fits the wire (a property of the decoder's
# answer, Unit for Bad, as in proof/wire/wire_str_exact.bend): a Nat by
# wire_nat_exact and wire_nat_decoded_fits, a String by wire_str_exact and
# the length its take reads (PWireStrExact.wr_take_spec), a message by its
# tag, a list item by item, an ask by its tag. A step that does not answer
# the error form read an ask with nothing left over.

# Strings
# -------

# a decoded string fits the wire
def nx.PS(d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {Notice.nt_str_fits(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def nx.sfit_conv(+n: Nat, hn: {LawsBase.wire_fits(n) == True{} : Bool}, -s2: String, d: Wr.Dec<String>, pt: PWireStrExact.wr_pt(s2, n, d)) -> nx.PS(d):
  match d:
    case Wr.Got{+a, +r}:
      (e1, e2) = pt
      %Equal.sym(Nat, String.length(a), n, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
      hn
    case Wr.Bad{}:
      Unit{}

def nx.str_fit_top(+s: String, r: Wr.Dec<Nat>, +er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> nx.PS(Wr.get_str.go(r)):
  match r:
    case Wr.Got{+n, +s2}:
      %Equal.sym(Wr.Dec<String>, Wr.take(n, s2), LLogicWire.wo_take(n, s2), LWire.wr_take_eq(n, s2)) : nx.PS(_)
      nx.sfit_conv(n, Wire.wire_nat_decoded_fits(s, n, s2, er), s2, LLogicWire.wo_take(n, s2), PWireStrExact.wr_take_spec(n, s2))
    case Wr.Bad{}:
      Unit{}

def nx.str_fit(+s: String) -> nx.PS(Wr.get_str(s)):
  nx.str_fit_top(s, Wr.get_nat(s), {==})

def nx.str_ex(+s: String) -> PWireStrExact.wr_ps(s, Wr.get_str(s)):
  PWireStrExact.wr_str_top(s, Wr.get_nat(s), {==})

# Messages
# --------

def nx.PM(s: String, d: Wr.Dec<No.Msg>) -> Type:
  match d:
    case Wr.Got{+m, +r}:
      {s == Notice.nt_spell_msg(m, r) : String} & {Notice.nt_msg_fits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def nx.msg_custom(-s: String, +k: String, -s1: String, +s2: String, es: {s == Wr.put_nat(1n, s1) : String}, es1: {s1 == Wr.put_str(k, s2) : String}, hk: {Notice.nt_str_fits(k) == True{} : Bool}, d: Wr.Dec<String>, ps: PWireStrExact.wr_ps(s2, d), pf: nx.PS(d)) -> nx.PM(s, FNo.get_msg.custom(k, d)):
  match d:
    case Wr.Got{+st, +s3}:
      +x = Wr.put_str(st, s3)
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(k, x)), es, Equal.cong(String, String, y => Wr.put_nat(1n, y), s1, Wr.put_str(k, x), Equal.trans(String, s1, Wr.put_str(k, s2), Wr.put_str(k, x), es1, Equal.cong(String, String, z => Wr.put_str(k, z), s2, x, ps)))), LA.notice.pn.and_t(Notice.nt_str_fits(k), Notice.nt_str_fits(st), hk, pf))
    case Wr.Bad{}:
      Unit{}

def nx.msg_kind(-s: String, -s1: String, es: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, ps: PWireStrExact.wr_ps(s1, d), pf: nx.PS(d)) -> nx.PM(s, FNo.get_msg.kind(d)):
  match d:
    case Wr.Got{+k, +s2}:
      nx.msg_custom(s, k, s1, s2, es, ps, pf, Wr.get_str(s2), nx.str_ex(s2), nx.str_fit(s2))
    case Wr.Bad{}:
      Unit{}

def nx.msg_tag(n: Nat, +s: String, +s1: String, es: {s == Wr.put_nat(n, s1) : String}) -> nx.PM(s, FNo.get_msg.tag(n, s1)):
  match n:
    case 0n:
      (es, {==})
    case 1n+a:
      match a:
        case 0n:
          nx.msg_kind(s, s1, es, Wr.get_str(s1), nx.str_ex(s1), nx.str_fit(s1))
        case 1n+b:
          Unit{}

def nx.msg_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> nx.PM(s, FNo.get_msg.go(r)):
  match r:
    case Wr.Got{+n, +s1}:
      nx.msg_tag(n, s, s1, Wire.wire_nat_exact(s, n, s1, er))
    case Wr.Bad{}:
      Unit{}

def nx.msg_spec(+s: String) -> nx.PM(s, FNo.get_msg(s)):
  nx.msg_top(s, Wr.get_nat(s), {==})

# Lists of messages
# -----------------

# what the item loop's answer says about its input s (m + 1 items)
def nx.PL1(s: String, m: Nat, d: Wr.Dec<List<&2, No.Msg>>) -> Type:
  match d:
    case Wr.Got{+ms, +r}:
      {s == LA.nt.items(ms, r) : String} & ({List.length(&2, No.Msg, ms) == 1n+m : Nat} & {Notice.nt_msgs_fit(ms) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def nx.list_step(-s: String, +x: No.Msg, +s3: String, -k: Nat, ex: {s == Notice.nt_spell_msg(x, s3) : String}, fx: {Notice.nt_msg_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, No.Msg>>, ih: nx.PL1(s3, k, d)) -> nx.PL1(s, 1n+k, Wr.get_list.cons(No.Msg, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, more) = ih
      (e2, e3) = more
      (Equal.trans(String, s, Notice.nt_spell_msg(x, s3), Notice.nt_spell_msg(x, LA.nt.items(ys, r)), ex, Equal.cong(String, String, z => Notice.nt_spell_msg(x, z), s3, LA.nt.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, No.Msg, ys), 1n+k, e2), LA.notice.pn.and_t(Notice.nt_msg_fits(x), Notice.nt_msgs_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only items that are spellings
def nx.list_spec(m: Nat, cur: Wr.Dec<No.Msg>, +s: String, pc: nx.PM(s, cur)) -> nx.PL1(s, m, Wr.get_list.go(~No.Msg, ~FNo.get_msg, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (ex, fx) = pc
      (ex, ({==}, LA.notice.pn.and_t(Notice.nt_msg_fits(x), True{}, fx, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (ex, fx) = pc
      nx.list_step(s, x, s3, k, ex, fx, Wr.get_list.go(~No.Msg, ~FNo.get_msg, k, FNo.get_msg(s3)), nx.list_spec(k, FNo.get_msg(s3), s3, nx.msg_spec(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder answer says about its input s
def nx.PLS(s: String, d: Wr.Dec<List<&2, No.Msg>>) -> Type:
  match d:
    case Wr.Got{+ms, +r}:
      {s == Wr.put_list(~No.Msg, ~Notice.nt_spell_msg, ms, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, No.Msg, ms)), Notice.nt_msgs_fit(ms)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def nx.list_eq(+s: String, +s2: String, +m: Nat, +ms: List<&2, No.Msg>, +r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == LA.nt.items(ms, r) : String}, e2: {List.length(&2, No.Msg, ms) == 1n+m : Nat}) -> {s == Wr.put_list(~No.Msg, ~Notice.nt_spell_msg, ms, r) : String}:
  %Equal.sym(String, Wr.put_list(~No.Msg, ~Notice.nt_spell_msg, ms, r), Wr.put_nat(List.length(&2, No.Msg, ms), LA.nt.items(ms, r)), LA.nt.put_list(ms, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, No.Msg, ms), 1n+m, e2) : {s == Wr.put_nat(_, LA.nt.items(ms, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def nx.list_fits(+ms: List<&2, No.Msg>, +m: Nat, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, e2: {List.length(&2, No.Msg, ms) == 1n+m : Nat}, e3: {Notice.nt_msgs_fit(ms) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, No.Msg, ms)), Notice.nt_msgs_fit(ms)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, No.Msg, ms), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), Notice.nt_msgs_fit(ms)) == True{} : Bool}
  LA.notice.pn.and_t(LawsBase.wire_fits(1n+m), Notice.nt_msgs_fit(ms), hn, e3)

def nx.list_conv(+s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, No.Msg>>, pl: nx.PL1(s2, m, d)) -> nx.PLS(s, d):
  match d:
    case Wr.Got{+ms, +r}:
      (e1, more) = pl
      (+e2, e3) = more
      (nx.list_eq(s, s2, m, ms, r, en, e1, e2), nx.list_fits(ms, m, hn, e2, e3))
    case Wr.Bad{}:
      Unit{}

def nx.list_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, hn: {LawsBase.wire_fits(n) == True{} : Bool}) -> nx.PLS(s, Wr.get_list.start(~No.Msg, ~FNo.get_msg, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      nx.list_conv(s, s2, m, en, hn, Wr.get_list.go(~No.Msg, ~FNo.get_msg, m, FNo.get_msg(s2)), nx.list_spec(m, FNo.get_msg(s2), s2, nx.msg_spec(s2)))

def nx.list_top(+s: String, r: Wr.Dec<Nat>, +er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> nx.PLS(s, Wr.get_list.start(~No.Msg, ~FNo.get_msg, r)):
  match r:
    case Wr.Got{+n, +s2}:
      nx.list_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, er), Wire.wire_nat_decoded_fits(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

def nx.list_ex(+s: String) -> nx.PLS(s, Wr.get_list(~No.Msg, ~FNo.get_msg, s)):
  nx.list_top(s, Wr.get_nat(s), {==})

# Asks
# ----

def nx.PA(s: String, d: Wr.Dec<No.Ask>) -> Type:
  match d:
    case Wr.Got{+q, +r}:
      {s == Notice.nt_spell_ask(q, r) : String} & {Notice.nt_ask_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def nx.ask_shows(-s: String, +sid: String, -s1: String, +s2: String, es: {s == Wr.put_nat(0n, s1) : String}, es1: {s1 == Wr.put_str(sid, s2) : String}, hs: {Notice.nt_str_fits(sid) == True{} : Bool}, d: Wr.Dec<No.Msg>, pm: nx.PM(s2, d)) -> nx.PA(s, FNo.get_ask.shows(sid, d)):
  match d:
    case Wr.Got{+m, +s3}:
      (e1, f1) = pm
      +x = Notice.nt_spell_msg(m, s3)
      (Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_str(sid, x)), es, Equal.cong(String, String, y => Wr.put_nat(0n, y), s1, Wr.put_str(sid, x), Equal.trans(String, s1, Wr.put_str(sid, s2), Wr.put_str(sid, x), es1, Equal.cong(String, String, z => Wr.put_str(sid, z), s2, x, e1)))), LA.notice.pn.and_t(Notice.nt_str_fits(sid), Notice.nt_msg_fits(m), hs, f1))
    case Wr.Bad{}:
      Unit{}

def nx.ask_shows_sid(-s: String, -s1: String, es: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, ps: PWireStrExact.wr_ps(s1, d), pf: nx.PS(d)) -> nx.PA(s, FNo.get_ask.shows.sid(d)):
  match d:
    case Wr.Got{+sid, +s2}:
      nx.ask_shows(s, sid, s1, s2, es, ps, pf, FNo.get_msg(s2), nx.msg_spec(s2))
    case Wr.Bad{}:
      Unit{}

def nx.ask_notes(-s: String, +sid: String, -s1: String, +s2: String, es: {s == Wr.put_nat(1n, s1) : String}, es1: {s1 == Wr.put_str(sid, s2) : String}, hs: {Notice.nt_str_fits(sid) == True{} : Bool}, d: Wr.Dec<List<&2, No.Msg>>, pl: nx.PLS(s2, d)) -> nx.PA(s, FNo.get_ask.notes(sid, d)):
  match d:
    case Wr.Got{+ms, +s3}:
      (e1, f1) = pl
      +x = Wr.put_list(~No.Msg, ~Notice.nt_spell_msg, ms, s3)
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(sid, x)), es, Equal.cong(String, String, y => Wr.put_nat(1n, y), s1, Wr.put_str(sid, x), Equal.trans(String, s1, Wr.put_str(sid, s2), Wr.put_str(sid, x), es1, Equal.cong(String, String, z => Wr.put_str(sid, z), s2, x, e1)))), LA.notice.pn.and_t(Notice.nt_str_fits(sid), Bool.and(LawsBase.wire_fits(List.length(&2, No.Msg, ms)), Notice.nt_msgs_fit(ms)), hs, f1))
    case Wr.Bad{}:
      Unit{}

def nx.ask_notes_sid(-s: String, -s1: String, es: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, ps: PWireStrExact.wr_ps(s1, d), pf: nx.PS(d)) -> nx.PA(s, FNo.get_ask.notes.sid(d)):
  match d:
    case Wr.Got{+sid, +s2}:
      nx.ask_notes(s, sid, s1, s2, es, ps, pf, Wr.get_list(~No.Msg, ~FNo.get_msg, s2), nx.list_ex(s2))
    case Wr.Bad{}:
      Unit{}

def nx.ask_tag(n: Nat, +s: String, +s1: String, es: {s == Wr.put_nat(n, s1) : String}) -> nx.PA(s, FNo.get_ask.tag(n, s1)):
  match n:
    case 0n:
      nx.ask_shows_sid(s, s1, es, Wr.get_str(s1), nx.str_ex(s1), nx.str_fit(s1))
    case 1n+a:
      match a:
        case 0n:
          nx.ask_notes_sid(s, s1, es, Wr.get_str(s1), nx.str_ex(s1), nx.str_fit(s1))
        case 1n+b:
          Unit{}

def nx.ask_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> nx.PA(s, FNo.get_ask.go(r)):
  match r:
    case Wr.Got{+n, +s1}:
      nx.ask_tag(n, s, s1, Wire.wire_nat_exact(s, n, s1, er))
    case Wr.Bad{}:
      Unit{}

# a decoded ask is the spelling of an ask that fits, then the rest
def nx.ask_spec(+s: String) -> nx.PA(s, FNo.get_ask(s)):
  nx.ask_top(s, Wr.get_nat(s), {==})

# The step
# --------

# an ask that fits, spelled whole as s
def nx.Ex(s: String) -> Type:
  &q: No.Ask -> {Notice.nt_ask_fits(q) == True{} : Bool} & {s == Notice.nt_spell_ask(q, "") : String}

def nx.got(rest: String, +rs: List<&2, No.Seen>, +s: String, +q: No.Ask, pa: nx.PA(s, Wr.Got{q, rest}), h: {LawsBase.wire_opens_err(Notice.nt_out(FNo.step.end(Wr.end(rest), rs, q))) == False{} : Bool}) -> nx.Ex(s):
  match rest:
    case SNil{}:
      (e1, f1) = pa
      (q, (f1, e1))
    case SCon{c, t}:
      LA.notice.pn.absurdF(nx.Ex(s), Equal.sym(Bool, True{}, False{}, h))

def nx.at(+rs: List<&2, No.Seen>, +s: String, d: Wr.Dec<No.Ask>, pa: nx.PA(s, d), h: {LawsBase.wire_opens_err(Notice.nt_out(FNo.step.ask(rs, d))) == False{} : Bool}) -> nx.Ex(s):
  match d:
    case Wr.Got{+q, +rest}:
      nx.got(rest, rs, s, q, pa, h)
    case Wr.Bad{}:
      LA.notice.pn.absurdF(nx.Ex(s), Equal.sym(Bool, True{}, False{}, h))

def Notice.notice_ffi_exact(rs, s, h):
  nx.at(rs, s, FNo.get_ask(s), nx.ask_spec(s), h)
