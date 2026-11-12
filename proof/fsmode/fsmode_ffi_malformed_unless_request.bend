# eukhe: the proof of LAW fsmode_ffi_malformed_unless_request
# Each decoder of bend/ffi_fsmode.bend answers Got{x, rest} only for an
# input that is the laws' spelling of x before rest, with every number and
# length within the wire (fx.*: a predicate per decoder answer, carried
# stage by stage with the wire's exactness laws wire_nat_exact,
# wire_str_exact and their fits wire_nat_decoded_fits,
# wire_str_decoded_fits). The entry answers anything but its error form
# only for a request read whole with nothing left: that input is the
# spelled request (fx.top).

import Base
import ../../bend/ffi_fsmode.bend as FFs
import ../../bend/fsmode.bend as Fs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/fsmode.bend as Fsmode
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ./base.bend as LA

# The spelling with a rest
# ------------------------

# the request a written before r (spell_ask(a) is fx.spell(a, ""))
def fx.cwd_head(c: Maybe<&2, String>, x: String) -> String:
  match c:
    case None{}:
      Wr.put_nat(3n, Wr.put_nat(0n, x))
    case Some{p}:
      Wr.put_nat(3n, Wr.put_nat(1n, Wr.put_str(p, x)))

def fx.spell(a: Fs.Ask, r: String) -> String:
  match a:
    case Fs.AskDir{k, u, o, m}:
      Wr.put_nat(0n, Fsmode.spell_node(k, Wr.put_nat(u, Wr.put_nat(o, Wr.put_nat(m, r)))))
    case Fs.AskPeer{p, o}:
      Wr.put_nat(1n, Wr.put_nat(p, Wr.put_nat(o, r)))
    case Fs.AskMade{k}:
      match k:
        case Fs.DirMade{}:
          Wr.put_nat(2n, Wr.put_nat(0n, r))
        case Fs.FileMade{}:
          Wr.put_nat(2n, Wr.put_nat(1n, r))
    case Fs.AskCwd{c, s}:
      fx.cwd_head(c, Fsmode.spell_stat(s, r))

def fx.spell_nil(a: Fs.Ask) -> {fx.spell(a, "") == Fsmode.spell_ask(a) : String}:
  match a:
    case Fs.AskDir{k, u, o, m}:
      {==}
    case Fs.AskPeer{p, o}:
      {==}
    case Fs.AskMade{k}:
      match k:
        case Fs.DirMade{}:
          {==}
        case Fs.FileMade{}:
          {==}
    case Fs.AskCwd{c, s}:
      match c:
        case None{}:
          {==}
        case Some{p}:
          {==}

# Logic
# -----

def fx.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# s is the tag t then s1, and s1 is x: s is the tag t then x
def fx.after(-s: String, +t: Nat, -s1: String, -x: String, pre: {s == Wr.put_nat(t, s1) : String}, e: {s1 == x : String}) -> {s == Wr.put_nat(t, x) : String}:
  Equal.trans(String, s, Wr.put_nat(t, s1), Wr.put_nat(t, x), pre, Equal.cong(String, String, z => Wr.put_nat(t, z), s1, x, e))

# Primitives
# ----------

def fx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> fx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

def fx.nat(+s: String) -> fx.NP(s, Wr.get_nat(s)):
  fx.nat.at(s, Wr.get_nat(s), {==})

def fx.SP(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fx.str.at(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> fx.SP(s, d):
  match d:
    case Wr.Got{+a, +r}:
      +e2 = ed
      (Wire.wire_str_exact(s, a, r, e2), Wire.wire_str_decoded_fits(s, a, r, e2))
    case Wr.Bad{}:
      Unit{}

def fx.str(+s: String) -> fx.SP(s, Wr.get_str(s)):
  fx.str.at(s, Wr.get_str(s), {==})

# Requests
# --------

def fx.AP(s: String, d: Wr.Dec<Fs.Ask>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == fx.spell(a, r) : String} & {Fsmode.ask_fits(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a socket dir: the node, the owner's uid, this uid, the mode bits

def fx.NdP(s: String, d: Wr.Dec<Fs.Node>) -> Type:
  match d:
    case Wr.Got{k, r}:
      {s == Fsmode.spell_node(k, r) : String}
    case Wr.Bad{}:
      Unit

def fx.node.tag(t: Nat, -s: String, -r: String, e: {s == Wr.put_nat(t, r) : String}) -> fx.NdP(s, FFs.get_node.tag(t, r)):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n:
      e
    case 4n+p:
      Unit{}

def fx.node(-s: String, d: Wr.Dec<Nat>, np: fx.NP(s, d)) -> fx.NdP(s, FFs.get_node(d)):
  match d:
    case Wr.Got{+t, +r}:
      (e, f) = np
      fx.node.tag(t, s, r, e)
    case Wr.Bad{}:
      Unit{}

def fx.dir.mode(-s: String, +k: Fs.Node, +u: Nat, +o: Nat, -s4: String,
  pre: {s == Wr.put_nat(0n, Fsmode.spell_node(k, Wr.put_nat(u, Wr.put_nat(o, s4)))) : String},
  fu: {LawsBase.wire_fits(u) == True{} : Bool}, fo: {LawsBase.wire_fits(o) == True{} : Bool},
  d: Wr.Dec<Nat>, np: fx.NP(s4, d)) -> fx.AP(s, FFs.get_dir.mode(k, u, o, d)):
  match d:
    case Wr.Got{+m, +r}:
      (e, fm) = np
      (Equal.trans(String, s, Wr.put_nat(0n, Fsmode.spell_node(k, Wr.put_nat(u, Wr.put_nat(o, s4)))), Wr.put_nat(0n, Fsmode.spell_node(k, Wr.put_nat(u, Wr.put_nat(o, Wr.put_nat(m, r))))), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, Fsmode.spell_node(k, Wr.put_nat(u, Wr.put_nat(o, z)))), s4, Wr.put_nat(m, r), e)),
        fx.and_tt(LawsBase.wire_fits(u), Bool.and(LawsBase.wire_fits(o), LawsBase.wire_fits(m)), fu, fx.and_tt(LawsBase.wire_fits(o), LawsBase.wire_fits(m), fo, fm)))
    case Wr.Bad{}:
      Unit{}

def fx.dir.own(-s: String, +k: Fs.Node, +u: Nat, -s3: String,
  pre: {s == Wr.put_nat(0n, Fsmode.spell_node(k, Wr.put_nat(u, s3))) : String},
  fu: {LawsBase.wire_fits(u) == True{} : Bool},
  d: Wr.Dec<Nat>, np: fx.NP(s3, d)) -> fx.AP(s, FFs.get_dir.own(k, u, d)):
  match d:
    case Wr.Got{+o, +s4}:
      (e, fo) = np
      fx.dir.mode(s, k, u, o, s4,
        Equal.trans(String, s, Wr.put_nat(0n, Fsmode.spell_node(k, Wr.put_nat(u, s3))), Wr.put_nat(0n, Fsmode.spell_node(k, Wr.put_nat(u, Wr.put_nat(o, s4)))), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, Fsmode.spell_node(k, Wr.put_nat(u, z))), s3, Wr.put_nat(o, s4), e)),
        fu, fo, Wr.get_nat(s4), fx.nat(s4))
    case Wr.Bad{}:
      Unit{}

def fx.dir.uid(-s: String, +k: Fs.Node, -s2: String,
  pre: {s == Wr.put_nat(0n, Fsmode.spell_node(k, s2)) : String},
  d: Wr.Dec<Nat>, np: fx.NP(s2, d)) -> fx.AP(s, FFs.get_dir.uid(k, d)):
  match d:
    case Wr.Got{+u, +s3}:
      (e, fu) = np
      fx.dir.own(s, k, u, s3,
        Equal.trans(String, s, Wr.put_nat(0n, Fsmode.spell_node(k, s2)), Wr.put_nat(0n, Fsmode.spell_node(k, Wr.put_nat(u, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, Fsmode.spell_node(k, z)), s2, Wr.put_nat(u, s3), e)),
        fu, Wr.get_nat(s3), fx.nat(s3))
    case Wr.Bad{}:
      Unit{}

def fx.dir(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Fs.Node>, ndp: fx.NdP(s1, d)) -> fx.AP(s, FFs.get_dir(d)):
  match d:
    case Wr.Got{+k, +s2}:
      fx.dir.uid(s, k, s2, fx.after(s, 0n, s1, Fsmode.spell_node(k, s2), pre, ndp), Wr.get_nat(s2), fx.nat(s2))
    case Wr.Bad{}:
      Unit{}

# a peer: its uid, this uid

def fx.peer.own(-s: String, +p: Nat, -s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(p, s2)) : String}, fp: {LawsBase.wire_fits(p) == True{} : Bool}, d: Wr.Dec<Nat>, np: fx.NP(s2, d)) -> fx.AP(s, FFs.get_peer.own(p, d)):
  match d:
    case Wr.Got{+o, +r}:
      (e, fo) = np
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(p, s2)), Wr.put_nat(1n, Wr.put_nat(p, Wr.put_nat(o, r))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(p, z)), s2, Wr.put_nat(o, r), e)),
        fx.and_tt(LawsBase.wire_fits(p), LawsBase.wire_fits(o), fp, fo))
    case Wr.Bad{}:
      Unit{}

def fx.peer(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, np: fx.NP(s1, d)) -> fx.AP(s, FFs.get_peer(d)):
  match d:
    case Wr.Got{+p, +s2}:
      (e, fp) = np
      fx.peer.own(s, p, s2, fx.after(s, 1n, s1, Wr.put_nat(p, s2), pre, e), fp, Wr.get_nat(s2), fx.nat(s2))
    case Wr.Bad{}:
      Unit{}

# what eukhe creates: 0 a dir, 1 a file

def fx.made.tag(t: Nat, -s: String, -s1: String, -r: String, pre: {s == Wr.put_nat(2n, s1) : String}, e: {s1 == Wr.put_nat(t, r) : String}) -> fx.AP(s, FFs.get_made.tag(t, r)):
  match t:
    case 0n:
      (fx.after(s, 2n, s1, Wr.put_nat(0n, r), pre, e), {==})
    case 1n:
      (fx.after(s, 2n, s1, Wr.put_nat(1n, r), pre, e), {==})
    case 2n+p:
      Unit{}

def fx.made(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, np: fx.NP(s1, d)) -> fx.AP(s, FFs.get_made(d)):
  match d:
    case Wr.Got{+t, +r}:
      (e, f) = np
      fx.made.tag(t, s, s1, r, pre, e)
    case Wr.Bad{}:
      Unit{}

# a create's cwd: none, or a path; then what metadata found

def fx.cfits(c: Maybe<&2, String>) -> Bool:
  match c:
    case None{}:
      True{}
    case Some{p}:
      LawsBase.wire_fits(String.length(p))

def fx.cfits_ask(c: Maybe<&2, String>, -st: Fs.Stat, f: {fx.cfits(c) == True{} : Bool}) -> {Fsmode.ask_fits(Fs.AskCwd{c, st}) == True{} : Bool}:
  match c:
    case None{}:
      {==}
    case Some{p}:
      f

def fx.stat.tag(t: Nat, -s: String, +c: Maybe<&2, String>, -s2: String, -r: String, pre: {s == fx.cwd_head(c, s2) : String}, fc: {fx.cfits(c) == True{} : Bool}, e: {s2 == Wr.put_nat(t, r) : String}) -> fx.AP(s, FFs.get_stat.tag(c, t, r)):
  match t:
    case 0n:
      (Equal.trans(String, s, fx.cwd_head(c, s2), fx.cwd_head(c, Wr.put_nat(0n, r)), pre, Equal.cong(String, String, z => fx.cwd_head(c, z), s2, Wr.put_nat(0n, r), e)), fx.cfits_ask(c, Fs.Absent{}, fc))
    case 1n:
      (Equal.trans(String, s, fx.cwd_head(c, s2), fx.cwd_head(c, Wr.put_nat(1n, r)), pre, Equal.cong(String, String, z => fx.cwd_head(c, z), s2, Wr.put_nat(1n, r), e)), fx.cfits_ask(c, Fs.AFile{}, fc))
    case 2n:
      (Equal.trans(String, s, fx.cwd_head(c, s2), fx.cwd_head(c, Wr.put_nat(2n, r)), pre, Equal.cong(String, String, z => fx.cwd_head(c, z), s2, Wr.put_nat(2n, r), e)), fx.cfits_ask(c, Fs.ADir{}, fc))
    case 3n+p:
      Unit{}

def fx.stat(-s: String, +c: Maybe<&2, String>, -s2: String, pre: {s == fx.cwd_head(c, s2) : String}, fc: {fx.cfits(c) == True{} : Bool}, d: Wr.Dec<Nat>, np: fx.NP(s2, d)) -> fx.AP(s, FFs.get_stat(c, d)):
  match d:
    case Wr.Got{+t, +r}:
      (e, f) = np
      fx.stat.tag(t, s, c, s2, r, pre, fc, e)
    case Wr.Bad{}:
      Unit{}

def fx.cwd.path(-s: String, -s2: String, pre: {s == Wr.put_nat(3n, Wr.put_nat(1n, s2)) : String}, d: Wr.Dec<String>, sp: fx.SP(s2, d)) -> fx.AP(s, FFs.get_cwd.path(d)):
  match d:
    case Wr.Got{+p, +s3}:
      (e, fp) = sp
      fx.stat(s, Some{p}, s3,
        Equal.trans(String, s, Wr.put_nat(3n, Wr.put_nat(1n, s2)), Wr.put_nat(3n, Wr.put_nat(1n, Wr.put_str(p, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(3n, Wr.put_nat(1n, z)), s2, Wr.put_str(p, s3), e)),
        fp, Wr.get_nat(s3), fx.nat(s3))
    case Wr.Bad{}:
      Unit{}

def fx.cwd.tag(t: Nat, -s: String, -s1: String, +s2: String, pre: {s == Wr.put_nat(3n, s1) : String}, e: {s1 == Wr.put_nat(t, s2) : String}) -> fx.AP(s, FFs.get_cwd.tag(t, s2)):
  match t:
    case 0n:
      fx.stat(s, None{}, s2, fx.after(s, 3n, s1, Wr.put_nat(0n, s2), pre, e), {==}, Wr.get_nat(s2), fx.nat(s2))
    case 1n:
      fx.cwd.path(s, s2, fx.after(s, 3n, s1, Wr.put_nat(1n, s2), pre, e), Wr.get_str(s2), fx.str(s2))
    case 2n+p:
      Unit{}

def fx.cwd(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Nat>, np: fx.NP(s1, d)) -> fx.AP(s, FFs.get_cwd(d)):
  match d:
    case Wr.Got{+t, +s2}:
      (e, f) = np
      fx.cwd.tag(t, s, s1, s2, pre, e)
    case Wr.Bad{}:
      Unit{}

# the request

def fx.ask.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> fx.AP(s, FFs.get_ask.tag(t, s1)):
  match t:
    case 0n:
      fx.dir(s, s1, pre, FFs.get_node(Wr.get_nat(s1)), fx.node(s1, Wr.get_nat(s1), fx.nat(s1)))
    case 1n:
      fx.peer(s, s1, pre, Wr.get_nat(s1), fx.nat(s1))
    case 2n:
      fx.made(s, s1, pre, Wr.get_nat(s1), fx.nat(s1))
    case 3n:
      fx.cwd(s, s1, pre, Wr.get_nat(s1), fx.nat(s1))
    case 4n+p:
      Unit{}

def fx.ask.go(-s: String, d: Wr.Dec<Nat>, np: fx.NP(s, d)) -> fx.AP(s, FFs.get_ask.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      fx.ask.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def fx.ask(+s: String) -> fx.AP(s, FFs.get_ask(s)):
  fx.ask.go(s, Wr.get_nat(s), fx.nat(s))

# The entry
# ---------

def fx.goal(+s: String) -> Type:
  &a: Fs.Ask -> {s == Fsmode.spell_ask(a) : String} & {Fsmode.ask_fits(a) == True{} : Bool}

# an answer other than the error form: a request read whole, nothing left
def fx.top(+s: String, d: Wr.Dec<Fs.Ask>, ap: fx.AP(s, d), other: {String.eq(FFs.run(d), "E fsmode: malformed request") == False{} : Bool}) -> fx.goal(s):
  match d:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          (e, f) = ap
          (a, (Equal.trans(String, s, fx.spell(a, ""), Fsmode.spell_ask(a), e, fx.spell_nil(a)), f))
        case SCon{x, y}:
          LA.fsmode.pf.absurdT(fx.goal(s), other)
    case Wr.Bad{}:
      LA.fsmode.pf.absurdT(fx.goal(s), other)

def Fsmode.fsmode_ffi_malformed_unless_request(s, other):
  fx.top(s, FFs.get_ask(s), fx.ask(s), other)
