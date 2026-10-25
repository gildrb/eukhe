# eukhe: lemmas the proofs of the tiny run entry share
# (bend/ffi_tiny_run.bend, laws tiny_run_entry_* of laws/tiny/run.bend)
#
# Reading: a spelled open, outcome or probe reads back whole and leaves
# the rest untouched (tre.*: tags compute, a tag text reads back by
# wire_str_round_trip). Exactness: each decoder answers Got{x, rest}
# only for an input that is the spec's spelling of x before rest, with x
# within the wire (tx.*: a predicate per decoder answer, carried stage by
# stage with wire_nat_exact, wire_str_exact and wire_nat_too_long).
# Replies: the entry's encoder is the spec's spelling (tre.put_do), and
# no reply opens with the error form (tre.do_ok).

import Base
import ../../../bend/tiny.bend as Tn
import ../../../bend/ffi_tiny_run.bend as FTr
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/tiny/run.bend as TinyRun
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_too_long.bend as PWireNatTooLong
import ../../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../../wire/wire_str_exact.bend as PWireStrExact
import ../../base/wire.bend as LWire
import ../../base/logic/string.bend as LLogicString
import ../base.bend as LA

# Logic
# -----

def tx.DT(-A: Data, d: Wr.Dec<A>, G: Type) -> Type:
  match d:
    case Wr.Got{x, r}:
      Unit
    case Wr.Bad{}:
      G

# a decoder answered Got and Bad
def tx.got_bad(-A: Data, -G: Type, -x: A, -r: String, e: {Wr.Got{x, r} == Wr.Bad{} : Wr.Dec<A>}) -> G:
  %e : tx.DT(A, _, G)
  Unit{}

# s is the tag t then s1, and s1 is x: s is the tag t then x
def tx.after(-s: String, +t: Nat, -s1: String, -x: String, pre: {s == Wr.put_nat(t, s1) : String}, e: {s1 == x : String}) -> {s == Wr.put_nat(t, x) : String}:
  Equal.trans(String, s, Wr.put_nat(t, s1), Wr.put_nat(t, x), pre, Equal.cong(String, String, z => Wr.put_nat(t, z), s1, x, e))

# Primitives
# ----------

def tx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String}
    case Wr.Bad{}:
      Unit

def tx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      Wire.wire_nat_exact(s, n, r, ed)
    case Wr.Bad{}:
      Unit{}

def tx.nat(+s: String) -> tx.NP(s, Wr.get_nat(s)):
  tx.nat.at(s, Wr.get_nat(s), {==})

# a decoded string's length fits: a longer one's count is refused
def tx.str_fits.at(b: Bool, +s: String, +a: String, +r: String, eb: {LawsBase.wire_fits(String.length(a)) == b : Bool}, e1: {s == Wr.put_str(a, r) : String}, ed: {Wr.get_str(s) == Wr.Got{a, r} : Wr.Dec<String>}) -> {LawsBase.wire_fits(String.length(a)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +x = LLogicString.wr_app(a, r)
      +c1 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(s), Wr.get_str(Wr.put_str(a, r)), Equal.sym(Wr.Dec<String>, Wr.get_str(s), Wr.Got{a, r}, ed), Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), s, Wr.put_str(a, r), e1))
      +c2 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_str(a, r)), Wr.get_str(Wr.put_nat(String.length(a), x)), c1, Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), Wr.put_str(a, r), Wr.put_nat(String.length(a), x), LWire.wr_put_str(a, r)))
      +c3 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_nat(String.length(a), x)), Wr.Bad{}, c2, Equal.cong(Wr.Dec<Nat>, Wr.Dec<String>, z => Wr.get_str.go(z), Wr.get_nat(Wr.put_nat(String.length(a), x)), Wr.Bad{}, Wire.wire_nat_too_long(String.length(a), x, eb)))
      tx.got_bad(String, {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, a, r, c3)

def tx.SP(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.str.at(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> tx.SP(s, d):
  match d:
    case Wr.Got{+a, +r}:
      +e2 = ed
      +e1 = Wire.wire_str_exact(s, a, r, e2)
      (e1, tx.str_fits.at(LawsBase.wire_fits(String.length(a)), s, a, r, {==}, e1, e2))
    case Wr.Bad{}:
      Unit{}

def tx.str(+s: String) -> tx.SP(s, Wr.get_str(s)):
  tx.str.at(s, Wr.get_str(s), {==})

# Probes
# ------

def tx.PrP(s: String, d: Wr.Dec<Tn.Probe>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == TinyRun.sp_w_probe(p, r) : String} & {TinyRun.sp_fit_probe(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.probe.pong(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, sp: tx.SP(s1, d)) -> tx.PrP(s, FTr.get_probe.pong(d)):
  match d:
    case Wr.Got{+a, +r}:
      (e, f) = sp
      (tx.after(s, 2n, s1, Wr.put_str(a, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def tx.probe.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tx.PrP(s, FTr.get_probe.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      (pre, {==})
    case 2n:
      tx.probe.pong(s, s1, pre, Wr.get_str(s1), tx.str(s1))
    case 3n:
      (pre, {==})
    case 4n:
      (pre, {==})
    case 5n:
      (pre, {==})
    case 6n+u:
      Unit{}

def tx.probe.go(-s: String, d: Wr.Dec<Nat>, np: tx.NP(s, d)) -> tx.PrP(s, FTr.get_probe(d)):
  match d:
    case Wr.Got{t, s1}:
      tx.probe.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def tx.probe(+s: String) -> tx.PrP(s, FTr.get_probe(Wr.get_nat(s))):
  tx.probe.go(s, Wr.get_nat(s), tx.nat(s))

# Heard, Launch
# --------------

def tx.HP(s: String, d: Wr.Dec<Tn.Heard>) -> Type:
  match d:
    case Wr.Got{h, r}:
      {s == Wr.put_nat(TinyRun.sp_w_heard(h), r) : String}
    case Wr.Bad{}:
      Unit

def tx.heard.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tx.HP(s, FTr.get_heard.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n:
      pre
    case 3n:
      pre
    case 4n+u:
      Unit{}

def tx.heard.go(-s: String, d: Wr.Dec<Nat>, np: tx.NP(s, d)) -> tx.HP(s, FTr.get_heard(d)):
  match d:
    case Wr.Got{t, s1}:
      tx.heard.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def tx.heard(+s: String) -> tx.HP(s, FTr.get_heard(Wr.get_nat(s))):
  tx.heard.go(s, Wr.get_nat(s), tx.nat(s))

def tx.LP(s: String, d: Wr.Dec<Tn.Launch>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Wr.put_nat(TinyRun.sp_w_launch(l), r) : String}
    case Wr.Bad{}:
      Unit

def tx.launch.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tx.LP(s, FTr.get_launch.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n+u:
      Unit{}

def tx.launch.go(-s: String, d: Wr.Dec<Nat>, np: tx.NP(s, d)) -> tx.LP(s, FTr.get_launch(d)):
  match d:
    case Wr.Got{t, s1}:
      tx.launch.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def tx.launch(+s: String) -> tx.LP(s, FTr.get_launch(Wr.get_nat(s))):
  tx.launch.go(s, Wr.get_nat(s), tx.nat(s))

# Outcomes
# --------

def tx.EP(s: String, d: Wr.Dec<Tn.Seen>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == TinyRun.sp_w_seen(e, r) : String} & {TinyRun.sp_fit_seen(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.seen.pinged(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Tn.Probe>, pp: tx.PrP(s1, d)) -> tx.EP(s, FTr.seen.pinged(d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, f) = pp
      (tx.after(s, 0n, s1, TinyRun.sp_w_probe(p, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def tx.seen.heard(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Tn.Heard>, hp: tx.HP(s1, d)) -> tx.EP(s, FTr.seen.heard(d)):
  match d:
    case Wr.Got{+h, +r}:
      (tx.after(s, 1n, s1, Wr.put_nat(TinyRun.sp_w_heard(h), r), pre, hp), {==})
    case Wr.Bad{}:
      Unit{}

def tx.seen.came(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Tn.Launch>, lp: tx.LP(s1, d)) -> tx.EP(s, FTr.seen.came(d)):
  match d:
    case Wr.Got{+l, +r}:
      (tx.after(s, 2n, s1, Wr.put_nat(TinyRun.sp_w_launch(l), r), pre, lp), {==})
    case Wr.Bad{}:
      Unit{}

def tx.seen.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tx.EP(s, FTr.get_seen.tag(t, s1)):
  match t:
    case 0n:
      tx.seen.pinged(s, s1, pre, FTr.get_probe(Wr.get_nat(s1)), tx.probe(s1))
    case 1n:
      tx.seen.heard(s, s1, pre, FTr.get_heard(Wr.get_nat(s1)), tx.heard(s1))
    case 2n:
      tx.seen.came(s, s1, pre, FTr.get_launch(Wr.get_nat(s1)), tx.launch(s1))
    case 3n:
      (pre, {==})
    case 4n:
      (pre, {==})
    case 5n+u:
      Unit{}

def tx.seen.go(-s: String, d: Wr.Dec<Nat>, np: tx.NP(s, d)) -> tx.EP(s, FTr.get_seen.go(d)):
  match d:
    case Wr.Got{t, s1}:
      tx.seen.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def tx.seen(+s: String) -> tx.EP(s, FTr.get_seen(s)):
  tx.seen.go(s, Wr.get_nat(s), tx.nat(s))

# Opens
# -----

def tx.OP(s: String, d: Wr.Dec<FTr.Open>) -> Type:
  match d:
    case Wr.Got{o, r}:
      {s == TinyRun.sp_w_open(o, r) : String} & {TinyRun.sp_fit_open(o) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.open.need(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, sp: tx.SP(s1, d)) -> tx.OP(s, FTr.open.need(d)):
  match d:
    case Wr.Got{+a, +r}:
      (e, f) = sp
      (tx.after(s, 0n, s1, Wr.put_str(a, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def tx.open.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tx.OP(s, FTr.get_open.tag(t, s1)):
  match t:
    case 0n:
      tx.open.need(s, s1, pre, Wr.get_str(s1), tx.str(s1))
    case 1n:
      (pre, {==})
    case 2n+u:
      Unit{}

def tx.open.go(-s: String, d: Wr.Dec<Nat>, np: tx.NP(s, d)) -> tx.OP(s, FTr.get_open.go(d)):
  match d:
    case Wr.Got{t, s1}:
      tx.open.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def tx.open(+s: String) -> tx.OP(s, FTr.get_open(s)):
  tx.open.go(s, Wr.get_nat(s), tx.nat(s))

# Reading
# -------

def tre.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def tre.probe(p: Tn.Probe, +rest: String, h: {TinyRun.sp_fit_probe(p) == True{} : Bool}) -> {FTr.get_probe(Wr.get_nat(TinyRun.sp_w_probe(p, rest))) == Wr.Got{p, rest} : Wr.Dec<Tn.Probe>}:
  match p:
    case Tn.Missing{}:
      {==}
    case Tn.Unreachable{}:
      {==}
    case Tn.Pong{+t}:
      %tre.str(t, rest, h) : {FTr.get_probe.pong(_) == Wr.Got{Tn.Pong{t}, rest} : Wr.Dec<Tn.Probe>}
      {==}
    case Tn.Odd{}:
      {==}
    case Tn.Garbled{}:
      {==}
    case Tn.Hung{}:
      {==}

# an outcome Rust spells reads back whole, the rest untouched
def tre.seen(e: Tn.Seen, +rest: String, h: {TinyRun.sp_fit_seen(e) == True{} : Bool}) -> {FTr.get_seen(TinyRun.sp_w_seen(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Tn.Seen>}:
  match e:
    case Tn.Pinged{+p}:
      %Equal.sym(Wr.Dec<Tn.Probe>, FTr.get_probe(Wr.get_nat(TinyRun.sp_w_probe(p, rest))), Wr.Got{p, rest}, tre.probe(p, rest, h)) : {FTr.seen.pinged(_) == Wr.Got{Tn.Pinged{p}, rest} : Wr.Dec<Tn.Seen>}
      {==}
    case Tn.ShutHeard{hd}:
      match hd:
        case Tn.Bye{}:
          {==}
        case Tn.Other{}:
          {==}
        case Tn.Eof{}:
          {==}
        case Tn.Lost{}:
          {==}
    case Tn.Came{l}:
      match l:
        case Tn.Bound{}:
          {==}
        case Tn.Adopted{}:
          {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

# an open Rust spells reads back whole, the rest untouched
def tre.open(o: FTr.Open, +rest: String, h: {TinyRun.sp_fit_open(o) == True{} : Bool}) -> {FTr.get_open(TinyRun.sp_w_open(o, rest)) == Wr.Got{o, rest} : Wr.Dec<FTr.Open>}:
  match o:
    case FTr.ONeed{+m}:
      %tre.str(m, rest, h) : {FTr.open.need(_) == Wr.Got{FTr.ONeed{m}, rest} : Wr.Dec<FTr.Open>}
      {==}
    case FTr.OSeat{}:
      {==}

# Replies
# -------

# the entry's encoder is the spec's spelling
def tre.put_do(d: Tn.Do) -> {FTr.put_do(d) == TinyRun.sp_w_do(d) : String}:
  match d:
    case Tn.DoPing{}:
      {==}
    case Tn.DoShutdown{}:
      {==}
    case Tn.DoLaunch{}:
      {==}
    case Tn.DoUse{g}:
      match g:
        case Tn.Started{}:
          {==}
        case Tn.Joined{}:
          {==}
        case Tn.Replaced{}:
          {==}
    case Tn.DoFail{w}:
      match w:
        case Tn.WhyIo{}:
          {==}
        case Tn.WhyProtocol{}:
          {==}
        case Tn.WhyMistagged{}:
          {==}
        case Tn.WhyVacant{}:
          {==}
        case Tn.WhySpawn{}:
          {==}
    case Tn.DoLock{}:
      {==}
    case Tn.DoAdopt{}:
      {==}
    case Tn.DoTake{}:
      {==}
    case Tn.DoFault{}:
      {==}
    case Tn.DoNothing{}:
      {==}

def tre.reply(r: Tn.Run & Tn.Do) -> {FTr.reply(r) == TinyRun.sp_reply(r) : FTr.St & String}:
  (x, +d) = r
  %tre.put_do(d) : {(FTr.Live{x}, FTr.put_do(d)) == (FTr.Live{x}, _) : FTr.St & String}
  {==}

# no reply opens with the error form
def tre.do_ok(d: Tn.Do) -> {LawsBase.wire_opens_err(FTr.put_do(d)) == False{} : Bool}:
  match d:
    case Tn.DoPing{}:
      Wire.wire_nat_not_err(0n, "")
    case Tn.DoShutdown{}:
      Wire.wire_nat_not_err(1n, "")
    case Tn.DoLaunch{}:
      Wire.wire_nat_not_err(2n, "")
    case Tn.DoUse{g}:
      Wire.wire_nat_not_err(3n, Wr.put_nat(FTr.got.tag(g), ""))
    case Tn.DoFail{w}:
      Wire.wire_nat_not_err(4n, Wr.put_nat(FTr.why.tag(w), ""))
    case Tn.DoLock{}:
      Wire.wire_nat_not_err(5n, "")
    case Tn.DoAdopt{}:
      Wire.wire_nat_not_err(6n, "")
    case Tn.DoTake{}:
      Wire.wire_nat_not_err(7n, "")
    case Tn.DoFault{}:
      Wire.wire_nat_not_err(8n, "")
    case Tn.DoNothing{}:
      Wire.wire_nat_not_err(9n, "")

def tre.reply_ok(r: Tn.Run & Tn.Do) -> {LawsBase.wire_opens_err(TinyRun.tr_snd(FTr.reply(r))) == False{} : Bool}:
  (x, d) = r
  tre.do_ok(d)
