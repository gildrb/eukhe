# eukhe: lemmas the proofs of laws/dash_conn.bend share
#
# The stepper's decoder is the laws' reader, stage by stage (dcn.read);
# its verdict encoder is the laws' speller (dcn.reply); the reader reads
# back every event Rust spells (dcn.rt: tags and Bools compute, a text
# reads back by wire_str_round_trip). A pass of the gate is Admit or
# Refuse, so what a step answers follows by cases on it (dcr.*); a closed
# socket answers only `closed` (dcr.closed_run).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

# Logic
# -----

def dcn.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def dcn.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : dcn.BD(_, A, Unit)
  Unit{}

def dcn.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : dcn.BD(_, Unit, A)
  Unit{}

# x is False and True
def dcn.contra(-A: Type, -x: Bool, a: {x == False{} : Bool}, b: {x == True{} : Bool}) -> A:
  dcn.absurdF(A, Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, a), b))

def dcn.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def dcn.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      dcn.absurdF({b == True{} : Bool}, h)

# The decoder is the reader
# -------------------------

def dcn.disk_text(r: Wr.Dec<String>) -> {FDa.get_file.text(r) == DashConn.rd_disk.text(r) : Wr.Dec<Da.Disk>}:
  match r:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dcn.disk(r: Wr.Dec<Nat>) -> {FDa.get_file(r) == DashConn.rd_disk(r) : Wr.Dec<Da.Disk>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          dcn.disk_text(Wr.get_str(s))
        case 3n:
          {==}
        case 4n+u:
          {==}
    case Wr.Bad{}:
      {==}

def dcn.said_spoken(r: Wr.Dec<String>) -> {FDa.get_said.spoken(r) == DashConn.rd_said.spoken(r) : Wr.Dec<Da.Said>}:
  match r:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dcn.said(r: Wr.Dec<Nat>) -> {FDa.get_said(r) == DashConn.rd_said(r) : Wr.Dec<Da.Said>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          dcn.said_spoken(Wr.get_str(s))
        case 1n:
          {==}
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def dcn.first_pair(r: Wr.Dec<Da.Said>) -> {FDa.get_first.pair(r) == DashConn.rd_first.pair(r) : Wr.Dec<Da.First>}:
  match r:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dcn.first(r: Wr.Dec<Nat>) -> {FDa.get_first(r) == DashConn.rd_first(r) : Wr.Dec<Da.First>}:
  match r:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          %dcn.said(Wr.get_nat(s)) : {FDa.get_first.pair(FDa.get_said(Wr.get_nat(s))) == DashConn.rd_first.pair(_) : Wr.Dec<Da.First>}
          dcn.first_pair(FDa.get_said(Wr.get_nat(s)))
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def dcn.ev_matches(x: Da.First, f: Da.Disk, r: Wr.Dec<Bool>) -> {FDa.get_ev.matches(x, f, r) == DashConn.rd_ev.matches(x, f, r) : Wr.Dec<Da.CEv>}:
  match r:
    case Wr.Got{m, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dcn.ev_first(x: Da.First, r: Wr.Dec<Da.Disk>) -> {FDa.get_ev.first(x, r) == DashConn.rd_ev.first(x, r) : Wr.Dec<Da.CEv>}:
  match r:
    case Wr.Got{f, s}:
      dcn.ev_matches(x, f, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def dcn.ev_pair(r: Wr.Dec<Da.First>) -> {FDa.get_ev.pair(r) == DashConn.rd_ev.pair(r) : Wr.Dec<Da.CEv>}:
  match r:
    case Wr.Got{+x, +s}:
      %dcn.disk(Wr.get_nat(s)) : {FDa.get_ev.first(x, FDa.get_file(Wr.get_nat(s))) == DashConn.rd_ev.first(x, _) : Wr.Dec<Da.CEv>}
      dcn.ev_first(x, FDa.get_file(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def dcn.ev_later(f: Da.Disk, r: Wr.Dec<Bool>) -> {FDa.get_ev.later(f, r) == DashConn.rd_ev.later(f, r) : Wr.Dec<Da.CEv>}:
  match r:
    case Wr.Got{m, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dcn.ev_frame(r: Wr.Dec<Da.Disk>) -> {FDa.get_ev.frame(r) == DashConn.rd_ev.frame(r) : Wr.Dec<Da.CEv>}:
  match r:
    case Wr.Got{f, s}:
      dcn.ev_later(f, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def dcn.ev_go(r: Wr.Dec<Nat>) -> {FDa.get_ev.go(r) == DashConn.rd_ev.go(r) : Wr.Dec<Da.CEv>}:
  match r:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          %dcn.first(Wr.get_nat(s)) : {FDa.get_ev.pair(FDa.get_first(Wr.get_nat(s))) == DashConn.rd_ev.pair(_) : Wr.Dec<Da.CEv>}
          dcn.ev_pair(FDa.get_first(Wr.get_nat(s)))
        case 1n:
          %dcn.disk(Wr.get_nat(s)) : {FDa.get_ev.frame(FDa.get_file(Wr.get_nat(s))) == DashConn.rd_ev.frame(_) : Wr.Dec<Da.CEv>}
          dcn.ev_frame(FDa.get_file(Wr.get_nat(s)))
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

# the stepper reads every input as the laws' reader does
def dcn.read(+s: String) -> {FDa.get_ev(s) == DashConn.read_ev(s) : Wr.Dec<Da.CEv>}:
  dcn.ev_go(Wr.get_nat(s))

# The encoder is the speller
# --------------------------

def dcn.verdict(v: Da.Verdict) -> {FDa.put_verdict(v) == DashConn.sp_w_verdict(v) : String}:
  match v:
    case Da.VPaired{}:
      {==}
    case Da.VRun{}:
      {==}
    case Da.VRefuse{t}:
      {==}
    case Da.VClosed{}:
      {==}

def dcn.reply(r: Da.Conn & Da.Verdict) -> {FDa.step.reply(r) == DashConn.cs_reply(r) : FDa.St & String}:
  (c, +v) = r
  %dcn.verdict(v) : {(FDa.Live{c}, FDa.put_verdict(v)) == (FDa.Live{c}, _) : FDa.St & String}
  {==}

# The reader reads back what Rust writes
# --------------------------------------

def dcn.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def dcn.rt_disk(f: Da.Disk, +rest: String, h: {Dash.sp_fit_disk(f) == True{} : Bool}) -> {Wr.Got{f, rest} == DashConn.rd_disk(Wr.get_nat(Dash.sp_w_disk(f, rest))) : Wr.Dec<Da.Disk>}:
  match f:
    case Da.NoFile{}:
      {==}
    case Da.Unread{}:
      {==}
    case Da.Holds{+s}:
      %dcn.str(s, rest, h) : {Wr.Got{Da.Holds{s}, rest} == DashConn.rd_disk.text(_) : Wr.Dec<Da.Disk>}
      {==}
    case Da.Huge{}:
      {==}

def dcn.rt_said(x: Da.Said, +rest: String, h: {Dash.sp_fit_said(x) == True{} : Bool}) -> {Wr.Got{x, rest} == DashConn.rd_said(Wr.get_nat(Dash.sp_w_said(x, rest))) : Wr.Dec<Da.Said>}:
  match x:
    case Da.Spoken{+t}:
      %dcn.str(t, rest, h) : {Wr.Got{Da.Spoken{t}, rest} == DashConn.rd_said.spoken(_) : Wr.Dec<Da.Said>}
      {==}
    case Da.Overlong{}:
      {==}

def dcn.rt_first(x: Da.First, +rest: String, h: {Dash.sp_fit_first(x) == True{} : Bool}) -> {Wr.Got{x, rest} == DashConn.rd_first(Wr.get_nat(Dash.sp_w_first(x, rest))) : Wr.Dec<Da.First>}:
  match x:
    case Da.NoText{}:
      {==}
    case Da.NotPairing{}:
      {==}
    case Da.Pair{+t}:
      %dcn.rt_said(t, rest, h) : {Wr.Got{Da.Pair{t}, rest} == DashConn.rd_first.pair(_) : Wr.Dec<Da.First>}
      {==}

def dcn.rt_matches(m: Bool, -x: Da.First, -f: Da.Disk, -rest: String) -> {DashConn.rd_ev.matches(x, f, Wr.get_bool(Wr.put_bool(m, rest))) == Wr.Got{Da.CFirst{x, f, m}, rest} : Wr.Dec<Da.CEv>}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def dcn.rt_later(m: Bool, -f: Da.Disk, -rest: String) -> {DashConn.rd_ev.later(f, Wr.get_bool(Wr.put_bool(m, rest))) == Wr.Got{Da.CFrame{f, m}, rest} : Wr.Dec<Da.CEv>}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# every event Rust spells reads back whole, the rest untouched
def dcn.rt(e: Da.CEv, +rest: String, h: {DashConn.sp_fit_ev(e) == True{} : Bool}) -> {DashConn.read_ev(DashConn.sp_w_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Da.CEv>}:
  match e:
    case Da.CFirst{+x, +f, +m}:
      +h2 = h
      +r2 = Wr.put_bool(m, rest)
      +r1 = Dash.sp_w_disk(f, r2)
      %dcn.rt_first(x, r1, dcn.and_l(Dash.sp_fit_first(x), Dash.sp_fit_disk(f), h2)) : {DashConn.rd_ev.pair(_) == Wr.Got{Da.CFirst{x, f, m}, rest} : Wr.Dec<Da.CEv>}
      %dcn.rt_disk(f, r2, dcn.and_r(Dash.sp_fit_first(x), Dash.sp_fit_disk(f), h2)) : {DashConn.rd_ev.first(x, _) == Wr.Got{Da.CFirst{x, f, m}, rest} : Wr.Dec<Da.CEv>}
      dcn.rt_matches(m, x, f, rest)
    case Da.CFrame{+f, +m}:
      %dcn.rt_disk(f, Wr.put_bool(m, rest), h) : {DashConn.rd_ev.frame(_) == Wr.Got{Da.CFrame{f, m}, rest} : Wr.Dec<Da.CEv>}
      dcn.rt_later(m, f, rest)

# What a step answers
# -------------------

# a first frame never runs; a later frame never pairs
def dcr.first_not_run(p: Da.Pass) -> {DashConn.cv_is_run(DashConn.cv_verdict(Da.first.pass(p))) == False{} : Bool}:
  match p:
    case Da.Admit{}:
      {==}
    case Da.Refuse{t}:
      {==}

def dcr.later_not_paired(p: Da.Pass) -> {DashConn.cv_is_paired(DashConn.cv_verdict(Da.frame.pass(p))) == False{} : Bool}:
  match p:
    case Da.Admit{}:
      {==}
    case Da.Refuse{t}:
      {==}

# a refusal closes
def dcr.first_closes(p: Da.Pass, h: {DashConn.cv_is_refuse(DashConn.cv_verdict(Da.first.pass(p))) == True{} : Bool}) -> {DashConn.cv_is_closed(DashConn.cv_conn(Da.first.pass(p))) == True{} : Bool}:
  match p:
    case Da.Admit{}:
      dcn.absurdF({False{} == True{} : Bool}, h)
    case Da.Refuse{t}:
      {==}

def dcr.later_closes(p: Da.Pass, h: {DashConn.cv_is_refuse(DashConn.cv_verdict(Da.frame.pass(p))) == True{} : Bool}) -> {DashConn.cv_is_closed(DashConn.cv_conn(Da.frame.pass(p))) == True{} : Bool}:
  match p:
    case Da.Admit{}:
      dcn.absurdF({False{} == True{} : Bool}, h)
    case Da.Refuse{t}:
      {==}

# a closed socket runs and opens nothing, whatever comes
def dcr.closed_run(es: List<&2, Da.CEv>) -> {DashConn.cv_any_live(DashConn.cv_run(es, Da.Closed{})) == False{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> t:
      dcr.closed_run(t)

def dcr.closed_quiet(c: Da.Conn, es: List<&2, Da.CEv>, h: {DashConn.cv_is_closed(c) == True{} : Bool}) -> {DashConn.cv_any_live(DashConn.cv_run(es, c)) == False{} : Bool}:
  match c:
    case Da.Waiting{}:
      dcn.absurdF({DashConn.cv_any_live(DashConn.cv_run(es, Da.Waiting{})) == False{} : Bool}, h)
    case Da.Paired{}:
      dcn.absurdF({DashConn.cv_any_live(DashConn.cv_run(es, Da.Paired{})) == False{} : Bool}, h)
    case Da.Closed{}:
      dcr.closed_run(es)
