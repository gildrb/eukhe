# eukhe: lemmas the proofs of laws/dash_conn.bend share
#
# The stepper's verdict encoder is the laws' speller (dcn.reply); its
# decoder reads back every event Rust spells (dcn.rt: tags and Bools
# compute, a text reads back by wire_str_round_trip). A pass of the gate is Admit or
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

# The decoder reads back what Rust writes
# --------------------------------------

def dcn.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def dcn.rt_disk(f: Da.Disk, +rest: String, h: {Dash.sp_fit_disk(f) == True{} : Bool}) -> {Wr.Got{f, rest} == FDa.get_file(Wr.get_nat(Dash.sp_w_disk(f, rest))) : Wr.Dec<Da.Disk>}:
  match f:
    case Da.NoFile{}:
      {==}
    case Da.Unread{}:
      {==}
    case Da.Holds{+s}:
      %dcn.str(s, rest, h) : {Wr.Got{Da.Holds{s}, rest} == FDa.get_file.text(_) : Wr.Dec<Da.Disk>}
      {==}
    case Da.Huge{}:
      {==}

def dcn.rt_said(x: Da.Said, +rest: String, h: {Dash.sp_fit_said(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FDa.get_said(Wr.get_nat(Dash.sp_w_said(x, rest))) : Wr.Dec<Da.Said>}:
  match x:
    case Da.Spoken{+t}:
      %dcn.str(t, rest, h) : {Wr.Got{Da.Spoken{t}, rest} == FDa.get_said.spoken(_) : Wr.Dec<Da.Said>}
      {==}
    case Da.Overlong{}:
      {==}

def dcn.rt_first(x: Da.First, +rest: String, h: {Dash.sp_fit_first(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FDa.get_first(Wr.get_nat(Dash.sp_w_first(x, rest))) : Wr.Dec<Da.First>}:
  match x:
    case Da.NoText{}:
      {==}
    case Da.NotPairing{}:
      {==}
    case Da.Pair{+t}:
      %dcn.rt_said(t, rest, h) : {Wr.Got{Da.Pair{t}, rest} == FDa.get_first.pair(_) : Wr.Dec<Da.First>}
      {==}

def dcn.rt_matches(m: Bool, -x: Da.First, -f: Da.Disk, -rest: String) -> {FDa.get_ev.matches(x, f, Wr.get_bool(Wr.put_bool(m, rest))) == Wr.Got{Da.CFirst{x, f, m}, rest} : Wr.Dec<Da.CEv>}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def dcn.rt_later(m: Bool, -f: Da.Disk, -rest: String) -> {FDa.get_ev.later(f, Wr.get_bool(Wr.put_bool(m, rest))) == Wr.Got{Da.CFrame{f, m}, rest} : Wr.Dec<Da.CEv>}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# every event Rust spells reads back whole, the rest untouched
def dcn.rt(e: Da.CEv, +rest: String, h: {DashConn.sp_fit_ev(e) == True{} : Bool}) -> {FDa.get_ev(DashConn.sp_w_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Da.CEv>}:
  match e:
    case Da.CFirst{+x, +f, +m}:
      +h2 = h
      +r2 = Wr.put_bool(m, rest)
      +r1 = Dash.sp_w_disk(f, r2)
      %dcn.rt_first(x, r1, dcn.and_l(Dash.sp_fit_first(x), Dash.sp_fit_disk(f), h2)) : {FDa.get_ev.pair(_) == Wr.Got{Da.CFirst{x, f, m}, rest} : Wr.Dec<Da.CEv>}
      %dcn.rt_disk(f, r2, dcn.and_r(Dash.sp_fit_first(x), Dash.sp_fit_disk(f), h2)) : {FDa.get_ev.first(x, _) == Wr.Got{Da.CFirst{x, f, m}, rest} : Wr.Dec<Da.CEv>}
      dcn.rt_matches(m, x, f, rest)
    case Da.CFrame{+f, +m}:
      %dcn.rt_disk(f, Wr.put_bool(m, rest), h) : {FDa.get_ev.frame(_) == Wr.Got{Da.CFrame{f, m}, rest} : Wr.Dec<Da.CEv>}
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

# A rotation (C5)
# ---------------

def drt.snd(-A: Type, -B: Type, p: A & B) -> B:
  (x, y) = p
  y

# a file that holds the token b holds a token
def drt.holds(+m: Maybe<&2, List<&2, Nat>>, +b: List<&2, Nat>, h: {m == Some{b} : Maybe<&2, List<&2, Nat>>}) -> {Dash.sp_has(m) == True{} : Bool}:
  %Equal.sym(Maybe<&2, List<&2, Nat>>, m, Some{b}, h) : {Dash.sp_has(_) == True{} : Bool}
  {==}

# Rust's comparison of the token a with a file that holds another token b
# fails
def drt.unmatched(+a: List<&2, Nat>, +g: Da.Disk, +b: List<&2, Nat>, rotated: {Dash.sp_stored(g) == Some{b} : Maybe<&2, List<&2, Nat>>}, other: {DashConn.cv_bytes_same(a, b) == False{} : Bool}) -> {DashConn.cv_rust_match(Some{a}, g) == False{} : Bool}:
  %Equal.sym(Maybe<&2, List<&2, Nat>>, Dash.sp_stored(g), Some{b}, rotated) : {DashConn.cv_rust_match.held(a, _) == False{} : Bool}
  other

def drt.pass_admit(p: Da.Pass) -> Bool:
  match p:
    case Da.Admit{}:
      True{}
    case Da.Refuse{x}:
      False{}

def drt.pass_text(p: Da.Pass) -> String:
  match p:
    case Da.Admit{}:
      ""
    case Da.Refuse{x}:
      x

# a first frame the gate refuses with w closes the socket and answers w
def drt.first_refuse(p: Da.Pass, +w: String, hp: {p == Da.Refuse{w} : Da.Pass}) -> {Da.first.pass(p) == (Da.Closed{}, Da.VRefuse{w}) : Da.Conn & Da.Verdict}:
  match p:
    case Da.Admit{}:
      dcn.absurdT({Da.first.pass(Da.Admit{}) == (Da.Closed{}, Da.VRefuse{w}) : Da.Conn & Da.Verdict}, Equal.cong(Da.Pass, Bool, z => drt.pass_admit(z), Da.Admit{}, Da.Refuse{w}, hp))
    case Da.Refuse{+x}:
      Equal.cong(String, Da.Conn & Da.Verdict, z => (Da.Closed{}, Da.VRefuse{z}), x, w, Equal.cong(Da.Pass, String, z => drt.pass_text(z), Da.Refuse{x}, Da.Refuse{w}, hp))

# a later frame the check refuses with w closes the socket and answers w
def drt.frame_refuse(p: Da.Pass, +w: String, hp: {p == Da.Refuse{w} : Da.Pass}) -> {Da.frame.pass(p) == (Da.Closed{}, Da.VRefuse{w}) : Da.Conn & Da.Verdict}:
  match p:
    case Da.Admit{}:
      dcn.absurdT({Da.frame.pass(Da.Admit{}) == (Da.Closed{}, Da.VRefuse{w}) : Da.Conn & Da.Verdict}, Equal.cong(Da.Pass, Bool, z => drt.pass_admit(z), Da.Admit{}, Da.Refuse{w}, hp))
    case Da.Refuse{+x}:
      Equal.cong(String, Da.Conn & Da.Verdict, z => (Da.Closed{}, Da.VRefuse{z}), x, w, Equal.cong(Da.Pass, String, z => drt.pass_text(z), Da.Refuse{x}, Da.Refuse{w}, hp))

# a step that refuses with w: the model's replies are w, then those of a
# closed socket
def drt.replies(r: Da.Conn & Da.Verdict, +w: String, +rest: List<&2, Da.CEv>, +hr: {r == (Da.Closed{}, Da.VRefuse{w}) : Da.Conn & Da.Verdict}) -> {DashConn.sp_w_verdict(DashConn.cv_verdict(r)) <> DashConn.cs_replies(rest, DashConn.cv_conn(r)) == DashConn.sp_w_verdict(Da.VRefuse{w}) <> DashConn.cs_replies(rest, Da.Closed{}) : List<&2, String>}:
  +hv = Equal.cong(Da.Conn & Da.Verdict, Da.Verdict, DashConn.cv_verdict, r, (Da.Closed{}, Da.VRefuse{w}), hr)
  +hc = Equal.cong(Da.Conn & Da.Verdict, Da.Conn, DashConn.cv_conn, r, (Da.Closed{}, Da.VRefuse{w}), hr)
  +e1 = Equal.cong(Da.Verdict, List<&2, String>, v => DashConn.sp_w_verdict(v) <> DashConn.cs_replies(rest, DashConn.cv_conn(r)), DashConn.cv_verdict(r), Da.VRefuse{w}, hv)
  +e2 = Equal.cong(Da.Conn, List<&2, String>, c => DashConn.sp_w_verdict(Da.VRefuse{w}) <> DashConn.cs_replies(rest, c), DashConn.cv_conn(r), Da.Closed{}, hc)
  Equal.trans(List<&2, String>, DashConn.sp_w_verdict(DashConn.cv_verdict(r)) <> DashConn.cs_replies(rest, DashConn.cv_conn(r)), DashConn.sp_w_verdict(Da.VRefuse{w}) <> DashConn.cs_replies(rest, DashConn.cv_conn(r)), DashConn.sp_w_verdict(Da.VRefuse{w}) <> DashConn.cs_replies(rest, Da.Closed{}), e1, e2)

# a closed socket answers `closed` to each later frame
def drt.closed(+p: Maybe<&2, List<&2, Nat>>, fs: List<&2, Da.Disk>) -> {DashConn.cs_replies(DashConn.cv_frames(p, fs), Da.Closed{}) == DashConn.cw_closed(fs) : List<&2, String>}:
  match fs:
    case Nil{}:
      {==}
    case f <> t:
      Equal.cong(List<&2, String>, List<&2, String>, z => DashConn.sp_w_verdict(Da.VClosed{}) <> z, DashConn.cs_replies(DashConn.cv_frames(p, t), Da.Closed{}), DashConn.cw_closed(t), drt.closed(p, t))

# the frames fit the wire when their files do
def drt.fit_frames(+p: Maybe<&2, List<&2, Nat>>, fs: List<&2, Da.Disk>) -> {DashConn.sp_fit_evs(DashConn.cv_frames(p, fs)) == DashConn.cv_fit_disks(fs) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case +f <> t:
      Equal.cong(Bool, Bool, z => Bool.and(Dash.sp_fit_disk(f), z), DashConn.sp_fit_evs(DashConn.cv_frames(p, t)), DashConn.cv_fit_disks(t), drt.fit_frames(p, t))

def drt.and3(x: Bool, -y: Bool, -z: Bool, hx: {x == True{} : Bool}, hyz: {Bool.and(y, z) == True{} : Bool}) -> {Bool.and(Bool.and(x, y), z) == True{} : Bool}:
  match x:
    case True{}:
      hyz
    case False{}:
      dcn.absurdF({Bool.and(Bool.and(False{}, y), z) == True{} : Bool}, hx)
