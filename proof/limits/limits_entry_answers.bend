# eukhe: the proof of LAW limits_entry_answers
#
# PROOF: a spelled request that fits reads back whole with the rest
# untouched (lpe.req: each decoder stage reads its field by the round trip
# laws of the wire, a list by wire_list_spells_items and
# wire_list_reads_items, the budget's amounts, asks and accounts by
# budget's lemmas); with nothing left the entry answers the model's answer
# by its encoders, which are the spec's spellings (lpe.reply).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../bend/ffi_limits.bend as FL
import ../../bend/ffi_budget.bend as FB
import ../../bend/wire.bend as Wr
import ../../laws/limits.bend as Limits
import ../../laws/budget.bend as Budget
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/base/dec.bend as LAWireDec
import ../budget/base/entry.bend as BE

# Round trip: the fields
# ----------------------

def lpe.and2(+a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def lpe.toggle(t: L.Toggle, rest: String) -> {Wr.Got{t, rest} == FL.get_toggle(Wr.put_bool(Limits.sp_on(t), rest)) : Wr.Dec<L.Toggle>}:
  match t:
    case L.Off{}:
      {==}
    case L.On{}:
      {==}

def lpe.kind(k: L.Run, rest: String) -> {Wr.Got{k, rest} == FL.get_kind(Wr.put_nat(Limits.sp_kind_tag(k), rest)) : Wr.Dec<L.Run>}:
  match k:
    case L.Interactive{}:
      {==}
    case L.Headless{}:
      {==}
    case L.Sdk{}:
      {==}
    case L.Scheduled{}:
      {==}
    case L.Loop{}:
      {==}
    case L.Autoresearch{}:
      {==}

def lpe.auth(a: L.Auth, rest: String) -> {Wr.Got{a, rest} == FL.get_auth(Wr.put_nat(Limits.sp_auth_tag(a), rest)) : Wr.Dec<L.Auth>}:
  match a:
    case L.Plan{}:
      {==}
    case L.ApiKey{}:
      {==}
    case L.Local{}:
      {==}

def lpe.scale(s: L.Scale, rest: String) -> {Wr.Got{s, rest} == FL.get_scale(Wr.put_nat(Limits.sp_scale_tag(s), rest)) : Wr.Dec<L.Scale>}:
  match s:
    case L.Quick{}:
      {==}
    case L.Deep{}:
      {==}

def lpe.val(v: L.Val, +rest: String, h: {Limits.sp_fit_val(v) == True{} : Bool}) -> {Wr.Got{v, rest} == FL.get_val(Limits.sp_w_val(v, rest)) : Wr.Dec<L.Val>}:
  match v:
    case L.Unset{}:
      {==}
    case L.At{+n}:
      %BE.be.nat(n, rest, h) : {Wr.Got{L.At{n}, rest} == FL.get_val.at(_) : Wr.Dec<L.Val>}
      {==}
    case L.Unlimited{}:
      {==}

def lpe.lims(l: L.Lims, +rest: String, h: {Limits.sp_fit_lims(l) == True{} : Bool}) -> {Wr.Got{l, rest} == FL.get_lims(Limits.sp_w_lims(l, rest)) : Wr.Dec<L.Lims>}:
  match l:
    case L.Lims{+c, +k, +m, +n, +r}:
      +h0 = h
      +b4 = Bool.and(Limits.sp_fit_val(n), Limits.sp_fit_val(r))
      +b3 = Bool.and(Limits.sp_fit_val(m), b4)
      +b2 = Bool.and(Limits.sp_fit_val(k), b3)
      +fc = BE.be.and_l(Limits.sp_fit_val(c), b2, h0)
      +h1 = BE.be.and_r(Limits.sp_fit_val(c), b2, h0)
      +fk = BE.be.and_l(Limits.sp_fit_val(k), b3, h1)
      +h2 = BE.be.and_r(Limits.sp_fit_val(k), b3, h1)
      +fm = BE.be.and_l(Limits.sp_fit_val(m), b4, h2)
      +h3 = BE.be.and_r(Limits.sp_fit_val(m), b4, h2)
      +fn = BE.be.and_l(Limits.sp_fit_val(n), Limits.sp_fit_val(r), h3)
      +fr = BE.be.and_r(Limits.sp_fit_val(n), Limits.sp_fit_val(r), h3)
      +s4 = Limits.sp_w_val(r, rest)
      +s3 = Limits.sp_w_val(n, s4)
      +s2 = Limits.sp_w_val(m, s3)
      +s1 = Limits.sp_w_val(k, s2)
      +v = {Wr.Got{L.Lims{c, k, m, n, r}, rest} : Wr.Dec<L.Lims>}
      %lpe.val(c, s1, fc) : {v == FL.get_lims.c(_) : Wr.Dec<L.Lims>}
      %lpe.val(k, s2, fk) : {v == FL.get_lims.k(c, _) : Wr.Dec<L.Lims>}
      %lpe.val(m, s3, fm) : {v == FL.get_lims.m(c, k, _) : Wr.Dec<L.Lims>}
      %lpe.val(n, s4, fn) : {v == FL.get_lims.n(c, k, m, _) : Wr.Dec<L.Lims>}
      %lpe.val(r, rest, fr) : {v == FL.get_lims.r(c, k, m, n, _) : Wr.Dec<L.Lims>}
      {==}

def lpe.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def lpe.win(+l: String, +u: Nat, +rest: String, fl: {LawsBase.wire_fits(String.length(l)) == True{} : Bool}, fu: {LawsBase.wire_fits(u) == True{} : Bool}) -> {Wr.Got{L.Win{l, u}, rest} == FL.get_win(Limits.sp_w_win(L.Win{l, u}, rest)) : Wr.Dec<L.Win>}:
  %lpe.str(l, Wr.put_nat(u, rest), fl) : {Wr.Got{L.Win{l, u}, rest} == FL.get_win.l(_) : Wr.Dec<L.Win>}
  %BE.be.nat(u, rest, fu) : {Wr.Got{L.Win{l, u}, rest} == FL.get_win.u(l, _) : Wr.Dec<L.Win>}
  {==}

# Round trip: the lists
# ---------------------

def lpe.nats(+xs: List<&2, Nat>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)) : Wr.Dec<List<&2, Nat>>}:
  Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)), Wr.Got{xs, rest}, Wire.wire_list_round_trip(xs, rest, h))

def lpe.strs(+xs: List<&2, String>, +rest: String, h: {LawsBase.wire_strs_fit(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~String, ~Wr.get_str, Wr.put_list(~String, ~Wr.put_str, xs, rest)) : Wr.Dec<List<&2, String>>}:
  %Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, xs, rest), LawsBase.wire_spell_strs(xs, rest), Wire.wire_strs_spells(xs, rest)) : {Wr.Got{xs, rest} == Wr.get_list(~String, ~Wr.get_str, _) : Wr.Dec<List<&2, String>>}
  Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, LawsBase.wire_spell_strs(xs, rest)), Wr.Got{xs, rest}, Wire.wire_strs_round_trip(xs, rest, h))

# the item loop reads the spelled limits back
def lpe.lims_items(xs: List<&2, L.Lims>, +rest: String, h: {Limits.sp_fit_limss(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == LawsBase.wire_items(~L.Lims, ~FL.get_lims, List.length(&2, L.Lims, xs), LawsBase.wire_put_items(~L.Lims, ~Limits.sp_w_lims, xs, rest)) : Wr.Dec<List<&2, L.Lims>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = h
      +fx = BE.be.and_l(Limits.sp_fit_lims(x), Limits.sp_fit_limss(t), h0)
      +ft = BE.be.and_r(Limits.sp_fit_lims(x), Limits.sp_fit_limss(t), h0)
      +m = List.length(&2, L.Lims, t)
      +s1 = LawsBase.wire_put_items(~L.Lims, ~Limits.sp_w_lims, t, rest)
      %lpe.lims(x, s1, fx) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.then(L.Lims, _, r => LawsBase.wire_items(~L.Lims, ~FL.get_lims, m, r)) : Wr.Dec<List<&2, L.Lims>>}
      %lpe.lims_items(t, rest, ft) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.cons(L.Lims, x, _) : Wr.Dec<List<&2, L.Lims>>}
      {==}

# a spelled list of limits that fits reads back
def lpe.limss(+xs: List<&2, L.Lims>, +rest: String, fc: {LawsBase.wire_fits(List.length(&2, L.Lims, xs)) == True{} : Bool}, fx: {Limits.sp_fit_limss(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~L.Lims, ~FL.get_lims, Wr.put_list(~L.Lims, ~Limits.sp_w_lims, xs, rest)) : Wr.Dec<List<&2, L.Lims>>}:
  +n = List.length(&2, L.Lims, xs)
  +s1 = LawsBase.wire_put_items(~L.Lims, ~Limits.sp_w_lims, xs, rest)
  %Equal.sym(String, Wr.put_list(~L.Lims, ~Limits.sp_w_lims, xs, rest), LawsBase.wire_dec(n, s1), Wire.wire_list_spells_items(~L.Lims, ~Limits.sp_w_lims, xs, rest)) : {Wr.Got{xs, rest} == Wr.get_list(~L.Lims, ~FL.get_lims, _) : Wr.Dec<List<&2, L.Lims>>}
  %LAWireDec.wdec.nat(n, s1) : {Wr.Got{xs, rest} == Wr.get_list(~L.Lims, ~FL.get_lims, _) : Wr.Dec<List<&2, L.Lims>>}
  %Equal.sym(Wr.Dec<List<&2, L.Lims>>, Wr.get_list(~L.Lims, ~FL.get_lims, Wr.put_nat(n, s1)), LawsBase.wire_read_list(~L.Lims, ~FL.get_lims, Wr.put_nat(n, s1)), Wire.wire_list_reads_items(~L.Lims, ~FL.get_lims, Wr.put_nat(n, s1))) : {Wr.Got{xs, rest} == _ : Wr.Dec<List<&2, L.Lims>>}
  %BE.be.nat(n, s1, fc) : {Wr.Got{xs, rest} == LawsBase.wire_read_list.count(~L.Lims, ~FL.get_lims, _) : Wr.Dec<List<&2, L.Lims>>}
  lpe.lims_items(xs, rest, fx)

# the item loop reads the spelled windows back
def lpe.win_items(ws: List<&2, L.Win>, +rest: String, h: {Limits.sp_fit_wins(ws) == True{} : Bool}) -> {Wr.Got{ws, rest} == LawsBase.wire_items(~L.Win, ~FL.get_win, List.length(&2, L.Win, ws), LawsBase.wire_put_items(~L.Win, ~Limits.sp_w_win, ws, rest)) : Wr.Dec<List<&2, L.Win>>}:
  match ws:
    case Nil{}:
      {==}
    case Con{hd, +t}:
      match hd:
        case L.Win{+l, +u}:
          +h0 = h
          +b1 = Bool.and(LawsBase.wire_fits(u), Limits.sp_fit_wins(t))
          +fl = BE.be.and_l(LawsBase.wire_fits(String.length(l)), b1, h0)
          +h1 = BE.be.and_r(LawsBase.wire_fits(String.length(l)), b1, h0)
          +fu = BE.be.and_l(LawsBase.wire_fits(u), Limits.sp_fit_wins(t), h1)
          +ft = BE.be.and_r(LawsBase.wire_fits(u), Limits.sp_fit_wins(t), h1)
          +m = List.length(&2, L.Win, t)
          +s1 = LawsBase.wire_put_items(~L.Win, ~Limits.sp_w_win, t, rest)
          %lpe.win(l, u, s1, fl, fu) : {Wr.Got{L.Win{l, u} <> t, rest} == LawsBase.wire_items.then(L.Win, _, r => LawsBase.wire_items(~L.Win, ~FL.get_win, m, r)) : Wr.Dec<List<&2, L.Win>>}
          %lpe.win_items(t, rest, ft) : {Wr.Got{L.Win{l, u} <> t, rest} == LawsBase.wire_items.cons(L.Win, L.Win{l, u}, _) : Wr.Dec<List<&2, L.Win>>}
          {==}

# a spelled list of windows that fits reads back
def lpe.wins(+ws: List<&2, L.Win>, +rest: String, fc: {LawsBase.wire_fits(List.length(&2, L.Win, ws)) == True{} : Bool}, fw: {Limits.sp_fit_wins(ws) == True{} : Bool}) -> {Wr.Got{ws, rest} == Wr.get_list(~L.Win, ~FL.get_win, Wr.put_list(~L.Win, ~Limits.sp_w_win, ws, rest)) : Wr.Dec<List<&2, L.Win>>}:
  +n = List.length(&2, L.Win, ws)
  +s1 = LawsBase.wire_put_items(~L.Win, ~Limits.sp_w_win, ws, rest)
  %Equal.sym(String, Wr.put_list(~L.Win, ~Limits.sp_w_win, ws, rest), LawsBase.wire_dec(n, s1), Wire.wire_list_spells_items(~L.Win, ~Limits.sp_w_win, ws, rest)) : {Wr.Got{ws, rest} == Wr.get_list(~L.Win, ~FL.get_win, _) : Wr.Dec<List<&2, L.Win>>}
  %LAWireDec.wdec.nat(n, s1) : {Wr.Got{ws, rest} == Wr.get_list(~L.Win, ~FL.get_win, _) : Wr.Dec<List<&2, L.Win>>}
  %Equal.sym(Wr.Dec<List<&2, L.Win>>, Wr.get_list(~L.Win, ~FL.get_win, Wr.put_nat(n, s1)), LawsBase.wire_read_list(~L.Win, ~FL.get_win, Wr.put_nat(n, s1)), Wire.wire_list_reads_items(~L.Win, ~FL.get_win, Wr.put_nat(n, s1))) : {Wr.Got{ws, rest} == _ : Wr.Dec<List<&2, L.Win>>}
  %BE.be.nat(n, s1, fc) : {Wr.Got{ws, rest} == LawsBase.wire_read_list.count(~L.Win, ~FL.get_win, _) : Wr.Dec<List<&2, L.Win>>}
  lpe.win_items(ws, rest, fw)

# Round trip: the request
# -----------------------

# a spelled request that fits reads back, the rest untouched
def lpe.req(q: FL.Req, +rest: String, h: {Limits.sp_fit_req(q) == True{} : Bool}) -> {FL.get_req(Limits.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FL.Req>}:
  match q:
    case FL.QFill{+t, +k, +a, +set, +ps, +own}:
      +h0 = h
      +b3 = Bool.and(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own))
      +b2 = Bool.and(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), b3)
      +fs = BE.be.and_l(Limits.sp_fit_lims(set), b2, h0)
      +h1 = BE.be.and_r(Limits.sp_fit_lims(set), b2, h0)
      +fc = BE.be.and_l(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), b3, h1)
      +h2 = BE.be.and_r(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), b3, h1)
      +fp = BE.be.and_l(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own), h2)
      +fo = BE.be.and_r(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own), h2)
      +s6 = Limits.sp_w_lims(own, rest)
      +s5 = Wr.put_list(~L.Lims, ~Limits.sp_w_lims, ps, s6)
      +s4 = Limits.sp_w_lims(set, s5)
      +s3 = Wr.put_nat(Limits.sp_auth_tag(a), s4)
      +s2 = Wr.put_nat(Limits.sp_kind_tag(k), s3)
      +v = {Wr.Got{FL.QFill{t, k, a, set, ps, own}, rest} : Wr.Dec<FL.Req>}
      %lpe.toggle(t, s2) : {FL.get_fill.t(_) == v : Wr.Dec<FL.Req>}
      %lpe.kind(k, s3) : {FL.get_fill.k(t, _) == v : Wr.Dec<FL.Req>}
      %lpe.auth(a, s4) : {FL.get_fill.a(t, k, _) == v : Wr.Dec<FL.Req>}
      %lpe.lims(set, s5, fs) : {FL.get_fill.set(t, k, a, _) == v : Wr.Dec<FL.Req>}
      %lpe.limss(ps, s6, fc, fp) : {FL.get_fill.ps(t, k, a, set, _) == v : Wr.Dec<FL.Req>}
      %lpe.lims(own, rest, fo) : {FL.get_fill.own(t, k, a, set, ps, _) == v : Wr.Dec<FL.Req>}
      {==}
    case FL.QProfile{+k, +a}:
      +v = {Wr.Got{FL.QProfile{k, a}, rest} : Wr.Dec<FL.Req>}
      %lpe.kind(k, Wr.put_nat(Limits.sp_auth_tag(a), rest)) : {FL.get_profile.k(_) == v : Wr.Dec<FL.Req>}
      %lpe.auth(a, rest) : {FL.get_profile.a(k, _) == v : Wr.Dec<FL.Req>}
      {==}
    case FL.QPreset{+s, +k, +a}:
      +v = {Wr.Got{FL.QPreset{s, k, a}, rest} : Wr.Dec<FL.Req>}
      %lpe.scale(s, Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(Limits.sp_auth_tag(a), rest))) : {FL.get_preset.c(_) == v : Wr.Dec<FL.Req>}
      %lpe.kind(k, Wr.put_nat(Limits.sp_auth_tag(a), rest)) : {FL.get_preset.k(s, _) == v : Wr.Dec<FL.Req>}
      %lpe.auth(a, rest) : {FL.get_preset.a(s, k, _) == v : Wr.Dec<FL.Req>}
      {==}
    case FL.QWraps{+us, +r}:
      +h0 = h
      +b1 = Bool.and(LawsBase.wire_nats_fit(us), LawsBase.wire_fits(r))
      +fl = BE.be.and_l(LawsBase.wire_fits(List.length(&2, Nat, us)), b1, h0)
      +h1 = BE.be.and_r(LawsBase.wire_fits(List.length(&2, Nat, us)), b1, h0)
      +fn = BE.be.and_l(LawsBase.wire_nats_fit(us), LawsBase.wire_fits(r), h1)
      +fr = BE.be.and_r(LawsBase.wire_nats_fit(us), LawsBase.wire_fits(r), h1)
      +v = {Wr.Got{FL.QWraps{us, r}, rest} : Wr.Dec<FL.Req>}
      %lpe.nats(us, Wr.put_nat(r, rest), lpe.and2(LawsBase.wire_fits(List.length(&2, Nat, us)), LawsBase.wire_nats_fit(us), fl, fn)) : {FL.get_wraps.us(_) == v : Wr.Dec<FL.Req>}
      %BE.be.nat(r, rest, fr) : {FL.get_wraps.r(us, _) == v : Wr.Dec<FL.Req>}
      {==}
    case FL.QNotice{+ws, +r, +told}:
      +h0 = h
      +b2 = Bool.and(LawsBase.wire_fits(r), LawsBase.wire_strs_fit(told))
      +b1 = Bool.and(Limits.sp_fit_wins(ws), b2)
      +fc = BE.be.and_l(LawsBase.wire_fits(List.length(&2, L.Win, ws)), b1, h0)
      +h1 = BE.be.and_r(LawsBase.wire_fits(List.length(&2, L.Win, ws)), b1, h0)
      +fw = BE.be.and_l(Limits.sp_fit_wins(ws), b2, h1)
      +h2 = BE.be.and_r(Limits.sp_fit_wins(ws), b2, h1)
      +fr = BE.be.and_l(LawsBase.wire_fits(r), LawsBase.wire_strs_fit(told), h2)
      +ft = BE.be.and_r(LawsBase.wire_fits(r), LawsBase.wire_strs_fit(told), h2)
      +s3 = Wr.put_list(~String, ~Wr.put_str, told, rest)
      +s2 = Wr.put_nat(r, s3)
      +v = {Wr.Got{FL.QNotice{ws, r, told}, rest} : Wr.Dec<FL.Req>}
      %lpe.wins(ws, s2, fc, fw) : {FL.get_notice.ws(_) == v : Wr.Dec<FL.Req>}
      %BE.be.nat(r, s3, fr) : {FL.get_notice.r(ws, _) == v : Wr.Dec<FL.Req>}
      %lpe.strs(told, rest, ft) : {FL.get_notice.told(ws, r, _) == v : Wr.Dec<FL.Req>}
      {==}
    case FL.QFloor{+l, +c, +keep}:
      +h0 = h
      +b1 = Bool.and(Budget.sp_fit_ask(c), Budget.sp_fit_ask(keep))
      +fl = BE.be.and_l(Limits.sp_fit_lims(l), b1, h0)
      +h1 = BE.be.and_r(Limits.sp_fit_lims(l), b1, h0)
      +fc = BE.be.and_l(Budget.sp_fit_ask(c), Budget.sp_fit_ask(keep), h1)
      +fk = BE.be.and_r(Budget.sp_fit_ask(c), Budget.sp_fit_ask(keep), h1)
      +s2 = Budget.sp_w_ask(keep, rest)
      +s1 = Budget.sp_w_ask(c, s2)
      +v = {Wr.Got{FL.QFloor{l, c, keep}, rest} : Wr.Dec<FL.Req>}
      %lpe.lims(l, s1, fl) : {FL.get_floor.l(_) == v : Wr.Dec<FL.Req>}
      %BE.be.ask(c, s2, fc) : {FL.get_floor.c(l, _) == v : Wr.Dec<FL.Req>}
      %BE.be.ask(keep, rest, fk) : {FL.get_floor.keep(l, c, _) == v : Wr.Dec<FL.Req>}
      {==}
    case FL.QRenew{+l, +mark, +now, +a}:
      +h0 = h
      +b2 = Bool.and(LawsBase.wire_fits(now), Budget.sp_fit_acct(a))
      +b1 = Bool.and(Budget.sp_fit_amt(mark), b2)
      +fl = BE.be.and_l(Limits.sp_fit_lims(l), b1, h0)
      +h1 = BE.be.and_r(Limits.sp_fit_lims(l), b1, h0)
      +fm = BE.be.and_l(Budget.sp_fit_amt(mark), b2, h1)
      +h2 = BE.be.and_r(Budget.sp_fit_amt(mark), b2, h1)
      +fn = BE.be.and_l(LawsBase.wire_fits(now), Budget.sp_fit_acct(a), h2)
      +fa = BE.be.and_r(LawsBase.wire_fits(now), Budget.sp_fit_acct(a), h2)
      +s3 = Budget.sp_w_acct(a, rest)
      +s2 = Wr.put_nat(now, s3)
      +s1 = Budget.sp_w_amt(mark, s2)
      +v = {Wr.Got{FL.QRenew{l, mark, now, a}, rest} : Wr.Dec<FL.Req>}
      %lpe.lims(l, s1, fl) : {FL.get_renew.l(_) == v : Wr.Dec<FL.Req>}
      %BE.be.amt(mark, s2, fm) : {FL.get_renew.mark(l, _) == v : Wr.Dec<FL.Req>}
      %BE.be.nat(now, s3, fn) : {FL.get_renew.now(l, mark, _) == v : Wr.Dec<FL.Req>}
      %BE.be.acct(a, rest, fa) : {FL.get_renew.a(l, mark, now, _) == v : Wr.Dec<FL.Req>}
      {==}
    case FL.QPrefix{+text, +ns}:
      +h0 = h
      +ft = BE.be.and_l(LawsBase.wire_fits(String.length(text)), LawsBase.wire_strs_fit(ns), h0)
      +fn = BE.be.and_r(LawsBase.wire_fits(String.length(text)), LawsBase.wire_strs_fit(ns), h0)
      +v = {Wr.Got{FL.QPrefix{text, ns}, rest} : Wr.Dec<FL.Req>}
      %lpe.str(text, Wr.put_list(~String, ~Wr.put_str, ns, rest), ft) : {FL.get_prefix.text(_) == v : Wr.Dec<FL.Req>}
      %lpe.strs(ns, rest, fn) : {FL.get_prefix.ns(text, _) == v : Wr.Dec<FL.Req>}
      {==}

# Replies: the encoders are the spec's spellings
# ----------------------------------------------

def lpe.w_val(v: L.Val, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {FL.put_val(v, r1) == Limits.sp_w_val(v, r2) : String}:
  match v:
    case L.Unset{}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), r1, r2, e)
    case L.At{n}:
      Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(n, z)), r1, r2, e)
    case L.Unlimited{}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), r1, r2, e)

def lpe.w_lims(l: L.Lims, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {FL.put_lims(l, r1) == Limits.sp_w_lims(l, r2) : String}:
  match l:
    case L.Lims{c, +k, +m, +n, +x}:
      -a4 = FL.put_val(x, r1)
      -b4 = Limits.sp_w_val(x, r2)
      -a3 = FL.put_val(n, a4)
      -b3 = Limits.sp_w_val(n, b4)
      -a2 = FL.put_val(m, a3)
      -b2 = Limits.sp_w_val(m, b3)
      -a1 = FL.put_val(k, a2)
      -b1 = Limits.sp_w_val(k, b2)
      lpe.w_val(c, a1, b1, lpe.w_val(k, a2, b2, lpe.w_val(m, a3, b3, lpe.w_val(n, a4, b4, lpe.w_val(x, r1, r2, e)))))

def lpe.w_src(x: L.Src, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {FL.put_src(x, r1) == Limits.sp_w_src(x, r2) : String}:
  match x:
    case L.UntilFinished{}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), r1, r2, e)
    case L.Set{}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), r1, r2, e)
    case L.LimitsProfile{}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), r1, r2, e)
    case L.Profile{}:
      Equal.cong(String, String, z => Wr.put_nat(3n, z), r1, r2, e)
    case L.Preset{i}:
      Equal.cong(String, String, z => Wr.put_nat(4n, Wr.put_nat(i, z)), r1, r2, e)

def lpe.w_filled(f: L.Filled) -> {FL.put_filled(f) == Limits.sp_w_filled(f) : String}:
  match f:
    case L.Filled{l, xs}:
      match xs:
        case L.Srcs{+c, +k, +m, +n, +r}:
          -a4 = FL.put_src(r, "")
          -b4 = Limits.sp_w_src(r, "")
          -a3 = FL.put_src(n, a4)
          -b3 = Limits.sp_w_src(n, b4)
          -a2 = FL.put_src(m, a3)
          -b2 = Limits.sp_w_src(m, b3)
          -a1 = FL.put_src(k, a2)
          -b1 = Limits.sp_w_src(k, b2)
          -a0 = FL.put_src(c, a1)
          -b0 = Limits.sp_w_src(c, b1)
          lpe.w_lims(l, a0, b0, lpe.w_src(c, a1, b1, lpe.w_src(k, a2, b2, lpe.w_src(m, a3, b3, lpe.w_src(n, a4, b4, lpe.w_src(r, "", "", {==}))))))

def lpe.w_mnat(m: Maybe<&2, Nat>) -> {FL.put_mnat(m) == Limits.sp_w_mnat(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{i}:
      {==}

def lpe.w_told(t: L.Told) -> {FL.put_told(t) == Limits.sp_w_told(t) : String}:
  match t:
    case L.Told{now, told}:
      {==}

def lpe.w_mdim(m: Maybe<&2, B.Dim>) -> {FL.put_mdim(m) == Limits.sp_w_mdim(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FB.put_dim(d, ""), Wr.put_nat(Budget.sp_dim_tag(d), ""), BE.be.w_dim(d, "", "", {==}))

def lpe.w_pair(p: L.KV, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {FL.put_pair(p, r1) == Limits.sp_w_kv(p, r2) : String}:
  match p:
    case L.KV{k, v}:
      match k:
        case L.KCost{}:
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_str(v, z)), r1, r2, e)
        case L.KTok{}:
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_str(v, z)), r1, r2, e)
        case L.KTime{}:
          Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(v, z)), r1, r2, e)
        case L.KCalls{}:
          Equal.cong(String, String, z => Wr.put_nat(3n, Wr.put_str(v, z)), r1, r2, e)
        case L.KReqs{}:
          Equal.cong(String, String, z => Wr.put_nat(4n, Wr.put_str(v, z)), r1, r2, e)

# the items of a list of pairs, by either writer
def lpe.w_pair_items(ps: List<&2, L.KV>, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {LawsBase.wire_put_items(~L.KV, ~FL.put_pair, ps, r1) == LawsBase.wire_put_items(~L.KV, ~Limits.sp_w_kv, ps, r2) : String}:
  match ps:
    case Nil{}:
      e
    case Con{p, t}:
      lpe.w_pair(p, LawsBase.wire_put_items(~L.KV, ~FL.put_pair, t, r1), LawsBase.wire_put_items(~L.KV, ~Limits.sp_w_kv, t, r2), lpe.w_pair_items(t, r1, r2, e))

# a list of pairs, by either writer: the count, then the items
def lpe.w_pairs(+ps: List<&2, L.KV>, +r1: String, +r2: String, e: {r1 == r2 : String}) -> {Wr.put_list(~L.KV, ~FL.put_pair, ps, r1) == Wr.put_list(~L.KV, ~Limits.sp_w_kv, ps, r2) : String}:
  -n = List.length(&2, L.KV, ps)
  -i1 = LawsBase.wire_put_items(~L.KV, ~FL.put_pair, ps, r1)
  -i2 = LawsBase.wire_put_items(~L.KV, ~Limits.sp_w_kv, ps, r2)
  Equal.trans(String, Wr.put_list(~L.KV, ~FL.put_pair, ps, r1), LawsBase.wire_dec(n, i1), Wr.put_list(~L.KV, ~Limits.sp_w_kv, ps, r2),
    Wire.wire_list_spells_items(~L.KV, ~FL.put_pair, ps, r1),
    Equal.trans(String, LawsBase.wire_dec(n, i1), LawsBase.wire_dec(n, i2), Wr.put_list(~L.KV, ~Limits.sp_w_kv, ps, r2),
      Equal.cong(String, String, z => LawsBase.wire_dec(n, z), i1, i2, lpe.w_pair_items(ps, r1, r2, e)),
      Equal.sym(String, Wr.put_list(~L.KV, ~Limits.sp_w_kv, ps, r2), LawsBase.wire_dec(n, i2), Wire.wire_list_spells_items(~L.KV, ~Limits.sp_w_kv, ps, r2))))

def lpe.w_prefix(p: L.Prefix) -> {FL.put_prefix(p) == Limits.sp_w_prefix(p) : String}:
  match p:
    case L.Read{+ks, +ps, +r}:
      Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_list(~Nat, ~Wr.put_nat, ks, z)), Wr.put_list(~L.KV, ~FL.put_pair, ps, Wr.put_str(r, "")), Wr.put_list(~L.KV, ~Limits.sp_w_kv, ps, Wr.put_str(r, "")), lpe.w_pairs(ps, Wr.put_str(r, ""), Wr.put_str(r, ""), {==}))
    case L.Refused{w}:
      {==}

# the entry's answer is the model's answer, spelled
def lpe.reply(q: FL.Req) -> {FL.answer(q) == Limits.sp_w_reply(q) : String}:
  match q:
    case FL.QFill{t, k, a, set, ps, own}:
      lpe.w_filled(L.fill(t, k, a, set, ps, own))
    case FL.QProfile{+k, +a}:
      lpe.w_lims(L.profile(k, a), "", "", {==})
    case FL.QPreset{+s, +k, +a}:
      lpe.w_lims(L.preset(s, k, a), "", "", {==})
    case FL.QWraps{us, r}:
      lpe.w_mnat(L.plan_wraps(us, r))
    case FL.QNotice{ws, r, told}:
      lpe.w_told(L.plan_notice(ws, r, told))
    case FL.QFloor{l, c, keep}:
      lpe.w_mdim(L.floor(l, c, keep))
    case FL.QRenew{+l, +mark, +now, +a}:
      BE.be.w_acct(L.renew(l, mark, now, a), "", "", {==})
    case FL.QPrefix{+text, +ns}:
      lpe.w_prefix(L.prefix(text, ns))

def Limits.limits_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FL.Req>, FL.get_req(Limits.sp_w_req(q, "")), Wr.Got{q, ""}, lpe.req(q, "", fit)) : {FL.ffi.got(_) == Limits.sp_w_reply(q) : String}
  lpe.reply(q)
