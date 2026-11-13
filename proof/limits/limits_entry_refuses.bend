# eukhe: the proof of LAW limits_entry_refuses
#
# PROOF: the entry answers either a reply, which opens with a Nat (never 'E'), or the one error form; so an answer that opens with 'E' is that error form.

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB
import ../../bend/ffi_limits.bend as FL
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/base/dec.bend as LAWireDec
import ../wire/wire_list_spells_items.bend as PWireListSpellsItems
import ../budget/base/entry.bend as BE
import ../../bend/ffi_budget.bend as FB

def ler.val(v: L.Val, rest: String) -> {LawsBase.wire_opens_err(FL.put_val(v, rest)) == False{} : Bool}:
  match v:
    case L.Unset{}:
      Wire.wire_nat_not_err(0n, rest)
    case L.At{n}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(n, rest))
    case L.Unlimited{}:
      Wire.wire_nat_not_err(2n, rest)

def ler.lims(l: L.Lims, rest: String) -> {LawsBase.wire_opens_err(FL.put_lims(l, rest)) == False{} : Bool}:
  match l:
    case L.Lims{c, k, m, n, r}:
      ler.val(c, FL.put_val(k, FL.put_val(m, FL.put_val(n, FL.put_val(r, rest)))))

def ler.filled(f: L.Filled) -> {LawsBase.wire_opens_err(FL.put_filled(f)) == False{} : Bool}:
  match f:
    case L.Filled{l, L.Srcs{c, k, m, n, r}}:
      ler.lims(l, FL.put_src(c, FL.put_src(k, FL.put_src(m, FL.put_src(n, FL.put_src(r, ""))))))

def ler.mnat(m: Maybe<&2, Nat>) -> {LawsBase.wire_opens_err(FL.put_mnat(m)) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{i}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(i, ""))

def ler.mdim(m: Maybe<&2, B.Dim>) -> {LawsBase.wire_opens_err(FL.put_mdim(m)) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{d}:
      Wire.wire_nat_not_err(1n, FB.put_dim(d, ""))

# a list of Nats opens with its count
def ler.nats(+xs: List<&2, Nat>, +rest: String) -> {LawsBase.wire_opens_err(Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)) == False{} : Bool}:
  %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest), LawsBase.wire_dec(List.length(&2, Nat, xs), LawsBase.wire_put_items(~Nat, ~Wr.put_nat, xs, rest)), Wire.wire_list_spells_items(~Nat, ~Wr.put_nat, xs, rest)) : {LawsBase.wire_opens_err(_) == False{} : Bool}
  %LAWireDec.wdec.nat(List.length(&2, Nat, xs), LawsBase.wire_put_items(~Nat, ~Wr.put_nat, xs, rest)) : {LawsBase.wire_opens_err(_) == False{} : Bool}
  Wire.wire_nat_not_err(List.length(&2, Nat, xs), LawsBase.wire_put_items(~Nat, ~Wr.put_nat, xs, rest))

def ler.told(t: L.Told) -> {LawsBase.wire_opens_err(FL.put_told(t)) == False{} : Bool}:
  match t:
    case L.Told{now, told}:
      ler.nats(now, Wr.put_list(~String, ~Wr.put_str, told, ""))

def ler.prefix(p: L.Prefix) -> {LawsBase.wire_opens_err(FL.put_prefix(p)) == False{} : Bool}:
  match p:
    case L.Read{ks, ps, r}:
      Wire.wire_nat_not_err(0n, Wr.put_list(~Nat, ~Wr.put_nat, ks, Wr.put_list(~L.KV, ~FL.put_pair, ps, Wr.put_str(r, ""))))
    case L.Refused{w}:
      Wire.wire_nat_not_err(1n, Wr.put_str(w, ""))

# no answer opens with 'E'
def ler.answer(q: FL.Req) -> {LawsBase.wire_opens_err(FL.answer(q)) == False{} : Bool}:
  match q:
    case FL.QFill{t, k, a, set, ps, own}:
      ler.filled(L.fill(t, k, a, set, ps, own))
    case FL.QProfile{k, a}:
      ler.lims(L.profile(k, a), "")
    case FL.QPreset{s, k, a}:
      ler.lims(L.preset(s, k, a), "")
    case FL.QWraps{us, r}:
      ler.mnat(L.plan_wraps(us, r))
    case FL.QNotice{ws, r, told}:
      ler.told(L.plan_notice(ws, r, told))
    case FL.QFloor{l, c, keep}:
      ler.mdim(L.floor(l, c, keep))
    case FL.QRenew{l, mark, now, a}:
      BE.be.acct_ok(L.renew(l, mark, now, a), "")
    case FL.QPrefix{text, ns}:
      ler.prefix(L.prefix(text, ns))

def ler.refuse(d: Wr.Dec<FL.Req>, bad: {LawsBase.wire_opens_err(FL.ffi.got(d)) == True{} : Bool}) -> {FL.ffi.got(d) == Wr.err("limits: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LB.lmb.absurd_tf({FL.answer(q) == Wr.err("limits: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FL.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FL.answer(q)), True{}, bad), ler.answer(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Limits.limits_entry_refuses(s, bad):
  ler.refuse(FL.get_req(s), bad)
