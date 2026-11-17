# eukhe: the proof of LAW irreversible_entry_exact
#
# PROOF: each decoder stage answers Got only for the spelling of what it
# read so far, every number within the wire (wire_nat_exact,
# wire_list_exact with their fits); a list that reads as a ledger is that
# ledger's spelling (LA.irb.ledger_exact); a value is answered only for a
# request read whole, nothing left (irx.top).

import Base
import ../../bend/irreversible.bend as Ir
import ../../bend/ffi_irreversible.bend as FIr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/irreversible.bend as Irreversible
import ../base/bool.bend as LBool
import ../base/staging.bend as LStg
import ../glob/base/entry.bend as LGlobEntry
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_list_exact.bend as PWireListExact
import ./base.bend as LA

# what a request decoder answers is the spelling of a request that fits,
# then its rest
def irx.Q(s: String, d: Wr.Dec<FIr.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Irreversible.sp_ir_req(q, r) : String} & {Irreversible.ir_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def irx.classes(+s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> irx.Q(s, FIr.get_classes(d)):
  match d:
    case Wr.Got{+cs, +s2}:
      +ee = ed
      +e = Wire.wire_list_exact(s1, cs, s2, ee)
      (Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Irreversible.sp_ir_ns(cs, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Irreversible.sp_ir_ns(cs, s2), e)), LGlobEntry.ge.nats_fit(s1, cs, s2, ee))
    case Wr.Bad{}:
      Unit{}

# Records (tag 1)
# ---------------

def irx.rec_k(+s: String, +es: List<&2, Ir.Entry>, +s2: String, pre: {s == Wr.put_nat(1n, Irreversible.sp_ir_ns(Irreversible.sp_ir_ledger(es), s2)) : String}, fl: {Irreversible.ir_ns_fit(Irreversible.sp_ir_ledger(es)) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> irx.Q(s, FIr.get_record.key(es, d)):
  match d:
    case Wr.Got{+k, +s3}:
      +ee = ed
      +l = Irreversible.sp_ir_ledger(es)
      +e = Wire.wire_nat_exact(s2, k, s3, ee)
      (Equal.trans(String, s, Wr.put_nat(1n, Irreversible.sp_ir_ns(l, s2)), Wr.put_nat(1n, Irreversible.sp_ir_ns(l, Wr.put_nat(k, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Irreversible.sp_ir_ns(l, z)), s2, Wr.put_nat(k, s3), e)), LBool.cb_and_intro(Irreversible.ir_ns_fit(l), LawsBase.wire_fits(k), fl, Wire.wire_nat_decoded_fits(s2, k, s3, ee)))
    case Wr.Bad{}:
      Unit{}

def irx.rec_m(+s: String, +xs: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(1n, Irreversible.sp_ir_ns(xs, s2)) : String}, fx: {Irreversible.ir_ns_fit(xs) == True{} : Bool}, m: Maybe<&2, List<&2, Ir.Entry>>, hm: LA.irb.LedgerOk(xs, m)) -> irx.Q(s, FIr.get_ledger.then(True{}, m, s2)):
  match m:
    case None{}:
      Unit{}
    case Some{+es}:
      +l = Irreversible.sp_ir_ledger(es)
      +hq = {hm : {xs == l : List<&2, Nat>}}
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, Irreversible.sp_ir_ns(xs, s2)), Wr.put_nat(1n, Irreversible.sp_ir_ns(l, s2)), pre, Equal.cong(List<&2, Nat>, String, z => Wr.put_nat(1n, Irreversible.sp_ir_ns(z, s2)), xs, l, hq))
      +f2 = Equal.trans(Bool, Irreversible.ir_ns_fit(l), Irreversible.ir_ns_fit(xs), True{}, Equal.cong(List<&2, Nat>, Bool, z => Irreversible.ir_ns_fit(z), l, xs, Equal.sym(List<&2, Nat>, xs, l, hq)), fx)
      irx.rec_k(s, es, s2, pre2, f2, Wr.get_nat(s2), {==})

def irx.rec(+s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> irx.Q(s, FIr.get_ledger(True{}, d)):
  match d:
    case Wr.Got{+xs, +s2}:
      +ee = ed
      +e = Wire.wire_list_exact(s1, xs, s2, ee)
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Irreversible.sp_ir_ns(xs, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Irreversible.sp_ir_ns(xs, s2), e))
      irx.rec_m(s, xs, s2, pre2, LGlobEntry.ge.nats_fit(s1, xs, s2, ee), FIr.entries.of(xs), LA.irb.ledger_exact(xs))
    case Wr.Bad{}:
      Unit{}

# Reports (tag 2)
# ---------------

def irx.rep_r(+s: String, +es: List<&2, Ir.Entry>, +s2: String, pre: {s == Wr.put_nat(2n, Irreversible.sp_ir_ns(Irreversible.sp_ir_ledger(es), s2)) : String}, fl: {Irreversible.ir_ns_fit(Irreversible.sp_ir_ledger(es)) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> irx.Q(s, FIr.get_report.run(es, d)):
  match d:
    case Wr.Got{+r, +s3}:
      +ee = ed
      +l = Irreversible.sp_ir_ledger(es)
      +e = Wire.wire_nat_exact(s2, r, s3, ee)
      (Equal.trans(String, s, Wr.put_nat(2n, Irreversible.sp_ir_ns(l, s2)), Wr.put_nat(2n, Irreversible.sp_ir_ns(l, Wr.put_nat(r, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Irreversible.sp_ir_ns(l, z)), s2, Wr.put_nat(r, s3), e)), LBool.cb_and_intro(Irreversible.ir_ns_fit(l), LawsBase.wire_fits(r), fl, Wire.wire_nat_decoded_fits(s2, r, s3, ee)))
    case Wr.Bad{}:
      Unit{}

def irx.rep_m(+s: String, +xs: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(2n, Irreversible.sp_ir_ns(xs, s2)) : String}, fx: {Irreversible.ir_ns_fit(xs) == True{} : Bool}, m: Maybe<&2, List<&2, Ir.Entry>>, hm: LA.irb.LedgerOk(xs, m)) -> irx.Q(s, FIr.get_ledger.then(False{}, m, s2)):
  match m:
    case None{}:
      Unit{}
    case Some{+es}:
      +l = Irreversible.sp_ir_ledger(es)
      +hq = {hm : {xs == l : List<&2, Nat>}}
      +pre2 = Equal.trans(String, s, Wr.put_nat(2n, Irreversible.sp_ir_ns(xs, s2)), Wr.put_nat(2n, Irreversible.sp_ir_ns(l, s2)), pre, Equal.cong(List<&2, Nat>, String, z => Wr.put_nat(2n, Irreversible.sp_ir_ns(z, s2)), xs, l, hq))
      +f2 = Equal.trans(Bool, Irreversible.ir_ns_fit(l), Irreversible.ir_ns_fit(xs), True{}, Equal.cong(List<&2, Nat>, Bool, z => Irreversible.ir_ns_fit(z), l, xs, Equal.sym(List<&2, Nat>, xs, l, hq)), fx)
      irx.rep_r(s, es, s2, pre2, f2, Wr.get_nat(s2), {==})

def irx.rep(+s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> irx.Q(s, FIr.get_ledger(False{}, d)):
  match d:
    case Wr.Got{+xs, +s2}:
      +ee = ed
      +e = Wire.wire_list_exact(s1, xs, s2, ee)
      +pre2 = Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Irreversible.sp_ir_ns(xs, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Irreversible.sp_ir_ns(xs, s2), e))
      irx.rep_m(s, xs, s2, pre2, LGlobEntry.ge.nats_fit(s1, xs, s2, ee), FIr.entries.of(xs), LA.irb.ledger_exact(xs))
    case Wr.Bad{}:
      Unit{}

# The tag
# -------

def irx.tag_at(+s: String, t: Nat, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> irx.Q(s, FIr.get_req.tag(t, s1)):
  match t:
    case 0n:
      irx.classes(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), {==})
    case 1n:
      irx.rec(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), {==})
    case 2n:
      irx.rep(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), {==})
    case 3n+u:
      Unit{}

def irx.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> irx.Q(s, FIr.get_req.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      irx.tag_at(s, t, s1, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

def irx.T(s: String) -> Type:
  Sigma<&1, &1, FIr.Req, q => {s == Irreversible.sp_ir_req(q, "") : String} & {Irreversible.ir_req_fits(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def irx.top(-s: String, d: Wr.Dec<FIr.Req>, hq: irx.Q(s, d), ok: {LawsBase.wire_opens_err(FIr.run(d)) == False{} : Bool}) -> irx.T(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, hq)
        case SCon{x, y}:
          LStg.stg.absurd(irx.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(irx.T(s), ok)

def Irreversible.irreversible_entry_exact(s, ok):
  irx.top(s, FIr.get_req(s), irx.tag(s, Wr.get_nat(s), {==}), ok)
