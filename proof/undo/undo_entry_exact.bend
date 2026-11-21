# eukhe: the proof of LAW undo_entry_exact
#
# PROOF: each decoder stage of bend/ffi_undo.bend answers Got{x, rest} only for an input that is the spec's spelling of x before rest, every number within the wire (unx.*: a predicate per decoder answer, carried stage by stage with wire_nat_exact, wire_nat_decoded_fits, wire_list_exact with wire_nats_spells, the glob area's ge.nats_fit, and LA.unb.rx for the rows). The entry answers a value only for a request read whole with nothing left.

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_list_exact.bend as PWireListExact
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../glob/base/entry.bend as LGlob

def unx.RP(s: String, d: Wr.Dec<FU.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Undo.sp_w_req(q, r) : String} & {Undo.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def unx.ev(-s: String, +l: List<&2, Nat>, +b: Nat, +s3: String, pre: {s == Wr.put_nat(0n, LawsBase.wire_spell_nats(l, Wr.put_nat(b, s3))) : String}, fl: {Undo.sp_fit_nats(l) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> unx.RP(s, FU.get_req.ev(l, b, d)):
  match d:
    case Wr.Got{+e, +s4}:
      +e1 = ed
      +ex = Wire.wire_nat_exact(s3, e, s4, e1)
      +fe = Wire.wire_nat_decoded_fits(s3, e, s4, e1)
      +p = LA.unb.under(s, s3, Wr.put_nat(e, s4), z => Wr.put_nat(0n, LawsBase.wire_spell_nats(l, Wr.put_nat(b, z))), pre, ex)
      %Equal.sym(Nat, Undo.sp_w_maybe(FU.maybe_of(b)), b, LA.unb.wm(b)) : {s == Wr.put_nat(0n, LawsBase.wire_spell_nats(l, Wr.put_nat(_, Wr.put_nat(Undo.sp_w_ev(FU.ev_of(e)), s4)))) : String} & {Bool.and(Undo.sp_fit_nats(l), Bool.and(LawsBase.wire_fits(_), LawsBase.wire_fits(Undo.sp_w_ev(FU.ev_of(e))))) == True{} : Bool}
      %Equal.sym(Nat, Undo.sp_w_ev(FU.ev_of(e)), e, LA.unb.we(e)) : {s == Wr.put_nat(0n, LawsBase.wire_spell_nats(l, Wr.put_nat(b, Wr.put_nat(_, s4)))) : String} & {Bool.and(Undo.sp_fit_nats(l), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(_))) == True{} : Bool}
      (p, LBool.cb_and_intro(Undo.sp_fit_nats(l), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(e)), fl, LBool.cb_and_intro(LawsBase.wire_fits(b), LawsBase.wire_fits(e), fb, fe)))
    case Wr.Bad{}:
      Unit{}

def unx.base(-s: String, +l: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(0n, LawsBase.wire_spell_nats(l, s2)) : String}, fl: {Undo.sp_fit_nats(l) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> unx.RP(s, FU.get_req.base(l, d)):
  match d:
    case Wr.Got{+b, +s3}:
      +e1 = ed
      +ex = Wire.wire_nat_exact(s2, b, s3, e1)
      +fb = Wire.wire_nat_decoded_fits(s2, b, s3, e1)
      unx.ev(s, l, b, s3, LA.unb.under(s, s2, Wr.put_nat(b, s3), z => Wr.put_nat(0n, LawsBase.wire_spell_nats(l, z)), pre, ex), fl, fb, Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

# a list of Nats decoded is its spelling, and fits
def unx.nats(+s1: String, +l: List<&2, Nat>, +s2: String, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == Wr.Got{l, s2} : Wr.Dec<List<&2, Nat>>}) -> {s1 == LawsBase.wire_spell_nats(l, s2) : String}:
  Equal.trans(String, s1, Wr.put_list(~Nat, ~Wr.put_nat, l, s2), LawsBase.wire_spell_nats(l, s2), Wire.wire_list_exact(s1, l, s2, ed), Wire.wire_nats_spells(l, s2))

def unx.live(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> unx.RP(s, FU.get_req.live(d)):
  match d:
    case Wr.Got{+l, +s2}:
      +e1 = ed
      unx.base(s, l, s2, LA.unb.under(s, s1, LawsBase.wire_spell_nats(l, s2), z => Wr.put_nat(0n, z), pre, unx.nats(s1, l, s2, e1)), LGlob.ge.nats_fit(s1, l, s2, e1), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def unx.fix_m(-s: String, +ns: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(1n, LawsBase.wire_spell_nats(ns, s2)) : String}, fn: {Undo.sp_fit_nats(ns) == True{} : Bool}, m: Maybe<&2, List<&2, U.Row>>, rx: LA.unb.RX(ns, m)) -> unx.RP(s, FU.get_req.fix(m, s2)):
  match m:
    case None{}:
      Unit{}
    case Some{rows}:
      %rx : {s == Wr.put_nat(1n, LawsBase.wire_spell_nats(_, s2)) : String} & {Undo.sp_fit_nats(_) == True{} : Bool}
      (pre, fn)

def unx.fix_rows(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> unx.RP(s, FU.get_req.fix_rows(d)):
  match d:
    case Wr.Got{+ns, +s2}:
      +e1 = ed
      unx.fix_m(s, ns, s2, LA.unb.under(s, s1, LawsBase.wire_spell_nats(ns, s2), z => Wr.put_nat(1n, z), pre, unx.nats(s1, ns, s2, e1)), LGlob.ge.nats_fit(s1, ns, s2, e1), FU.rows_of(ns), LA.unb.rx(ns))
    case Wr.Bad{}:
      Unit{}

def unx.seen_m(-s: String, +ns: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(2n, LawsBase.wire_spell_nats(ns, s2)) : String}, fn: {Undo.sp_fit_nats(ns) == True{} : Bool}, m: Maybe<&2, List<&2, U.Row>>, rx: LA.unb.RX(ns, m)) -> unx.RP(s, FU.get_req.seen(m, s2)):
  match m:
    case None{}:
      Unit{}
    case Some{rows}:
      %rx : {s == Wr.put_nat(2n, LawsBase.wire_spell_nats(_, s2)) : String} & {Undo.sp_fit_nats(_) == True{} : Bool}
      (pre, fn)

def unx.seen_rows(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> unx.RP(s, FU.get_req.seen_rows(d)):
  match d:
    case Wr.Got{+ns, +s2}:
      +e1 = ed
      unx.seen_m(s, ns, s2, LA.unb.under(s, s1, LawsBase.wire_spell_nats(ns, s2), z => Wr.put_nat(2n, z), pre, unx.nats(s1, ns, s2, e1)), LGlob.ge.nats_fit(s1, ns, s2, e1), FU.rows_of(ns), LA.unb.rx(ns))
    case Wr.Bad{}:
      Unit{}

def unx.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> unx.RP(s, FU.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          unx.live(s, s1, Wire.wire_nat_exact(s, 0n, s1, ed), Wr.get_list(~Nat, ~Wr.get_nat, s1), {==})
        case 1n:
          unx.fix_rows(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_list(~Nat, ~Wr.get_nat, s1), {==})
        case 2n:
          unx.seen_rows(s, s1, Wire.wire_nat_exact(s, 2n, s1, ed), Wr.get_list(~Nat, ~Wr.get_nat, s1), {==})
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def unx.top(-s: String, d: Wr.Dec<FU.Req>, rp: unx.RP(s, d), ok: {LawsBase.wire_opens_err(FU.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FU.Req, r => {s == Undo.sp_w_req(r, "") : String} & {Undo.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FU.Req, r2 => {s == Undo.sp_w_req(r2, "") : String} & {Undo.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FU.Req, r2 => {s == Undo.sp_w_req(r2, "") : String} & {Undo.sp_fit_req(r2) == True{} : Bool}>, ok)

def Undo.undo_entry_exact(s, ok):
  unx.top(s, FU.get_req(s), unx.tag(s, Wr.get_nat(s), {==}), ok)
