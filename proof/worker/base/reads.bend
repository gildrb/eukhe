# eukhe: what each decoder answer of the worker entry says about its input
# (ci_*): a Got answer comes from the spelling of the value, which fits the
# wire. Each stage is a wire value its exactness law inverts
# (wire_nat_exact, wire_str_exact, wire_bool_exact, wire_list_exact),
# threading `pre`, the input spelled so far; a decoded value fits
# (wire_*_decoded_fit(s)). Used by worker_ffi_reads_only_requests and
# worker_ffi_malformed_unless_request.

import Base
import ../../../bend/worker.bend as Wk
import ../../../bend/ffi_worker.bend as FWk
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/worker.bend as Worker
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_str_exact.bend as PWireStrExact
import ../../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/wire_list_exact.bend as PWireListExact
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../base.bend as LAWorker

# ---- primitives ----

def ci_nat(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ci_nat_at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ci_nat(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e = ed
      (Wire.wire_nat_exact(s, n, r, e), Wire.wire_nat_decoded_fits(s, n, r, e))
    case Wr.Bad{}:
      Unit{}

def ci_str(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{+t, r}:
      {s == Wr.put_str(t, r) : String} & {LawsBase.wire_fits(String.length(t)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ci_str_at(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> ci_str(s, d):
  match d:
    case Wr.Got{+t, +r}:
      +e = ed
      (Wire.wire_str_exact(s, t, r, e), Wire.wire_str_decoded_fits(s, t, r, e))
    case Wr.Bad{}:
      Unit{}

def ci_bool(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def ci_bool_at(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> ci_bool(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

# ---- lists of Nats ----

# a decoded list of Nats: its length and its items fit
def cx_go_p(m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {List.length(&2, Nat, xs) == 1n+m : Nat} & {LawsBase.wire_nats_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cx_go_cons(+m: Nat, +x: Nat, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, v: cx_go_p(m, d)) -> cx_go_p(1n+m, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = v
      (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, xs), 1n+m, e1), LAWorker.wb_and_tt(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(xs), fx, e2))
    case Wr.Bad{}:
      Unit{}

def cx_go(m: Nat, +s: String, cur: Wr.Dec<Nat>, ec: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) -> cx_go_p(m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +r}:
      ({==}, LAWorker.wb_and_tt(LawsBase.wire_fits(x), True{}, Wire.wire_nat_decoded_fits(s, x, r, ec), {==}))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +r}:
      cx_go_cons(k, x, Wire.wire_nat_decoded_fits(s, x, r, ec), Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(r)), cx_go(k, r, Wr.get_nat(r), {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

def cx_nf(d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {Worker.wk_nats_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cx_nf_go(+m: Nat, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, v: cx_go_p(m, d)) -> cx_nf(d):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = v
      %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e1) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
      LAWorker.wb_and_tt(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(xs), fn, e2)
    case Wr.Bad{}:
      Unit{}

def cx_nf_n(n: Nat, +s1: String, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> cx_nf(Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s1})):
  match n:
    case 0n:
      {==}
    case 1n++m:
      cx_nf_go(m, fn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s1)), cx_go(m, s1, Wr.get_nat(s1), {==}))

def cx_nf_start(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cx_nf(Wr.get_list.start(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+n, +s1}:
      cx_nf_n(n, s1, Wire.wire_nat_decoded_fits(s, n, s1, ed))
    case Wr.Bad{}:
      Unit{}

# a decoded list of Nats fits the wire: its count and every item
def cx_nats_fit(+s: String, -xs: List<&2, Nat>, -r: String, ed: {FWk.get_nats(s) == Wr.Got{xs, r} : Wr.Dec<List<&2, Nat>>}) -> {Worker.wk_nats_fit(xs) == True{} : Bool}:
  %ed : cx_nf(_)
  cx_nf_start(s, Wr.get_nat(s), {==})

def ci_nats(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == LawsBase.wire_spell_nats(xs, r) : String} & {Worker.wk_nats_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ci_nats_at(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {FWk.get_nats(s) == d : Wr.Dec<List<&2, Nat>>}) -> ci_nats(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      +e = ed
      (Equal.trans(String, s, Wr.put_list(~Nat, ~Wr.put_nat, xs, r), LawsBase.wire_spell_nats(xs, r), Wire.wire_list_exact(s, xs, r, e), Wire.wire_nats_spells(xs, r)),
        cx_nats_fit(s, xs, r, e))
    case Wr.Bad{}:
      Unit{}

# ---- the pause state ----

def ci_mode(s: String, d: Wr.Dec<Wk.Mode>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Worker.wk_spell_mode(m, r) : String}
    case Wr.Bad{}:
      Unit

def cm_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> ci_mode(s, FWk.get_mode.tag(t, s1)):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n+x:
      Unit{}

def cm_go(+s: String, d: Wr.Dec<Nat>, cn: ci_nat(s, d)) -> ci_mode(s, FWk.get_mode.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      cm_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def ci_mode_all(+s: String) -> ci_mode(s, FWk.get_mode(s)):
  cm_go(s, Wr.get_nat(s), ci_nat_at(s, Wr.get_nat(s), {==}))

def ci_parked(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+p, r}:
      {s == Worker.wk_spell_parked(p, r) : String} & {LawsBase.wire_mfits(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cp_some(-s: String, +s1: String, e: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, cn: ci_nat(s1, d)) -> ci_parked(s, FWk.get_parked.some(d)):
  match d:
    case Wr.Got{+x, +s2}:
      (e2, f) = cn
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(x, s2)), e, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(x, s2), e2)), f)
    case Wr.Bad{}:
      Unit{}

def cp_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> ci_parked(s, FWk.get_parked.tag(t, s1)):
  match t:
    case 0n:
      (e, {==})
    case 1n:
      cp_some(s, s1, e, Wr.get_nat(s1), ci_nat_at(s1, Wr.get_nat(s1), {==}))
    case 2n+x:
      Unit{}

def cp_go(+s: String, d: Wr.Dec<Nat>, cn: ci_nat(s, d)) -> ci_parked(s, FWk.get_parked.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      cp_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def ci_parked_all(+s: String) -> ci_parked(s, FWk.get_parked(s)):
  cp_go(s, Wr.get_nat(s), ci_nat_at(s, Wr.get_nat(s), {==}))

def ci_st(s: String, d: Wr.Dec<Wk.St>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == Worker.wk_spell_st(x, r) : String} & {Worker.wk_st_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cs_n(-s0: String, +m: Wk.Mode, +p: Maybe<&2, Nat>, +k: List<&2, Nat>, +s3: String,
  pre: {s0 == Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, LawsBase.wire_spell_nats(k, s3))) : String},
  fp: {LawsBase.wire_mfits(p) == True{} : Bool}, fk: {Worker.wk_nats_fit(k) == True{} : Bool},
  d: Wr.Dec<Nat>, cn: ci_nat(s3, d)) -> ci_st(s0, FWk.get_st.n(m, p, k, d)):
  match d:
    case Wr.Got{+n, +s4}:
      (e, f) = cn
      (Equal.trans(String, s0, Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, LawsBase.wire_spell_nats(k, s3))), Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, LawsBase.wire_spell_nats(k, Wr.put_nat(n, s4)))), pre,
          Equal.cong(String, String, z => Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, LawsBase.wire_spell_nats(k, z))), s3, Wr.put_nat(n, s4), e)),
        LAWorker.wb_and_tt(LawsBase.wire_mfits(p), Bool.and(Worker.wk_nats_fit(k), LawsBase.wire_fits(n)), fp, LAWorker.wb_and_tt(Worker.wk_nats_fit(k), LawsBase.wire_fits(n), fk, f)))
    case Wr.Bad{}:
      Unit{}

def cs_kept(-s0: String, +m: Wk.Mode, +p: Maybe<&2, Nat>, +s2: String,
  pre: {s0 == Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, s2)) : String}, fp: {LawsBase.wire_mfits(p) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, ck: ci_nats(s2, d)) -> ci_st(s0, FWk.get_st.kept(m, p, d)):
  match d:
    case Wr.Got{+k, +s3}:
      (e, f) = ck
      cs_n(s0, m, p, k, s3,
        Equal.trans(String, s0, Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, s2)), Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, LawsBase.wire_spell_nats(k, s3))), pre,
          Equal.cong(String, String, z => Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, z)), s2, LawsBase.wire_spell_nats(k, s3), e)),
        fp, f, Wr.get_nat(s3), ci_nat_at(s3, Wr.get_nat(s3), {==}))
    case Wr.Bad{}:
      Unit{}

def cs_parked(-s0: String, +m: Wk.Mode, +s1: String, pre: {s0 == Worker.wk_spell_mode(m, s1) : String},
  d: Wr.Dec<Maybe<&2, Nat>>, cp: ci_parked(s1, d)) -> ci_st(s0, FWk.get_st.parked(m, d)):
  match d:
    case Wr.Got{+p, +s2}:
      (e, f) = cp
      cs_kept(s0, m, p, s2,
        Equal.trans(String, s0, Worker.wk_spell_mode(m, s1), Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, s2)), pre,
          Equal.cong(String, String, z => Worker.wk_spell_mode(m, z), s1, Worker.wk_spell_parked(p, s2), e)),
        f, FWk.get_nats(s2), ci_nats_at(s2, FWk.get_nats(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def cs_mode(+s0: String, d: Wr.Dec<Wk.Mode>, cm: ci_mode(s0, d)) -> ci_st(s0, FWk.get_st.mode(d)):
  match d:
    case Wr.Got{+m, +s1}:
      cs_parked(s0, m, s1, cm, FWk.get_parked(s1), ci_parked_all(s1))
    case Wr.Bad{}:
      Unit{}

# every state the reader reads is spelled, and fits
def ci_st_all(+s: String) -> ci_st(s, FWk.get_st(s)):
  cs_mode(s, FWk.get_mode(s), ci_mode_all(s))

# ---- events ----

def ci_ev(s: String, d: Wr.Dec<Wk.Ev>) -> Type:
  match d:
    case Wr.Got{+e, r}:
      {s == Worker.wk_spell_ev(e, r) : String} & {Worker.wk_ev_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ce_gate_id(-s: String, +g: Nat, +s1: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(g, s1)) : String}, fg: {LawsBase.wire_fits(g) == True{} : Bool},
  d: Wr.Dec<Nat>, cn: ci_nat(s1, d)) -> ci_ev(s, FWk.get_ev.gate.id(g, d)):
  match d:
    case Wr.Got{+i, +s2}:
      (e, f) = cn
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(g, s1)), Wr.put_nat(2n, Wr.put_nat(g, Wr.put_nat(i, s2))), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(g, z)), s1, Wr.put_nat(i, s2), e)),
        LAWorker.wb_and_tt(LawsBase.wire_fits(g), LawsBase.wire_fits(i), fg, f))
    case Wr.Bad{}:
      Unit{}

def ce_gate(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, cn: ci_nat(s1, d)) -> ci_ev(s, FWk.get_ev.gate(d)):
  match d:
    case Wr.Got{+g, +s2}:
      (e, f) = cn
      ce_gate_id(s, g, s2,
        Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_nat(g, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_nat(g, s2), e)),
        f, Wr.get_nat(s2), ci_nat_at(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def ce_wakes(-s: String, +i: Nat, +s1: String, pre: {s == Wr.put_nat(4n, Wr.put_nat(i, s1)) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool},
  d: Wr.Dec<Bool>, cb: ci_bool(s1, d)) -> ci_ev(s, FWk.get_ev.msg.wakes(i, d)):
  match d:
    case Wr.Got{+w, +s2}:
      (Equal.trans(String, s, Wr.put_nat(4n, Wr.put_nat(i, s1)), Wr.put_nat(4n, Wr.put_nat(i, Wr.put_bool(w, s2))), pre,
          Equal.cong(String, String, z => Wr.put_nat(4n, Wr.put_nat(i, z)), s1, Wr.put_bool(w, s2), cb)),
        fi)
    case Wr.Bad{}:
      Unit{}

def ce_msg(-s: String, +s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<Nat>, cn: ci_nat(s1, d)) -> ci_ev(s, FWk.get_ev.msg(d)):
  match d:
    case Wr.Got{+i, +s2}:
      (e, f) = cn
      ce_wakes(s, i, s2,
        Equal.trans(String, s, Wr.put_nat(4n, s1), Wr.put_nat(4n, Wr.put_nat(i, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(4n, z), s1, Wr.put_nat(i, s2), e)),
        f, Wr.get_bool(s2), ci_bool_at(s2, Wr.get_bool(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def ce_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> ci_ev(s, FWk.get_ev.tag(t, s1)):
  match t:
    case 0n:
      (e, {==})
    case 1n:
      (e, {==})
    case 2n:
      ce_gate(s, s1, e, Wr.get_nat(s1), ci_nat_at(s1, Wr.get_nat(s1), {==}))
    case 3n:
      (e, {==})
    case 4n:
      ce_msg(s, s1, e, Wr.get_nat(s1), ci_nat_at(s1, Wr.get_nat(s1), {==}))
    case 5n:
      (e, {==})
    case 6n+x:
      Unit{}

def ce_go(+s: String, d: Wr.Dec<Nat>, cn: ci_nat(s, d)) -> ci_ev(s, FWk.get_ev.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      ce_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

# every event the reader reads is spelled, and fits
def ci_ev_all(+s: String) -> ci_ev(s, FWk.get_ev(s)):
  ce_go(s, Wr.get_nat(s), ci_nat_at(s, Wr.get_nat(s), {==}))

# ---- messages ----

def ci_umsg(s: String, d: Wr.Dec<Wk.UMsg>) -> Type:
  match d:
    case Wr.Got{+m, r}:
      {s == Worker.wk_spell_umsg(m, r) : String} & {Worker.wk_umsg_fits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cu_text(-s: String, +q: Nat, +s1: String, pre: {s == Wr.put_nat(q, s1) : String}, fq: {LawsBase.wire_fits(q) == True{} : Bool},
  d: Wr.Dec<String>, ct: ci_str(s1, d)) -> ci_umsg(s, FWk.get_umsg.text(q, d)):
  match d:
    case Wr.Got{+t, +s2}:
      (e, f) = ct
      (Equal.trans(String, s, Wr.put_nat(q, s1), Wr.put_nat(q, Wr.put_str(t, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(q, z), s1, Wr.put_str(t, s2), e)),
        LAWorker.wb_and_tt(LawsBase.wire_fits(q), LawsBase.wire_fits(String.length(t)), fq, f))
    case Wr.Bad{}:
      Unit{}

def cu_seq(+s: String, d: Wr.Dec<Nat>, cn: ci_nat(s, d)) -> ci_umsg(s, FWk.get_umsg.seq(d)):
  match d:
    case Wr.Got{+q, +s1}:
      (e, f) = cn
      cu_text(s, q, s1, e, f, Wr.get_str(s1), ci_str_at(s1, Wr.get_str(s1), {==}))
    case Wr.Bad{}:
      Unit{}

def ci_umsg_all(+s: String) -> ci_umsg(s, FWk.get_umsg(s)):
  cu_seq(s, Wr.get_nat(s), ci_nat_at(s, Wr.get_nat(s), {==}))

def ci_umsg_at(+s: String, -d: Wr.Dec<Wk.UMsg>, er: {FWk.get_umsg(s) == d : Wr.Dec<Wk.UMsg>}) -> ci_umsg(s, d):
  %er : ci_umsg(s, _)
  ci_umsg_all(s)

# what the message loop's answer says about its input s (m + 1 messages)
def ci_ul(s: String, m: Nat, d: Wr.Dec<List<&2, Wk.UMsg>>) -> Type:
  match d:
    case Wr.Got{+ms, r}:
      {s == Worker.wk_spell_umsgs.items(ms, r) : String} & ({List.length(&2, Wk.UMsg, ms) == 1n+m : Nat} & {Worker.wk_umsgs_all(ms) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def cl_step(-s: String, +x: Wk.UMsg, +s3: String, -k: Nat, ea: {s == Worker.wk_spell_umsg(x, s3) : String}, eb: {Worker.wk_umsg_fits(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Wk.UMsg>>, ih: ci_ul(s3, k, d)) -> ci_ul(s, 1n+k, Wr.get_list.cons(Wk.UMsg, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, ee) = ih
      (e2, e3) = ee
      (Equal.trans(String, s, Worker.wk_spell_umsg(x, s3), Worker.wk_spell_umsg(x, Worker.wk_spell_umsgs.items(ys, r)), ea,
          Equal.cong(String, String, z => Worker.wk_spell_umsg(x, z), s3, Worker.wk_spell_umsgs.items(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Wk.UMsg, ys), 1n+k, e2),
          LAWorker.wb_and_tt(Worker.wk_umsg_fits(x), Worker.wk_umsgs_all(ys), eb, e3)))
    case Wr.Bad{}:
      Unit{}

def cl_step2(-s: String, +x: Wk.UMsg, +s3: String, -k: Nat, ex: ci_umsg(s, Wr.Got{x, s3}),
  d: Wr.Dec<List<&2, Wk.UMsg>>, ih: ci_ul(s3, k, d)) -> ci_ul(s, 1n+k, Wr.get_list.cons(Wk.UMsg, x, d)):
  (ea, eb) = ex
  cl_step(s, x, s3, k, ea, eb, d, ih)

def cl_one(-s: String, +x: Wk.UMsg, -s3: String, ex: ci_umsg(s, Wr.Got{x, s3})) -> ci_ul(s, 0n, Wr.Got{[x], s3}):
  (ea, eb) = ex
  (ea, ({==}, LAWorker.wb_and_tt(Worker.wk_umsg_fits(x), True{}, eb, {==})))

# the message loop accepts only spelled messages that fit
def cl_spec(m: Nat, cur: Wr.Dec<Wk.UMsg>, +s: String, er: {FWk.get_umsg(s) == cur : Wr.Dec<Wk.UMsg>}) ->
  ci_ul(s, m, Wr.get_list.go(~Wk.UMsg, ~FWk.get_umsg, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      cl_one(s, x, s3, ci_umsg_at(s, Wr.Got{x, s3}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      cl_step2(s, x, s3, k, ci_umsg_at(s, Wr.Got{x, s3}, er),
        Wr.get_list.go(~Wk.UMsg, ~FWk.get_umsg, k, FWk.get_umsg(s3)), cl_spec(k, FWk.get_umsg(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

def ci_umsgs(s: String, d: Wr.Dec<List<&2, Wk.UMsg>>) -> Type:
  match d:
    case Wr.Got{+ms, r}:
      {s == Worker.wk_spell_umsgs(ms, r) : String} & {Worker.wk_umsgs_fit(ms) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cl_eq(+s: String, +s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, +ms: List<&2, Wk.UMsg>, -r: String,
  e1: {s2 == Worker.wk_spell_umsgs.items(ms, r) : String}, e2: {List.length(&2, Wk.UMsg, ms) == 1n+m : Nat}) -> {s == Worker.wk_spell_umsgs(ms, r) : String}:
  %Equal.sym(Nat, List.length(&2, Wk.UMsg, ms), 1n+m, e2) : {s == Wr.put_nat(_, Worker.wk_spell_umsgs.items(ms, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def cl_fit(-m: Nat, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, +ms: List<&2, Wk.UMsg>,
  e2: {List.length(&2, Wk.UMsg, ms) == 1n+m : Nat}, e3: {Worker.wk_umsgs_all(ms) == True{} : Bool}) -> {Worker.wk_umsgs_fit(ms) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Wk.UMsg, ms), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), Worker.wk_umsgs_all(ms)) == True{} : Bool}
  LAWorker.wb_and_tt(LawsBase.wire_fits(1n+m), Worker.wk_umsgs_all(ms), hn, e3)

def cl_conv(+s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Wk.UMsg>>, tl: ci_ul(s2, m, d)) -> ci_umsgs(s, d):
  match d:
    case Wr.Got{+ms, +r}:
      (e1, ee) = tl
      (e2, e3) = ee
      +e4 = e2
      (cl_eq(s, s2, m, en, ms, r, e1, e4), cl_fit(m, hn, ms, e4, e3))
    case Wr.Bad{}:
      Unit{}

def cl_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, hn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  ci_umsgs(s, Wr.get_list.start(~Wk.UMsg, ~FWk.get_umsg, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      cl_conv(s, s2, m, en, hn, Wr.get_list.go(~Wk.UMsg, ~FWk.get_umsg, m, FWk.get_umsg(s2)), cl_spec(m, FWk.get_umsg(s2), s2, {==}))

def cl_top(+s: String, d: Wr.Dec<Nat>, cn: ci_nat(s, d)) -> ci_umsgs(s, Wr.get_list.start(~Wk.UMsg, ~FWk.get_umsg, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (e, f) = cn
      cl_nat(s, n, s2, e, f)
    case Wr.Bad{}:
      Unit{}

# every message list the reader reads is spelled, and fits
def ci_umsgs_all(+s: String) -> ci_umsgs(s, FWk.get_umsgs(s)):
  cl_top(s, Wr.get_nat(s), ci_nat_at(s, Wr.get_nat(s), {==}))

# ---- the note ----

def ci_note(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Worker.wk_spell_note(n, r) : String} & {Worker.wk_note_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cn_some(-s: String, +s1: String, e: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, ct: ci_str(s1, d)) -> ci_note(s, FWk.get_note.some(d)):
  match d:
    case Wr.Got{+t, +s2}:
      (e2, f) = ct
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(t, s2)), e, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_str(t, s2), e2)), f)
    case Wr.Bad{}:
      Unit{}

def cn_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> ci_note(s, FWk.get_note.tag(t, s1)):
  match t:
    case 0n:
      (e, {==})
    case 1n:
      cn_some(s, s1, e, Wr.get_str(s1), ci_str_at(s1, Wr.get_str(s1), {==}))
    case 2n+x:
      Unit{}

def cn_go(+s: String, d: Wr.Dec<Nat>, cn: ci_nat(s, d)) -> ci_note(s, FWk.get_note.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      cn_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def ci_note_all(+s: String) -> ci_note(s, FWk.get_note(s)):
  cn_go(s, Wr.get_nat(s), ci_nat_at(s, Wr.get_nat(s), {==}))

# ---- the request ----

def ci_req(s: String, d: Wr.Dec<FWk.Req>) -> Type:
  match d:
    case Wr.Got{+r, rest}:
      {s == Worker.wk_spell_req(r, rest) : String} & {Worker.wk_req_fits(r) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cr_ev(-s0: String, +x: Wk.St, +s1: String, pre: {s0 == Wr.put_nat(0n, Worker.wk_spell_st(x, s1)) : String}, fx: {Worker.wk_st_fits(x) == True{} : Bool},
  d: Wr.Dec<Wk.Ev>, ce: ci_ev(s1, d)) -> ci_req(s0, FWk.get_req.ev(x, d)):
  match d:
    case Wr.Got{+e, +s2}:
      (e1, f) = ce
      (Equal.trans(String, s0, Wr.put_nat(0n, Worker.wk_spell_st(x, s1)), Wr.put_nat(0n, Worker.wk_spell_st(x, Worker.wk_spell_ev(e, s2))), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, Worker.wk_spell_st(x, z)), s1, Worker.wk_spell_ev(e, s2), e1)),
        LAWorker.wb_and_tt(Worker.wk_st_fits(x), Worker.wk_ev_fits(e), fx, f))
    case Wr.Bad{}:
      Unit{}

def cr_st(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Wk.St>, cs: ci_st(s1, d)) -> ci_req(s0, FWk.get_req.st(d)):
  match d:
    case Wr.Got{+x, +s2}:
      (e, f) = cs
      cr_ev(s0, x, s2,
        Equal.trans(String, s0, Wr.put_nat(0n, s1), Wr.put_nat(0n, Worker.wk_spell_st(x, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Worker.wk_spell_st(x, s2), e)),
        f, FWk.get_ev(s2), ci_ev_all(s2))
    case Wr.Bad{}:
      Unit{}

def cr_note(-s0: String, +c: Nat, +ms: List<&2, Wk.UMsg>, +s2: String,
  pre: {s0 == Wr.put_nat(1n, Wr.put_nat(c, Worker.wk_spell_umsgs(ms, s2))) : String},
  fc: {LawsBase.wire_fits(c) == True{} : Bool}, fms: {Worker.wk_umsgs_fit(ms) == True{} : Bool},
  d: Wr.Dec<Maybe<&2, String>>, cn: ci_note(s2, d)) -> ci_req(s0, FWk.get_req.note(c, ms, d)):
  match d:
    case Wr.Got{+n, +s3}:
      (e, f) = cn
      (Equal.trans(String, s0, Wr.put_nat(1n, Wr.put_nat(c, Worker.wk_spell_umsgs(ms, s2))), Wr.put_nat(1n, Wr.put_nat(c, Worker.wk_spell_umsgs(ms, Worker.wk_spell_note(n, s3)))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(c, Worker.wk_spell_umsgs(ms, z))), s2, Worker.wk_spell_note(n, s3), e)),
        LAWorker.wb_and_tt(LawsBase.wire_fits(c), Bool.and(Worker.wk_umsgs_fit(ms), Worker.wk_note_fits(n)), fc, LAWorker.wb_and_tt(Worker.wk_umsgs_fit(ms), Worker.wk_note_fits(n), fms, f)))
    case Wr.Bad{}:
      Unit{}

def cr_msgs(-s0: String, +c: Nat, +s1: String, pre: {s0 == Wr.put_nat(1n, Wr.put_nat(c, s1)) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool},
  d: Wr.Dec<List<&2, Wk.UMsg>>, cm: ci_umsgs(s1, d)) -> ci_req(s0, FWk.get_req.msgs(c, d)):
  match d:
    case Wr.Got{+ms, +s2}:
      (e, f) = cm
      cr_note(s0, c, ms, s2,
        Equal.trans(String, s0, Wr.put_nat(1n, Wr.put_nat(c, s1)), Wr.put_nat(1n, Wr.put_nat(c, Worker.wk_spell_umsgs(ms, s2))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(c, z)), s1, Worker.wk_spell_umsgs(ms, s2), e)),
        fc, f, FWk.get_note(s2), ci_note_all(s2))
    case Wr.Bad{}:
      Unit{}

def cr_cursor(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, cn: ci_nat(s1, d)) -> ci_req(s0, FWk.get_req.cursor(d)):
  match d:
    case Wr.Got{+c, +s2}:
      (e, f) = cn
      cr_msgs(s0, c, s2,
        Equal.trans(String, s0, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(c, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(c, s2), e)),
        f, FWk.get_umsgs(s2), ci_umsgs_all(s2))
    case Wr.Bad{}:
      Unit{}

def cr_tag(-s0: String, t: Nat, +s1: String, e: {s0 == Wr.put_nat(t, s1) : String}) -> ci_req(s0, FWk.get_req.tag(t, s1)):
  match t:
    case 0n:
      cr_st(s0, s1, e, FWk.get_st(s1), ci_st_all(s1))
    case 1n:
      cr_cursor(s0, s1, e, Wr.get_nat(s1), ci_nat_at(s1, Wr.get_nat(s1), {==}))
    case 2n+x:
      Unit{}

def cr_go(+s: String, d: Wr.Dec<Nat>, cn: ci_nat(s, d)) -> ci_req(s, FWk.get_req.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      cr_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

# every request the decoder reads is spelled, and fits
def ci_req_all(+s: String) -> ci_req(s, FWk.get_req(s)):
  cr_go(s, Wr.get_nat(s), ci_nat_at(s, Wr.get_nat(s), {==}))
