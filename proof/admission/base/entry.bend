# eukhe: lemmas of the entry laws of area admission: the stepper's
# encoders write what the spec's spellers write and its decoders read what
# the spec's readers read (laws/admission.bend, ads_*), on every input.

import Base
import ../../../bend/admission.bend as Ad
import ../../../bend/ffi_admission.bend as FAd
import ../../../bend/wire.bend as Wr
import ../../../laws/admission/entry.bend as AdmissionEntry

# Encoders
# --------

def pae.cls(c: Ad.Cls, rest: String) -> {FAd.put_cls(c, rest) == AdmissionEntry.ads_spell_cls(c, rest) : String}:
  match c:
    case Ad.Ia{}:
      {==}
    case Ad.Bg{}:
      {==}

def pae.sts(s: Ad.Sts, rest: String) -> {FAd.put_sts(s, rest) == AdmissionEntry.ads_spell_sts(s, rest) : String}:
  match s:
    case Ad.Queued{}:
      {==}
    case Ad.Granted{}:
      {==}
    case Ad.Held{}:
      {==}
    case Ad.Preempted{}:
      {==}
    case Ad.Ended{}:
      {==}

def pae.lim(l: Ad.Lim, rest: String) -> {FAd.put_lim(l, rest) == AdmissionEntry.ads_spell_lim(l, rest) : String}:
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{p}:
      {==}

def pae.lv(t: Ad.Lv, rest: String) -> {FAd.put_lv(t, rest) == AdmissionEntry.ads_spell_lv(t, rest) : String}:
  match t:
    case Ad.Lv{k, c, s}:
      match c:
        case Ad.Ia{}:
          match s:
            case Ad.Queued{}:
              {==}
            case Ad.Granted{}:
              {==}
            case Ad.Held{}:
              {==}
            case Ad.Preempted{}:
              {==}
            case Ad.Ended{}:
              {==}
        case Ad.Bg{}:
          match s:
            case Ad.Queued{}:
              {==}
            case Ad.Granted{}:
              {==}
            case Ad.Held{}:
              {==}
            case Ad.Preempted{}:
              {==}
            case Ad.Ended{}:
              {==}

def pae.lvs_step(+x: Ad.Lv, r: Nat & String) -> {Wr.put_list.step(~Ad.Lv, ~FAd.put_lv, x, r) == Wr.put_list.step(~Ad.Lv, ~AdmissionEntry.ads_spell_lv, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %pae.lv(x, s) : {(1n+n, FAd.put_lv(x, s)) == (1n+n, _) : Nat & String}
      {==}

def pae.lvs_go(xs: List<&2, Ad.Lv>, +rest: String) -> {Wr.put_list.go(~Ad.Lv, ~FAd.put_lv, xs, rest) == Wr.put_list.go(~Ad.Lv, ~AdmissionEntry.ads_spell_lv, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %pae.lvs_go(t, rest) : {Wr.put_list.step(~Ad.Lv, ~FAd.put_lv, x, Wr.put_list.go(~Ad.Lv, ~FAd.put_lv, t, rest)) == Wr.put_list.step(~Ad.Lv, ~AdmissionEntry.ads_spell_lv, x, _) : Nat & String}
      pae.lvs_step(x, Wr.put_list.go(~Ad.Lv, ~FAd.put_lv, t, rest))

def pae.lvs(xs: List<&2, Ad.Lv>, +rest: String) -> {Wr.put_list(~Ad.Lv, ~FAd.put_lv, xs, rest) == Wr.put_list(~Ad.Lv, ~AdmissionEntry.ads_spell_lv, xs, rest) : String}:
  %pae.lvs_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Ad.Lv, ~FAd.put_lv, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

def pae.live(x: Ad.Live, +rest: String) -> {FAd.put_live(x, rest) == AdmissionEntry.ads_spell_live(x, rest) : String}:
  match x:
    case Ad.Live{+l, +q, +ts, +n}:
      %pae.lvs(ts, Wr.put_nat(n, rest)) : {FAd.put_lim(l, Wr.put_nat(q, Wr.put_list(~Ad.Lv, ~FAd.put_lv, ts, Wr.put_nat(n, rest)))) == AdmissionEntry.ads_spell_lim(l, Wr.put_nat(q, _)) : String}
      pae.lim(l, Wr.put_nat(q, Wr.put_list(~Ad.Lv, ~FAd.put_lv, ts, Wr.put_nat(n, rest))))

def pae.op(o: Ad.Op, +rest: String) -> {FAd.put_op(o, rest) == AdmissionEntry.ads_spell_op(o, rest) : String}:
  match o:
    case Ad.Admit{c}:
      match c:
        case Ad.Ia{}:
          {==}
        case Ad.Bg{}:
          {==}
    case Ad.Collect{k}:
      {==}
    case Ad.Release{k}:
      {==}
    case Ad.Depart{k}:
      {==}
    case Ad.Limit{l, q}:
      match l:
        case Ad.Unl{}:
          {==}
        case Ad.Cap{p}:
          {==}

# Decoders
# --------

def pae.cls_tag(n: Nat, s: String) -> {FAd.get_cls.tag(n, s) == AdmissionEntry.ads_read_cls.tag(n, s) : Wr.Dec<Ad.Cls>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match m:
        case 0n:
          {==}
        case 1n+x:
          {==}

def pae.cls_go(d: Wr.Dec<Nat>) -> {FAd.get_cls.go(d) == AdmissionEntry.ads_read_cls.go(d) : Wr.Dec<Ad.Cls>}:
  match d:
    case Wr.Got{n, s}:
      pae.cls_tag(n, s)
    case Wr.Bad{}:
      {==}

def pae.get_cls(s: String) -> {FAd.get_cls(s) == AdmissionEntry.ads_read_cls(s) : Wr.Dec<Ad.Cls>}:
  pae.cls_go(Wr.get_nat(s))

def pae.cap(d: Wr.Dec<Nat>) -> {FAd.get_lim.cap(d) == AdmissionEntry.ads_read_cap(d) : Wr.Dec<Ad.Lim>}:
  match d:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pae.lim_tag(n: Nat, s: String) -> {FAd.get_lim.tag(n, s) == AdmissionEntry.ads_read_lim.tag(n, s) : Wr.Dec<Ad.Lim>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match m:
        case 0n:
          pae.cap(Wr.get_nat(s))
        case 1n+x:
          {==}

def pae.lim_go(d: Wr.Dec<Nat>) -> {FAd.get_lim.go(d) == AdmissionEntry.ads_read_lim.go(d) : Wr.Dec<Ad.Lim>}:
  match d:
    case Wr.Got{n, s}:
      pae.lim_tag(n, s)
    case Wr.Bad{}:
      {==}

def pae.get_lim(s: String) -> {FAd.get_lim(s) == AdmissionEntry.ads_read_lim(s) : Wr.Dec<Ad.Lim>}:
  pae.lim_go(Wr.get_nat(s))

def pae.admit(d: Wr.Dec<Ad.Cls>) -> {FAd.get_op.admit(d) == AdmissionEntry.ads_read_admit(d) : Wr.Dec<Ad.Op>}:
  match d:
    case Wr.Got{c, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pae.collect(d: Wr.Dec<Nat>) -> {FAd.get_op.k(d, 0n) == AdmissionEntry.ads_read_collect(d) : Wr.Dec<Ad.Op>}:
  match d:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pae.release(d: Wr.Dec<Nat>) -> {FAd.get_op.k(d, 1n) == AdmissionEntry.ads_read_release(d) : Wr.Dec<Ad.Op>}:
  match d:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pae.leave(d: Wr.Dec<Nat>) -> {FAd.get_op.k(d, 2n) == AdmissionEntry.ads_read_leave(d) : Wr.Dec<Ad.Op>}:
  match d:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pae.limit_q(l: Ad.Lim, d: Wr.Dec<Nat>) -> {FAd.get_op.q(l, d) == AdmissionEntry.ads_read_limit.q(l, d) : Wr.Dec<Ad.Op>}:
  match d:
    case Wr.Got{q, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pae.limit(d: Wr.Dec<Ad.Lim>) -> {FAd.get_op.limit(d) == AdmissionEntry.ads_read_limit(d) : Wr.Dec<Ad.Op>}:
  match d:
    case Wr.Got{l, s}:
      pae.limit_q(l, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pae.op_tag(n: Nat, +s: String) -> {FAd.get_op.tag(n, s) == AdmissionEntry.ads_read_op.tag(n, s) : Wr.Dec<Ad.Op>}:
  match n:
    case 0n:
      %pae.get_cls(s) : {FAd.get_op.admit(FAd.get_cls(s)) == AdmissionEntry.ads_read_admit(_) : Wr.Dec<Ad.Op>}
      pae.admit(FAd.get_cls(s))
    case 1n+a:
      match a:
        case 0n:
          pae.collect(Wr.get_nat(s))
        case 1n+b:
          match b:
            case 0n:
              pae.release(Wr.get_nat(s))
            case 1n+c:
              match c:
                case 0n:
                  pae.leave(Wr.get_nat(s))
                case 1n+d:
                  match d:
                    case 0n:
                      %pae.get_lim(s) : {FAd.get_op.limit(FAd.get_lim(s)) == AdmissionEntry.ads_read_limit(_) : Wr.Dec<Ad.Op>}
                      pae.limit(FAd.get_lim(s))
                    case 1n+e:
                      {==}

def pae.op_go(d: Wr.Dec<Nat>) -> {FAd.get_op.go(d) == AdmissionEntry.ads_read_op.go(d) : Wr.Dec<Ad.Op>}:
  match d:
    case Wr.Got{n, s}:
      pae.op_tag(n, s)
    case Wr.Bad{}:
      {==}

def pae.get_op(s: String) -> {FAd.get_op(s) == AdmissionEntry.ads_read_op(s) : Wr.Dec<Ad.Op>}:
  pae.op_go(Wr.get_nat(s))

def pae.open_q(l: Ad.Lim, d: Wr.Dec<Nat>) -> {FAd.get_open.q(l, d) == AdmissionEntry.ads_read_open.q(l, d) : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}:
  match d:
    case Wr.Got{q, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pae.open_go(d: Wr.Dec<Ad.Lim>) -> {FAd.get_open.go(d) == AdmissionEntry.ads_read_open.go(d) : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}:
  match d:
    case Wr.Got{l, s}:
      pae.open_q(l, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pae.get_open(+s: String) -> {FAd.get_open(s) == AdmissionEntry.ads_read_open(s) : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}:
  %pae.get_lim(s) : {FAd.get_open.go(FAd.get_lim(s)) == AdmissionEntry.ads_read_open.go(_) : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}
  pae.open_go(FAd.get_lim(s))

# The stepper
# -----------

def pae.open_end(b: Bool, +l: Ad.Lim, +q: Nat) -> {FAd.open.end(b, l, q) == AdmissionEntry.ads_open.end(b, l, q) : FAd.St & String}:
  match b:
    case True{}:
      %pae.live(Ad.Live{l, q, Nil{}, 0n}, "") : {(FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, FAd.put_live(Ad.Live{l, q, Nil{}, 0n}, "")) == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, _) : FAd.St & String}
      {==}
    case False{}:
      {==}

def pae.open_req(lq: +Sigma<Ad.Lim, x => Nat>, b: Bool) -> {FAd.open.req(lq, b) == AdmissionEntry.ads_open.req(lq, b) : FAd.St & String}:
  match lq:
    case (l, q):
      pae.open_end(b, l, q)

def pae.open_go2(d: Wr.Dec<+Sigma<Ad.Lim, x => Nat>>) -> {FAd.open.go(d) == AdmissionEntry.ads_open.go(d) : FAd.St & String}:
  match d:
    case Wr.Got{lq, s}:
      pae.open_req(lq, Wr.end(s))
    case Wr.Bad{}:
      {==}

# an open is the spec's, on every input
def pae.open(+s: String) -> {FAd.open(s) == AdmissionEntry.ads_open(s) : FAd.St & String}:
  %pae.get_open(s) : {FAd.open.go(FAd.get_open(s)) == AdmissionEntry.ads_open.go(_) : FAd.St & String}
  pae.open_go2(FAd.get_open(s))
