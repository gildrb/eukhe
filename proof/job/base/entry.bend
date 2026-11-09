# eukhe: what the job entry's and the rewind entry's decoders read
#
# Each decoder of a part answers a value only for input that spells it as
# the laws do (laws/job.bend), every number within the wire: each number
# read is exactly its encoding (wire_nat_exact, wire_u32_exact,
# wire_bool_exact) and fits (wire_nat_decoded_fits).

import Base
import ../../../bend/ffi_job.bend as FJb
import ../../../bend/ffi_job_rewind.bend as FJr
import ../../../bend/job.bend as Jb
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/job.bend as Job
import ../../../laws/wire.bend as Wire
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/logic/bool.bend as LLogicBool
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_u32_exact.bend as PWireU32Exact
import ../../wire/wire_bool_exact.bend as PWireBoolExact

def jer.and_tt(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LLogicLogic.pj.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

# s0 spelled with s in place of x is s0 spelled with y, when x is y
def jer.then(f: String -> String, -s0: String, -x: String, -y: String, pre: {s0 == f(x) : String}, e: {x == y : String}) -> {s0 == f(y) : String}:
  Equal.trans(String, s0, f(x), f(y), pre, Equal.cong(String, String, f, x, y, e))

# The job entry
# -------------

def jer.CodeRP(r: String, d: Wr.Dec<Jb.Code>) -> Type:
  match d:
    case Wr.Got{c, q}:
      {r == Job.job_spell_code(c, q) : String}
    case Wr.Bad{}:
      Unit

def jer.code_lo(+hi: U32, -r: String, +s: String, d: Wr.Dec<U32>, ed: {Wr.get_u32(s) == d : Wr.Dec<U32>}, pre: {r == Wr.put_u32(hi, s) : String}) -> jer.CodeRP(r, FJb.get_code.lo(hi, d)):
  match d:
    case Wr.Got{+lo, +q}:
      +e = ed
      jer.then(z => Wr.put_u32(hi, z), r, s, Wr.put_u32(lo, q), pre, Wire.wire_u32_exact(s, lo, q, e))
    case Wr.Bad{}:
      Unit{}

def jer.code_hi(+r: String, d: Wr.Dec<U32>, ed: {Wr.get_u32(r) == d : Wr.Dec<U32>}) -> jer.CodeRP(r, FJb.get_code.hi(d)):
  match d:
    case Wr.Got{+hi, +s}:
      +e = ed
      jer.code_lo(hi, r, s, Wr.get_u32(s), {==}, Wire.wire_u32_exact(r, hi, s, e))
    case Wr.Bad{}:
      Unit{}

def jer.code(+r: String) -> jer.CodeRP(r, FJb.get_code(r)):
  jer.code_hi(r, Wr.get_u32(r), {==})

def jer.EndRP(r: String, d: Wr.Dec<Jb.End>) -> Type:
  match d:
    case Wr.Got{x, q}:
      {r == Job.job_spell_end(x, q) : String}
    case Wr.Bad{}:
      Unit

def jer.end_code(-r0: String, -s: String, d: Wr.Dec<Jb.Code>, rp: jer.CodeRP(s, d), pre: {r0 == Wr.put_nat(0n, s) : String}) -> jer.EndRP(r0, FJb.get_end.code(d)):
  match d:
    case Wr.Got{+c, +q}:
      jer.then(z => Wr.put_nat(0n, z), r0, s, Job.job_spell_code(c, q), pre, rp)
    case Wr.Bad{}:
      Unit{}

def jer.end_tag(-r0: String, t: Nat, +s: String, pre: {r0 == Wr.put_nat(t, s) : String}) -> jer.EndRP(r0, FJb.get_end.tag(t, s)):
  match t:
    case 0n:
      jer.end_code(r0, s, FJb.get_code(s), jer.code(s), pre)
    case 1n+p:
      match p:
        case 0n:
          pre
        case 1n+q:
          Unit{}

def jer.end_go(+r: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> jer.EndRP(r, FJb.get_end.go(d)):
  match d:
    case Wr.Got{+t, +s}:
      +e = ed
      jer.end_tag(r, t, s, Wire.wire_nat_exact(r, t, s, e))
    case Wr.Bad{}:
      Unit{}

def jer.end(+r: String) -> jer.EndRP(r, FJb.get_end(r)):
  jer.end_go(r, Wr.get_nat(r), {==})

def jer.JobRP(r: String, d: Wr.Dec<Jb.J>) -> Type:
  match d:
    case Wr.Got{j, q}:
      {Job.wire_job_fits(j) == True{} : Bool} & {r == Job.job_spell_job(j, q) : String}
    case Wr.Bad{}:
      Unit

def jer.live_d(+k: Nat, -r0: String, +s1: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, pre: {r0 == Wr.put_nat(0n, Wr.put_nat(k, s1)) : String}) -> jer.JobRP(r0, FJb.get_job.d(k, d)):
  match d:
    case Wr.Got{+dd, +q}:
      +e = ed
      (jer.and_tt(LawsBase.wire_fits(k), LawsBase.wire_fits(dd), fk, Wire.wire_nat_decoded_fits(s1, dd, q, e)), jer.then(z => Wr.put_nat(0n, Wr.put_nat(k, z)), r0, s1, Wr.put_nat(dd, q), pre, Wire.wire_nat_exact(s1, dd, q, e)))
    case Wr.Bad{}:
      Unit{}

def jer.live(-r0: String, +s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, pre: {r0 == Wr.put_nat(0n, s) : String}) -> jer.JobRP(r0, FJb.get_job.k(d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      jer.live_d(k, r0, s1, Wr.get_nat(s1), {==}, Wire.wire_nat_decoded_fits(s, k, s1, e), jer.then(z => Wr.put_nat(0n, z), r0, s, Wr.put_nat(k, s1), pre, Wire.wire_nat_exact(s, k, s1, e)))
    case Wr.Bad{}:
      Unit{}

def jer.ended_x(+k: Nat, +dd: Nat, -r0: String, -s2: String, d: Wr.Dec<Jb.End>, rp: jer.EndRP(s2, d), fkd: {Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(dd)) == True{} : Bool}, pre: {r0 == Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(dd, s2))) : String}) -> jer.JobRP(r0, FJb.get_job.e(k, dd, d)):
  match d:
    case Wr.Got{+x, +q}:
      (fkd, jer.then(z => Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(dd, z))), r0, s2, Job.job_spell_end(x, q), pre, rp))
    case Wr.Bad{}:
      Unit{}

def jer.ended_d(+k: Nat, -r0: String, +s1: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, pre: {r0 == Wr.put_nat(1n, Wr.put_nat(k, s1)) : String}) -> jer.JobRP(r0, FJb.get_job.ed(k, d)):
  match d:
    case Wr.Got{+dd, +s2}:
      +e = ed
      jer.ended_x(k, dd, r0, s2, FJb.get_end(s2), jer.end(s2), jer.and_tt(LawsBase.wire_fits(k), LawsBase.wire_fits(dd), fk, Wire.wire_nat_decoded_fits(s1, dd, s2, e)), jer.then(z => Wr.put_nat(1n, Wr.put_nat(k, z)), r0, s1, Wr.put_nat(dd, s2), pre, Wire.wire_nat_exact(s1, dd, s2, e)))
    case Wr.Bad{}:
      Unit{}

def jer.ended(-r0: String, +s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, pre: {r0 == Wr.put_nat(1n, s) : String}) -> jer.JobRP(r0, FJb.get_job.ek(d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      jer.ended_d(k, r0, s1, Wr.get_nat(s1), {==}, Wire.wire_nat_decoded_fits(s, k, s1, e), jer.then(z => Wr.put_nat(1n, z), r0, s, Wr.put_nat(k, s1), pre, Wire.wire_nat_exact(s, k, s1, e)))
    case Wr.Bad{}:
      Unit{}

def jer.job_tag(-r0: String, t: Nat, +s: String, pre: {r0 == Wr.put_nat(t, s) : String}) -> jer.JobRP(r0, FJb.get_job.tag(t, s)):
  match t:
    case 0n:
      jer.live(r0, s, Wr.get_nat(s), {==}, pre)
    case 1n+p:
      match p:
        case 0n:
          jer.ended(r0, s, Wr.get_nat(s), {==}, pre)
        case 1n+q:
          Unit{}

def jer.job_go(+r: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> jer.JobRP(r, FJb.get_job.go(d)):
  match d:
    case Wr.Got{+t, +s}:
      +e = ed
      jer.job_tag(r, t, s, Wire.wire_nat_exact(r, t, s, e))
    case Wr.Bad{}:
      Unit{}

def jer.job(+r: String) -> jer.JobRP(r, FJb.get_job(r)):
  jer.job_go(r, Wr.get_nat(r), {==})

def jer.EvRP(r: String, d: Wr.Dec<Jb.JEv>) -> Type:
  match d:
    case Wr.Got{e, q}:
      {Job.wire_ev_fits(e) == True{} : Bool} & {r == Job.job_spell_ev(e, q) : String}
    case Wr.Bad{}:
      Unit

def jer.ev_out(-r0: String, +s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, pre: {r0 == Wr.put_nat(0n, s) : String}) -> jer.EvRP(r0, FJb.get_ev.out(d)):
  match d:
    case Wr.Got{+n, +q}:
      +e = ed
      (Wire.wire_nat_decoded_fits(s, n, q, e), jer.then(z => Wr.put_nat(0n, z), r0, s, Wr.put_nat(n, q), pre, Wire.wire_nat_exact(s, n, q, e)))
    case Wr.Bad{}:
      Unit{}

def jer.ev_quit(-r0: String, -s: String, d: Wr.Dec<Jb.Code>, rp: jer.CodeRP(s, d), pre: {r0 == Wr.put_nat(1n, s) : String}) -> jer.EvRP(r0, FJb.get_ev.quit(d)):
  match d:
    case Wr.Got{+c, +q}:
      ({==}, jer.then(z => Wr.put_nat(1n, z), r0, s, Job.job_spell_code(c, q), pre, rp))
    case Wr.Bad{}:
      Unit{}

def jer.ev_tag(-r0: String, t: Nat, +s: String, pre: {r0 == Wr.put_nat(t, s) : String}) -> jer.EvRP(r0, FJb.get_ev.tag(t, s)):
  match t:
    case 0n:
      jer.ev_out(r0, s, Wr.get_nat(s), {==}, pre)
    case 1n+a:
      match a:
        case 0n:
          jer.ev_quit(r0, s, FJb.get_code(s), jer.code(s), pre)
        case 1n+b:
          match b:
            case 0n:
              ({==}, pre)
            case 1n+c:
              match c:
                case 0n:
                  ({==}, pre)
                case 1n+x:
                  Unit{}

def jer.ev_go(+r: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> jer.EvRP(r, FJb.get_ev.go(d)):
  match d:
    case Wr.Got{+t, +s}:
      +e = ed
      jer.ev_tag(r, t, s, Wire.wire_nat_exact(r, t, s, e))
    case Wr.Bad{}:
      Unit{}

def jer.ev(+r: String) -> jer.EvRP(r, FJb.get_ev(r)):
  jer.ev_go(r, Wr.get_nat(r), {==})

# a cap: 0, or 1 then the number
def jer.CapRP(r: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, q}:
      {LawsBase.wire_mfits(m) == True{} : Bool} & {r == Job.job_spell_cap(m, q) : String}
    case Wr.Bad{}:
      Unit

def jer.cap_some(-r0: String, +s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, pre: {r0 == Wr.put_nat(1n, s) : String}) -> jer.CapRP(r0, FJb.get_cap.some(d)):
  match d:
    case Wr.Got{+x, +q}:
      +e = ed
      (Wire.wire_nat_decoded_fits(s, x, q, e), jer.then(z => Wr.put_nat(1n, z), r0, s, Wr.put_nat(x, q), pre, Wire.wire_nat_exact(s, x, q, e)))
    case Wr.Bad{}:
      Unit{}

def jer.cap_tag(-r0: String, t: Nat, +s: String, pre: {r0 == Wr.put_nat(t, s) : String}) -> jer.CapRP(r0, FJb.get_cap.tag(t, s)):
  match t:
    case 0n:
      ({==}, pre)
    case 1n+p:
      match p:
        case 0n:
          jer.cap_some(r0, s, Wr.get_nat(s), {==}, pre)
        case 1n+q:
          Unit{}

def jer.cap_go(+r: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> jer.CapRP(r, FJb.get_cap.go(d)):
  match d:
    case Wr.Got{+t, +s}:
      +e = ed
      jer.cap_tag(r, t, s, Wire.wire_nat_exact(r, t, s, e))
    case Wr.Bad{}:
      Unit{}

def jer.cap(+r: String) -> jer.CapRP(r, FJb.get_cap(r)):
  jer.cap_go(r, Wr.get_nat(r), {==})

# The rewind entry
# ----------------

# a commit: 0, or 1 then the number
def jer.CommitRP(r: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, q}:
      {LawsBase.wire_mfits(m) == True{} : Bool} & {r == Job.rw_spell_commit(m, q) : String}
    case Wr.Bad{}:
      Unit

def jer.commit_some(-r0: String, +s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, pre: {r0 == Wr.put_nat(1n, s) : String}) -> jer.CommitRP(r0, FJr.get_commit.some(d)):
  match d:
    case Wr.Got{+x, +q}:
      +e = ed
      (Wire.wire_nat_decoded_fits(s, x, q, e), jer.then(z => Wr.put_nat(1n, z), r0, s, Wr.put_nat(x, q), pre, Wire.wire_nat_exact(s, x, q, e)))
    case Wr.Bad{}:
      Unit{}

def jer.commit_tag(-r0: String, t: Nat, +s: String, pre: {r0 == Wr.put_nat(t, s) : String}) -> jer.CommitRP(r0, FJr.get_commit.tag(t, s)):
  match t:
    case 0n:
      ({==}, pre)
    case 1n:
      jer.commit_some(r0, s, Wr.get_nat(s), {==}, pre)
    case 2n+p:
      Unit{}

def jer.commit_go(+r: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> jer.CommitRP(r, FJr.get_commit.go(d)):
  match d:
    case Wr.Got{+t, +s}:
      +e = ed
      jer.commit_tag(r, t, s, Wire.wire_nat_exact(r, t, s, e))
    case Wr.Bad{}:
      Unit{}

def jer.commit(+r: String) -> jer.CommitRP(r, FJr.get_commit(r)):
  jer.commit_go(r, Wr.get_nat(r), {==})

def jer.SeenRP(r: String, d: Wr.Dec<Jb.Seen>) -> Type:
  match d:
    case Wr.Got{x, q}:
      {Job.rw_seens_fit([x]) == True{} : Bool} & {r == Job.rw_spell_seen(x, q) : String}
    case Wr.Bad{}:
      Unit

def jer.seen_after(+b: Bool, -r0: String, -s: String, d: Wr.Dec<Maybe<&2, Nat>>, rp: jer.CommitRP(s, d), pre: {r0 == Wr.put_bool(b, s) : String}) -> jer.SeenRP(r0, FJr.get_seen.after(b, d)):
  match d:
    case Wr.Got{+a, +q}:
      (fa, ea) = rp
      (jer.and_tt(LawsBase.wire_mfits(a), True{}, fa, {==}), jer.then(z => Wr.put_bool(b, z), r0, s, Job.rw_spell_commit(a, q), pre, ea))
    case Wr.Bad{}:
      Unit{}

def jer.seen_go(+r: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(r) == d : Wr.Dec<Bool>}) -> jer.SeenRP(r, FJr.get_seen.go(d)):
  match d:
    case Wr.Got{+b, +s}:
      +e = ed
      jer.seen_after(b, r, s, FJr.get_commit(s), jer.commit(s), Wire.wire_bool_exact(r, b, s, e))
    case Wr.Bad{}:
      Unit{}

def jer.seen(+r: String) -> jer.SeenRP(r, FJr.get_seen(r)):
  jer.seen_go(r, Wr.get_bool(r), {==})

# n jobs read: as many as the count, each fits, spelled
def jer.SeensRP(r: String, n: Nat, d: Wr.Dec<List<&2, Jb.Seen>>) -> Type:
  match d:
    case Wr.Got{xs, q}:
      {List.length(&2, Jb.Seen, xs) == n : Nat} & ({Job.rw_seens_fit(xs) == True{} : Bool} & {r == Job.rw_spell_seens(xs, q) : String})
    case Wr.Bad{}:
      Unit

def jer.fit_cons(x: Jb.Seen, -xs: List<&2, Jb.Seen>, fx: {Job.rw_seens_fit([x]) == True{} : Bool}, fxs: {Job.rw_seens_fit(xs) == True{} : Bool}) -> {Job.rw_seens_fit(x <> xs) == True{} : Bool}:
  match x:
    case Jb.Seen{r, +a}:
      jer.and_tt(LawsBase.wire_mfits(a), Job.rw_seens_fit(xs), LLogicBool.wr_and_l(LawsBase.wire_mfits(a), True{}, fx), fxs)

def jer.seens_cons(+x: Jb.Seen, -k: Nat, -r0: String, -q: String, d: Wr.Dec<List<&2, Jb.Seen>>, ih: jer.SeensRP(q, 1n+k, d), fx: {Job.rw_seens_fit([x]) == True{} : Bool}, ex: {r0 == Job.rw_spell_seen(x, q) : String}) -> jer.SeensRP(r0, 2n+k, FJr.get_seens.cons(x, d)):
  match d:
    case Wr.Got{+xs, +q2}:
      (el, (fxs, ets)) = ih
      (Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Jb.Seen, xs), 1n+k, el), (jer.fit_cons(x, xs, fx, fxs), jer.then(z => Job.rw_spell_seen(x, z), r0, q, Job.rw_spell_seens(xs, q2), ex, ets)))
    case Wr.Bad{}:
      Unit{}

# m more jobs after the one cur answers
def jer.seens_go(m: Nat, -r0: String, cur: Wr.Dec<Jb.Seen>, rp: jer.SeenRP(r0, cur)) -> jer.SeensRP(r0, 1n+m, FJr.get_seens.go(m, cur)):
  match m:
    case 0n:
      match cur:
        case Wr.Got{+x, +q}:
          (fx, ex) = rp
          ({==}, (fx, ex))
        case Wr.Bad{}:
          Unit{}
    case 1n++k:
      match cur:
        case Wr.Got{+x, +q}:
          (fx, ex) = rp
          jer.seens_cons(x, k, r0, q, FJr.get_seens.go(k, FJr.get_seen(q)), jer.seens_go(k, q, FJr.get_seen(q), jer.seen(q)), fx, ex)
        case Wr.Bad{}:
          Unit{}

# the jobs after their count n
def jer.seens(+n: Nat, +s: String) -> jer.SeensRP(s, n, FJr.get_seens(Wr.Got{n, s})):
  match n:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+m:
      jer.seens_go(m, s, FJr.get_seen(s), jer.seen(s))
