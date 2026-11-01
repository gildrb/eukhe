# eukhe: the proof of LAW job_notice_entry_exact
#
# PROOF: the decoder answers Got{q, rest} only after the Nat decoder
# answered Got{n, r} (then the input is put_nat(n, r): wire_nat_exact), n
# is one of the four tags (any other is refused), and the Bool decoder
# answered Got{t, rest} on r (then r is put_bool(t, rest):
# wire_bool_exact). The entry answers a value only for a request read whole
# with nothing left: that input is the spelled request.

import Base
import ../../bend/job_notice.bend as JN
import ../../laws/job_notice.bend as JobNotice
import ../../bend/ffi_job_notice.bend as FJn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ./base.bend as LA

# the decoder's answer is the spelling of what it read, before the rest
def jex.RP(s: String, d: Wr.Dec<FJn.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      match q:
        case FJn.Req{by, t}:
          {s == JobNotice.sp_w_req(by, t, r) : String}
    case Wr.Bad{}:
      Unit

# the Bool after the tag of by
def jex.taken(+by: JN.Stopper, -s0: String, +s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}, pre: {s0 == Wr.put_nat(JobNotice.sp_tag(by), s) : String}) -> jex.RP(s0, FJn.get_req.taken(by, d)):
  match d:
    case Wr.Got{+t, +r}:
      +e = ed
      Equal.trans(String, s0, Wr.put_nat(JobNotice.sp_tag(by), s), Wr.put_nat(JobNotice.sp_tag(by), Wr.put_bool(t, r)), pre, Equal.cong(String, String, x => Wr.put_nat(JobNotice.sp_tag(by), x), s, Wr.put_bool(t, r), Wire.wire_bool_exact(s, t, r, e)))
    case Wr.Bad{}:
      Unit{}

# the stopper of tag n
def jex.by(-s0: String, n: Nat, +s: String, pre: {s0 == Wr.put_nat(n, s) : String}) -> jex.RP(s0, FJn.get_req.by(n, s)):
  match n:
    case 0n:
      jex.taken(JN.NoStop{}, s0, s, Wr.get_bool(s), {==}, pre)
    case 1n+a:
      match a:
        case 0n:
          jex.taken(JN.AgentStop{}, s0, s, Wr.get_bool(s), {==}, pre)
        case 1n+b:
          match b:
            case 0n:
              jex.taken(JN.UserStop{}, s0, s, Wr.get_bool(s), {==}, pre)
            case 1n+c:
              match c:
                case 0n:
                  jex.taken(JN.InterruptStop{}, s0, s, Wr.get_bool(s), {==}, pre)
                case 1n+k:
                  Unit{}

def jex.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> jex.RP(s, FJn.get_req.tag(d)):
  match d:
    case Wr.Got{+n, +r}:
      +e = ed
      jex.by(s, n, r, Wire.wire_nat_exact(s, n, r, e))
    case Wr.Bad{}:
      Unit{}

def jex.Goal(s: String) -> Type:
  Sigma<&1, &1, JN.Stopper, by => Sigma<&1, &1, Bool, t => {s == JobNotice.sp_w_req(by, t, "") : String}>>

# a value answered: a request read whole, nothing left
def jex.top(-s: String, d: Wr.Dec<FJn.Req>, rp: jex.RP(s, d), ok: {LawsBase.wire_opens_err(FJn.ffi.got(d)) == False{} : Bool}) -> jex.Goal(s):
  match d:
    case Wr.Got{q, rest}:
      match q:
        case FJn.Req{by, t}:
          match rest:
            case SNil{}:
              (by, (t, rp))
            case SCon{x, y}:
              LA.jnb.absurd_tf(jex.Goal(s), ok)
    case Wr.Bad{}:
      LA.jnb.absurd_tf(jex.Goal(s), ok)

def JobNotice.job_notice_entry_exact(s, ok):
  jex.top(s, FJn.get_req(s), jex.tag(s, Wr.get_nat(s), {==}), ok)
