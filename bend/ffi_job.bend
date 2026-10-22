import Base
import ./wire.bend as W
import ./job.bend as M

# ffi_job: one event of a job (bend/job.bend `feed`, with the bytes kept
# plus dropped held to the bound t, and `ends.of`) as an entry of the
# compiled Bend core. The request: t (Rust sends the wire's largest Nat),
# the output cap (Maybe: None is
# the opt-out), the job, the event. The reply: the job after the event,
# then the ends the event reported (a List).
#   J:   Live 0 (kept, dropped) | Ended 1 (kept, dropped, End)
#   End: Exited 0 (Code) | Killed 1          Code: hi, lo (U32 words)
#   JEv: Out 0 (n) | Quit 1 (Code) | Kill 2 | Tick 3

# Encoders
# --------

def put_code(c: M.Code, rest: String) -> String:
  match c:
    case M.Code{hi, lo}:
      W.put_u32(hi, W.put_u32(lo, rest))

def put_end(e: M.End, rest: String) -> String:
  match e:
    case M.Exited{c}:
      W.put_nat(0n, put_code(c, rest))
    case M.Killed{}:
      W.put_nat(1n, rest)

def put_job(j: M.J, rest: String) -> String:
  match j:
    case M.Live{k, d}:
      W.put_nat(0n, W.put_nat(k, W.put_nat(d, rest)))
    case M.Ended{k, d, e}:
      W.put_nat(1n, W.put_nat(k, W.put_nat(d, put_end(e, rest))))

def put_ev(e: M.JEv, rest: String) -> String:
  match e:
    case M.Out{n}:
      W.put_nat(0n, W.put_nat(n, rest))
    case M.Quit{c}:
      W.put_nat(1n, put_code(c, rest))
    case M.Kill{}:
      W.put_nat(2n, rest)
    case M.Tick{}:
      W.put_nat(3n, rest)

def put_cap(c: Maybe<&2, Nat>, rest: String) -> String:
  match c:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_nat(x, rest))

def put_req(t: Nat, cap: Maybe<&2, Nat>, j: M.J, e: M.JEv) -> String:
  W.put_nat(t, put_cap(cap, put_job(j, put_ev(e, ""))))

def put_reply(j: M.J, es: List<&2, M.End>) -> String:
  put_job(j, W.put_list(~M.End, ~put_end, es, ""))

# Decoders
# --------

def get_code.lo(+hi: U32, r: W.Dec<U32>) -> W.Dec<M.Code>:
  match r:
    case W.Got{lo, s}:
      W.Got{M.Code{hi, lo}, s}
    case W.Bad{}:
      W.Bad{}

def get_code.hi(r: W.Dec<U32>) -> W.Dec<M.Code>:
  match r:
    case W.Got{+hi, s}:
      get_code.lo(hi, W.get_u32(s))
    case W.Bad{}:
      W.Bad{}

def get_code(s: String) -> W.Dec<M.Code>:
  get_code.hi(W.get_u32(s))

def get_end.code(r: W.Dec<M.Code>) -> W.Dec<M.End>:
  match r:
    case W.Got{c, s}:
      W.Got{M.Exited{c}, s}
    case W.Bad{}:
      W.Bad{}

def get_end.tag(t: Nat, s: String) -> W.Dec<M.End>:
  match t:
    case 0n:
      get_end.code(get_code(s))
    case 1n+p:
      match p:
        case 0n:
          W.Got{M.Killed{}, s}
        case 1n+q:
          W.Bad{}

def get_end.go(r: W.Dec<Nat>) -> W.Dec<M.End>:
  match r:
    case W.Got{t, s}:
      get_end.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_end(s: String) -> W.Dec<M.End>:
  get_end.go(W.get_nat(s))

def get_job.d(+k: Nat, r: W.Dec<Nat>) -> W.Dec<M.J>:
  match r:
    case W.Got{d, s}:
      W.Got{M.Live{k, d}, s}
    case W.Bad{}:
      W.Bad{}

def get_job.k(r: W.Dec<Nat>) -> W.Dec<M.J>:
  match r:
    case W.Got{+k, s}:
      get_job.d(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_job.e(+k: Nat, +d: Nat, r: W.Dec<M.End>) -> W.Dec<M.J>:
  match r:
    case W.Got{e, s}:
      W.Got{M.Ended{k, d, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_job.ed(+k: Nat, r: W.Dec<Nat>) -> W.Dec<M.J>:
  match r:
    case W.Got{+d, s}:
      get_job.e(k, d, get_end(s))
    case W.Bad{}:
      W.Bad{}

def get_job.ek(r: W.Dec<Nat>) -> W.Dec<M.J>:
  match r:
    case W.Got{+k, s}:
      get_job.ed(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_job.tag(t: Nat, s: String) -> W.Dec<M.J>:
  match t:
    case 0n:
      get_job.k(W.get_nat(s))
    case 1n+p:
      match p:
        case 0n:
          get_job.ek(W.get_nat(s))
        case 1n+q:
          W.Bad{}

def get_job.go(r: W.Dec<Nat>) -> W.Dec<M.J>:
  match r:
    case W.Got{t, s}:
      get_job.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_job(s: String) -> W.Dec<M.J>:
  get_job.go(W.get_nat(s))

def get_ev.out(r: W.Dec<Nat>) -> W.Dec<M.JEv>:
  match r:
    case W.Got{n, s}:
      W.Got{M.Out{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.quit(r: W.Dec<M.Code>) -> W.Dec<M.JEv>:
  match r:
    case W.Got{c, s}:
      W.Got{M.Quit{c}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(t: Nat, s: String) -> W.Dec<M.JEv>:
  match t:
    case 0n:
      get_ev.out(W.get_nat(s))
    case 1n+a:
      match a:
        case 0n:
          get_ev.quit(get_code(s))
        case 1n+b:
          match b:
            case 0n:
              W.Got{M.Kill{}, s}
            case 1n+c:
              match c:
                case 0n:
                  W.Got{M.Tick{}, s}
                case 1n+d:
                  W.Bad{}

def get_ev.go(r: W.Dec<Nat>) -> W.Dec<M.JEv>:
  match r:
    case W.Got{t, s}:
      get_ev.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_ev(s: String) -> W.Dec<M.JEv>:
  get_ev.go(W.get_nat(s))

def get_cap.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_cap.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n+p:
      match p:
        case 0n:
          get_cap.some(W.get_nat(s))
        case 1n+q:
          W.Bad{}

def get_cap.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_cap.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_cap(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_cap.go(W.get_nat(s))

# The entry
# ---------

def run.end(left: Bool, +t: Nat, +cap: Maybe<&2, Nat>, +j: M.J, +e: M.JEv) -> String:
  match left:
    case True{}:
      put_reply(M.feed(t, cap, j, e), M.ends.of(j, e))
    case False{}:
      W.err("job: input left over")

def run.ev(+t: Nat, +cap: Maybe<&2, Nat>, +j: M.J, r: W.Dec<M.JEv>) -> String:
  match r:
    case W.Got{+e, s}:
      run.end(W.end(s), t, cap, j, e)
    case W.Bad{}:
      W.err("job: bad event")

def run.job(+t: Nat, +cap: Maybe<&2, Nat>, r: W.Dec<M.J>) -> String:
  match r:
    case W.Got{+j, s}:
      run.ev(t, cap, j, get_ev(s))
    case W.Bad{}:
      W.err("job: bad job")

def run.cap(+t: Nat, r: W.Dec<Maybe<&2, Nat>>) -> String:
  match r:
    case W.Got{+cap, s}:
      run.job(t, cap, get_job(s))
    case W.Bad{}:
      W.err("job: bad cap")

def run.t(r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{+t, s}:
      run.cap(t, get_cap(s))
    case W.Bad{}:
      W.err("job: bad bound")

def ffi(input: String) -> String:
  run.t(W.get_nat(input))
