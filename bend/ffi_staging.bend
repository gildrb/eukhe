# ffi_staging: the entry of the compiled Bend core for the staging rule
# (the real rule of bend/staging.bend and bend/listing.bend;
# crates/eukhe-core/src/durable/staging.rs, discovery.rs). The Rust gathers the facts and performs the
# removals, renames and reads; this entry decides. The wire format is
# bend/wire.bend; malformed input, or input left over, answers the error
# form. A request is a tag and its body:
#
#   0 publish  Bool taken                    -> verdict: 0 moved, 1 taken
#   1 meet     List<Seen>                    -> List<met>: 0 keep, 1 descend,
#                                               2 leftover, 3 orphan lock
#   2 judge    cand lock Time Time List<Time> -> plan: 0 keep, 1 remove dir,
#                                               2 remove dir and lock,
#                                               3 remove lock file
#   3 scan     List<Seen>                    -> List<Pick>
#   4 rows     List<Obs>                     -> List<Row>
#
#   Seen  name kind          name: 0 String (UTF-8) | 1 (not UTF-8)
#                            kind: 0 Bool main (a directory) | 1 (a file)
#                                  | 2 (a symlink or anything else)
#   Time  Nat secs, Nat nanos (after the epoch)
#   cand  0 a staging directory or a tombstone | 1 an orphan lock file
#   lock  0 held | 1 free (the sweep holds it) | 2 no lock file
#   Obs   Seen, cwd (0 none | 1 String), List<Time> (the files' times)
#   Pick  0 skip | 1 String (a storage's id) | 2 String (a legacy file's id)
#   Row   Nat at (the entry's place), Pick, Time (the newest)

import Base
import ./wire.bend as W
import ./staging.bend as Sg
import ./listing.bend as Ls

# Requests
# --------

type Req is Data:
  Publish{taken: Bool}
  Meet{es: List<&2, Sg.Seen>}
  Judge{c: Sg.Cand, l: Sg.Lock, now: Sg.Time, own: Sg.Time, inner: List<&2, Sg.Time>}
  Scan{es: List<&2, Sg.Seen>}
  Rows{os: List<&2, Ls.Obs>}

# a name
def get_name.utf(r: W.Dec<String>) -> W.Dec<Sg.Name>:
  match r:
    case W.Got{x, s}:
      W.Got{Sg.Utf{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_name.tag(t: Nat, s: String) -> W.Dec<Sg.Name>:
  match t:
    case 0n:
      get_name.utf(W.get_str(s))
    case 1n+p:
      match p:
        case 0n:
          W.Got{Sg.Raw{}, s}
        case 1n+q:
          W.Bad{}

def get_name.go(r: W.Dec<Nat>) -> W.Dec<Sg.Name>:
  match r:
    case W.Got{t, s}:
      get_name.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_name(s: String) -> W.Dec<Sg.Name>:
  get_name.go(W.get_nat(s))

# an entry's type
def get_form.dir(r: W.Dec<Bool>) -> W.Dec<Sg.Form>:
  match r:
    case W.Got{m, s}:
      W.Got{Sg.KDir{m}, s}
    case W.Bad{}:
      W.Bad{}

def get_form.tag(t: Nat, s: String) -> W.Dec<Sg.Form>:
  match t:
    case 0n:
      get_form.dir(W.get_bool(s))
    case 1n+p:
      match p:
        case 0n:
          W.Got{Sg.KFile{}, s}
        case 1n+q:
          match q:
            case 0n:
              W.Got{Sg.KOther{}, s}
            case 1n+u:
              W.Bad{}

def get_form.go(r: W.Dec<Nat>) -> W.Dec<Sg.Form>:
  match r:
    case W.Got{t, s}:
      get_form.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_form(s: String) -> W.Dec<Sg.Form>:
  get_form.go(W.get_nat(s))

# an entry of a listing
def get_seen.form(n: Sg.Name, r: W.Dec<Sg.Form>) -> W.Dec<Sg.Seen>:
  match r:
    case W.Got{k, s}:
      W.Got{Sg.Seen{n, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_seen.go(r: W.Dec<Sg.Name>) -> W.Dec<Sg.Seen>:
  match r:
    case W.Got{n, s}:
      get_seen.form(n, get_form(s))
    case W.Bad{}:
      W.Bad{}

def get_seen(s: String) -> W.Dec<Sg.Seen>:
  get_seen.go(get_name(s))

# a time
def get_time.nanos(secs: Nat, r: W.Dec<Nat>) -> W.Dec<Sg.Time>:
  match r:
    case W.Got{n, s}:
      W.Got{Sg.Time{secs, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_time.go(r: W.Dec<Nat>) -> W.Dec<Sg.Time>:
  match r:
    case W.Got{secs, s}:
      get_time.nanos(secs, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_time(s: String) -> W.Dec<Sg.Time>:
  get_time.go(W.get_nat(s))

# a cwd: none, or its text
def get_cwd.some(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_cwd.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n+p:
      match p:
        case 0n:
          get_cwd.some(W.get_str(s))
        case 1n+q:
          W.Bad{}

def get_cwd.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      get_cwd.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_cwd(s: String) -> W.Dec<Maybe<&2, String>>:
  get_cwd.go(W.get_nat(s))

# an entry of the sessions directory with what the Rust read of it
def get_obs.times(e: Sg.Seen, c: Maybe<&2, String>, r: W.Dec<List<&2, Sg.Time>>) -> W.Dec<Ls.Obs>:
  match r:
    case W.Got{ts, s}:
      W.Got{Ls.Obs{e, c, ts}, s}
    case W.Bad{}:
      W.Bad{}

def get_obs.cwd(e: Sg.Seen, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Ls.Obs>:
  match r:
    case W.Got{c, s}:
      get_obs.times(e, c, W.get_list(~Sg.Time, ~get_time, s))
    case W.Bad{}:
      W.Bad{}

def get_obs.go(r: W.Dec<Sg.Seen>) -> W.Dec<Ls.Obs>:
  match r:
    case W.Got{e, s}:
      get_obs.cwd(e, get_cwd(s))
    case W.Bad{}:
      W.Bad{}

def get_obs(s: String) -> W.Dec<Ls.Obs>:
  get_obs.go(get_seen(s))

# what is judged, and its lock probe
def get_cand.tag(t: Nat, s: String) -> W.Dec<Sg.Cand>:
  match t:
    case 0n:
      W.Got{Sg.CDir{}, s}
    case 1n+p:
      match p:
        case 0n:
          W.Got{Sg.CLock{}, s}
        case 1n+q:
          W.Bad{}

def get_cand.go(r: W.Dec<Nat>) -> W.Dec<Sg.Cand>:
  match r:
    case W.Got{t, s}:
      get_cand.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_lock.tag(t: Nat, s: String) -> W.Dec<Sg.Lock>:
  match t:
    case 0n:
      W.Got{Sg.LHeld{}, s}
    case 1n+p:
      match p:
        case 0n:
          W.Got{Sg.LFree{}, s}
        case 1n+q:
          match q:
            case 0n:
              W.Got{Sg.LAbsent{}, s}
            case 1n+u:
              W.Bad{}

def get_lock.go(r: W.Dec<Nat>) -> W.Dec<Sg.Lock>:
  match r:
    case W.Got{t, s}:
      get_lock.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the bodies of the requests
def get_publish(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{b, s}:
      W.Got{Publish{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_meet(r: W.Dec<List<&2, Sg.Seen>>) -> W.Dec<Req>:
  match r:
    case W.Got{es, s}:
      W.Got{Meet{es}, s}
    case W.Bad{}:
      W.Bad{}

def get_judge.inner(c: Sg.Cand, l: Sg.Lock, now: Sg.Time, own: Sg.Time, r: W.Dec<List<&2, Sg.Time>>) -> W.Dec<Req>:
  match r:
    case W.Got{ts, s}:
      W.Got{Judge{c, l, now, own, ts}, s}
    case W.Bad{}:
      W.Bad{}

def get_judge.own(c: Sg.Cand, l: Sg.Lock, now: Sg.Time, r: W.Dec<Sg.Time>) -> W.Dec<Req>:
  match r:
    case W.Got{own, s}:
      get_judge.inner(c, l, now, own, W.get_list(~Sg.Time, ~get_time, s))
    case W.Bad{}:
      W.Bad{}

def get_judge.now(c: Sg.Cand, l: Sg.Lock, r: W.Dec<Sg.Time>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_judge.own(c, l, now, get_time(s))
    case W.Bad{}:
      W.Bad{}

def get_judge.lock(c: Sg.Cand, r: W.Dec<Sg.Lock>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      get_judge.now(c, l, get_time(s))
    case W.Bad{}:
      W.Bad{}

def get_judge(r: W.Dec<Sg.Cand>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_judge.lock(c, get_lock.go(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_scan(r: W.Dec<List<&2, Sg.Seen>>) -> W.Dec<Req>:
  match r:
    case W.Got{es, s}:
      W.Got{Scan{es}, s}
    case W.Bad{}:
      W.Bad{}

def get_rows(r: W.Dec<List<&2, Ls.Obs>>) -> W.Dec<Req>:
  match r:
    case W.Got{os, s}:
      W.Got{Rows{os}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_publish(W.get_bool(s))
    case 1n+a:
      match a:
        case 0n:
          get_meet(W.get_list(~Sg.Seen, ~get_seen, s))
        case 1n+b:
          match b:
            case 0n:
              get_judge(get_cand.go(W.get_nat(s)))
            case 1n+c:
              match c:
                case 0n:
                  get_scan(W.get_list(~Sg.Seen, ~get_seen, s))
                case 1n+d:
                  match d:
                    case 0n:
                      get_rows(W.get_list(~Ls.Obs, ~get_obs, s))
                    case 1n+e:
                      W.Bad{}

def get_req.go(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Replies
# -------

def put_verdict(v: Sg.Verdict, rest: String) -> String:
  match v:
    case Sg.Moved{}:
      W.put_nat(0n, rest)
    case Sg.Taken{}:
      W.put_nat(1n, rest)

def put_met(m: Sg.Met, rest: String) -> String:
  match m:
    case Sg.MKeep{}:
      W.put_nat(0n, rest)
    case Sg.MDescend{}:
      W.put_nat(1n, rest)
    case Sg.MLeftover{}:
      W.put_nat(2n, rest)
    case Sg.MOrphan{}:
      W.put_nat(3n, rest)

def put_plan(p: Sg.Plan, rest: String) -> String:
  match p:
    case Sg.PKeep{}:
      W.put_nat(0n, rest)
    case Sg.PRmDir{}:
      W.put_nat(1n, rest)
    case Sg.PRmDirLock{}:
      W.put_nat(2n, rest)
    case Sg.PRmFile{}:
      W.put_nat(3n, rest)

def put_pick(p: Ls.Pick, rest: String) -> String:
  match p:
    case Ls.PSkip{}:
      W.put_nat(0n, rest)
    case Ls.PStore{s}:
      W.put_nat(1n, W.put_str(s, rest))
    case Ls.PLegacy{s}:
      W.put_nat(2n, W.put_str(s, rest))

def put_time(t: Sg.Time, rest: String) -> String:
  match t:
    case Sg.Time{s, n}:
      W.put_nat(s, W.put_nat(n, rest))

def put_row(r: Ls.Row, rest: String) -> String:
  match r:
    case Ls.Row{i, p, t}:
      W.put_nat(i, put_pick(p, put_time(t, rest)))

# the reply to a request: the rule's decision
def reply(r: Req) -> String:
  match r:
    case Publish{t}:
      put_verdict(Sg.settle(t), "")
    case Meet{es}:
      W.put_list(~Sg.Met, ~put_met, Sg.meet(es), "")
    case Judge{c, l, now, own, inner}:
      put_plan(Sg.judge(c, l, now, own, inner), "")
    case Scan{es}:
      W.put_list(~Ls.Pick, ~put_pick, Ls.scan(es), "")
    case Rows{os}:
      W.put_list(~Ls.Row, ~put_row, Ls.rows(os), "")

# the reply to a request read whole (done: nothing is left)
def answer.end(done: Bool, r: Req) -> String:
  match done:
    case True{}:
      reply(r)
    case False{}:
      W.err("staging: input left over")

def answer(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{r, s}:
      answer.end(W.end(s), r)
    case W.Bad{}:
      W.err("staging: malformed request")

def ffi(input: String) -> String:
  answer(get_req(input))
