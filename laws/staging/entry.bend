# eukhe: the laws of area staging, section entry: the reply of the
# compiled core's staging entry (bend/ffi_staging.bend) to every input
# string (laws/staging.bend holds the rule's laws and the entry's laws on
# the requests Rust spells; that file is near 1,000 lines)

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../bend/ffi_staging.bend as FSg
import ../../bend/wire.bend as Wr
import ../staging.bend as Staging

# LAWS (R8 of laws/staging.bend): the entry answers every request Rust
# spells with the spelled decision of the real rule; any other input gets
# the error form. The reader below is the wire grammar of the entry (the
# header of bend/ffi_staging.bend) written with the wire primitives alone
# (Wr.get_nat, Wr.get_str, Wr.get_bool, Wr.get_list, Wr.end, Wr.err: pinned
# by laws/wire.bend); it never calls the entry's own decoders. The reply is
# Staging.sp_w_reply, the spelled decision of the rule, whose every part
# is pinned by a law of laws/staging.bend or laws/listing.bend to its spec
# on every input: the publish's verdict (publish_settles: two verdicts),
# the sweep's class of each entry (meet_exact), the judged plan
# (judge_exact), the listing's scan (scan_exact) and its rows
# (rows_each_once and rows_are_entries: the rows are exactly the spec's
# rows of the listed entries; rows_newest_first and rows_order_strict:
# they are in the one order a strict order allows).

# Reader: the requests the entry accepts
# --------------------------------------

def sr_name.utf(r: Wr.Dec<String>) -> Wr.Dec<Sg.Name>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Sg.Utf{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# a name: 0 then its text (UTF-8) | 1 (not UTF-8)
def sr_name(r: Wr.Dec<Nat>) -> Wr.Dec<Sg.Name>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sr_name.utf(Wr.get_str(s))
        case 1n:
          Wr.Got{Sg.Raw{}, s}
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_form.dir(r: Wr.Dec<Bool>) -> Wr.Dec<Sg.Form>:
  match r:
    case Wr.Got{m, s}:
      Wr.Got{Sg.KDir{m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# an entry's type: 0 a directory, then whether it holds main.jsonl | 1 a
# file | 2 anything else
def sr_form(r: Wr.Dec<Nat>) -> Wr.Dec<Sg.Form>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sr_form.dir(Wr.get_bool(s))
        case 1n:
          Wr.Got{Sg.KFile{}, s}
        case 2n:
          Wr.Got{Sg.KOther{}, s}
        case 3n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_seen.form(n: Sg.Name, r: Wr.Dec<Sg.Form>) -> Wr.Dec<Sg.Seen>:
  match r:
    case Wr.Got{k, s}:
      Wr.Got{Sg.Seen{n, k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_seen.name(r: Wr.Dec<Sg.Name>) -> Wr.Dec<Sg.Seen>:
  match r:
    case Wr.Got{n, s}:
      sr_seen.form(n, sr_form(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# an entry of a listing: its name, then its type
def sr_seen(s: String) -> Wr.Dec<Sg.Seen>:
  sr_seen.name(sr_name(Wr.get_nat(s)))

def sr_time.nanos(secs: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Sg.Time>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Sg.Time{secs, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_time.secs(r: Wr.Dec<Nat>) -> Wr.Dec<Sg.Time>:
  match r:
    case Wr.Got{secs, s}:
      sr_time.nanos(secs, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a time: its seconds, then its nanoseconds
def sr_time(s: String) -> Wr.Dec<Sg.Time>:
  sr_time.secs(Wr.get_nat(s))

def sr_cwd.some(r: Wr.Dec<String>) -> Wr.Dec<Maybe<&2, String>>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Some{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# a cwd: 0 none | 1 then its text
def sr_cwd(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, String>>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{None{}, s}
        case 1n:
          sr_cwd.some(Wr.get_str(s))
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_obs.times(e: Sg.Seen, c: Maybe<&2, String>, r: Wr.Dec<List<&2, Sg.Time>>) -> Wr.Dec<Ls.Obs>:
  match r:
    case Wr.Got{ts, s}:
      Wr.Got{Ls.Obs{e, c, ts}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_obs.cwd(e: Sg.Seen, r: Wr.Dec<Maybe<&2, String>>) -> Wr.Dec<Ls.Obs>:
  match r:
    case Wr.Got{c, s}:
      sr_obs.times(e, c, Wr.get_list(~Sg.Time, ~sr_time, s))
    case Wr.Bad{}:
      Wr.Bad{}

def sr_obs.seen(r: Wr.Dec<Sg.Seen>) -> Wr.Dec<Ls.Obs>:
  match r:
    case Wr.Got{e, s}:
      sr_obs.cwd(e, sr_cwd(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# an entry of the sessions directory: the entry, its cwd, its files' times
def sr_obs(s: String) -> Wr.Dec<Ls.Obs>:
  sr_obs.seen(sr_seen(s))

# what is judged: 0 a staging directory or a tombstone | 1 an orphan lock
# file
def sr_cand(r: Wr.Dec<Nat>) -> Wr.Dec<Sg.Cand>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Sg.CDir{}, s}
        case 1n:
          Wr.Got{Sg.CLock{}, s}
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# a lock probe: 0 held | 1 free | 2 no lock file
def sr_lock(r: Wr.Dec<Nat>) -> Wr.Dec<Sg.Lock>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Sg.LHeld{}, s}
        case 1n:
          Wr.Got{Sg.LFree{}, s}
        case 2n:
          Wr.Got{Sg.LAbsent{}, s}
        case 3n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_judge.inner(c: Sg.Cand, l: Sg.Lock, now: Sg.Time, own: Sg.Time, r: Wr.Dec<List<&2, Sg.Time>>) -> Wr.Dec<FSg.Req>:
  match r:
    case Wr.Got{ts, s}:
      Wr.Got{FSg.Judge{c, l, now, own, ts}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_judge.own(c: Sg.Cand, l: Sg.Lock, now: Sg.Time, r: Wr.Dec<Sg.Time>) -> Wr.Dec<FSg.Req>:
  match r:
    case Wr.Got{own, s}:
      sr_judge.inner(c, l, now, own, Wr.get_list(~Sg.Time, ~sr_time, s))
    case Wr.Bad{}:
      Wr.Bad{}

def sr_judge.now(c: Sg.Cand, l: Sg.Lock, r: Wr.Dec<Sg.Time>) -> Wr.Dec<FSg.Req>:
  match r:
    case Wr.Got{now, s}:
      sr_judge.own(c, l, now, sr_time(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sr_judge.lock(c: Sg.Cand, r: Wr.Dec<Sg.Lock>) -> Wr.Dec<FSg.Req>:
  match r:
    case Wr.Got{l, s}:
      sr_judge.now(c, l, sr_time(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a judge request's body: the candidate, its lock probe, now, its own
# time, the times of its direct entries
def sr_judge(r: Wr.Dec<Sg.Cand>) -> Wr.Dec<FSg.Req>:
  match r:
    case Wr.Got{c, s}:
      sr_judge.lock(c, sr_lock(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def sr_publish(r: Wr.Dec<Bool>) -> Wr.Dec<FSg.Req>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{FSg.Publish{b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_meet(r: Wr.Dec<List<&2, Sg.Seen>>) -> Wr.Dec<FSg.Req>:
  match r:
    case Wr.Got{es, s}:
      Wr.Got{FSg.Meet{es}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_scan(r: Wr.Dec<List<&2, Sg.Seen>>) -> Wr.Dec<FSg.Req>:
  match r:
    case Wr.Got{es, s}:
      Wr.Got{FSg.Scan{es}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sr_rows(r: Wr.Dec<List<&2, Ls.Obs>>) -> Wr.Dec<FSg.Req>:
  match r:
    case Wr.Got{os, s}:
      Wr.Got{FSg.Rows{os}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# a request: its tag, then its body (0 publish: a Bool; 1 meet: a list of
# entries; 2 judge; 3 scan: a list of entries; 4 rows: a list of entries
# of the sessions directory)
def sr_req(r: Wr.Dec<Nat>) -> Wr.Dec<FSg.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sr_publish(Wr.get_bool(s))
        case 1n:
          sr_meet(Wr.get_list(~Sg.Seen, ~sr_seen, s))
        case 2n:
          sr_judge(sr_cand(Wr.get_nat(s)))
        case 3n:
          sr_scan(Wr.get_list(~Sg.Seen, ~sr_seen, s))
        case 4n:
          sr_rows(Wr.get_list(~Ls.Obs, ~sr_obs, s))
        case 5n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# The reply to every input
# ------------------------

def sr_entry.end(done: Bool, r: FSg.Req) -> String:
  match done:
    case True{}:
      Staging.sp_w_reply(r)
    case False{}:
      Wr.err("staging: input left over")

def sr_entry.go(d: Wr.Dec<FSg.Req>) -> String:
  match d:
    case Wr.Got{r, s}:
      sr_entry.end(Wr.end(s), r)
    case Wr.Bad{}:
      Wr.err("staging: malformed request")

# the reply to the input s: a request read whole gets the spelled decision
# of the rule; a request with input left over, the error form "staging:
# input left over"; anything else, the error form "staging: malformed
# request"
def sr_entry(s: String) -> String:
  sr_entry.go(sr_req(Wr.get_nat(s)))

# LAW staging_entry_spec (R8): the entry's reply to every input string is
# the spec's: a request read whole by the wire grammar gets the spelled
# decision of the rule; input left over after a request and every other
# input get the exact error form of their fault
# EXCLUDES: a reply that the laws do not determine for some input (an
#   error form with another text, or the text of the other fault; a value
#   answered to malformed input; a request read by a reader the laws do not
#   fix)
law staging_entry_spec:
  for +s: String
  {FSg.ffi(s) == sr_entry(s) : String}
