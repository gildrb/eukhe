# eukhe: the proof of LAW staging_entry_spec
#
# Each decoder of bend/ffi_staging.bend answers what the laws' reader of
# the same part answers, on every input (sq.*: the leaf decoders by
# cases; a part made of parts by rewriting each part of the reader's side
# to the decoder's, then by cases; a list item by item, sq.*_go). So the
# entry reads every input as the reader does; a request read whole gets
# the entry's reply, which is Staging.sp_w_reply (staging_entry_answers'
# se.reply), and every other input the same error form on both sides.

import Base
import ../../bend/ffi_staging.bend as FSg
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../bend/wire.bend as Wr
import ../../laws/staging/entry.bend as StagingEntry
import ./staging_entry_answers.bend as PA

# Names, forms, entries
# ---------------------

def sq.name_utf(r: Wr.Dec<String>) -> {FSg.get_name.utf(r) == StagingEntry.sr_name.utf(r) : Wr.Dec<Sg.Name>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.name(r: Wr.Dec<Nat>) -> {FSg.get_name.go(r) == StagingEntry.sr_name(r) : Wr.Dec<Sg.Name>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sq.name_utf(Wr.get_str(s))
        case 1n+p:
          match p:
            case 0n:
              {==}
            case 1n+q:
              {==}
    case Wr.Bad{}:
      {==}

def sq.form_dir(r: Wr.Dec<Bool>) -> {FSg.get_form.dir(r) == StagingEntry.sr_form.dir(r) : Wr.Dec<Sg.Form>}:
  match r:
    case Wr.Got{m, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.form(r: Wr.Dec<Nat>) -> {FSg.get_form.go(r) == StagingEntry.sr_form(r) : Wr.Dec<Sg.Form>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sq.form_dir(Wr.get_bool(s))
        case 1n+p:
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+u:
                  {==}
    case Wr.Bad{}:
      {==}

def sq.seen_form(n: Sg.Name, r: Wr.Dec<Sg.Form>) -> {FSg.get_seen.form(n, r) == StagingEntry.sr_seen.form(n, r) : Wr.Dec<Sg.Seen>}:
  match r:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.seen_name(r: Wr.Dec<Sg.Name>) -> {FSg.get_seen.go(r) == StagingEntry.sr_seen.name(r) : Wr.Dec<Sg.Seen>}:
  match r:
    case Wr.Got{n, +s}:
      %sq.form(Wr.get_nat(s)) : {FSg.get_seen.form(n, FSg.get_form.go(Wr.get_nat(s))) == StagingEntry.sr_seen.form(n, _) : Wr.Dec<Sg.Seen>}
      sq.seen_form(n, FSg.get_form.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def sq.seen(+s: String) -> {FSg.get_seen(s) == StagingEntry.sr_seen(s) : Wr.Dec<Sg.Seen>}:
  %sq.name(Wr.get_nat(s)) : {FSg.get_seen.go(FSg.get_name.go(Wr.get_nat(s))) == StagingEntry.sr_seen.name(_) : Wr.Dec<Sg.Seen>}
  sq.seen_name(FSg.get_name.go(Wr.get_nat(s)))

# Times, cwds, entries of the sessions directory
# ----------------------------------------------

def sq.time_nanos(secs: Nat, r: Wr.Dec<Nat>) -> {FSg.get_time.nanos(secs, r) == StagingEntry.sr_time.nanos(secs, r) : Wr.Dec<Sg.Time>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.time_secs(r: Wr.Dec<Nat>) -> {FSg.get_time.go(r) == StagingEntry.sr_time.secs(r) : Wr.Dec<Sg.Time>}:
  match r:
    case Wr.Got{secs, s}:
      sq.time_nanos(secs, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def sq.time(s: String) -> {FSg.get_time(s) == StagingEntry.sr_time(s) : Wr.Dec<Sg.Time>}:
  sq.time_secs(Wr.get_nat(s))

def sq.times_go(m: Nat, cur: Wr.Dec<Sg.Time>) -> {Wr.get_list.go(~Sg.Time, ~FSg.get_time, m, cur) == Wr.get_list.go(~Sg.Time, ~StagingEntry.sr_time, m, cur) : Wr.Dec<List<&2, Sg.Time>>}:
  match m:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+k:
      match cur:
        case Wr.Got{x, +s}:
          %sq.time(s) : {Wr.get_list.cons(Sg.Time, x, Wr.get_list.go(~Sg.Time, ~FSg.get_time, k, FSg.get_time(s))) == Wr.get_list.cons(Sg.Time, x, Wr.get_list.go(~Sg.Time, ~StagingEntry.sr_time, k, _)) : Wr.Dec<List<&2, Sg.Time>>}
          %sq.times_go(k, FSg.get_time(s)) : {Wr.get_list.cons(Sg.Time, x, Wr.get_list.go(~Sg.Time, ~FSg.get_time, k, FSg.get_time(s))) == Wr.get_list.cons(Sg.Time, x, _) : Wr.Dec<List<&2, Sg.Time>>}
          {==}
        case Wr.Bad{}:
          {==}

def sq.times_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Sg.Time, ~FSg.get_time, r) == Wr.get_list.start(~Sg.Time, ~StagingEntry.sr_time, r) : Wr.Dec<List<&2, Sg.Time>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %sq.time(s) : {Wr.get_list.go(~Sg.Time, ~FSg.get_time, m, FSg.get_time(s)) == Wr.get_list.go(~Sg.Time, ~StagingEntry.sr_time, m, _) : Wr.Dec<List<&2, Sg.Time>>}
          sq.times_go(m, FSg.get_time(s))
    case Wr.Bad{}:
      {==}

def sq.times(s: String) -> {Wr.get_list(~Sg.Time, ~FSg.get_time, s) == Wr.get_list(~Sg.Time, ~StagingEntry.sr_time, s) : Wr.Dec<List<&2, Sg.Time>>}:
  sq.times_start(Wr.get_nat(s))

def sq.cwd_some(r: Wr.Dec<String>) -> {FSg.get_cwd.some(r) == StagingEntry.sr_cwd.some(r) : Wr.Dec<Maybe<&2, String>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.cwd(r: Wr.Dec<Nat>) -> {FSg.get_cwd.go(r) == StagingEntry.sr_cwd(r) : Wr.Dec<Maybe<&2, String>>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n+p:
          match p:
            case 0n:
              sq.cwd_some(Wr.get_str(s))
            case 1n+q:
              {==}
    case Wr.Bad{}:
      {==}

def sq.obs_times(e: Sg.Seen, c: Maybe<&2, String>, r: Wr.Dec<List<&2, Sg.Time>>) -> {FSg.get_obs.times(e, c, r) == StagingEntry.sr_obs.times(e, c, r) : Wr.Dec<Ls.Obs>}:
  match r:
    case Wr.Got{ts, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.obs_cwd(e: Sg.Seen, r: Wr.Dec<Maybe<&2, String>>) -> {FSg.get_obs.cwd(e, r) == StagingEntry.sr_obs.cwd(e, r) : Wr.Dec<Ls.Obs>}:
  match r:
    case Wr.Got{c, +s}:
      %sq.times(s) : {FSg.get_obs.times(e, c, Wr.get_list(~Sg.Time, ~FSg.get_time, s)) == StagingEntry.sr_obs.times(e, c, _) : Wr.Dec<Ls.Obs>}
      sq.obs_times(e, c, Wr.get_list(~Sg.Time, ~FSg.get_time, s))
    case Wr.Bad{}:
      {==}

def sq.obs_seen(r: Wr.Dec<Sg.Seen>) -> {FSg.get_obs.go(r) == StagingEntry.sr_obs.seen(r) : Wr.Dec<Ls.Obs>}:
  match r:
    case Wr.Got{e, +s}:
      %sq.cwd(Wr.get_nat(s)) : {FSg.get_obs.cwd(e, FSg.get_cwd.go(Wr.get_nat(s))) == StagingEntry.sr_obs.cwd(e, _) : Wr.Dec<Ls.Obs>}
      sq.obs_cwd(e, FSg.get_cwd.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def sq.obs(+s: String) -> {FSg.get_obs(s) == StagingEntry.sr_obs(s) : Wr.Dec<Ls.Obs>}:
  %sq.seen(s) : {FSg.get_obs.go(FSg.get_seen(s)) == StagingEntry.sr_obs.seen(_) : Wr.Dec<Ls.Obs>}
  sq.obs_seen(FSg.get_seen(s))

# Lists of entries
# ----------------

def sq.seens_go(m: Nat, cur: Wr.Dec<Sg.Seen>) -> {Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, m, cur) == Wr.get_list.go(~Sg.Seen, ~StagingEntry.sr_seen, m, cur) : Wr.Dec<List<&2, Sg.Seen>>}:
  match m:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+k:
      match cur:
        case Wr.Got{x, +s}:
          %sq.seen(s) : {Wr.get_list.cons(Sg.Seen, x, Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, k, FSg.get_seen(s))) == Wr.get_list.cons(Sg.Seen, x, Wr.get_list.go(~Sg.Seen, ~StagingEntry.sr_seen, k, _)) : Wr.Dec<List<&2, Sg.Seen>>}
          %sq.seens_go(k, FSg.get_seen(s)) : {Wr.get_list.cons(Sg.Seen, x, Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, k, FSg.get_seen(s))) == Wr.get_list.cons(Sg.Seen, x, _) : Wr.Dec<List<&2, Sg.Seen>>}
          {==}
        case Wr.Bad{}:
          {==}

def sq.seens_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Sg.Seen, ~FSg.get_seen, r) == Wr.get_list.start(~Sg.Seen, ~StagingEntry.sr_seen, r) : Wr.Dec<List<&2, Sg.Seen>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %sq.seen(s) : {Wr.get_list.go(~Sg.Seen, ~FSg.get_seen, m, FSg.get_seen(s)) == Wr.get_list.go(~Sg.Seen, ~StagingEntry.sr_seen, m, _) : Wr.Dec<List<&2, Sg.Seen>>}
          sq.seens_go(m, FSg.get_seen(s))
    case Wr.Bad{}:
      {==}

def sq.seens(s: String) -> {Wr.get_list(~Sg.Seen, ~FSg.get_seen, s) == Wr.get_list(~Sg.Seen, ~StagingEntry.sr_seen, s) : Wr.Dec<List<&2, Sg.Seen>>}:
  sq.seens_start(Wr.get_nat(s))

def sq.obss_go(m: Nat, cur: Wr.Dec<Ls.Obs>) -> {Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, m, cur) == Wr.get_list.go(~Ls.Obs, ~StagingEntry.sr_obs, m, cur) : Wr.Dec<List<&2, Ls.Obs>>}:
  match m:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+k:
      match cur:
        case Wr.Got{x, +s}:
          %sq.obs(s) : {Wr.get_list.cons(Ls.Obs, x, Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, k, FSg.get_obs(s))) == Wr.get_list.cons(Ls.Obs, x, Wr.get_list.go(~Ls.Obs, ~StagingEntry.sr_obs, k, _)) : Wr.Dec<List<&2, Ls.Obs>>}
          %sq.obss_go(k, FSg.get_obs(s)) : {Wr.get_list.cons(Ls.Obs, x, Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, k, FSg.get_obs(s))) == Wr.get_list.cons(Ls.Obs, x, _) : Wr.Dec<List<&2, Ls.Obs>>}
          {==}
        case Wr.Bad{}:
          {==}

def sq.obss_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Ls.Obs, ~FSg.get_obs, r) == Wr.get_list.start(~Ls.Obs, ~StagingEntry.sr_obs, r) : Wr.Dec<List<&2, Ls.Obs>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %sq.obs(s) : {Wr.get_list.go(~Ls.Obs, ~FSg.get_obs, m, FSg.get_obs(s)) == Wr.get_list.go(~Ls.Obs, ~StagingEntry.sr_obs, m, _) : Wr.Dec<List<&2, Ls.Obs>>}
          sq.obss_go(m, FSg.get_obs(s))
    case Wr.Bad{}:
      {==}

def sq.obss(s: String) -> {Wr.get_list(~Ls.Obs, ~FSg.get_obs, s) == Wr.get_list(~Ls.Obs, ~StagingEntry.sr_obs, s) : Wr.Dec<List<&2, Ls.Obs>>}:
  sq.obss_start(Wr.get_nat(s))

# The judge request
# -----------------

def sq.cand(r: Wr.Dec<Nat>) -> {FSg.get_cand.go(r) == StagingEntry.sr_cand(r) : Wr.Dec<Sg.Cand>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n+p:
          match p:
            case 0n:
              {==}
            case 1n+q:
              {==}
    case Wr.Bad{}:
      {==}

def sq.lock(r: Wr.Dec<Nat>) -> {FSg.get_lock.go(r) == StagingEntry.sr_lock(r) : Wr.Dec<Sg.Lock>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n+p:
          match p:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+u:
                  {==}
    case Wr.Bad{}:
      {==}

def sq.judge_inner(c: Sg.Cand, l: Sg.Lock, now: Sg.Time, own: Sg.Time, r: Wr.Dec<List<&2, Sg.Time>>) -> {FSg.get_judge.inner(c, l, now, own, r) == StagingEntry.sr_judge.inner(c, l, now, own, r) : Wr.Dec<FSg.Req>}:
  match r:
    case Wr.Got{ts, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.judge_own(c: Sg.Cand, l: Sg.Lock, now: Sg.Time, r: Wr.Dec<Sg.Time>) -> {FSg.get_judge.own(c, l, now, r) == StagingEntry.sr_judge.own(c, l, now, r) : Wr.Dec<FSg.Req>}:
  match r:
    case Wr.Got{own, +s}:
      %sq.times(s) : {FSg.get_judge.inner(c, l, now, own, Wr.get_list(~Sg.Time, ~FSg.get_time, s)) == StagingEntry.sr_judge.inner(c, l, now, own, _) : Wr.Dec<FSg.Req>}
      sq.judge_inner(c, l, now, own, Wr.get_list(~Sg.Time, ~FSg.get_time, s))
    case Wr.Bad{}:
      {==}

def sq.judge_now(c: Sg.Cand, l: Sg.Lock, r: Wr.Dec<Sg.Time>) -> {FSg.get_judge.now(c, l, r) == StagingEntry.sr_judge.now(c, l, r) : Wr.Dec<FSg.Req>}:
  match r:
    case Wr.Got{now, +s}:
      %sq.time(s) : {FSg.get_judge.own(c, l, now, FSg.get_time(s)) == StagingEntry.sr_judge.own(c, l, now, _) : Wr.Dec<FSg.Req>}
      sq.judge_own(c, l, now, FSg.get_time(s))
    case Wr.Bad{}:
      {==}

def sq.judge_lock(c: Sg.Cand, r: Wr.Dec<Sg.Lock>) -> {FSg.get_judge.lock(c, r) == StagingEntry.sr_judge.lock(c, r) : Wr.Dec<FSg.Req>}:
  match r:
    case Wr.Got{l, +s}:
      %sq.time(s) : {FSg.get_judge.now(c, l, FSg.get_time(s)) == StagingEntry.sr_judge.now(c, l, _) : Wr.Dec<FSg.Req>}
      sq.judge_now(c, l, FSg.get_time(s))
    case Wr.Bad{}:
      {==}

def sq.judge(r: Wr.Dec<Sg.Cand>) -> {FSg.get_judge(r) == StagingEntry.sr_judge(r) : Wr.Dec<FSg.Req>}:
  match r:
    case Wr.Got{c, +s}:
      %sq.lock(Wr.get_nat(s)) : {FSg.get_judge.lock(c, FSg.get_lock.go(Wr.get_nat(s))) == StagingEntry.sr_judge.lock(c, _) : Wr.Dec<FSg.Req>}
      sq.judge_lock(c, FSg.get_lock.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

# The request
# -----------

def sq.publish(r: Wr.Dec<Bool>) -> {FSg.get_publish(r) == StagingEntry.sr_publish(r) : Wr.Dec<FSg.Req>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.meet(r: Wr.Dec<List<&2, Sg.Seen>>) -> {FSg.get_meet(r) == StagingEntry.sr_meet(r) : Wr.Dec<FSg.Req>}:
  match r:
    case Wr.Got{es, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.scan(r: Wr.Dec<List<&2, Sg.Seen>>) -> {FSg.get_scan(r) == StagingEntry.sr_scan(r) : Wr.Dec<FSg.Req>}:
  match r:
    case Wr.Got{es, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.rows(r: Wr.Dec<List<&2, Ls.Obs>>) -> {FSg.get_rows(r) == StagingEntry.sr_rows(r) : Wr.Dec<FSg.Req>}:
  match r:
    case Wr.Got{os, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sq.req(r: Wr.Dec<Nat>) -> {FSg.get_req.go(r) == StagingEntry.sr_req(r) : Wr.Dec<FSg.Req>}:
  match r:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          sq.publish(Wr.get_bool(s))
        case 1n+a:
          match a:
            case 0n:
              %sq.seens(s) : {FSg.get_meet(Wr.get_list(~Sg.Seen, ~FSg.get_seen, s)) == StagingEntry.sr_meet(_) : Wr.Dec<FSg.Req>}
              sq.meet(Wr.get_list(~Sg.Seen, ~FSg.get_seen, s))
            case 1n+b:
              match b:
                case 0n:
                  %sq.cand(Wr.get_nat(s)) : {FSg.get_judge(FSg.get_cand.go(Wr.get_nat(s))) == StagingEntry.sr_judge(_) : Wr.Dec<FSg.Req>}
                  sq.judge(FSg.get_cand.go(Wr.get_nat(s)))
                case 1n+c:
                  match c:
                    case 0n:
                      %sq.seens(s) : {FSg.get_scan(Wr.get_list(~Sg.Seen, ~FSg.get_seen, s)) == StagingEntry.sr_scan(_) : Wr.Dec<FSg.Req>}
                      sq.scan(Wr.get_list(~Sg.Seen, ~FSg.get_seen, s))
                    case 1n+d:
                      match d:
                        case 0n:
                          %sq.obss(s) : {FSg.get_rows(Wr.get_list(~Ls.Obs, ~FSg.get_obs, s)) == StagingEntry.sr_rows(_) : Wr.Dec<FSg.Req>}
                          sq.rows(Wr.get_list(~Ls.Obs, ~FSg.get_obs, s))
                        case 1n+e:
                          {==}
    case Wr.Bad{}:
      {==}

# The reply
# ---------

def sq.end(b: Bool, r: FSg.Req) -> {FSg.answer.end(b, r) == StagingEntry.sr_entry.end(b, r) : String}:
  match b:
    case True{}:
      PA.se.reply(r)
    case False{}:
      {==}

def sq.answer(d: Wr.Dec<FSg.Req>) -> {FSg.answer(d) == StagingEntry.sr_entry.go(d) : String}:
  match d:
    case Wr.Got{r, s}:
      sq.end(Wr.end(s), r)
    case Wr.Bad{}:
      {==}

def StagingEntry.staging_entry_spec(s):
  %sq.req(Wr.get_nat(s)) : {FSg.answer(FSg.get_req.go(Wr.get_nat(s))) == StagingEntry.sr_entry.go(_) : String}
  sq.answer(FSg.get_req.go(Wr.get_nat(s)))
