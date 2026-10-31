import Base
import ./wire.bend as W
import ./cron_store.bend as CS
import ./cron_file.bend as CF
import ./ffi_cron.bend as FC

# ffi_cron_file: the passes of the cron job store over a whole jobs file
# (bend/cron_file.bend `take`, `recover`, `finish`, on the clock unit
# CS.MINUTE: times in ms) as an entry of the compiled Bend core. The facts
# of a job, a next run, a status and whose a claim is are spelled as in
# bend/ffi_cron.bend. A request is a tag, then
#   0  a claim pass: the job records, the claim records (the key of the
#      job each names: Maybe), the time the jobs are due by, the clock
#   1  a recovery: the job records, the claim records (each 0 read, then
#      the key of the job it names (Maybe) and whose it is (0 this
#      process's, then T|F it still runs it; 1 another's, then T|F that
#      process is dead) | 1 one this build cannot read)
#   2  a finish step: the job records, the claim records (each 0 read,
#      then the key of the job it names (Maybe) and T|F it is the dispatch
#      recorded | 1 one this build cannot read), whether the run ran (T)
#      or was skipped (F), whether it failed (T|F), the clock
# where a list is its count, then its items, and a job record is its key
# (a Nat), then its facts.
# Reply:
#   0  the claim pass of each job (bend/ffi_cron.bend reply 0), in order
#   1  T|F for each claim record (it stays), then the recovery of each job
#      (bend/ffi_cron.bend reply 2)
#   2  T|F for each claim record (it stays), then the finish step of each
#      job (bend/ffi_cron.bend reply 3)
# Any other input: the error form.

# Decoding
# --------

def get_slot.fact(k: Nat, r: W.Dec<CS.Fact>) -> W.Dec<CF.Slot>:
  match r:
    case W.Got{f, s}:
      W.Got{CF.Slot{k, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_slot.key(r: W.Dec<Nat>) -> W.Dec<CF.Slot>:
  match r:
    case W.Got{k, s}:
      get_slot.fact(k, FC.get_fact(s))
    case W.Bad{}:
      W.Bad{}

# a job record at the start of s
def get_slot(s: String) -> W.Dec<CF.Slot>:
  get_slot.key(W.get_nat(s))

def get_slots(s: String) -> W.Dec<List<&2, CF.Slot>>:
  W.get_list(~CF.Slot, ~get_slot, s)

def get_key(s: String) -> W.Dec<Maybe<&2, Nat>>:
  FC.get_mnat(W.get_nat(s))

def get_hold.who(m: Maybe<&2, Nat>, r: W.Dec<CS.Who>) -> W.Dec<CF.Hold>:
  match r:
    case W.Got{w, s}:
      W.Got{CF.Held{m, w}, s}
    case W.Bad{}:
      W.Bad{}

def get_hold.key(r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<CF.Hold>:
  match r:
    case W.Got{m, s}:
      get_hold.who(m, FC.get_who(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_hold.tag(t: Nat, s: String) -> W.Dec<CF.Hold>:
  match t:
    case 0n:
      get_hold.key(get_key(s))
    case 1n:
      W.Got{CF.Unheld{}, s}
    case 2n+p:
      W.Bad{}

def get_hold.go(r: W.Dec<Nat>) -> W.Dec<CF.Hold>:
  match r:
    case W.Got{t, s}:
      get_hold.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a claim record of a recovery at the start of s
def get_hold(s: String) -> W.Dec<CF.Hold>:
  get_hold.go(W.get_nat(s))

def get_pin.hit(m: Maybe<&2, Nat>, r: W.Dec<Bool>) -> W.Dec<CF.Pin>:
  match r:
    case W.Got{h, s}:
      W.Got{CF.Pinned{m, h}, s}
    case W.Bad{}:
      W.Bad{}

def get_pin.key(r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<CF.Pin>:
  match r:
    case W.Got{m, s}:
      get_pin.hit(m, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_pin.tag(t: Nat, s: String) -> W.Dec<CF.Pin>:
  match t:
    case 0n:
      get_pin.key(get_key(s))
    case 1n:
      W.Got{CF.Unpinned{}, s}
    case 2n+p:
      W.Bad{}

def get_pin.go(r: W.Dec<Nat>) -> W.Dec<CF.Pin>:
  match r:
    case W.Got{t, s}:
      get_pin.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a claim record of a finish step at the start of s
def get_pin(s: String) -> W.Dec<CF.Pin>:
  get_pin.go(W.get_nat(s))

def get_take.now(js: List<&2, CF.Slot>, cs: List<&2, Maybe<&2, Nat>>, d: Nat, r: W.Dec<Nat>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{n, s}:
      W.Got{CF.PassTake{js, cs, d, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_take.due(js: List<&2, CF.Slot>, cs: List<&2, Maybe<&2, Nat>>, r: W.Dec<Nat>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{d, s}:
      get_take.now(js, cs, d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_take.cs(js: List<&2, CF.Slot>, r: W.Dec<List<&2, Maybe<&2, Nat>>>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{cs, s}:
      get_take.due(js, cs, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_take(r: W.Dec<List<&2, CF.Slot>>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{js, s}:
      get_take.cs(js, W.get_list(~Maybe<&2, Nat>, ~get_key, s))
    case W.Bad{}:
      W.Bad{}

def get_recover.cs(js: List<&2, CF.Slot>, r: W.Dec<List<&2, CF.Hold>>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{cs, s}:
      W.Got{CF.PassRecover{js, cs}, s}
    case W.Bad{}:
      W.Bad{}

def get_recover(r: W.Dec<List<&2, CF.Slot>>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{js, s}:
      get_recover.cs(js, W.get_list(~CF.Hold, ~get_hold, s))
    case W.Bad{}:
      W.Bad{}

def get_finish.now(js: List<&2, CF.Slot>, cs: List<&2, CF.Pin>, a: Bool, b: Bool, r: W.Dec<Nat>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{n, s}:
      W.Got{CF.PassFinish{js, cs, a, b, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_finish.failed(js: List<&2, CF.Slot>, cs: List<&2, CF.Pin>, a: Bool, r: W.Dec<Bool>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{b, s}:
      get_finish.now(js, cs, a, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_finish.ran(js: List<&2, CF.Slot>, cs: List<&2, CF.Pin>, r: W.Dec<Bool>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{a, s}:
      get_finish.failed(js, cs, a, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_finish.cs(js: List<&2, CF.Slot>, r: W.Dec<List<&2, CF.Pin>>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{cs, s}:
      get_finish.ran(js, cs, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_finish(r: W.Dec<List<&2, CF.Slot>>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{js, s}:
      get_finish.cs(js, W.get_list(~CF.Pin, ~get_pin, s))
    case W.Bad{}:
      W.Bad{}

def get_pass.tag(t: Nat, s: String) -> W.Dec<CF.Pass>:
  match t:
    case 0n:
      get_take(get_slots(s))
    case 1n:
      get_recover(get_slots(s))
    case 2n:
      get_finish(get_slots(s))
    case 3n+p:
      W.Bad{}

def get_pass.go(r: W.Dec<Nat>) -> W.Dec<CF.Pass>:
  match r:
    case W.Got{t, s}:
      get_pass.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_pass(s: String) -> W.Dec<CF.Pass>:
  get_pass.go(W.get_nat(s))

# Encoding
# --------

def put_tooks(xs: List<&2, CS.Took>, rest: String) -> String:
  W.put_list(~CS.Took, ~FC.put_took, xs, rest)

def put_keeps(xs: List<&2, Bool>, rest: String) -> String:
  W.put_list(~Bool, ~W.put_bool, xs, rest)

def put_backs(xs: List<&2, CS.Back>, rest: String) -> String:
  W.put_list(~CS.Back, ~FC.put_back, xs, rest)

def put_fins(xs: List<&2, CS.Fin>, rest: String) -> String:
  W.put_list(~CS.Fin, ~FC.put_fin, xs, rest)

def put_swept(x: CF.Swept, rest: String) -> String:
  match x:
    case CF.Swept{ks, bs}:
      put_keeps(ks, put_backs(bs, rest))

def put_closed(x: CF.Closed, rest: String) -> String:
  match x:
    case CF.Closed{ks, fs}:
      put_keeps(ks, put_fins(fs, rest))

# The entry
# ---------

# the answer to a request
def answer(a: CF.Pass) -> String:
  match a:
    case CF.PassTake{js, cs, d, n}:
      put_tooks(CF.take(js, cs, d, n), "")
    case CF.PassRecover{js, cs}:
      put_swept(CF.recover(js, cs), "")
    case CF.PassFinish{js, cs, r, b, n}:
      put_closed(CF.finish(CS.MINUTE(), js, cs, r, b, n), "")

def fail() -> String:
  W.err("cron_file: malformed request")

def run.end(whole: Bool, a: CF.Pass) -> String:
  match whole:
    case True{}:
      answer(a)
    case False{}:
      fail()

def run(r: W.Dec<CF.Pass>) -> String:
  match r:
    case W.Got{a, s}:
      run.end(W.end(s), a)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(get_pass(input))
