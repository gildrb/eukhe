# eukhe: the laws of area cron_file: the entry (bend/ffi_cron_file.bend)
# answers the passes of laws/cron_file/pass.bend on the store's clock, and
# refuses every other input

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../bend/ffi_cron_file.bend as FF
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ../cron.bend as Cron
import ./pass.bend as CronFile

# The entry's wire
# ----------------
# The spellers and the reader are the entry's grammar written with the
# wire primitives and the spellers of laws/cron.bend alone.

def spell_slot(x: CF.Slot, rest: String) -> String:
  match x:
    case CF.Slot{k, f}:
      Wr.put_nat(k, Cron.spell_fact(f, rest))

def spell_hold(x: CF.Hold, rest: String) -> String:
  match x:
    case CF.Held{m, w}:
      Wr.put_nat(0n, Cron.spell_mnat(m, Cron.spell_who(w, rest)))
    case CF.Unheld{}:
      Wr.put_nat(1n, rest)

def spell_pin(x: CF.Pin, rest: String) -> String:
  match x:
    case CF.Pinned{m, h}:
      Wr.put_nat(0n, Cron.spell_mnat(m, Wr.put_bool(h, rest)))
    case CF.Unpinned{}:
      Wr.put_nat(1n, rest)

def spell_slots(js: List<&2, CF.Slot>, rest: String) -> String:
  Wr.put_list(~CF.Slot, ~spell_slot, js, rest)

# the request Rust writes for a
def spell_pass(a: CF.Pass) -> String:
  match a:
    case CF.PassTake{js, cs, d, n}:
      Wr.put_nat(0n, spell_slots(js, Wr.put_list(~Maybe<&2, Nat>, ~Cron.spell_mnat, cs, Wr.put_nat(d, Wr.put_nat(n, "")))))
    case CF.PassRecover{js, cs}:
      Wr.put_nat(1n, spell_slots(js, Wr.put_list(~CF.Hold, ~spell_hold, cs, "")))
    case CF.PassFinish{js, cs, r, b, n}:
      Wr.put_nat(2n, spell_slots(js, Wr.put_list(~CF.Pin, ~spell_pin, cs, Wr.put_bool(r, Wr.put_bool(b, Wr.put_nat(n, ""))))))

def slot_fit(x: CF.Slot) -> Bool:
  match x:
    case CF.Slot{k, f}:
      Bool.and(LawsBase.wire_fits(k), Cron.fact_fits(f))

def slots_fit(js: List<&2, CF.Slot>) -> Bool:
  match js:
    case Nil{}:
      True{}
    case j <> t:
      Bool.and(slot_fit(j), slots_fit(t))

def keys_fit(cs: List<&2, Maybe<&2, Nat>>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case m <> t:
      Bool.and(LawsBase.core_mfits(m), keys_fit(t))

def hold_fit(c: CF.Hold) -> Bool:
  match c:
    case CF.Held{m, w}:
      LawsBase.core_mfits(m)
    case CF.Unheld{}:
      True{}

def holds_fit(cs: List<&2, CF.Hold>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> t:
      Bool.and(hold_fit(c), holds_fit(t))

def pin_fit(c: CF.Pin) -> Bool:
  match c:
    case CF.Pinned{m, h}:
      LawsBase.core_mfits(m)
    case CF.Unpinned{}:
      True{}

def pins_fit(cs: List<&2, CF.Pin>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> t:
      Bool.and(pin_fit(c), pins_fit(t))

# every number of a fits the wire: each count, key, fact and time
def pass_fits(a: CF.Pass) -> Bool:
  match a:
    case CF.PassTake{+js, +cs, d, n}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, CF.Slot, js)), slots_fit(js)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Maybe<&2, Nat>, cs)), keys_fit(cs)), Bool.and(LawsBase.wire_fits(d), LawsBase.wire_fits(n))))
    case CF.PassRecover{+js, +cs}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, CF.Slot, js)), slots_fit(js)), Bool.and(LawsBase.wire_fits(List.length(&2, CF.Hold, cs)), holds_fit(cs)))
    case CF.PassFinish{+js, +cs, r, b, n}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, CF.Slot, js)), slots_fit(js)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, CF.Pin, cs)), pins_fit(cs)), LawsBase.wire_fits(n)))

def spell_keeps(ks: List<&2, Bool>, rest: String) -> String:
  Wr.put_list(~Bool, ~Wr.put_bool, ks, rest)

def spell_swept(x: CF.Swept) -> String:
  match x:
    case CF.Swept{ks, bs}:
      spell_keeps(ks, Wr.put_list(~CS.Back, ~Cron.spell_back, bs, ""))

def spell_closed(x: CF.Closed) -> String:
  match x:
    case CF.Closed{ks, fs}:
      spell_keeps(ks, Wr.put_list(~CS.Fin, ~Cron.spell_fin, fs, ""))

# the reply to a: the decision of the spec, on the store's clock
def spell_answer(a: CF.Pass) -> String:
  match a:
    case CF.PassTake{js, cs, d, n}:
      Wr.put_list(~CS.Took, ~Cron.spell_took, CronFile.take_all_spec(js, cs, d, n), "")
    case CF.PassRecover{js, cs}:
      spell_swept(CronFile.recover_all_spec(js, cs))
    case CF.PassFinish{js, cs, r, b, n}:
      spell_closed(CronFile.finish_all_spec(Cron.minute_spec(), js, cs, r, b, n))

# Reader: the requests the entry accepts

def read_slot.fact(k: Nat, r: Wr.Dec<CS.Fact>) -> Wr.Dec<CF.Slot>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{CF.Slot{k, f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_slot.key(r: Wr.Dec<Nat>) -> Wr.Dec<CF.Slot>:
  match r:
    case Wr.Got{k, s}:
      read_slot.fact(k, Cron.read_fact(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_slot(s: String) -> Wr.Dec<CF.Slot>:
  read_slot.key(Wr.get_nat(s))

def read_key(s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  Cron.read_mnat(Wr.get_nat(s))

def read_hold.who(m: Maybe<&2, Nat>, r: Wr.Dec<CS.Who>) -> Wr.Dec<CF.Hold>:
  match r:
    case Wr.Got{w, s}:
      Wr.Got{CF.Held{m, w}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_hold.key(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<CF.Hold>:
  match r:
    case Wr.Got{m, s}:
      read_hold.who(m, Cron.read_who(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_hold.tag(t: Nat, s: String) -> Wr.Dec<CF.Hold>:
  match t:
    case 0n:
      read_hold.key(read_key(s))
    case 1n:
      Wr.Got{CF.Unheld{}, s}
    case 2n+p:
      Wr.Bad{}

def read_hold.go(r: Wr.Dec<Nat>) -> Wr.Dec<CF.Hold>:
  match r:
    case Wr.Got{t, s}:
      read_hold.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_hold(s: String) -> Wr.Dec<CF.Hold>:
  read_hold.go(Wr.get_nat(s))

def read_pin.hit(m: Maybe<&2, Nat>, r: Wr.Dec<Bool>) -> Wr.Dec<CF.Pin>:
  match r:
    case Wr.Got{h, s}:
      Wr.Got{CF.Pinned{m, h}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_pin.key(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<CF.Pin>:
  match r:
    case Wr.Got{m, s}:
      read_pin.hit(m, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_pin.tag(t: Nat, s: String) -> Wr.Dec<CF.Pin>:
  match t:
    case 0n:
      read_pin.key(read_key(s))
    case 1n:
      Wr.Got{CF.Unpinned{}, s}
    case 2n+p:
      Wr.Bad{}

def read_pin.go(r: Wr.Dec<Nat>) -> Wr.Dec<CF.Pin>:
  match r:
    case Wr.Got{t, s}:
      read_pin.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_pin(s: String) -> Wr.Dec<CF.Pin>:
  read_pin.go(Wr.get_nat(s))

def read_take.now(js: List<&2, CF.Slot>, cs: List<&2, Maybe<&2, Nat>>, d: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{CF.PassTake{js, cs, d, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_take.due(js: List<&2, CF.Slot>, cs: List<&2, Maybe<&2, Nat>>, r: Wr.Dec<Nat>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{d, s}:
      read_take.now(js, cs, d, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_take.cs(js: List<&2, CF.Slot>, r: Wr.Dec<List<&2, Maybe<&2, Nat>>>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{cs, s}:
      read_take.due(js, cs, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_take(r: Wr.Dec<List<&2, CF.Slot>>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{js, s}:
      read_take.cs(js, Wr.get_list(~Maybe<&2, Nat>, ~read_key, s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_recover.cs(js: List<&2, CF.Slot>, r: Wr.Dec<List<&2, CF.Hold>>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{cs, s}:
      Wr.Got{CF.PassRecover{js, cs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_recover(r: Wr.Dec<List<&2, CF.Slot>>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{js, s}:
      read_recover.cs(js, Wr.get_list(~CF.Hold, ~read_hold, s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_finish.now(js: List<&2, CF.Slot>, cs: List<&2, CF.Pin>, a: Bool, b: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{CF.PassFinish{js, cs, a, b, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_finish.failed(js: List<&2, CF.Slot>, cs: List<&2, CF.Pin>, a: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{b, s}:
      read_finish.now(js, cs, a, b, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_finish.ran(js: List<&2, CF.Slot>, cs: List<&2, CF.Pin>, r: Wr.Dec<Bool>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{a, s}:
      read_finish.failed(js, cs, a, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_finish.cs(js: List<&2, CF.Slot>, r: Wr.Dec<List<&2, CF.Pin>>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{cs, s}:
      read_finish.ran(js, cs, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_finish(r: Wr.Dec<List<&2, CF.Slot>>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{js, s}:
      read_finish.cs(js, Wr.get_list(~CF.Pin, ~read_pin, s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_pass.tag(t: Nat, s: String) -> Wr.Dec<CF.Pass>:
  match t:
    case 0n:
      read_take(Wr.get_list(~CF.Slot, ~read_slot, s))
    case 1n:
      read_recover(Wr.get_list(~CF.Slot, ~read_slot, s))
    case 2n:
      read_finish(Wr.get_list(~CF.Slot, ~read_slot, s))
    case 3n+p:
      Wr.Bad{}

def read_pass.go(r: Wr.Dec<Nat>) -> Wr.Dec<CF.Pass>:
  match r:
    case Wr.Got{t, s}:
      read_pass.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_pass.end(whole: Bool, a: CF.Pass) -> Maybe<&2, CF.Pass>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_pass.whole(r: Wr.Dec<CF.Pass>) -> Maybe<&2, CF.Pass>:
  match r:
    case Wr.Got{a, s}:
      read_pass.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_pass(s: String) -> Maybe<&2, CF.Pass>:
  read_pass.whole(read_pass.go(Wr.get_nat(s)))

# Laws
# ----

# LAW cron_file_entry_answers: on every request Rust writes whose numbers fit the wire, the entry answers the spec's pass on the store's clock (a minute is 60000 ms)
# EXCLUDES: a misread record, count or time, a reply in another order, a pass other than the spec's
law cron_file_entry_answers:
  for +a: CF.Pass
  for fits: {pass_fits(a) == True{} : Bool}
  {FF.ffi(spell_pass(a)) == spell_answer(a) : String}

# LAW cron_file_entry_malformed_exact: every input that is not exactly one request (input left over after it included) gets exactly the error form 'E ', then "cron_file: malformed request"
# EXCLUDES: a default pass on a malformed or truncated request
law cron_file_entry_malformed_exact:
  for +s: String
  for no: {read_pass(s) == None{} : Maybe<&2, CF.Pass>}
  {FF.ffi(s) == SCon{'E', SCon{' ', "cron_file: malformed request"}} : String}

# LAW cron_file_entry_example: anchor: the strings Rust sends: a claim pass over two due jobs, one named by a claim record (rolled) and one not (claimed); a recovery that clears the claim of a dead process and keeps a record it cannot read; a finish step that drops the dispatch's claim record and counts a good run; a request with input left over is refused
# EXCLUDES: replies spelled in another order, a claim on a job a claim record names
law cron_file_entry_example:
  {FF.ffi("0,2,5,0,1,6,1,10,0,7,0,1,6,1,10,0,1,1,7,10,10,") == "2,2,1,16,1,1,16," : String} &
  {FF.ffi("1,1,5,0,1,6,1,10,0,2,0,1,5,1,T1,") == "2,FT1,1,0,1,10," : String} &
  {FF.ffi("2,1,5,0,1,6,1,10,0,2,0,1,5,T1,TF10,") == "2,FT1,1,0,1,10,0," : String} &
  {read_pass("2,1,5,0,1,6,1,10,0,2,0,1,5,T1,TF10,x") == None{} : Maybe<&2, CF.Pass>} &
  {FF.ffi("2,1,5,0,1,6,1,10,0,2,0,1,5,T1,TF10,x") == "E cron_file: malformed request" : String}

# LAW cron_file_entry_fits_example: anchor: a request whose numbers fit the wire exists, so cron_file_entry_answers speaks of something
# EXCLUDES: a vacuous cron_file_entry_answers
law cron_file_entry_fits_example:
  exs a: CF.Pass
  {pass_fits(a) == True{} : Bool}

