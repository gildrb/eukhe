# eukhe: lemmas the proofs of area cron_file share: the entry's wire
# (bend/ffi_cron_file.bend). Each record the laws spell reads back; each
# list of records that fits reads back; the entry's reply writers write
# what the laws' spellers write; the entry reads every input as the laws'
# reader does, stage by stage.

import Base
import ../../../bend/cron.bend as Cr
import ../../../bend/cron_store.bend as CS
import ../../../bend/cron_file.bend as CF
import ../../../bend/ffi_cron.bend as FC
import ../../../bend/ffi_cron_file.bend as FF
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/cron.bend as Cron
import ../../../laws/cron_file/pass.bend as CronFile
import ../../../laws/cron_file/entry.bend as CronFileEntry
import ../../../laws/cron_file/view.bend as CronFileView
import ../../base/wire.bend as LWire
import ../../cron/base/entry.bend as LCe
import ../../cron/base/answer.bend as LAn
import ./logic.bend as LCfl

# Records
# -------

def cfw.slot(x: CF.Slot, +rest: String, +fit: {CronFileEntry.slot_fit(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FF.get_slot(CronFileEntry.spell_slot(x, rest)) : Wr.Dec<CF.Slot>}:
  match x:
    case CF.Slot{+k, +f}:
      %LWire.pw6.nat(k, Cron.spell_fact(f, rest), LCfl.cfl.and_l(LawsBase.wire_fits(k), Cron.fact_fits(f), fit)) : {Wr.Got{CF.Slot{k, f}, rest} == FF.get_slot.key(_) : Wr.Dec<CF.Slot>}
      %LCe.crr.fact(f, rest, LCfl.cfl.and_r(LawsBase.wire_fits(k), Cron.fact_fits(f), fit)) : {Wr.Got{CF.Slot{k, f}, rest} == FF.get_slot.fact(k, _) : Wr.Dec<CF.Slot>}
      {==}

def cfw.key(m: Maybe<&2, Nat>, +rest: String, fit: {LawsBase.core_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FF.get_key(Cron.spell_mnat(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  LCe.crr.mnat(m, rest, fit)

def cfw.who(w: CS.Who, rest: String) -> {Wr.Got{w, rest} == FC.get_who(Wr.get_nat(Cron.spell_who(w, rest))) : Wr.Dec<CS.Who>}:
  match w:
    case CS.Mine{b}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case CS.Theirs{b}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def cfw.hold(x: CF.Hold, +rest: String, fit: {CronFileEntry.hold_fit(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FF.get_hold(CronFileEntry.spell_hold(x, rest)) : Wr.Dec<CF.Hold>}:
  match x:
    case CF.Held{+m, +w}:
      %cfw.key(m, Cron.spell_who(w, rest), fit) : {Wr.Got{CF.Held{m, w}, rest} == FF.get_hold.key(_) : Wr.Dec<CF.Hold>}
      %cfw.who(w, rest) : {Wr.Got{CF.Held{m, w}, rest} == FF.get_hold.who(m, _) : Wr.Dec<CF.Hold>}
      {==}
    case CF.Unheld{}:
      {==}

def cfw.pin(x: CF.Pin, +rest: String, fit: {CronFileEntry.pin_fit(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FF.get_pin(CronFileEntry.spell_pin(x, rest)) : Wr.Dec<CF.Pin>}:
  match x:
    case CF.Pinned{+m, +h}:
      %cfw.key(m, Wr.put_bool(h, rest), fit) : {Wr.Got{CF.Pinned{m, h}, rest} == FF.get_pin.key(_) : Wr.Dec<CF.Pin>}
      %LCe.crr.bool(h, rest) : {Wr.Got{CF.Pinned{m, h}, rest} == FF.get_pin.hit(m, _) : Wr.Dec<CF.Pin>}
      {==}
    case CF.Unpinned{}:
      {==}

# Lists of records
# ----------------

def cfw.slots_items(xs: List<&2, CF.Slot>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      CronFileEntry.spell_slot(x, cfw.slots_items(t, rest))

def cfw.slots_put_go(xs: List<&2, CF.Slot>, -rest: String) -> {Wr.put_list.go(~CF.Slot, ~CronFileEntry.spell_slot, xs, rest) == (List.length(&2, CF.Slot, xs), cfw.slots_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~CF.Slot, ~CronFileEntry.spell_slot, t, rest), (List.length(&2, CF.Slot, t), cfw.slots_items(t, rest)), cfw.slots_put_go(t, rest)) : {Wr.put_list.step(~CF.Slot, ~CronFileEntry.spell_slot, x, _) == (1n+List.length(&2, CF.Slot, t), CronFileEntry.spell_slot(x, cfw.slots_items(t, rest))) : Nat & String}
      {==}

def cfw.slots_put(+xs: List<&2, CF.Slot>, -rest: String) -> {Wr.put_list(~CF.Slot, ~CronFileEntry.spell_slot, xs, rest) == Wr.put_nat(List.length(&2, CF.Slot, xs), cfw.slots_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~CF.Slot, ~CronFileEntry.spell_slot, xs, rest), (List.length(&2, CF.Slot, xs), cfw.slots_items(xs, rest)), cfw.slots_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, CF.Slot, xs), cfw.slots_items(xs, rest)) : String}
  {==}

def cfw.slots_go_rt(+t: List<&2, CF.Slot>, +x: CF.Slot, +rest: String, +hf: {CronFileEntry.slots_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~CF.Slot, ~FF.get_slot, List.length(&2, CF.Slot, t), FF.get_slot(CronFileEntry.spell_slot(x, cfw.slots_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, CF.Slot>>}:
  match t:
    case Nil{}:
      %cfw.slot(x, rest, LCfl.cfl.and_l(CronFileEntry.slot_fit(x), True{}, hf)) : {Wr.get_list.go(~CF.Slot, ~FF.get_slot, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, CF.Slot>>}
      {==}
    case Con{+y, +u}:
      %cfw.slot(x, CronFileEntry.spell_slot(y, cfw.slots_items(u, rest)), LCfl.cfl.and_l(CronFileEntry.slot_fit(x), CronFileEntry.slots_fit(y <> u), hf)) : {Wr.get_list.go(~CF.Slot, ~FF.get_slot, 1n+List.length(&2, CF.Slot, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, CF.Slot>>}
      %Equal.sym(Wr.Dec<List<&2, CF.Slot>>, Wr.get_list.go(~CF.Slot, ~FF.get_slot, List.length(&2, CF.Slot, u), FF.get_slot(CronFileEntry.spell_slot(y, cfw.slots_items(u, rest)))), Wr.Got{y <> u, rest}, cfw.slots_go_rt(u, y, rest, LCfl.cfl.and_r(CronFileEntry.slot_fit(x), CronFileEntry.slots_fit(y <> u), hf))) : {Wr.get_list.cons(CF.Slot, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, CF.Slot>>}
      {==}

# a list of records that fits reads back, and the rest is untouched
def cfw.slots_rt(+xs: List<&2, CF.Slot>, +rest: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, CF.Slot, xs)), CronFileEntry.slots_fit(xs)) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~CF.Slot, ~FF.get_slot, Wr.put_list(~CF.Slot, ~CronFileEntry.spell_slot, xs, rest)) : Wr.Dec<List<&2, CF.Slot>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(String, Wr.put_list(~CF.Slot, ~CronFileEntry.spell_slot, x <> t, rest), Wr.put_nat(List.length(&2, CF.Slot, x <> t), cfw.slots_items(x <> t, rest)), cfw.slots_put(x <> t, rest)) : {Wr.Got{x <> t, rest} == Wr.get_list(~CF.Slot, ~FF.get_slot, _) : Wr.Dec<List<&2, CF.Slot>>}
      %LWire.pw6.nat(List.length(&2, CF.Slot, x <> t), cfw.slots_items(x <> t, rest), LCfl.cfl.and_l(LawsBase.wire_fits(List.length(&2, CF.Slot, x <> t)), CronFileEntry.slots_fit(x <> t), h)) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~CF.Slot, ~FF.get_slot, _) : Wr.Dec<List<&2, CF.Slot>>}
      Equal.sym(Wr.Dec<List<&2, CF.Slot>>, Wr.get_list.go(~CF.Slot, ~FF.get_slot, List.length(&2, CF.Slot, t), FF.get_slot(CronFileEntry.spell_slot(x, cfw.slots_items(t, rest)))), Wr.Got{x <> t, rest}, cfw.slots_go_rt(t, x, rest, LCfl.cfl.and_r(LawsBase.wire_fits(List.length(&2, CF.Slot, x <> t)), CronFileEntry.slots_fit(x <> t), h)))

def cfw.keys_items(xs: List<&2, Maybe<&2, Nat>>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Cron.spell_mnat(x, cfw.keys_items(t, rest))

def cfw.keys_put_go(xs: List<&2, Maybe<&2, Nat>>, -rest: String) -> {Wr.put_list.go(~Maybe<&2, Nat>, ~Cron.spell_mnat, xs, rest) == (List.length(&2, Maybe<&2, Nat>, xs), cfw.keys_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Maybe<&2, Nat>, ~Cron.spell_mnat, t, rest), (List.length(&2, Maybe<&2, Nat>, t), cfw.keys_items(t, rest)), cfw.keys_put_go(t, rest)) : {Wr.put_list.step(~Maybe<&2, Nat>, ~Cron.spell_mnat, x, _) == (1n+List.length(&2, Maybe<&2, Nat>, t), Cron.spell_mnat(x, cfw.keys_items(t, rest))) : Nat & String}
      {==}

def cfw.keys_put(+xs: List<&2, Maybe<&2, Nat>>, -rest: String) -> {Wr.put_list(~Maybe<&2, Nat>, ~Cron.spell_mnat, xs, rest) == Wr.put_nat(List.length(&2, Maybe<&2, Nat>, xs), cfw.keys_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Maybe<&2, Nat>, ~Cron.spell_mnat, xs, rest), (List.length(&2, Maybe<&2, Nat>, xs), cfw.keys_items(xs, rest)), cfw.keys_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Maybe<&2, Nat>, xs), cfw.keys_items(xs, rest)) : String}
  {==}

def cfw.keys_go_rt(+t: List<&2, Maybe<&2, Nat>>, +x: Maybe<&2, Nat>, +rest: String, +hf: {CronFileEntry.keys_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Maybe<&2, Nat>, ~FF.get_key, List.length(&2, Maybe<&2, Nat>, t), FF.get_key(Cron.spell_mnat(x, cfw.keys_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Maybe<&2, Nat>>>}:
  match t:
    case Nil{}:
      %cfw.key(x, rest, LCfl.cfl.and_l(LawsBase.core_mfits(x), True{}, hf)) : {Wr.get_list.go(~Maybe<&2, Nat>, ~FF.get_key, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
      {==}
    case Con{+y, +u}:
      %cfw.key(x, Cron.spell_mnat(y, cfw.keys_items(u, rest)), LCfl.cfl.and_l(LawsBase.core_mfits(x), CronFileEntry.keys_fit(y <> u), hf)) : {Wr.get_list.go(~Maybe<&2, Nat>, ~FF.get_key, 1n+List.length(&2, Maybe<&2, Nat>, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
      %Equal.sym(Wr.Dec<List<&2, Maybe<&2, Nat>>>, Wr.get_list.go(~Maybe<&2, Nat>, ~FF.get_key, List.length(&2, Maybe<&2, Nat>, u), FF.get_key(Cron.spell_mnat(y, cfw.keys_items(u, rest)))), Wr.Got{y <> u, rest}, cfw.keys_go_rt(u, y, rest, LCfl.cfl.and_r(LawsBase.core_mfits(x), CronFileEntry.keys_fit(y <> u), hf))) : {Wr.get_list.cons(Maybe<&2, Nat>, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
      {==}

# a list of records that fits reads back, and the rest is untouched
def cfw.keys_rt(+xs: List<&2, Maybe<&2, Nat>>, +rest: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, Maybe<&2, Nat>, xs)), CronFileEntry.keys_fit(xs)) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Maybe<&2, Nat>, ~FF.get_key, Wr.put_list(~Maybe<&2, Nat>, ~Cron.spell_mnat, xs, rest)) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(String, Wr.put_list(~Maybe<&2, Nat>, ~Cron.spell_mnat, x <> t, rest), Wr.put_nat(List.length(&2, Maybe<&2, Nat>, x <> t), cfw.keys_items(x <> t, rest)), cfw.keys_put(x <> t, rest)) : {Wr.Got{x <> t, rest} == Wr.get_list(~Maybe<&2, Nat>, ~FF.get_key, _) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
      %LWire.pw6.nat(List.length(&2, Maybe<&2, Nat>, x <> t), cfw.keys_items(x <> t, rest), LCfl.cfl.and_l(LawsBase.wire_fits(List.length(&2, Maybe<&2, Nat>, x <> t)), CronFileEntry.keys_fit(x <> t), h)) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~Maybe<&2, Nat>, ~FF.get_key, _) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
      Equal.sym(Wr.Dec<List<&2, Maybe<&2, Nat>>>, Wr.get_list.go(~Maybe<&2, Nat>, ~FF.get_key, List.length(&2, Maybe<&2, Nat>, t), FF.get_key(Cron.spell_mnat(x, cfw.keys_items(t, rest)))), Wr.Got{x <> t, rest}, cfw.keys_go_rt(t, x, rest, LCfl.cfl.and_r(LawsBase.wire_fits(List.length(&2, Maybe<&2, Nat>, x <> t)), CronFileEntry.keys_fit(x <> t), h)))

def cfw.holds_items(xs: List<&2, CF.Hold>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      CronFileEntry.spell_hold(x, cfw.holds_items(t, rest))

def cfw.holds_put_go(xs: List<&2, CF.Hold>, -rest: String) -> {Wr.put_list.go(~CF.Hold, ~CronFileEntry.spell_hold, xs, rest) == (List.length(&2, CF.Hold, xs), cfw.holds_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~CF.Hold, ~CronFileEntry.spell_hold, t, rest), (List.length(&2, CF.Hold, t), cfw.holds_items(t, rest)), cfw.holds_put_go(t, rest)) : {Wr.put_list.step(~CF.Hold, ~CronFileEntry.spell_hold, x, _) == (1n+List.length(&2, CF.Hold, t), CronFileEntry.spell_hold(x, cfw.holds_items(t, rest))) : Nat & String}
      {==}

def cfw.holds_put(+xs: List<&2, CF.Hold>, -rest: String) -> {Wr.put_list(~CF.Hold, ~CronFileEntry.spell_hold, xs, rest) == Wr.put_nat(List.length(&2, CF.Hold, xs), cfw.holds_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~CF.Hold, ~CronFileEntry.spell_hold, xs, rest), (List.length(&2, CF.Hold, xs), cfw.holds_items(xs, rest)), cfw.holds_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, CF.Hold, xs), cfw.holds_items(xs, rest)) : String}
  {==}

def cfw.holds_go_rt(+t: List<&2, CF.Hold>, +x: CF.Hold, +rest: String, +hf: {CronFileEntry.holds_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~CF.Hold, ~FF.get_hold, List.length(&2, CF.Hold, t), FF.get_hold(CronFileEntry.spell_hold(x, cfw.holds_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, CF.Hold>>}:
  match t:
    case Nil{}:
      %cfw.hold(x, rest, LCfl.cfl.and_l(CronFileEntry.hold_fit(x), True{}, hf)) : {Wr.get_list.go(~CF.Hold, ~FF.get_hold, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, CF.Hold>>}
      {==}
    case Con{+y, +u}:
      %cfw.hold(x, CronFileEntry.spell_hold(y, cfw.holds_items(u, rest)), LCfl.cfl.and_l(CronFileEntry.hold_fit(x), CronFileEntry.holds_fit(y <> u), hf)) : {Wr.get_list.go(~CF.Hold, ~FF.get_hold, 1n+List.length(&2, CF.Hold, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, CF.Hold>>}
      %Equal.sym(Wr.Dec<List<&2, CF.Hold>>, Wr.get_list.go(~CF.Hold, ~FF.get_hold, List.length(&2, CF.Hold, u), FF.get_hold(CronFileEntry.spell_hold(y, cfw.holds_items(u, rest)))), Wr.Got{y <> u, rest}, cfw.holds_go_rt(u, y, rest, LCfl.cfl.and_r(CronFileEntry.hold_fit(x), CronFileEntry.holds_fit(y <> u), hf))) : {Wr.get_list.cons(CF.Hold, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, CF.Hold>>}
      {==}

# a list of records that fits reads back, and the rest is untouched
def cfw.holds_rt(+xs: List<&2, CF.Hold>, +rest: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, CF.Hold, xs)), CronFileEntry.holds_fit(xs)) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~CF.Hold, ~FF.get_hold, Wr.put_list(~CF.Hold, ~CronFileEntry.spell_hold, xs, rest)) : Wr.Dec<List<&2, CF.Hold>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(String, Wr.put_list(~CF.Hold, ~CronFileEntry.spell_hold, x <> t, rest), Wr.put_nat(List.length(&2, CF.Hold, x <> t), cfw.holds_items(x <> t, rest)), cfw.holds_put(x <> t, rest)) : {Wr.Got{x <> t, rest} == Wr.get_list(~CF.Hold, ~FF.get_hold, _) : Wr.Dec<List<&2, CF.Hold>>}
      %LWire.pw6.nat(List.length(&2, CF.Hold, x <> t), cfw.holds_items(x <> t, rest), LCfl.cfl.and_l(LawsBase.wire_fits(List.length(&2, CF.Hold, x <> t)), CronFileEntry.holds_fit(x <> t), h)) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~CF.Hold, ~FF.get_hold, _) : Wr.Dec<List<&2, CF.Hold>>}
      Equal.sym(Wr.Dec<List<&2, CF.Hold>>, Wr.get_list.go(~CF.Hold, ~FF.get_hold, List.length(&2, CF.Hold, t), FF.get_hold(CronFileEntry.spell_hold(x, cfw.holds_items(t, rest)))), Wr.Got{x <> t, rest}, cfw.holds_go_rt(t, x, rest, LCfl.cfl.and_r(LawsBase.wire_fits(List.length(&2, CF.Hold, x <> t)), CronFileEntry.holds_fit(x <> t), h)))

def cfw.pins_items(xs: List<&2, CF.Pin>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      CronFileEntry.spell_pin(x, cfw.pins_items(t, rest))

def cfw.pins_put_go(xs: List<&2, CF.Pin>, -rest: String) -> {Wr.put_list.go(~CF.Pin, ~CronFileEntry.spell_pin, xs, rest) == (List.length(&2, CF.Pin, xs), cfw.pins_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~CF.Pin, ~CronFileEntry.spell_pin, t, rest), (List.length(&2, CF.Pin, t), cfw.pins_items(t, rest)), cfw.pins_put_go(t, rest)) : {Wr.put_list.step(~CF.Pin, ~CronFileEntry.spell_pin, x, _) == (1n+List.length(&2, CF.Pin, t), CronFileEntry.spell_pin(x, cfw.pins_items(t, rest))) : Nat & String}
      {==}

def cfw.pins_put(+xs: List<&2, CF.Pin>, -rest: String) -> {Wr.put_list(~CF.Pin, ~CronFileEntry.spell_pin, xs, rest) == Wr.put_nat(List.length(&2, CF.Pin, xs), cfw.pins_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~CF.Pin, ~CronFileEntry.spell_pin, xs, rest), (List.length(&2, CF.Pin, xs), cfw.pins_items(xs, rest)), cfw.pins_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, CF.Pin, xs), cfw.pins_items(xs, rest)) : String}
  {==}

def cfw.pins_go_rt(+t: List<&2, CF.Pin>, +x: CF.Pin, +rest: String, +hf: {CronFileEntry.pins_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~CF.Pin, ~FF.get_pin, List.length(&2, CF.Pin, t), FF.get_pin(CronFileEntry.spell_pin(x, cfw.pins_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, CF.Pin>>}:
  match t:
    case Nil{}:
      %cfw.pin(x, rest, LCfl.cfl.and_l(CronFileEntry.pin_fit(x), True{}, hf)) : {Wr.get_list.go(~CF.Pin, ~FF.get_pin, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, CF.Pin>>}
      {==}
    case Con{+y, +u}:
      %cfw.pin(x, CronFileEntry.spell_pin(y, cfw.pins_items(u, rest)), LCfl.cfl.and_l(CronFileEntry.pin_fit(x), CronFileEntry.pins_fit(y <> u), hf)) : {Wr.get_list.go(~CF.Pin, ~FF.get_pin, 1n+List.length(&2, CF.Pin, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, CF.Pin>>}
      %Equal.sym(Wr.Dec<List<&2, CF.Pin>>, Wr.get_list.go(~CF.Pin, ~FF.get_pin, List.length(&2, CF.Pin, u), FF.get_pin(CronFileEntry.spell_pin(y, cfw.pins_items(u, rest)))), Wr.Got{y <> u, rest}, cfw.pins_go_rt(u, y, rest, LCfl.cfl.and_r(CronFileEntry.pin_fit(x), CronFileEntry.pins_fit(y <> u), hf))) : {Wr.get_list.cons(CF.Pin, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, CF.Pin>>}
      {==}

# a list of records that fits reads back, and the rest is untouched
def cfw.pins_rt(+xs: List<&2, CF.Pin>, +rest: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, CF.Pin, xs)), CronFileEntry.pins_fit(xs)) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~CF.Pin, ~FF.get_pin, Wr.put_list(~CF.Pin, ~CronFileEntry.spell_pin, xs, rest)) : Wr.Dec<List<&2, CF.Pin>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(String, Wr.put_list(~CF.Pin, ~CronFileEntry.spell_pin, x <> t, rest), Wr.put_nat(List.length(&2, CF.Pin, x <> t), cfw.pins_items(x <> t, rest)), cfw.pins_put(x <> t, rest)) : {Wr.Got{x <> t, rest} == Wr.get_list(~CF.Pin, ~FF.get_pin, _) : Wr.Dec<List<&2, CF.Pin>>}
      %LWire.pw6.nat(List.length(&2, CF.Pin, x <> t), cfw.pins_items(x <> t, rest), LCfl.cfl.and_l(LawsBase.wire_fits(List.length(&2, CF.Pin, x <> t)), CronFileEntry.pins_fit(x <> t), h)) : {Wr.Got{x <> t, rest} == Wr.get_list.start(~CF.Pin, ~FF.get_pin, _) : Wr.Dec<List<&2, CF.Pin>>}
      Equal.sym(Wr.Dec<List<&2, CF.Pin>>, Wr.get_list.go(~CF.Pin, ~FF.get_pin, List.length(&2, CF.Pin, t), FF.get_pin(CronFileEntry.spell_pin(x, cfw.pins_items(t, rest)))), Wr.Got{x <> t, rest}, cfw.pins_go_rt(t, x, rest, LCfl.cfl.and_r(LawsBase.wire_fits(List.length(&2, CF.Pin, x <> t)), CronFileEntry.pins_fit(x <> t), h)))

# Reply writers
# -------------

def cfw.tooks_step(+x: CS.Took, r: Nat & String) -> {Wr.put_list.step(~CS.Took, ~FC.put_took, x, r) == Wr.put_list.step(~CS.Took, ~Cron.spell_took, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %LAn.crw.took(x, s) : {(1n+n, FC.put_took(x, s)) == (1n+n, _) : Nat & String}
      {==}

def cfw.tooks_go(xs: List<&2, CS.Took>, +rest: String) -> {Wr.put_list.go(~CS.Took, ~FC.put_took, xs, rest) == Wr.put_list.go(~CS.Took, ~Cron.spell_took, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cfw.tooks_go(t, rest) : {Wr.put_list.step(~CS.Took, ~FC.put_took, x, Wr.put_list.go(~CS.Took, ~FC.put_took, t, rest)) == Wr.put_list.step(~CS.Took, ~Cron.spell_took, x, _) : Nat & String}
      cfw.tooks_step(x, Wr.put_list.go(~CS.Took, ~FC.put_took, t, rest))

def cfw.tooks(xs: List<&2, CS.Took>, +rest: String) -> {Wr.put_list(~CS.Took, ~FC.put_took, xs, rest) == Wr.put_list(~CS.Took, ~Cron.spell_took, xs, rest) : String}:
  %cfw.tooks_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~CS.Took, ~FC.put_took, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

def cfw.backs_step(+x: CS.Back, r: Nat & String) -> {Wr.put_list.step(~CS.Back, ~FC.put_back, x, r) == Wr.put_list.step(~CS.Back, ~Cron.spell_back, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %LAn.crw.back(x, s) : {(1n+n, FC.put_back(x, s)) == (1n+n, _) : Nat & String}
      {==}

def cfw.backs_go(xs: List<&2, CS.Back>, +rest: String) -> {Wr.put_list.go(~CS.Back, ~FC.put_back, xs, rest) == Wr.put_list.go(~CS.Back, ~Cron.spell_back, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cfw.backs_go(t, rest) : {Wr.put_list.step(~CS.Back, ~FC.put_back, x, Wr.put_list.go(~CS.Back, ~FC.put_back, t, rest)) == Wr.put_list.step(~CS.Back, ~Cron.spell_back, x, _) : Nat & String}
      cfw.backs_step(x, Wr.put_list.go(~CS.Back, ~FC.put_back, t, rest))

def cfw.backs(xs: List<&2, CS.Back>, +rest: String) -> {Wr.put_list(~CS.Back, ~FC.put_back, xs, rest) == Wr.put_list(~CS.Back, ~Cron.spell_back, xs, rest) : String}:
  %cfw.backs_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~CS.Back, ~FC.put_back, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

def cfw.fins_step(+x: CS.Fin, r: Nat & String) -> {Wr.put_list.step(~CS.Fin, ~FC.put_fin, x, r) == Wr.put_list.step(~CS.Fin, ~Cron.spell_fin, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %LAn.crw.fin(x, s) : {(1n+n, FC.put_fin(x, s)) == (1n+n, _) : Nat & String}
      {==}

def cfw.fins_go(xs: List<&2, CS.Fin>, +rest: String) -> {Wr.put_list.go(~CS.Fin, ~FC.put_fin, xs, rest) == Wr.put_list.go(~CS.Fin, ~Cron.spell_fin, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cfw.fins_go(t, rest) : {Wr.put_list.step(~CS.Fin, ~FC.put_fin, x, Wr.put_list.go(~CS.Fin, ~FC.put_fin, t, rest)) == Wr.put_list.step(~CS.Fin, ~Cron.spell_fin, x, _) : Nat & String}
      cfw.fins_step(x, Wr.put_list.go(~CS.Fin, ~FC.put_fin, t, rest))

def cfw.fins(xs: List<&2, CS.Fin>, +rest: String) -> {Wr.put_list(~CS.Fin, ~FC.put_fin, xs, rest) == Wr.put_list(~CS.Fin, ~Cron.spell_fin, xs, rest) : String}:
  %cfw.fins_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~CS.Fin, ~FC.put_fin, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

# The reader
# ----------

def cfe.slot_fact(k: Nat, r: Wr.Dec<CS.Fact>) -> {CronFileEntry.read_slot.fact(k, r) == FF.get_slot.fact(k, r) : Wr.Dec<CF.Slot>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cfe.slot_key(r: Wr.Dec<Nat>) -> {CronFileEntry.read_slot.key(r) == FF.get_slot.key(r) : Wr.Dec<CF.Slot>}:
  match r:
    case Wr.Got{+k, +s}:
      %LCe.cre.fact(s) : {CronFileEntry.read_slot.fact(k, Cron.read_fact(s)) == FF.get_slot.fact(k, _) : Wr.Dec<CF.Slot>}
      cfe.slot_fact(k, Cron.read_fact(s))
    case Wr.Bad{}:
      {==}

def cfe.slot(+s: String) -> {CronFileEntry.read_slot(s) == FF.get_slot(s) : Wr.Dec<CF.Slot>}:
  cfe.slot_key(Wr.get_nat(s))

def cfe.key(+s: String) -> {CronFileEntry.read_key(s) == FF.get_key(s) : Wr.Dec<Maybe<&2, Nat>>}:
  LCe.cre.mnat(Wr.get_nat(s))

def cfe.hold_who(m: Maybe<&2, Nat>, r: Wr.Dec<CS.Who>) -> {CronFileEntry.read_hold.who(m, r) == FF.get_hold.who(m, r) : Wr.Dec<CF.Hold>}:
  match r:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cfe.hold_key(r: Wr.Dec<Maybe<&2, Nat>>) -> {CronFileEntry.read_hold.key(r) == FF.get_hold.key(r) : Wr.Dec<CF.Hold>}:
  match r:
    case Wr.Got{+m, +s}:
      %LCe.cre.who(Wr.get_nat(s)) : {CronFileEntry.read_hold.who(m, Cron.read_who(Wr.get_nat(s))) == FF.get_hold.who(m, _) : Wr.Dec<CF.Hold>}
      cfe.hold_who(m, Cron.read_who(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def cfe.hold_tag(t: Nat, +s: String) -> {CronFileEntry.read_hold.tag(t, s) == FF.get_hold.tag(t, s) : Wr.Dec<CF.Hold>}:
  match t:
    case 0n:
      %cfe.key(s) : {CronFileEntry.read_hold.key(CronFileEntry.read_key(s)) == FF.get_hold.key(_) : Wr.Dec<CF.Hold>}
      cfe.hold_key(CronFileEntry.read_key(s))
    case 1n:
      {==}
    case 2n+p:
      {==}

def cfe.hold_go(r: Wr.Dec<Nat>) -> {CronFileEntry.read_hold.go(r) == FF.get_hold.go(r) : Wr.Dec<CF.Hold>}:
  match r:
    case Wr.Got{t, s}:
      cfe.hold_tag(t, s)
    case Wr.Bad{}:
      {==}

def cfe.hold(+s: String) -> {CronFileEntry.read_hold(s) == FF.get_hold(s) : Wr.Dec<CF.Hold>}:
  cfe.hold_go(Wr.get_nat(s))

def cfe.pin_hit(m: Maybe<&2, Nat>, r: Wr.Dec<Bool>) -> {CronFileEntry.read_pin.hit(m, r) == FF.get_pin.hit(m, r) : Wr.Dec<CF.Pin>}:
  match r:
    case Wr.Got{h, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cfe.pin_key(r: Wr.Dec<Maybe<&2, Nat>>) -> {CronFileEntry.read_pin.key(r) == FF.get_pin.key(r) : Wr.Dec<CF.Pin>}:
  match r:
    case Wr.Got{m, s}:
      cfe.pin_hit(m, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def cfe.pin_tag(t: Nat, +s: String) -> {CronFileEntry.read_pin.tag(t, s) == FF.get_pin.tag(t, s) : Wr.Dec<CF.Pin>}:
  match t:
    case 0n:
      %cfe.key(s) : {CronFileEntry.read_pin.key(CronFileEntry.read_key(s)) == FF.get_pin.key(_) : Wr.Dec<CF.Pin>}
      cfe.pin_key(CronFileEntry.read_key(s))
    case 1n:
      {==}
    case 2n+p:
      {==}

def cfe.pin_go(r: Wr.Dec<Nat>) -> {CronFileEntry.read_pin.go(r) == FF.get_pin.go(r) : Wr.Dec<CF.Pin>}:
  match r:
    case Wr.Got{t, s}:
      cfe.pin_tag(t, s)
    case Wr.Bad{}:
      {==}

def cfe.pin(+s: String) -> {CronFileEntry.read_pin(s) == FF.get_pin(s) : Wr.Dec<CF.Pin>}:
  cfe.pin_go(Wr.get_nat(s))

def cfe.slots_go(k: Nat, cur: Wr.Dec<CF.Slot>) -> {Wr.get_list.go(~CF.Slot, ~CronFileEntry.read_slot, k, cur) == Wr.get_list.go(~CF.Slot, ~FF.get_slot, k, cur) : Wr.Dec<List<&2, CF.Slot>>}:
  match k:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %cfe.slot(s) : {Wr.get_list.cons(CF.Slot, x, Wr.get_list.go(~CF.Slot, ~CronFileEntry.read_slot, m, CronFileEntry.read_slot(s))) == Wr.get_list.cons(CF.Slot, x, Wr.get_list.go(~CF.Slot, ~FF.get_slot, m, _)) : Wr.Dec<List<&2, CF.Slot>>}
          %cfe.slots_go(m, CronFileEntry.read_slot(s)) : {Wr.get_list.cons(CF.Slot, x, Wr.get_list.go(~CF.Slot, ~CronFileEntry.read_slot, m, CronFileEntry.read_slot(s))) == Wr.get_list.cons(CF.Slot, x, _) : Wr.Dec<List<&2, CF.Slot>>}
          {==}
        case Wr.Bad{}:
          {==}

def cfe.slots_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~CF.Slot, ~CronFileEntry.read_slot, r) == Wr.get_list.start(~CF.Slot, ~FF.get_slot, r) : Wr.Dec<List<&2, CF.Slot>>}:
  match r:
    case Wr.Got{k, +s}:
      match k:
        case 0n:
          {==}
        case 1n+m:
          %cfe.slot(s) : {Wr.get_list.go(~CF.Slot, ~CronFileEntry.read_slot, m, CronFileEntry.read_slot(s)) == Wr.get_list.go(~CF.Slot, ~FF.get_slot, m, _) : Wr.Dec<List<&2, CF.Slot>>}
          cfe.slots_go(m, CronFileEntry.read_slot(s))
    case Wr.Bad{}:
      {==}

def cfe.slots(+s: String) -> {Wr.get_list(~CF.Slot, ~CronFileEntry.read_slot, s) == Wr.get_list(~CF.Slot, ~FF.get_slot, s) : Wr.Dec<List<&2, CF.Slot>>}:
  cfe.slots_start(Wr.get_nat(s))

def cfe.keys_go(k: Nat, cur: Wr.Dec<Maybe<&2, Nat>>) -> {Wr.get_list.go(~Maybe<&2, Nat>, ~CronFileEntry.read_key, k, cur) == Wr.get_list.go(~Maybe<&2, Nat>, ~FF.get_key, k, cur) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}:
  match k:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %cfe.key(s) : {Wr.get_list.cons(Maybe<&2, Nat>, x, Wr.get_list.go(~Maybe<&2, Nat>, ~CronFileEntry.read_key, m, CronFileEntry.read_key(s))) == Wr.get_list.cons(Maybe<&2, Nat>, x, Wr.get_list.go(~Maybe<&2, Nat>, ~FF.get_key, m, _)) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
          %cfe.keys_go(m, CronFileEntry.read_key(s)) : {Wr.get_list.cons(Maybe<&2, Nat>, x, Wr.get_list.go(~Maybe<&2, Nat>, ~CronFileEntry.read_key, m, CronFileEntry.read_key(s))) == Wr.get_list.cons(Maybe<&2, Nat>, x, _) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
          {==}
        case Wr.Bad{}:
          {==}

def cfe.keys_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Maybe<&2, Nat>, ~CronFileEntry.read_key, r) == Wr.get_list.start(~Maybe<&2, Nat>, ~FF.get_key, r) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}:
  match r:
    case Wr.Got{k, +s}:
      match k:
        case 0n:
          {==}
        case 1n+m:
          %cfe.key(s) : {Wr.get_list.go(~Maybe<&2, Nat>, ~CronFileEntry.read_key, m, CronFileEntry.read_key(s)) == Wr.get_list.go(~Maybe<&2, Nat>, ~FF.get_key, m, _) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
          cfe.keys_go(m, CronFileEntry.read_key(s))
    case Wr.Bad{}:
      {==}

def cfe.keys(+s: String) -> {Wr.get_list(~Maybe<&2, Nat>, ~CronFileEntry.read_key, s) == Wr.get_list(~Maybe<&2, Nat>, ~FF.get_key, s) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}:
  cfe.keys_start(Wr.get_nat(s))

def cfe.holds_go(k: Nat, cur: Wr.Dec<CF.Hold>) -> {Wr.get_list.go(~CF.Hold, ~CronFileEntry.read_hold, k, cur) == Wr.get_list.go(~CF.Hold, ~FF.get_hold, k, cur) : Wr.Dec<List<&2, CF.Hold>>}:
  match k:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %cfe.hold(s) : {Wr.get_list.cons(CF.Hold, x, Wr.get_list.go(~CF.Hold, ~CronFileEntry.read_hold, m, CronFileEntry.read_hold(s))) == Wr.get_list.cons(CF.Hold, x, Wr.get_list.go(~CF.Hold, ~FF.get_hold, m, _)) : Wr.Dec<List<&2, CF.Hold>>}
          %cfe.holds_go(m, CronFileEntry.read_hold(s)) : {Wr.get_list.cons(CF.Hold, x, Wr.get_list.go(~CF.Hold, ~CronFileEntry.read_hold, m, CronFileEntry.read_hold(s))) == Wr.get_list.cons(CF.Hold, x, _) : Wr.Dec<List<&2, CF.Hold>>}
          {==}
        case Wr.Bad{}:
          {==}

def cfe.holds_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~CF.Hold, ~CronFileEntry.read_hold, r) == Wr.get_list.start(~CF.Hold, ~FF.get_hold, r) : Wr.Dec<List<&2, CF.Hold>>}:
  match r:
    case Wr.Got{k, +s}:
      match k:
        case 0n:
          {==}
        case 1n+m:
          %cfe.hold(s) : {Wr.get_list.go(~CF.Hold, ~CronFileEntry.read_hold, m, CronFileEntry.read_hold(s)) == Wr.get_list.go(~CF.Hold, ~FF.get_hold, m, _) : Wr.Dec<List<&2, CF.Hold>>}
          cfe.holds_go(m, CronFileEntry.read_hold(s))
    case Wr.Bad{}:
      {==}

def cfe.holds(+s: String) -> {Wr.get_list(~CF.Hold, ~CronFileEntry.read_hold, s) == Wr.get_list(~CF.Hold, ~FF.get_hold, s) : Wr.Dec<List<&2, CF.Hold>>}:
  cfe.holds_start(Wr.get_nat(s))

def cfe.pins_go(k: Nat, cur: Wr.Dec<CF.Pin>) -> {Wr.get_list.go(~CF.Pin, ~CronFileEntry.read_pin, k, cur) == Wr.get_list.go(~CF.Pin, ~FF.get_pin, k, cur) : Wr.Dec<List<&2, CF.Pin>>}:
  match k:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %cfe.pin(s) : {Wr.get_list.cons(CF.Pin, x, Wr.get_list.go(~CF.Pin, ~CronFileEntry.read_pin, m, CronFileEntry.read_pin(s))) == Wr.get_list.cons(CF.Pin, x, Wr.get_list.go(~CF.Pin, ~FF.get_pin, m, _)) : Wr.Dec<List<&2, CF.Pin>>}
          %cfe.pins_go(m, CronFileEntry.read_pin(s)) : {Wr.get_list.cons(CF.Pin, x, Wr.get_list.go(~CF.Pin, ~CronFileEntry.read_pin, m, CronFileEntry.read_pin(s))) == Wr.get_list.cons(CF.Pin, x, _) : Wr.Dec<List<&2, CF.Pin>>}
          {==}
        case Wr.Bad{}:
          {==}

def cfe.pins_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~CF.Pin, ~CronFileEntry.read_pin, r) == Wr.get_list.start(~CF.Pin, ~FF.get_pin, r) : Wr.Dec<List<&2, CF.Pin>>}:
  match r:
    case Wr.Got{k, +s}:
      match k:
        case 0n:
          {==}
        case 1n+m:
          %cfe.pin(s) : {Wr.get_list.go(~CF.Pin, ~CronFileEntry.read_pin, m, CronFileEntry.read_pin(s)) == Wr.get_list.go(~CF.Pin, ~FF.get_pin, m, _) : Wr.Dec<List<&2, CF.Pin>>}
          cfe.pins_go(m, CronFileEntry.read_pin(s))
    case Wr.Bad{}:
      {==}

def cfe.pins(+s: String) -> {Wr.get_list(~CF.Pin, ~CronFileEntry.read_pin, s) == Wr.get_list(~CF.Pin, ~FF.get_pin, s) : Wr.Dec<List<&2, CF.Pin>>}:
  cfe.pins_start(Wr.get_nat(s))

def cfe.take_now(js: List<&2, CF.Slot>, cs: List<&2, Maybe<&2, Nat>>, d: Nat, r: Wr.Dec<Nat>) -> {CronFileEntry.read_take.now(js, cs, d, r) == FF.get_take.now(js, cs, d, r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cfe.take_due(js: List<&2, CF.Slot>, cs: List<&2, Maybe<&2, Nat>>, r: Wr.Dec<Nat>) -> {CronFileEntry.read_take.due(js, cs, r) == FF.get_take.due(js, cs, r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{d, s}:
      cfe.take_now(js, cs, d, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cfe.take_cs(js: List<&2, CF.Slot>, r: Wr.Dec<List<&2, Maybe<&2, Nat>>>) -> {CronFileEntry.read_take.cs(js, r) == FF.get_take.cs(js, r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{cs, s}:
      cfe.take_due(js, cs, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cfe.take(r: Wr.Dec<List<&2, CF.Slot>>) -> {CronFileEntry.read_take(r) == FF.get_take(r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{+js, +s}:
      %cfe.keys(s) : {CronFileEntry.read_take.cs(js, Wr.get_list(~Maybe<&2, Nat>, ~CronFileEntry.read_key, s)) == FF.get_take.cs(js, _) : Wr.Dec<CF.Pass>}
      cfe.take_cs(js, Wr.get_list(~Maybe<&2, Nat>, ~CronFileEntry.read_key, s))
    case Wr.Bad{}:
      {==}

def cfe.recover_cs(js: List<&2, CF.Slot>, r: Wr.Dec<List<&2, CF.Hold>>) -> {CronFileEntry.read_recover.cs(js, r) == FF.get_recover.cs(js, r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{cs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cfe.recover(r: Wr.Dec<List<&2, CF.Slot>>) -> {CronFileEntry.read_recover(r) == FF.get_recover(r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{+js, +s}:
      %cfe.holds(s) : {CronFileEntry.read_recover.cs(js, Wr.get_list(~CF.Hold, ~CronFileEntry.read_hold, s)) == FF.get_recover.cs(js, _) : Wr.Dec<CF.Pass>}
      cfe.recover_cs(js, Wr.get_list(~CF.Hold, ~CronFileEntry.read_hold, s))
    case Wr.Bad{}:
      {==}

def cfe.finish_now(js: List<&2, CF.Slot>, cs: List<&2, CF.Pin>, a: Bool, b: Bool, r: Wr.Dec<Nat>) -> {CronFileEntry.read_finish.now(js, cs, a, b, r) == FF.get_finish.now(js, cs, a, b, r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cfe.finish_failed(js: List<&2, CF.Slot>, cs: List<&2, CF.Pin>, a: Bool, r: Wr.Dec<Bool>) -> {CronFileEntry.read_finish.failed(js, cs, a, r) == FF.get_finish.failed(js, cs, a, r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{b, s}:
      cfe.finish_now(js, cs, a, b, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cfe.finish_ran(js: List<&2, CF.Slot>, cs: List<&2, CF.Pin>, r: Wr.Dec<Bool>) -> {CronFileEntry.read_finish.ran(js, cs, r) == FF.get_finish.ran(js, cs, r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{a, s}:
      cfe.finish_failed(js, cs, a, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def cfe.finish_cs(js: List<&2, CF.Slot>, r: Wr.Dec<List<&2, CF.Pin>>) -> {CronFileEntry.read_finish.cs(js, r) == FF.get_finish.cs(js, r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{cs, s}:
      cfe.finish_ran(js, cs, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def cfe.finish(r: Wr.Dec<List<&2, CF.Slot>>) -> {CronFileEntry.read_finish(r) == FF.get_finish(r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{+js, +s}:
      %cfe.pins(s) : {CronFileEntry.read_finish.cs(js, Wr.get_list(~CF.Pin, ~CronFileEntry.read_pin, s)) == FF.get_finish.cs(js, _) : Wr.Dec<CF.Pass>}
      cfe.finish_cs(js, Wr.get_list(~CF.Pin, ~CronFileEntry.read_pin, s))
    case Wr.Bad{}:
      {==}

def cfe.pass_tag(t: Nat, +s: String) -> {CronFileEntry.read_pass.tag(t, s) == FF.get_pass.tag(t, s) : Wr.Dec<CF.Pass>}:
  match t:
    case 0n:
      %cfe.slots(s) : {CronFileEntry.read_take(Wr.get_list(~CF.Slot, ~CronFileEntry.read_slot, s)) == FF.get_take(_) : Wr.Dec<CF.Pass>}
      cfe.take(Wr.get_list(~CF.Slot, ~CronFileEntry.read_slot, s))
    case 1n:
      %cfe.slots(s) : {CronFileEntry.read_recover(Wr.get_list(~CF.Slot, ~CronFileEntry.read_slot, s)) == FF.get_recover(_) : Wr.Dec<CF.Pass>}
      cfe.recover(Wr.get_list(~CF.Slot, ~CronFileEntry.read_slot, s))
    case 2n:
      %cfe.slots(s) : {CronFileEntry.read_finish(Wr.get_list(~CF.Slot, ~CronFileEntry.read_slot, s)) == FF.get_finish(_) : Wr.Dec<CF.Pass>}
      cfe.finish(Wr.get_list(~CF.Slot, ~CronFileEntry.read_slot, s))
    case 3n+p:
      {==}

# the entry reads every input as the laws' reader does
def cfe.pass(r: Wr.Dec<Nat>) -> {CronFileEntry.read_pass.go(r) == FF.get_pass.go(r) : Wr.Dec<CF.Pass>}:
  match r:
    case Wr.Got{t, s}:
      cfe.pass_tag(t, s)
    case Wr.Bad{}:
      {==}
