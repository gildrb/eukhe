# eukhe: the proof of LAW cron_serve_step_unknown_tag
# An encoded tag past the known ones (after a known prefix that reads
# back) reads back as itself, or Bad when too long
# (LAWireSpell.ws_nat_read); either way the entry answers its error form
# and keeps the runs.

import Base
import ../../bend/cron_serve.bend as Sv
import ../../bend/ffi_cron_serve.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/cron_serve/entry.bend as CronServeEntry
import ../wire/base/spell.bend as LAWireSpell
import ../base/wire.bend as LWire

def cut.ev(b: Bool, +runs: List<&2, String>, +n: Nat, +rest: String) -> {FC.step.go(runs, FC.get_ev(LAWireSpell.ws_nat_answer(b, 2n+n, rest))) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cut.disk(b: Bool, +runs: List<&2, String>, +me: Nat, +n: Nat, +rest: String) -> {FC.step.go(runs, FC.get_serve.disk(me, FC.get_disk(LAWireSpell.ws_nat_answer(b, 3n+n, rest)))) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cut.op(b: Bool, +runs: List<&2, String>, +me: Nat, +n: Nat, +rest: String) -> {FC.step.go(runs, FC.get_serve.op(me, Sv.Missing{}, FC.get_op(LAWireSpell.ws_nat_answer(b, 6n+n, rest)))) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cut.first(+runs: List<&2, String>, +n: Nat, +r: String) -> {FC.step(FC.Open{runs}, Wr.put_nat(2n+n, r)) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, r)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, r), LAWireSpell.ws_nat_read(2n+n, r)) : {FC.step.go(runs, FC.get_ev(_)) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}
  cut.ev(LawsBase.wire_fits(2n+n), runs, n, r)

def cut.second(+runs: List<&2, String>, +n: Nat, +r: String, +me: Nat, +fits: {LawsBase.wire_fits(me) == True{} : Bool}) -> {FC.step(FC.Open{runs}, Wr.put_nat(0n, Wr.put_nat(me, Wr.put_nat(3n+n, r)))) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}:
  %LWire.pw6.nat(0n, Wr.put_nat(me, Wr.put_nat(3n+n, r)), {==}) : {FC.step.go(runs, FC.get_ev(_)) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}
  %LWire.pw6.nat(me, Wr.put_nat(3n+n, r), fits) : {FC.step.go(runs, FC.get_serve(_)) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n+n, r)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(3n+n), 3n+n, r), LAWireSpell.ws_nat_read(3n+n, r)) : {FC.step.go(runs, FC.get_serve.disk(me, FC.get_disk(_))) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}
  cut.disk(LawsBase.wire_fits(3n+n), runs, me, n, r)

def cut.third(+runs: List<&2, String>, +n: Nat, +r: String, +me: Nat, +fits: {LawsBase.wire_fits(me) == True{} : Bool}) -> {FC.step(FC.Open{runs}, Wr.put_nat(0n, Wr.put_nat(me, Wr.put_nat(0n, Wr.put_nat(6n+n, r))))) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}:
  %LWire.pw6.nat(0n, Wr.put_nat(me, Wr.put_nat(0n, Wr.put_nat(6n+n, r))), {==}) : {FC.step.go(runs, FC.get_ev(_)) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}
  %LWire.pw6.nat(me, Wr.put_nat(0n, Wr.put_nat(6n+n, r)), fits) : {FC.step.go(runs, FC.get_serve(_)) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}
  %LWire.pw6.nat(0n, Wr.put_nat(6n+n, r), {==}) : {FC.step.go(runs, FC.get_serve.disk(me, FC.get_disk(_))) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(6n+n, r)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, r), LAWireSpell.ws_nat_read(6n+n, r)) : {FC.step.go(runs, FC.get_serve.op(me, Sv.Missing{}, FC.get_op(_))) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}
  cut.op(LawsBase.wire_fits(6n+n), runs, me, n, r)

def CronServeEntry.cron_serve_step_unknown_tag(runs, n, rest, me, fits):
  (cut.first(runs, n, rest), (cut.second(runs, n, rest, me, fits), cut.third(runs, n, rest, me, fits)))
