# eukhe: lemmas of the entry proofs of area strength: the entry's decoder
# reads every input as the laws' reader does (sr.vlabel to sr.req: stage
# by stage; the gauges by their item loop, sr.list_go; the slots and the
# actor as the verify entry's, LR.vr.slots, LR.vr.actor)

import Base
import ../../../bend/verify.bend as V
import ../../../bend/strength.bend as St
import ../../../bend/ffi_strength.bend as FS
import ../../../bend/ffi_verify.bend as FV
import ../../../bend/wire.bend as Wr
import ../../../spec/verified/strength_wire.bend as SW
import ../../verify/base/read.bend as LR

# Labels, bars, marks, gauges
# ---------------------------

def sr.vlabel(d: Wr.Dec<Nat>) -> {FS.get_vlabel(d) == SW.r_vlabel(d) : Wr.Dec<V.Label>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sr.bar_pct(d: Wr.Dec<Nat>) -> {FS.get_bar.pct(d) == SW.r_bar.pct(d) : Wr.Dec<St.Bar>}:
  match d:
    case Wr.Got{pct, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sr.bar(d: Wr.Dec<Nat>) -> {FS.get_bar(d) == SW.r_bar(d) : Wr.Dec<St.Bar>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          sr.bar_pct(Wr.get_nat(s))
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sr.mark_at(c: Nat, n: Nat, p: Nat, d: Wr.Dec<Nat>) -> {FS.get_mark.at(c, n, p, d) == SW.r_mark.at(c, n, p, d) : Wr.Dec<St.Mark>}:
  match d:
    case Wr.Got{at, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sr.mark_planned(c: Nat, n: Nat, d: Wr.Dec<Nat>) -> {FS.get_mark.planned(c, n, d) == SW.r_mark.planned(c, n, d) : Wr.Dec<St.Mark>}:
  match d:
    case Wr.Got{p, s}:
      sr.mark_at(c, n, p, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def sr.mark_ran(c: Nat, d: Wr.Dec<Nat>) -> {FS.get_mark.ran(c, d) == SW.r_mark.ran(c, d) : Wr.Dec<St.Mark>}:
  match d:
    case Wr.Got{n, s}:
      sr.mark_planned(c, n, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def sr.mark_caught(d: Wr.Dec<Nat>) -> {FS.get_mark.caught(d) == SW.r_mark.caught(d) : Wr.Dec<St.Mark>}:
  match d:
    case Wr.Got{c, s}:
      sr.mark_ran(c, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def sr.mark(d: Wr.Dec<Nat>) -> {FS.get_mark(d) == SW.r_mark(d) : Wr.Dec<St.Mark>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          sr.mark_caught(Wr.get_nat(s))
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sr.gauge_mark(b: St.Bar, d: Wr.Dec<St.Mark>) -> {FS.get_gauge.mark(b, d) == SW.r_gauge.mark(b, d) : Wr.Dec<St.Gauge>}:
  match d:
    case Wr.Got{m, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sr.gauge_bar(d: Wr.Dec<St.Bar>) -> {FS.get_gauge.bar(d) == SW.r_gauge.bar(d) : Wr.Dec<St.Gauge>}:
  match d:
    case Wr.Got{+b, +s}:
      %sr.mark(Wr.get_nat(s)) : {FS.get_gauge.mark(b, FS.get_mark(Wr.get_nat(s))) == SW.r_gauge.mark(b, _) : Wr.Dec<St.Gauge>}
      sr.gauge_mark(b, FS.get_mark(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def sr.gauge(+s: String) -> {FS.get_gauge(s) == SW.r_gauge(s) : Wr.Dec<St.Gauge>}:
  %sr.bar(Wr.get_nat(s)) : {FS.get_gauge.bar(FS.get_bar(Wr.get_nat(s))) == SW.r_gauge.bar(_) : Wr.Dec<St.Gauge>}
  sr.gauge_bar(FS.get_bar(Wr.get_nat(s)))

# the item loops read the same gauges
def sr.list_go(n: Nat, cur: Wr.Dec<St.Gauge>) -> {Wr.get_list.go(~St.Gauge, ~FS.get_gauge, n, cur) == Wr.get_list.go(~St.Gauge, ~SW.r_gauge, n, cur) : Wr.Dec<List<&2, St.Gauge>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %sr.gauge(s) : {Wr.get_list.cons(St.Gauge, x, Wr.get_list.go(~St.Gauge, ~FS.get_gauge, m, FS.get_gauge(s))) == Wr.get_list.cons(St.Gauge, x, Wr.get_list.go(~St.Gauge, ~SW.r_gauge, m, _)) : Wr.Dec<List<&2, St.Gauge>>}
          %sr.list_go(m, FS.get_gauge(s)) : {Wr.get_list.cons(St.Gauge, x, Wr.get_list.go(~St.Gauge, ~FS.get_gauge, m, FS.get_gauge(s))) == Wr.get_list.cons(St.Gauge, x, _) : Wr.Dec<List<&2, St.Gauge>>}
          {==}
        case Wr.Bad{}:
          {==}

def sr.list_start(d: Wr.Dec<Nat>) -> {Wr.get_list.start(~St.Gauge, ~FS.get_gauge, d) == Wr.get_list.start(~St.Gauge, ~SW.r_gauge, d) : Wr.Dec<List<&2, St.Gauge>>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %sr.gauge(s) : {Wr.get_list.go(~St.Gauge, ~FS.get_gauge, m, FS.get_gauge(s)) == Wr.get_list.go(~St.Gauge, ~SW.r_gauge, m, _) : Wr.Dec<List<&2, St.Gauge>>}
          sr.list_go(m, FS.get_gauge(s))
    case Wr.Bad{}:
      {==}

def sr.gauges(s: String) -> {FS.get_gauges(s) == SW.r_gauges(s) : Wr.Dec<List<&2, St.Gauge>>}:
  sr.list_start(Wr.get_nat(s))

# Requests
# --------
def sr.settle_gs(l: V.Label, now: Nat, d: Wr.Dec<List<&2, St.Gauge>>) -> {FS.get_req.settle_gs(l, now, d) == SW.r_req.settle_gs(l, now, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{gs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sr.settle_now(l: V.Label, d: Wr.Dec<Nat>) -> {FS.get_req.settle_now(l, d) == SW.r_req.settle_now(l, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+now, +s}:
      %sr.gauges(s) : {FS.get_req.settle_gs(l, now, FS.get_gauges(s)) == SW.r_req.settle_gs(l, now, _) : Wr.Dec<FS.Req>}
      sr.settle_gs(l, now, FS.get_gauges(s))
    case Wr.Bad{}:
      {==}

def sr.settle(d: Wr.Dec<V.Label>) -> {FS.get_req.settle(d) == SW.r_req.settle(d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{l, s}:
      sr.settle_now(l, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def sr.label_gs(l: V.Label, now: Nat, d: Wr.Dec<List<&2, St.Gauge>>) -> {FS.get_req.label_gs(l, now, d) == SW.r_req.label_gs(l, now, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{gs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sr.label_now(l: V.Label, d: Wr.Dec<Nat>) -> {FS.get_req.label_now(l, d) == SW.r_req.label_now(l, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+now, +s}:
      %sr.gauges(s) : {FS.get_req.label_gs(l, now, FS.get_gauges(s)) == SW.r_req.label_gs(l, now, _) : Wr.Dec<FS.Req>}
      sr.label_gs(l, now, FS.get_gauges(s))
    case Wr.Bad{}:
      {==}

def sr.label(d: Wr.Dec<V.Label>) -> {FS.get_req.label(d) == SW.r_req.label(d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{l, s}:
      sr.label_now(l, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def sr.exit_gs(base: Nat, now: Nat, slots: List<&2, V.Slot>, d: Wr.Dec<List<&2, St.Gauge>>) -> {FS.get_req.exit_gs(base, now, slots, d) == SW.r_req.exit_gs(base, now, slots, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{gs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sr.exit_slots(base: Nat, now: Nat, d: Wr.Dec<List<&2, V.Slot>>) -> {FS.get_req.exit_slots(base, now, d) == SW.r_req.exit_slots(base, now, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+slots, +s}:
      %sr.gauges(s) : {FS.get_req.exit_gs(base, now, slots, FS.get_gauges(s)) == SW.r_req.exit_gs(base, now, slots, _) : Wr.Dec<FS.Req>}
      sr.exit_gs(base, now, slots, FS.get_gauges(s))
    case Wr.Bad{}:
      {==}

def sr.exit_now(base: Nat, d: Wr.Dec<Nat>) -> {FS.get_req.exit_now(base, d) == SW.r_req.exit_now(base, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+now, +s}:
      %LR.vr.slots(s) : {FS.get_req.exit_slots(base, now, FV.get_slots(s)) == SW.r_req.exit_slots(base, now, _) : Wr.Dec<FS.Req>}
      sr.exit_slots(base, now, FV.get_slots(s))
    case Wr.Bad{}:
      {==}

def sr.exit(d: Wr.Dec<Nat>) -> {FS.get_req.exit(d) == SW.r_req.exit(d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{base, s}:
      sr.exit_now(base, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def sr.record_gs(who: V.Actor, i: Nat, m: St.Mark, d: Wr.Dec<List<&2, St.Gauge>>) -> {FS.get_req.record_gs(who, i, m, d) == SW.r_req.record_gs(who, i, m, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{gs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sr.record_mark(who: V.Actor, i: Nat, d: Wr.Dec<St.Mark>) -> {FS.get_req.record_mark(who, i, d) == SW.r_req.record_mark(who, i, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+m, +s}:
      %sr.gauges(s) : {FS.get_req.record_gs(who, i, m, FS.get_gauges(s)) == SW.r_req.record_gs(who, i, m, _) : Wr.Dec<FS.Req>}
      sr.record_gs(who, i, m, FS.get_gauges(s))
    case Wr.Bad{}:
      {==}

def sr.record_i(who: V.Actor, d: Wr.Dec<Nat>) -> {FS.get_req.record_i(who, d) == SW.r_req.record_i(who, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+i, +s}:
      %sr.mark(Wr.get_nat(s)) : {FS.get_req.record_mark(who, i, FS.get_mark(Wr.get_nat(s))) == SW.r_req.record_mark(who, i, _) : Wr.Dec<FS.Req>}
      sr.record_mark(who, i, FS.get_mark(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def sr.record(d: Wr.Dec<V.Actor>) -> {FS.get_req.record(d) == SW.r_req.record(d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{who, s}:
      sr.record_i(who, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def sr.strength_g(now: Nat, d: Wr.Dec<St.Gauge>) -> {FS.get_req.strength_g(now, d) == SW.r_req.strength_g(now, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{g, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sr.strength(d: Wr.Dec<Nat>) -> {FS.get_req.strength(d) == SW.r_req.strength(d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+now, +s}:
      %sr.gauge(s) : {FS.get_req.strength_g(now, FS.get_gauge(s)) == SW.r_req.strength_g(now, _) : Wr.Dec<FS.Req>}
      sr.strength_g(now, FS.get_gauge(s))
    case Wr.Bad{}:
      {==}

# the entry's decoder is the laws' reader
def sr.req(d: Wr.Dec<Nat>) -> {FS.get_req(d) == SW.r_req(d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          %sr.vlabel(Wr.get_nat(s)) : {FS.get_req.settle(FS.get_vlabel(Wr.get_nat(s))) == SW.r_req.settle(_) : Wr.Dec<FS.Req>}
          sr.settle(FS.get_vlabel(Wr.get_nat(s)))
        case 1n:
          %sr.vlabel(Wr.get_nat(s)) : {FS.get_req.label(FS.get_vlabel(Wr.get_nat(s))) == SW.r_req.label(_) : Wr.Dec<FS.Req>}
          sr.label(FS.get_vlabel(Wr.get_nat(s)))
        case 2n:
          sr.exit(Wr.get_nat(s))
        case 3n:
          %LR.vr.actor(Wr.get_nat(s)) : {FS.get_req.record(FV.get_actor(Wr.get_nat(s))) == SW.r_req.record(_) : Wr.Dec<FS.Req>}
          sr.record(FV.get_actor(Wr.get_nat(s)))
        case 4n:
          sr.strength(Wr.get_nat(s))
        case 5n+u:
          {==}
    case Wr.Bad{}:
      {==}
