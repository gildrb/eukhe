# eukhe: lemmas of the entry proofs of area attack: the entry's decoder
# reads every input as the laws' reader does (ar.outcome_tag to ar.req:
# stage by stage; the outcomes by their item loop, ar.list_go; verify's
# label and the gauges as the strength entry's, LSR.sr.vlabel,
# LSR.sr.gauges; the slots as the verify entry's, LVR.vr.slots)

import Base
import ../../../bend/verify.bend as V
import ../../../bend/strength.bend as St
import ../../../bend/attack.bend as At
import ../../../bend/ffi_strength.bend as FS
import ../../../bend/ffi_verify.bend as FV
import ../../../bend/ffi_attack.bend as FA
import ../../../bend/wire.bend as Wr
import ../../../spec/verified/attack_wire.bend as SAW
import ../../verify/base/read.bend as LVR
import ../../strength/base/read.bend as LSR

# Outcomes and the judge's verdict
# --------------------------------

def ar.outcome_tag(d: Wr.Dec<Nat>) -> {FA.get_outcome.tag(d) == SAW.r_outcome.tag(d) : Wr.Dec<At.Outcome>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def ar.outcome(s: String) -> {FA.get_outcome(s) == SAW.r_outcome(s) : Wr.Dec<At.Outcome>}:
  ar.outcome_tag(Wr.get_nat(s))

# the item loops read the same outcomes
def ar.list_go(n: Nat, cur: Wr.Dec<At.Outcome>) -> {Wr.get_list.go(~At.Outcome, ~FA.get_outcome, n, cur) == Wr.get_list.go(~At.Outcome, ~SAW.r_outcome, n, cur) : Wr.Dec<List<&2, At.Outcome>>}:
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
          %ar.outcome(s) : {Wr.get_list.cons(At.Outcome, x, Wr.get_list.go(~At.Outcome, ~FA.get_outcome, m, FA.get_outcome(s))) == Wr.get_list.cons(At.Outcome, x, Wr.get_list.go(~At.Outcome, ~SAW.r_outcome, m, _)) : Wr.Dec<List<&2, At.Outcome>>}
          %ar.list_go(m, FA.get_outcome(s)) : {Wr.get_list.cons(At.Outcome, x, Wr.get_list.go(~At.Outcome, ~FA.get_outcome, m, FA.get_outcome(s))) == Wr.get_list.cons(At.Outcome, x, _) : Wr.Dec<List<&2, At.Outcome>>}
          {==}
        case Wr.Bad{}:
          {==}

def ar.list_start(d: Wr.Dec<Nat>) -> {Wr.get_list.start(~At.Outcome, ~FA.get_outcome, d) == Wr.get_list.start(~At.Outcome, ~SAW.r_outcome, d) : Wr.Dec<List<&2, At.Outcome>>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %ar.outcome(s) : {Wr.get_list.go(~At.Outcome, ~FA.get_outcome, m, FA.get_outcome(s)) == Wr.get_list.go(~At.Outcome, ~SAW.r_outcome, m, _) : Wr.Dec<List<&2, At.Outcome>>}
          ar.list_go(m, FA.get_outcome(s))
    case Wr.Bad{}:
      {==}

def ar.outcomes(s: String) -> {FA.get_outcomes(s) == SAW.r_outcomes(s) : Wr.Dec<List<&2, At.Outcome>>}:
  ar.list_start(Wr.get_nat(s))

def ar.agrees_yes(d: Wr.Dec<Bool>) -> {FA.get_agrees.yes(d) == SAW.r_agrees.yes(d) : Wr.Dec<Maybe<&2, Bool>>}:
  match d:
    case Wr.Got{yes, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ar.agrees(d: Wr.Dec<Nat>) -> {FA.get_agrees(d) == SAW.r_agrees(d) : Wr.Dec<Maybe<&2, Bool>>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          ar.agrees_yes(Wr.get_bool(s))
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

# Requests
# --------

def ar.outcome_agrees(ran: Bool, passes: Bool, differs: Bool, d: Wr.Dec<Maybe<&2, Bool>>) -> {FA.get_req.outcome_agrees(ran, passes, differs, d) == SAW.r_req.outcome_agrees(ran, passes, differs, d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{agrees, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ar.outcome_differs(ran: Bool, passes: Bool, d: Wr.Dec<Bool>) -> {FA.get_req.outcome_differs(ran, passes, d) == SAW.r_req.outcome_differs(ran, passes, d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{+differs, +s}:
      %ar.agrees(Wr.get_nat(s)) : {FA.get_req.outcome_agrees(ran, passes, differs, FA.get_agrees(Wr.get_nat(s))) == SAW.r_req.outcome_agrees(ran, passes, differs, _) : Wr.Dec<FA.Req>}
      ar.outcome_agrees(ran, passes, differs, FA.get_agrees(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def ar.outcome_passes(ran: Bool, d: Wr.Dec<Bool>) -> {FA.get_req.outcome_passes(ran, d) == SAW.r_req.outcome_passes(ran, d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{passes, s}:
      ar.outcome_differs(ran, passes, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ar.outcome_req(d: Wr.Dec<Bool>) -> {FA.get_req.outcome(d) == SAW.r_req.outcome(d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{ran, s}:
      ar.outcome_passes(ran, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ar.label_os(l: V.Label, now: Nat, gs: List<&2, St.Gauge>, d: Wr.Dec<List<&2, At.Outcome>>) -> {FA.get_req.label_os(l, now, gs, d) == SAW.r_req.label_os(l, now, gs, d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{os, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ar.label_gs(l: V.Label, now: Nat, d: Wr.Dec<List<&2, St.Gauge>>) -> {FA.get_req.label_gs(l, now, d) == SAW.r_req.label_gs(l, now, d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{+gs, +s}:
      %ar.outcomes(s) : {FA.get_req.label_os(l, now, gs, FA.get_outcomes(s)) == SAW.r_req.label_os(l, now, gs, _) : Wr.Dec<FA.Req>}
      ar.label_os(l, now, gs, FA.get_outcomes(s))
    case Wr.Bad{}:
      {==}

def ar.label_now(l: V.Label, d: Wr.Dec<Nat>) -> {FA.get_req.label_now(l, d) == SAW.r_req.label_now(l, d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{+now, +s}:
      %LSR.sr.gauges(s) : {FA.get_req.label_gs(l, now, FS.get_gauges(s)) == SAW.r_req.label_gs(l, now, _) : Wr.Dec<FA.Req>}
      ar.label_gs(l, now, FS.get_gauges(s))
    case Wr.Bad{}:
      {==}

def ar.label(d: Wr.Dec<V.Label>) -> {FA.get_req.label(d) == SAW.r_req.label(d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{l, s}:
      ar.label_now(l, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ar.exit_os(base: Nat, now: Nat, slots: List<&2, V.Slot>, gs: List<&2, St.Gauge>, d: Wr.Dec<List<&2, At.Outcome>>) -> {FA.get_req.exit_os(base, now, slots, gs, d) == SAW.r_req.exit_os(base, now, slots, gs, d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{os, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ar.exit_gs(base: Nat, now: Nat, slots: List<&2, V.Slot>, d: Wr.Dec<List<&2, St.Gauge>>) -> {FA.get_req.exit_gs(base, now, slots, d) == SAW.r_req.exit_gs(base, now, slots, d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{+gs, +s}:
      %ar.outcomes(s) : {FA.get_req.exit_os(base, now, slots, gs, FA.get_outcomes(s)) == SAW.r_req.exit_os(base, now, slots, gs, _) : Wr.Dec<FA.Req>}
      ar.exit_os(base, now, slots, gs, FA.get_outcomes(s))
    case Wr.Bad{}:
      {==}

def ar.exit_slots(base: Nat, now: Nat, d: Wr.Dec<List<&2, V.Slot>>) -> {FA.get_req.exit_slots(base, now, d) == SAW.r_req.exit_slots(base, now, d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{+slots, +s}:
      %LSR.sr.gauges(s) : {FA.get_req.exit_gs(base, now, slots, FS.get_gauges(s)) == SAW.r_req.exit_gs(base, now, slots, _) : Wr.Dec<FA.Req>}
      ar.exit_gs(base, now, slots, FS.get_gauges(s))
    case Wr.Bad{}:
      {==}

def ar.exit_now(base: Nat, d: Wr.Dec<Nat>) -> {FA.get_req.exit_now(base, d) == SAW.r_req.exit_now(base, d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{+now, +s}:
      %LVR.vr.slots(s) : {FA.get_req.exit_slots(base, now, FV.get_slots(s)) == SAW.r_req.exit_slots(base, now, _) : Wr.Dec<FA.Req>}
      ar.exit_slots(base, now, FV.get_slots(s))
    case Wr.Bad{}:
      {==}

def ar.exit(d: Wr.Dec<Nat>) -> {FA.get_req.exit(d) == SAW.r_req.exit(d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{base, s}:
      ar.exit_now(base, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# the entry's decoder is the laws' reader
def ar.req(d: Wr.Dec<Nat>) -> {FA.get_req(d) == SAW.r_req(d) : Wr.Dec<FA.Req>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          ar.outcome_req(Wr.get_bool(s))
        case 1n:
          %LSR.sr.vlabel(Wr.get_nat(s)) : {FA.get_req.label(FS.get_vlabel(Wr.get_nat(s))) == SAW.r_req.label(_) : Wr.Dec<FA.Req>}
          ar.label(FS.get_vlabel(Wr.get_nat(s)))
        case 2n:
          ar.exit(Wr.get_nat(s))
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}
