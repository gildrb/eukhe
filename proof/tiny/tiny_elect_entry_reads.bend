# eukhe: the proof of LAW tiny_elect_entry_reads
#
# PROOF: tags compute; a probe's tag text and the launch tag read back by
# wire_str_round_trip (their lengths fit by the premise), so each stage
# of the decoder hands the next one exactly the rest after its field.

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_elect.bend as FTe
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny.bend as Tiny
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ./base.bend as LA

def te.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def te.probe(p: Tn.Probe, +rest: String, h: {Tiny.sp_fit_probe(p) == True{} : Bool}) -> {FTe.get_probe(Wr.get_nat(Tiny.sp_w_probe(p, rest))) == Wr.Got{p, rest} : Wr.Dec<Tn.Probe>}:
  match p:
    case Tn.Missing{}:
      {==}
    case Tn.Unreachable{}:
      {==}
    case Tn.Pong{+t}:
      %te.str(t, rest, h) : {FTe.get_probe.pong(_) == Wr.Got{Tn.Pong{t}, rest} : Wr.Dec<Tn.Probe>}
      {==}
    case Tn.Odd{}:
      {==}
    case Tn.Garbled{}:
      {==}
    case Tn.Hung{}:
      {==}

# a probe's spelling read back, as the decoder's stage sees it
def te.probe_back(+p: Tn.Probe, +rest: String, h: {Tiny.sp_fit_probe(p) == True{} : Bool}) -> {Wr.Got{p, rest} == FTe.get_probe(Wr.get_nat(Tiny.sp_w_probe(p, rest))) : Wr.Dec<Tn.Probe>}:
  Equal.sym(Wr.Dec<Tn.Probe>, FTe.get_probe(Wr.get_nat(Tiny.sp_w_probe(p, rest))), Wr.Got{p, rest}, te.probe(p, rest, h))

def te.req(q: FTe.Req, +rest: String, h: {Tiny.sp_fit_req(q) == True{} : Bool}) -> {FTe.get_req(Tiny.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FTe.Req>}:
  match q:
    case FTe.QElect{+p, +m}:
      +hh = h
      %te.probe_back(p, Wr.put_str(m, rest), LA.tiny.pn.and_l(Tiny.sp_fit_probe(p), LawsBase.wire_fits(String.length(m)), hh)) : {FTe.get_pm(True{}, _) == Wr.Got{FTe.QElect{p, m}, rest} : Wr.Dec<FTe.Req>}
      %te.str(m, rest, LA.tiny.pn.and_r(Tiny.sp_fit_probe(p), LawsBase.wire_fits(String.length(m)), hh)) : {FTe.get_pm.mine(True{}, p, _) == Wr.Got{FTe.QElect{p, m}, rest} : Wr.Dec<FTe.Req>}
      {==}
    case FTe.QShut{hd}:
      match hd:
        case Tn.Bye{}:
          {==}
        case Tn.Other{}:
          {==}
        case Tn.Eof{}:
          {==}
        case Tn.Lost{}:
          {==}
    case FTe.QLaunched{f, l}:
      match f l:
        case Tn.First{} Tn.Bound{}:
          {==}
        case Tn.First{} Tn.Adopted{}:
          {==}
        case Tn.Again{} Tn.Bound{}:
          {==}
        case Tn.Again{} Tn.Adopted{}:
          {==}
    case FTe.QConfirm{+p, +m}:
      +hh = h
      %te.probe_back(p, Wr.put_str(m, rest), LA.tiny.pn.and_l(Tiny.sp_fit_probe(p), LawsBase.wire_fits(String.length(m)), hh)) : {FTe.get_pm(False{}, _) == Wr.Got{FTe.QConfirm{p, m}, rest} : Wr.Dec<FTe.Req>}
      %te.str(m, rest, LA.tiny.pn.and_r(Tiny.sp_fit_probe(p), LawsBase.wire_fits(String.length(m)), hh)) : {FTe.get_pm.mine(False{}, p, _) == Wr.Got{FTe.QConfirm{p, m}, rest} : Wr.Dec<FTe.Req>}
      {==}
    case FTe.QBind{+p}:
      %te.probe_back(p, rest, h) : {FTe.get_bind(_) == Wr.Got{FTe.QBind{p}, rest} : Wr.Dec<FTe.Req>}
      {==}

def Tiny.tiny_elect_entry_reads(q, rest, h):
  te.req(q, rest, h)
