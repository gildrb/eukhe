# eukhe: the proof of LAW tiny_elect_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (tiny_elect_entry_reads), so the entry answers the code's choice; each
# choice is the spec's (tiny_elect_spec, tiny_confirm_spec; the others
# compute) and each reply tag is the spec's spelling (te.act, te.check).

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_elect.bend as FTe
import ../../bend/wire.bend as Wr
import ../../laws/tiny.bend as Tiny
import ./tiny_elect_spec.bend as PTinyElectSpec
import ./tiny_confirm_spec.bend as PTinyConfirmSpec
import ./tiny_elect_entry_reads.bend as PTinyElectEntryReads

def te.act(a: Tn.Act) -> {FTe.act.tag(a) == Tiny.sp_w_act(a) : Nat}:
  match a:
    case Tn.Join{}:
      {==}
    case Tn.Replace{}:
      {==}
    case Tn.Start{}:
      {==}
    case Tn.Broken{}:
      {==}

def te.check(c: Tn.Check) -> {FTe.check.tag(c) == Tiny.sp_w_check(c) : Nat}:
  match c:
    case Tn.Serving{}:
      {==}
    case Tn.Mistagged{}:
      {==}
    case Tn.Vacant{}:
      {==}
    case Tn.Faulty{}:
      {==}

def te.reply(q: FTe.Req) -> {FTe.answer(q) == Tiny.sp_w_reply(q) : String}:
  match q:
    case FTe.QElect{+p, +m}:
      %Tiny.tiny_elect_spec(p, m) : {Wr.put_nat(FTe.act.tag(Tn.elect(p, m)), "") == Wr.put_nat(Tiny.sp_w_act(_), "") : String}
      %te.act(Tn.elect(p, m)) : {Wr.put_nat(FTe.act.tag(Tn.elect(p, m)), "") == Wr.put_nat(_, "") : String}
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
      %Tiny.tiny_confirm_spec(p, m) : {Wr.put_nat(FTe.check.tag(Tn.confirm(p, m)), "") == Wr.put_nat(Tiny.sp_w_check(_), "") : String}
      %te.check(Tn.confirm(p, m)) : {Wr.put_nat(FTe.check.tag(Tn.confirm(p, m)), "") == Wr.put_nat(_, "") : String}
      {==}
    case FTe.QBind{p}:
      match p:
        case Tn.Missing{}:
          {==}
        case Tn.Unreachable{}:
          {==}
        case Tn.Pong{t}:
          {==}
        case Tn.Odd{}:
          {==}
        case Tn.Garbled{}:
          {==}
        case Tn.Hung{}:
          {==}

def Tiny.tiny_elect_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FTe.Req>, FTe.get_req(Tiny.sp_w_req(q, "")), Wr.Got{q, ""}, Tiny.tiny_elect_entry_reads(q, "", h)) : {FTe.ffi.got(_) == Tiny.sp_w_reply(q) : String}
  te.reply(q)
