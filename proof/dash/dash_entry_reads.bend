# eukhe: the proof of LAW dash_entry_reads
#
# PROOF: tags and rotations compute; a text reads back by
# wire_str_round_trip and the mode by wire_nat_round_trip (their sizes fit
# by the premise), so each stage of the decoder hands the next one exactly
# the rest after its field.

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash.bend as Dash
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ./base.bend as LA

def dr.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def dr.disk(f: Da.Disk, +rest: String, h: {Dash.sp_fit_disk(f) == True{} : Bool}) -> {FDa.get_file(Wr.get_nat(Dash.sp_w_disk(f, rest))) == Wr.Got{f, rest} : Wr.Dec<Da.Disk>}:
  match f:
    case Da.NoFile{}:
      {==}
    case Da.Unread{}:
      {==}
    case Da.Holds{+s}:
      %dr.str(s, rest, h) : {FDa.get_file.text(_) == Wr.Got{Da.Holds{s}, rest} : Wr.Dec<Da.Disk>}
      {==}
    case Da.Huge{}:
      {==}

def dr.disk_back(+f: Da.Disk, +rest: String, h: {Dash.sp_fit_disk(f) == True{} : Bool}) -> {Wr.Got{f, rest} == FDa.get_file(Wr.get_nat(Dash.sp_w_disk(f, rest))) : Wr.Dec<Da.Disk>}:
  Equal.sym(Wr.Dec<Da.Disk>, FDa.get_file(Wr.get_nat(Dash.sp_w_disk(f, rest))), Wr.Got{f, rest}, dr.disk(f, rest, h))

def dr.said(x: Da.Said, +rest: String, h: {Dash.sp_fit_said(x) == True{} : Bool}) -> {FDa.get_said(Wr.get_nat(Dash.sp_w_said(x, rest))) == Wr.Got{x, rest} : Wr.Dec<Da.Said>}:
  match x:
    case Da.Spoken{+t}:
      %dr.str(t, rest, h) : {FDa.get_said.spoken(_) == Wr.Got{Da.Spoken{t}, rest} : Wr.Dec<Da.Said>}
      {==}
    case Da.Overlong{}:
      {==}

def dr.said_back(+x: Da.Said, +rest: String, h: {Dash.sp_fit_said(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FDa.get_said(Wr.get_nat(Dash.sp_w_said(x, rest))) : Wr.Dec<Da.Said>}:
  Equal.sym(Wr.Dec<Da.Said>, FDa.get_said(Wr.get_nat(Dash.sp_w_said(x, rest))), Wr.Got{x, rest}, dr.said(x, rest, h))

def dr.rotation(o: Da.Rotation, -rest: String) -> {Wr.Got{o, rest} == FDa.get_rotation(Wr.get_nat(Wr.put_nat(Dash.sp_w_rotation(o), rest))) : Wr.Dec<Da.Rotation>}:
  match o:
    case Da.KeepToken{}:
      {==}
    case Da.RotateToken{}:
      {==}

def dr.req(q: FDa.Req, +rest: String, h: {Dash.sp_fit_req(q) == True{} : Bool}) -> {FDa.get_req(Dash.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FDa.Req>}:
  match q:
    case FDa.QToken{+t}:
      %dr.said_back(t, rest, h) : {FDa.get_token(_) == Wr.Got{FDa.QToken{t}, rest} : Wr.Dec<FDa.Req>}
      {==}
    case FDa.QStored{+f}:
      %dr.disk_back(f, rest, h) : {FDa.get_stored(_) == Wr.Got{FDa.QStored{f}, rest} : Wr.Dec<FDa.Req>}
      {==}
    case FDa.QKeep{+o, +f, +m}:
      +hh = h
      +r2 = Wr.put_nat(m, rest)
      +r1 = Dash.sp_w_disk(f, r2)
      %dr.rotation(o, r1) : {FDa.get_keep(_) == Wr.Got{FDa.QKeep{o, f, m}, rest} : Wr.Dec<FDa.Req>}
      %dr.disk_back(f, r2, LA.pe.and_l(Dash.sp_fit_disk(f), LawsBase.wire_fits(m), hh)) : {FDa.get_keep.file(o, _) == Wr.Got{FDa.QKeep{o, f, m}, rest} : Wr.Dec<FDa.Req>}
      %LWire.pc.nat(m, rest, LA.pe.and_r(Dash.sp_fit_disk(f), LawsBase.wire_fits(m), hh)) : {FDa.get_keep.mode(o, f, _) == Wr.Got{FDa.QKeep{o, f, m}, rest} : Wr.Dec<FDa.Req>}
      {==}

def Dash.dash_entry_reads(q, rest, h):
  dr.req(q, rest, h)
