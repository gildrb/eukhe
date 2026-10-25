# eukhe: the proof of LAW dash_access_entry_reads
#
# PROOF: the tag computes; each text reads back by wire_str_round_trip and
# the allowed hosts by the list round trip of the doc_commit entry
# (dcw.strs.rt; their lengths fit by the premise), so each stage of the
# decoder hands the next one exactly the rest after its field.

import Base
import ../../bend/ffi_dash_access.bend as FAc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash_access.bend as DashAccess
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../doc_commit/base.bend as LADocCommit
import ../doc_commit/entry/list_strs.bend as LS
import ./base.bend as LA

def dar.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def dar.req(q: FAc.Req, +rest: String, h: {DashAccess.sp_fit_req(q) == True{} : Bool}) -> {FAc.get_req(DashAccess.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FAc.Req>}:
  match q:
    case FAc.QHost{+hh, +al}:
      +hq = h
      +fs = LADocCommit.dcw.and_r(LawsBase.wire_fits(String.length(hh)), Bool.and(LawsBase.wire_fits(List.length(&2, String, al)), DashAccess.sp_fit_strs(al)), hq)
      +fn = LADocCommit.dcw.and_l(LawsBase.wire_fits(List.length(&2, String, al)), DashAccess.sp_fit_strs(al), fs)
      +fd = Equal.trans(Bool, DocCommit.sp_fit_strs(al), DashAccess.sp_fit_strs(al), True{}, Equal.sym(Bool, DashAccess.sp_fit_strs(al), DocCommit.sp_fit_strs(al), LA.dab.fits(al)), LADocCommit.dcw.and_r(LawsBase.wire_fits(List.length(&2, String, al)), DashAccess.sp_fit_strs(al), fs))
      +l = Wr.put_list(~String, ~Wr.put_str, al, rest)
      %dar.str(hh, l, LADocCommit.dcw.and_l(LawsBase.wire_fits(String.length(hh)), Bool.and(LawsBase.wire_fits(List.length(&2, String, al)), DashAccess.sp_fit_strs(al)), hq)) : {FAc.get_host(_) == Wr.Got{FAc.QHost{hh, al}, rest} : Wr.Dec<FAc.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, l), Wr.Got{al, rest}, LS.dcw.strs.rt(al, rest, fn, fd)) : {FAc.get_host.allowed(hh, _) == Wr.Got{FAc.QHost{hh, al}, rest} : Wr.Dec<FAc.Req>}
      {==}
    case FAc.QOrigin{+o, +hh}:
      +hq = h
      %dar.str(o, Wr.put_str(hh, rest), LADocCommit.dcw.and_l(LawsBase.wire_fits(String.length(o)), LawsBase.wire_fits(String.length(hh)), hq)) : {FAc.get_origin(_) == Wr.Got{FAc.QOrigin{o, hh}, rest} : Wr.Dec<FAc.Req>}
      %dar.str(hh, rest, LADocCommit.dcw.and_r(LawsBase.wire_fits(String.length(o)), LawsBase.wire_fits(String.length(hh)), hq)) : {FAc.get_origin.host(o, _) == Wr.Got{FAc.QOrigin{o, hh}, rest} : Wr.Dec<FAc.Req>}
      {==}

def DashAccess.dash_access_entry_reads(q, rest, h):
  dar.req(q, rest, h)
