# eukhe: the proof of LAW commit_entry_reads
#
# PROOF: tags compute; every field reads back by the wire's round trips
# (each length and count fits by the premise): the lists item by item
# (dcw.mets/fates/strs/ents.back), a Pub, a Base and a Disk
# (dcw.rd_*), so each stage of the decoder hands the next one exactly the
# rest after its field.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../bend/ffi_doc_commit.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./base.bend as LA
import ./entry/wire.bend as LE
import ./entry/list_met.bend as LM
import ./entry/list_fate.bend as LFa
import ./entry/list_strs.bend as LS
import ./entry/list_ents.bend as LN
import ./entry/fields.bend as LF

def dcw.reads(q: FCm.Req, +rest: String, h: {DocCommit.sp_fit_req(q) == True{} : Bool}) -> {FCm.get_req(DocCommit.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FCm.Req>}:
  match q:
    case FCm.QCheck{+ms}:
      %LM.dcw.mets.back(ms, rest, h) : {FCm.get_check(_) == Wr.Got{FCm.QCheck{ms}, rest} : Wr.Dec<FCm.Req>}
      {==}
    case FCm.QPublish{+p}:
      %LF.dcw.rd_pub_back(p, rest) : {FCm.get_publish(_) == Wr.Got{FCm.QPublish{p}, rest} : Wr.Dec<FCm.Req>}
      {==}
    case FCm.QAnswer{+fs}:
      %LFa.dcw.fates.back(fs, rest, h) : {FCm.get_answer(_) == Wr.Got{FCm.QAnswer{fs}, rest} : Wr.Dec<FCm.Req>}
      {==}
    case FCm.QGate{+b, +d}:
      +hh = h
      %LF.dcw.rd_base_back(b, DocCommit.sp_w_disk(d, rest), LA.dcw.and_l(DocCommit.sp_fit_base(b), DocCommit.sp_fit_disk(d), hh)) : {FCm.get_gate(_) == Wr.Got{FCm.QGate{b, d}, rest} : Wr.Dec<FCm.Req>}
      %LF.dcw.rd_disk_back(d, rest, LA.dcw.and_r(DocCommit.sp_fit_base(b), DocCommit.sp_fit_disk(d), hh)) : {FCm.get_gate.disk(b, _) == Wr.Got{FCm.QGate{b, d}, rest} : Wr.Dec<FCm.Req>}
      {==}
    case FCm.QSeen{+d, +xs}:
      +hh = h
      +fr = LA.dcw.and_r(LawsBase.wire_fits(String.length(d)), Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), DocCommit.sp_fit_strs(xs)), hh)
      %LE.dcw.str_back(d, Wr.put_list(~String, ~Wr.put_str, xs, rest), LA.dcw.and_l(LawsBase.wire_fits(String.length(d)), Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), DocCommit.sp_fit_strs(xs)), hh)) : {FCm.get_seen(_) == Wr.Got{FCm.QSeen{d, xs}, rest} : Wr.Dec<FCm.Req>}
      %LS.dcw.strs.back(xs, rest, LA.dcw.and_l(LawsBase.wire_fits(List.length(&2, String, xs)), DocCommit.sp_fit_strs(xs), fr), LA.dcw.and_r(LawsBase.wire_fits(List.length(&2, String, xs)), DocCommit.sp_fit_strs(xs), fr)) : {FCm.get_seen.list(d, _) == Wr.Got{FCm.QSeen{d, xs}, rest} : Wr.Dec<FCm.Req>}
      {==}
    case FCm.QPrefix{+hs}:
      %LE.dcw.str_back(hs, rest, h) : {FCm.get_prefix(_) == Wr.Got{FCm.QPrefix{hs}, rest} : Wr.Dec<FCm.Req>}
      {==}
    case FCm.QSweep{+hs, +es}:
      +hh = h
      +fr = LA.dcw.and_r(LawsBase.wire_fits(String.length(hs)), Bool.and(LawsBase.wire_fits(List.length(&2, Cm.Ent, es)), DocCommit.sp_fit_ents(es)), hh)
      %LE.dcw.str_back(hs, Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, es, rest), LA.dcw.and_l(LawsBase.wire_fits(String.length(hs)), Bool.and(LawsBase.wire_fits(List.length(&2, Cm.Ent, es)), DocCommit.sp_fit_ents(es)), hh)) : {FCm.get_sweep(_) == Wr.Got{FCm.QSweep{hs, es}, rest} : Wr.Dec<FCm.Req>}
      %LN.dcw.ents.back(es, rest, LA.dcw.and_l(LawsBase.wire_fits(List.length(&2, Cm.Ent, es)), DocCommit.sp_fit_ents(es), fr), LA.dcw.and_r(LawsBase.wire_fits(List.length(&2, Cm.Ent, es)), DocCommit.sp_fit_ents(es), fr)) : {FCm.get_sweep.ents(hs, _) == Wr.Got{FCm.QSweep{hs, es}, rest} : Wr.Dec<FCm.Req>}
      {==}

def DocCommit.commit_entry_reads(q, rest, h):
  dcw.reads(q, rest, h)
