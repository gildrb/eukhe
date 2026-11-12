# eukhe: the proof of LAW notice_ffi_refused
#
# A refused open is the state Shut (notice_ffi_open_refused); from Shut,
# each step answers the refused-open error and stays Shut, so by induction
# on the inputs every reply after the open's is that error.

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ./notice_ffi_open_refused.bend as PNoticeFfiOpenRefused

# a refused stepper whose last reply was x: x, then the refused-open error
# for each input
def nfr.shut(ins: List<&2, String>, +x: String) -> {Notice.nt_feed(ins, (FNo.Shut{}, x)) == x <> Notice.nt_refused(ins) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case i <> t:
      +e = Wr.err("notice: the open was refused")
      Equal.cong(List<&2, String>, List<&2, String>, y => x <> y, Notice.nt_feed(t, (FNo.Shut{}, e)), e <> Notice.nt_refused(t), nfr.shut(t, e))

def nfr.go(+s: String, h: {String.is_empty(s) == False{} : Bool}, +ins: List<&2, String>) -> {Notice.nt_feed(ins, FNo.open(s)) == Wr.err("notice: the open takes no input") <> Notice.nt_refused(ins) : List<&2, String>}:
  +x = Wr.err("notice: the open takes no input")
  %Equal.sym(FNo.St & String, FNo.open(s), (FNo.Shut{}, x), Notice.notice_ffi_open_refused(s, h)) : {Notice.nt_feed(ins, _) == x <> Notice.nt_refused(ins) : List<&2, String>}
  nfr.shut(ins, x)

def Notice.notice_ffi_refused(s, h, ins):
  nfr.go(s, h, ins)
