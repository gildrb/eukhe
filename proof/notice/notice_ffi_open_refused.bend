# eukhe: the proof of LAW notice_ffi_open_refused

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ./base.bend as LA

def nfo.go(+s: String, h: {String.is_empty(s) == False{} : Bool}) -> {FNo.open(s) == (FNo.Shut{}, Wr.err("notice: the open takes no input")) : FNo.St & String}:
  %Equal.sym(Bool, String.is_empty(s), False{}, h) : {FNo.open.go(_) == (FNo.Shut{}, Wr.err("notice: the open takes no input")) : FNo.St & String}
  {==}

def Notice.notice_ffi_open_refused(s, h):
  nfo.go(s, h)
