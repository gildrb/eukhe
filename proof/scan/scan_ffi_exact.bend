# eukhe: the proof of LAW scan_ffi_exact

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../base/logic/logic.bend as LLogicLogic
import ../../laws/scan.bend as Scan
import ./base.bend as LAScan

# PROOF of LAW scan_ffi_exact: a reply that is not the error form comes from tags read one by one, each decoded number its encoding (wire_nat_exact), the request spelled so far carried along (Equal.trans, Equal.cong), nothing left at the end (sc_ex, sc_asked, sc_cursor, sc_after, sc_mark, sc_fallback, sc_idc, sc_ida).

def Scan.scan_ffi_exact(x, ok):
  LAScan.sc_ex(x, Wr.get_nat(x), {==}, ok)
