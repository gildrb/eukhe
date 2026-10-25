# eukhe: the proof of LAW codemode_describe_ffi_reads

import Base
import ../../bend/codemode_describe.bend as Dsc
import ../../bend/ffi_codemode_describe.bend as FDsc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/codemode_describe.bend as CodemodeDescribe
import ./base/read.bend as LACdRead

# PROOF of LAW codemode_describe_ffi_reads: each decoder reads its spelled value back, the rest untouched (cdq.req).

def CodemodeDescribe.codemode_describe_ffi_reads(q, rest, h):
  LACdRead.cdq.req(q, rest, h)
