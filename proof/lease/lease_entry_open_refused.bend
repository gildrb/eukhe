# eukhe: the proof of LAW lease_entry_open_refused

import Base
import ../../bend/lease.bend as Ls
import ../../bend/ffi_lease.bend as FLs
import ../../laws/lease.bend as Lease

def leo.go(+s: String, h: {String.is_empty(s) == False{} : Bool}) -> {FLs.open(s) == (FLs.Shut{}, SCon{'E', SCon{' ', "lease: the open takes no input"}}) : FLs.St & String}:
  %Equal.sym(Bool, String.is_empty(s), False{}, h) : {FLs.open.go(_) == (FLs.Shut{}, SCon{'E', SCon{' ', "lease: the open takes no input"}}) : FLs.St & String}
  {==}

def Lease.lease_entry_open_refused(s, h):
  leo.go(s, h)
