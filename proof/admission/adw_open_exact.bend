# eukhe: the proof of LAW adw_open_exact
# An open reads the limits as the spec reads them (LE.pae.get_open) and
# spells the controller as the spec does (LE.pae.live).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission/entry.bend as AdmissionEntry
import ./base/entry.bend as LE

def AdmissionEntry.adw_open_exact(s):
  LE.pae.open(s)
