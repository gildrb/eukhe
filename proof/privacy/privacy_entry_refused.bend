# eukhe: the proof of LAW privacy_entry_refused
#
# PROOF: the refused state answers its error form, by the step's
# definition.

import Base
import ../../bend/ffi_privacy.bend as FP
import ../../bend/wire.bend as Wr
import ../../laws/privacy/entry.bend as PrivacyEntry

def PrivacyEntry.privacy_entry_refused(s):
  {==}
