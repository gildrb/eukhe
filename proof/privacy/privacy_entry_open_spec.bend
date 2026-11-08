# eukhe: the proof of LAW privacy_entry_open_spec
#
# PROOF: case on the input: none opens the empty map and its reply
# computes; any char is input left, which opens the refused state.

import Base
import ../../bend/privacy/token.bend as Tk
import ../../bend/ffi_privacy.bend as FP
import ../../laws/privacy/entry.bend as PrivacyEntry

def PrivacyEntry.privacy_entry_open_spec(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}
