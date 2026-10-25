# eukhe: the proof of LAW redirect_input_text_spec
#
# PROOF: by the failure's case (rib.text).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../bend/ffi_redirect_input.bend as FRi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/redirect_input.bend as RedirectInput
import ./base.bend as LA

def RedirectInput.redirect_input_text_spec(f):
  LA.rib.text(f)
