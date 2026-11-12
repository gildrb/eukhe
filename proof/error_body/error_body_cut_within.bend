# eukhe: the proof of LAW error_body_cut_within
#
# PROOF: the code counts a text's chars and its chars past U+FFFF
# (LA.ebu.units), within the cap, so it keeps the text.

import Base
import ../../bend/error_body.bend as Eb
import ../../laws/error_body.bend as ErrorBody
import ../base/staging.bend as LStg
import ./base.bend as LA

def ErrorBody.error_body_cut_within(text, cap, h):
  %Equal.sym(Nat, Eb.units(text), ErrorBody.sp_units(text), LA.ebu.units(text)) : {Eb.truncate.at(text, cap, _, Nat.is_le(_, cap)) == text : String}
  %Equal.sym(Bool, Nat.is_le(ErrorBody.sp_units(text), cap), True{}, h) : {Eb.truncate.at(text, cap, ErrorBody.sp_units(text), _) == text : String}
  {==}
