# eukhe: the proof of LAW error_body_show_body
#
# PROOF: without a prefix both sides compute; with one, the code's
# `<q> (<s>): <x>` is the label then `: ` then x by appending's
# associativity (LA.ebs.label).

import Base
import ../../bend/error_body.bend as Eb
import ../../laws/error_body.bend as ErrorBody
import ../base/staging.bend as LStg
import ./base.bend as LA

def ebsb.go(p: Maybe<&2, String>, +s: String, +x: String, -m: String) -> {Eb.show(False{}, Some{s}, Some{x}, p, m) == String.concat([ErrorBody.sp_label(p, s), ": ", x]) : String}:
  match p:
    case None{}:
      {==}
    case Some{q}:
      LA.ebs.label(q, s, x)

def ErrorBody.error_body_show_body(s, x, p, m):
  ebsb.go(p, s, x, m)
