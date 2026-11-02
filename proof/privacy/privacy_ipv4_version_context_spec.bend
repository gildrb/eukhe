# eukhe: the proof of LAW privacy_ipv4_version_context_spec
#
# PROOF: each symbol the grammar reads stands for the spec's kind of its
# char (pcx.kind_of); the line, its blanks and punctuation dropped, the
# operator and the last word are then the spec's, step by step, over
# those kinds (pcx.vctx, proof/privacy/base/context.bend).

import Base
import ../../bend/privacy/context.bend as Cx
import ../../spec/harness/privacy_context.bend as Sv
import ./base/context.bend as LCx
import ../../laws/privacy/ip.bend as PrivacyIp

def PrivacyIp.privacy_ipv4_version_context_spec(before):
  LCx.pcx.vctx(before)
