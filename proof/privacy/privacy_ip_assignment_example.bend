# eukhe: the proof of LAW privacy_ip_assignment_example
#
# PROOF: closed: both sides compute.

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../spec/harness/privacy_context.bend as Sv
import ../../laws/privacy/ip.bend as PrivacyIp

def PrivacyIp.privacy_ip_assignment_example():
  ({==}, {==})
