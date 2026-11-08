# eukhe: the proof of LAW privacy_ip_v6_or_v4
#
# PROOF: the answer is the IPv6, else the IPv4, by its definition.

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../laws/privacy/ip.bend as PrivacyIp

def PrivacyIp.privacy_ip_v6_or_v4(before, rest):
  {==}
