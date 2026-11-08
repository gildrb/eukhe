# eukhe: the proof of LAW privacy_ipv6_decides
#
# PROOF: the reader reads the text a shaped address writes back as that
# address, up to t (pdc.read_full, pdc.read_gap, pdc.read_q; an address
# with no group and no IPv4 is never counted, pdc.v6_bad); from what it
# reads, its decision is the spec's (pdc.from_got).

import Base
import ./base/decide.bend as LDc
import ../../laws/privacy/ip.bend as PrivacyIp

def PrivacyIp.privacy_ipv6_decides(a, before, t, sh, st):
  LDc.pdc.decides(a, before, t, sh, st)
