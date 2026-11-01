# eukhe: the proof of LAW privacy_ipv4_decides
#
# PROOF: the grammar's chars before the address are the spec's (pd4.edge4);
# it reads the four octets back with what follows them (LQd.pqd.quad_read),
# whose chars it judges as the spec does (pd4.after4), with the length the
# octets write (pd4.len4); case analysis on the gate (pd4.go).

import Base
import ./base/v4.bend as LV4
import ../../laws/privacy/ip.bend as PrivacyIp

def PrivacyIp.privacy_ipv4_decides(q, before, t, ok, st):
  LV4.pd4.decides(q, before, t, ok, st)
