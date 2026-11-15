# eukhe: the proof of LAW limits_notice_kept_once
#
# PROOF: the labels told of after are a list made once (notice.once),
# which holds no label twice whatever it came from (lto.once).

import Base
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ./limits_notice_told_once.bend as PNoticeToldOnce

def Limits.limits_notice_kept_once(ws, r, told):
  PNoticeToldOnce.lto.once(List.append(&2, String, L.notice.over(ws, Nat.sub(1000n, r)), L.notice.keep(told, L.notice.labels(ws))))
