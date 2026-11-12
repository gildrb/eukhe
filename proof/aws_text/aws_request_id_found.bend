# eukhe: the proof of LAW aws_request_id_found
#
# PROOF: what rid.index answers from 0 is 0 plus the place of a request-id
# header (awf.rid_found); d + 0 is d.

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base/first.bend as LF

def arf.fin(+names: List<&2, String>, -i: Nat, s: LF.awf.RF(names, 0n, i)) -> {AwsText.sp_rid_at(names, i) == True{} : Bool}:
  (+d, (sr, e)) = s
  %Equal.trans(Nat, d, Nat.add(d, 0n), i, Equal.sym(Nat, Nat.add(d, 0n), d, LF.awf.add_zero(d)), e) : {AwsText.sp_rid_at(names, _) == True{} : Bool}
  sr

def AwsText.aws_request_id_found(names, i, h):
  arf.fin(names, i, LF.awf.rid_found(names, 0n, i, h))
