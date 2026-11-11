# eukhe: the proof of LAW aws_request_id_least
#
# PROOF: a request-id header at place k makes rid.index answer, from 0, at
# most k + 0 (awf.rid_least); k + 0 is k.

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ./base/first.bend as LF

def arl.G(names: List<&2, String>, k: Nat) -> Type:
  Sigma<&1, &1, Nat, i => {A.request_id(names) == Some{i} : Maybe<&2, Nat>} & {Nat.is_le(i, k) == True{} : Bool}>

def arl.le(-i: Nat, k: Nat, le: {Nat.is_le(i, Nat.add(k, 0n)) == True{} : Bool}) -> {Nat.is_le(i, k) == True{} : Bool}:
  %LF.awf.add_zero(k) : {Nat.is_le(i, _) == True{} : Bool}
  le

def arl.fin(-names: List<&2, String>, +k: Nat, s: LF.awf.RL(names, 0n, k)) -> arl.G(names, k):
  (+i, (e, le)) = s
  (i, (e, arl.le(i, k, le)))

def AwsText.aws_request_id_least(names, k, h):
  arl.fin(names, k, LF.awf.rid_least(names, k, 0n, h))
