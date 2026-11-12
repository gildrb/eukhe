# eukhe: the proof of LAW verify_assign_resets
#
# PROOF: by the premise the Assign is the admitted one (LA.va.assign_is); its
# n open slots have length n and n open ones (LA.va.opens_length, LA.va.opens_count);
# the rest computes.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA

def Verify.verify_assign_resets(n, rev, slots, claimed, tries, few):
  %LA.va.assign_is(n, rev, slots, claimed, tries, few) : ({S.admitted(_) == True{} : Bool} & {List.length(&2, V.Slot, S.slots(S.after(_))) == n : Nat} & {S.opens(S.slots(S.after(_))) == n : Nat} & {S.rev(S.after(_)) == 1n+rev : Nat} & {S.claimed(S.after(_)) == False{} : Bool} & {S.tries(S.after(_)) == 0n : Nat})
  ({==}, (LA.va.opens_length(n), (LA.va.opens_count(n), ({==}, ({==}, {==})))))
