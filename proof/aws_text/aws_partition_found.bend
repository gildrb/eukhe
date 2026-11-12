# eukhe: the proof of LAW aws_partition_found
#
# PROOF: what partition.go answers from 0 is the row j of a prefix, at a
# place n, whose shape the region has (awf.go_found); each such (j, n) of
# the code's table is an entry k of the AWS table with the same prefix and
# partition j (closed, case by case); no other (j, n) holds a prefix.

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ../model_name/base.bend as LA
import ./base/first.bend as LF

def apf.G(r: String, i: Nat) -> Type:
  Sigma<&1, &1, Nat, k => {Nat.is_lt(k, 16n) == True{} : Bool} & ({A.shape(AwsText.sp_aws_prefix(k), r) == True{} : Bool} & {AwsText.sp_aws_part(k) == i : Nat})>

def apf.cell(+r: String, -i: Nat, j: Nat, n: Nat, a: {LF.awf.at(LF.awf.row(A.partitions(), j), n, r) == True{} : Bool}, e: {Nat.add(j, 0n) == i : Nat}) -> apf.G(r, i):
  match j:
    case 0n:
      match n:
        case 0n:
          (0n, ({==}, (a, e)))
        case 1n:
          (1n, ({==}, (a, e)))
        case 2n:
          (2n, ({==}, (a, e)))
        case 3n:
          (3n, ({==}, (a, e)))
        case 4n:
          (4n, ({==}, (a, e)))
        case 5n:
          (5n, ({==}, (a, e)))
        case 6n:
          (6n, ({==}, (a, e)))
        case 7n:
          (7n, ({==}, (a, e)))
        case 8n:
          (8n, ({==}, (a, e)))
        case 9n+x:
          LA.mnb.absurd_f(apf.G(r, i), a)
    case 1n:
      match n:
        case 0n:
          (9n, ({==}, (a, e)))
        case 1n+x:
          LA.mnb.absurd_f(apf.G(r, i), a)
    case 2n:
      match n:
        case 0n:
          (10n, ({==}, (a, e)))
        case 1n+x:
          LA.mnb.absurd_f(apf.G(r, i), a)
    case 3n:
      match n:
        case 0n:
          (11n, ({==}, (a, e)))
        case 1n+x:
          LA.mnb.absurd_f(apf.G(r, i), a)
    case 4n:
      match n:
        case 0n:
          (12n, ({==}, (a, e)))
        case 1n+x:
          LA.mnb.absurd_f(apf.G(r, i), a)
    case 5n:
      match n:
        case 0n:
          (13n, ({==}, (a, e)))
        case 1n+x:
          LA.mnb.absurd_f(apf.G(r, i), a)
    case 6n:
      match n:
        case 0n:
          (14n, ({==}, (a, e)))
        case 1n+x:
          LA.mnb.absurd_f(apf.G(r, i), a)
    case 7n:
      match n:
        case 0n:
          (15n, ({==}, (a, e)))
        case 1n+x:
          LA.mnb.absurd_f(apf.G(r, i), a)
    case 8n+x:
      LA.mnb.absurd_f(apf.G(r, i), a)

def apf.fin(+r: String, -i: Nat, s: LF.awf.GF(A.partitions(), r, 0n, i)) -> apf.G(r, i):
  (+j, (+n, (a, e))) = s
  apf.cell(r, i, j, n, a, e)

def AwsText.aws_partition_found(r, i, h):
  apf.fin(r, i, LF.awf.go_found(A.partitions(), r, 0n, i, h))
