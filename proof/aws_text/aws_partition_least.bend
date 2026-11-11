# eukhe: the proof of LAW aws_partition_least
#
# PROOF: entry k of the AWS table is the prefix at place n of row j of the
# code's table (closed, case by case); its shape makes shapes of that row
# True (awf.shapes_hit), so partition.go answers from 0 at most j
# (awf.go_hit), which is the entry's partition.

import Base
import ../../bend/aws_text.bend as A
import ../../laws/aws_text.bend as AwsText
import ../model_name/base.bend as LA
import ./base/first.bend as LF

def apl.G(r: String, k: Nat) -> Type:
  Sigma<&1, &1, Nat, i => {A.partition(r) == Some{i} : Maybe<&2, Nat>} & {Nat.is_le(i, AwsText.sp_aws_part(k)) == True{} : Bool}>

# no k + 16 is below 16
def apl.past(+r: String, x: Nat, hk: {Nat.is_lt(x, 0n) == True{} : Bool}) -> apl.G(r, 16n+x):
  match x:
    case 0n:
      LA.mnb.absurd_f(apl.G(r, 16n), hk)
    case 1n+y:
      LA.mnb.absurd_f(apl.G(r, 17n+y), hk)

def AwsText.aws_partition_least(r, k, hk, hs):
  match k:
    case 0n:
      LF.awf.go_hit(A.partitions(), 0n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 0n), 0n, r, hs))
    case 1n:
      LF.awf.go_hit(A.partitions(), 0n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 0n), 1n, r, hs))
    case 2n:
      LF.awf.go_hit(A.partitions(), 0n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 0n), 2n, r, hs))
    case 3n:
      LF.awf.go_hit(A.partitions(), 0n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 0n), 3n, r, hs))
    case 4n:
      LF.awf.go_hit(A.partitions(), 0n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 0n), 4n, r, hs))
    case 5n:
      LF.awf.go_hit(A.partitions(), 0n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 0n), 5n, r, hs))
    case 6n:
      LF.awf.go_hit(A.partitions(), 0n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 0n), 6n, r, hs))
    case 7n:
      LF.awf.go_hit(A.partitions(), 0n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 0n), 7n, r, hs))
    case 8n:
      LF.awf.go_hit(A.partitions(), 0n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 0n), 8n, r, hs))
    case 9n:
      LF.awf.go_hit(A.partitions(), 1n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 1n), 0n, r, hs))
    case 10n:
      LF.awf.go_hit(A.partitions(), 2n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 2n), 0n, r, hs))
    case 11n:
      LF.awf.go_hit(A.partitions(), 3n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 3n), 0n, r, hs))
    case 12n:
      LF.awf.go_hit(A.partitions(), 4n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 4n), 0n, r, hs))
    case 13n:
      LF.awf.go_hit(A.partitions(), 5n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 5n), 0n, r, hs))
    case 14n:
      LF.awf.go_hit(A.partitions(), 6n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 6n), 0n, r, hs))
    case 15n:
      LF.awf.go_hit(A.partitions(), 7n, r, 0n, LF.awf.shapes_hit(LF.awf.row(A.partitions(), 7n), 0n, r, hs))
    case 16n+x:
      apl.past(r, x, hk)
