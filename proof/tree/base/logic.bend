# eukhe: lemmas the proofs of area tree share: logic

import Base

def pt.CD(c: Cmp, l: Type, e: Type, g: Type) -> Type:
  match c:
    case LT{}:
      l
    case EQ{}:
      e
    case GT{}:
      g

# Membership
# ----------

def pt.void(-A: Type, e: Empty) -> A:
  match e:
