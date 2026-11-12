# eukhe: lemmas of area budget shared by its proofs: the amount of a sum,
# of a difference and of zero in one dimension (bend/budget.bend add4,
# sub4, zero against spec/budget/ledger.bend at)

import Base
import ../../../bend/budget.bend as B
import ../../../spec/budget/ledger.bend as S

# a sum of amounts is the sum in each dimension
def ba.at_add4(d: B.Dim, x: B.Amt, y: B.Amt) -> {S.at(d, B.add4(x, y)) == Nat.add(S.at(d, x), S.at(d, y)) : Nat}:
  match d:
    case B.Cost{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Tok{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Time{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Calls{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Reqs{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}

# a difference of amounts is the difference in each dimension
def ba.at_sub4(d: B.Dim, x: B.Amt, y: B.Amt) -> {S.at(d, B.sub4(x, y)) == Nat.sub(S.at(d, x), S.at(d, y)) : Nat}:
  match d:
    case B.Cost{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Tok{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Time{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Calls{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}
    case B.Reqs{}:
      match x:
        case B.Amt{xc, xk, xn, xr}:
          match y:
            case B.Amt{yc, yk, yn, yr}:
              {==}

# zero is zero in each dimension
def ba.at_zero(d: B.Dim) -> {S.at(d, B.zero()) == 0n : Nat}:
  match d:
    case B.Cost{}:
      {==}
    case B.Tok{}:
      {==}
    case B.Time{}:
      {==}
    case B.Calls{}:
      {==}
    case B.Reqs{}:
      {==}
