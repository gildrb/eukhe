# eukhe: the proof of LAW overflow_length_reply
#
# PROOF: a length reply is no error and no stop, so only its usage test counts: a window, no output, and the reads at least the window minus a hundredth of it rounded down; that bound is the exact one (olr.main): w - d <= u exactly when w - u <= d (olr.swap), and x <= w / 100 exactly when 100 x <= w (olr.div, by induction on x with the window split at 100).

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/overflow.bend as O
import ../../bend/ffi_overflow.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as Overflow
import ./base.bend as LA
import ../base/pair.bend as LPair

# 0 is at most every x
def olr.le0(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# x - 0 is x
def olr.sub0(x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a - (1 + b) <= d exactly when a - b <= 1 + d
def olr.shift(a: Nat, b: Nat, +d: Nat) -> {Nat.is_le(Nat.sub(a, 1n+b), d) == Nat.is_le(Nat.sub(a, b), 1n+d) : Bool}:
  match a:
    case 0n:
      olr.le0(d)
    case 1n++ap:
      match b:
        case 0n:
          %Equal.sym(Nat, Nat.sub(ap, 0n), ap, olr.sub0(ap)) : {Nat.is_le(_, d) == Nat.is_le(ap, d) : Bool}
          {==}
        case 1n+bp:
          olr.shift(ap, bp, d)

# w - d <= u exactly when w - u <= d (truncated subtraction, every w, d, u)
def olr.swap(w: Nat, +d: Nat, +u: Nat) -> {Nat.is_le(Nat.sub(w, d), u) == Nat.is_le(Nat.sub(w, u), d) : Bool}:
  match w:
    case 0n:
      Equal.trans(Bool, Nat.is_le(0n, u), True{}, Nat.is_le(0n, d), olr.le0(u), Equal.sym(Bool, Nat.is_le(0n, d), True{}, olr.le0(d)))
    case 1n++wp:
      match d:
        case 0n:
          match u:
            case 0n:
              {==}
            case 1n++up:
              %olr.sub0(wp) : {Nat.is_le(_, up) == Nat.is_le(Nat.sub(wp, up), 0n) : Bool}
              olr.swap(wp, 0n, up)
        case 1n++dp:
          match u:
            case 0n:
              %olr.sub0(wp) : {Nat.is_le(Nat.sub(wp, dp), 0n) == Nat.is_le(_, dp) : Bool}
              olr.swap(wp, dp, 0n)
            case 1n++up:
              Equal.trans(Bool, Nat.is_le(Nat.sub(wp, dp), 1n+up), Nat.is_le(Nat.sub(wp, 1n+up), dp), Nat.is_le(Nat.sub(wp, up), 1n+dp), olr.swap(wp, dp, 1n+up), olr.shift(wp, up, dp))

# x is at most w / 100 (rounded down) exactly when 100 x is at most w: by
# induction on x, a window below 100 holding no hundred and one of 100 or
# more holding one more hundred than the window 100 smaller
def olr.div(x: Nat, +w: Nat) -> {Nat.is_le(x, Nat.div(w, 100n)) == Nat.is_le(Nat.mul(x, 100n), w) : Bool}:
  match x:
    case 0n:
      Equal.trans(Bool, Nat.is_le(0n, Nat.div(w, 100n)), True{}, Nat.is_le(0n, w), olr.le0(Nat.div(w, 100n)), Equal.sym(Bool, Nat.is_le(0n, w), True{}, olr.le0(w)))
    case 1n++xp:
      match w:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n:
          {==}
        case 9n:
          {==}
        case 10n:
          {==}
        case 11n:
          {==}
        case 12n:
          {==}
        case 13n:
          {==}
        case 14n:
          {==}
        case 15n:
          {==}
        case 16n:
          {==}
        case 17n:
          {==}
        case 18n:
          {==}
        case 19n:
          {==}
        case 20n:
          {==}
        case 21n:
          {==}
        case 22n:
          {==}
        case 23n:
          {==}
        case 24n:
          {==}
        case 25n:
          {==}
        case 26n:
          {==}
        case 27n:
          {==}
        case 28n:
          {==}
        case 29n:
          {==}
        case 30n:
          {==}
        case 31n:
          {==}
        case 32n:
          {==}
        case 33n:
          {==}
        case 34n:
          {==}
        case 35n:
          {==}
        case 36n:
          {==}
        case 37n:
          {==}
        case 38n:
          {==}
        case 39n:
          {==}
        case 40n:
          {==}
        case 41n:
          {==}
        case 42n:
          {==}
        case 43n:
          {==}
        case 44n:
          {==}
        case 45n:
          {==}
        case 46n:
          {==}
        case 47n:
          {==}
        case 48n:
          {==}
        case 49n:
          {==}
        case 50n:
          {==}
        case 51n:
          {==}
        case 52n:
          {==}
        case 53n:
          {==}
        case 54n:
          {==}
        case 55n:
          {==}
        case 56n:
          {==}
        case 57n:
          {==}
        case 58n:
          {==}
        case 59n:
          {==}
        case 60n:
          {==}
        case 61n:
          {==}
        case 62n:
          {==}
        case 63n:
          {==}
        case 64n:
          {==}
        case 65n:
          {==}
        case 66n:
          {==}
        case 67n:
          {==}
        case 68n:
          {==}
        case 69n:
          {==}
        case 70n:
          {==}
        case 71n:
          {==}
        case 72n:
          {==}
        case 73n:
          {==}
        case 74n:
          {==}
        case 75n:
          {==}
        case 76n:
          {==}
        case 77n:
          {==}
        case 78n:
          {==}
        case 79n:
          {==}
        case 80n:
          {==}
        case 81n:
          {==}
        case 82n:
          {==}
        case 83n:
          {==}
        case 84n:
          {==}
        case 85n:
          {==}
        case 86n:
          {==}
        case 87n:
          {==}
        case 88n:
          {==}
        case 89n:
          {==}
        case 90n:
          {==}
        case 91n:
          {==}
        case 92n:
          {==}
        case 93n:
          {==}
        case 94n:
          {==}
        case 95n:
          {==}
        case 96n:
          {==}
        case 97n:
          {==}
        case 98n:
          {==}
        case 99n:
          {==}
        case 100n++v:
          %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(v, 99n, 1n, 0n)), 1n+Pair.fst(Nat, Nat, Nat.divmod.go(v, 99n, 0n, 0n)), LPair.wn_dm_fst(v, 99n, 0n, 0n)) : {Nat.is_le(1n+xp, _) == Nat.is_le(Nat.mul(1n+xp, 100n), 100n+v) : Bool}
          olr.div(xp, v)

# the code's 99% bound (the window minus a hundredth of it rounded down) is
# the exact one: the reads fall short of the window by at most a hundredth
# of it
def olr.main(+w: Nat, +u: Nat) -> {Nat.is_le(Nat.sub(w, Nat.div(w, 100n)), u) == Nat.is_le(Nat.mul(Nat.sub(w, u), 100n), w) : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.sub(w, Nat.div(w, 100n)), u), Nat.is_le(Nat.sub(w, u), Nat.div(w, 100n)), Nat.is_le(Nat.mul(Nat.sub(w, u), 100n), w), olr.swap(w, Nat.div(w, 100n), u), olr.div(Nat.sub(w, u), w))

def Overflow.overflow_length_reply(msg, provider, window, input, cache_read, output):
  +u = Nat.add(input, cache_read)
  %Equal.sym(Bool, Nat.is_le(Nat.sub(window, Nat.div(window, 100n)), u), Nat.is_le(Nat.mul(Nat.sub(window, u), 100n), window), olr.main(window, u)) : {Bool.and(Nat.is_lt(0n, window), Bool.and(Nat.is_eq(output, 0n), _)) == Bool.and(Nat.is_lt(0n, window), Bool.and(Nat.is_eq(output, 0n), Nat.is_le(Nat.mul(Nat.sub(window, u), 100n), window))) : Bool}
  {==}
