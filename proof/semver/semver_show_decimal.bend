# eukhe: the proof of LAW semver_show_decimal

import Base
import ../../bend/semver.bend as Sv
import ../../LAWS.bend as Laws

# Decimal writing (semver_show_decimal): the spec's writer of the law file
# and the model's Num.str agree.

# digits written before x ++ acc: the digits before x, then acc
def ps.str_app(ds: List<&2, Sv.Dig>, x: String, acc: String) -> {Sv.Num.str(ds, String.append(x, acc)) == String.append(Sv.Num.str(ds, x), acc) : String}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      ps.str_app(rest, SCon{Sv.Dig.chr(d), x}, acc)

# reversing onto acc, then reversing that, gives acc reversed onto s
def ps.rev_rev(s: String, acc: String) -> {String.reverse.go(String.reverse.go(s, acc), SNil{}) == String.reverse.go(acc, s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      ps.rev_rev(t, SCon{h, acc})

# the digits as text, last digit first
def ps.lsf(ds: List<&2, Sv.Dig>) -> String:
  match ds:
    case Nil{}:
      SNil{}
    case d <> rest:
      SCon{Sv.Dig.chr(d), ps.lsf(rest)}

# writing digits before acc is reversing their text onto acc
def ps.str_rev(ds: List<&2, Sv.Dig>, acc: String) -> {Sv.Num.str(ds, acc) == String.reverse.go(ps.lsf(ds), acc) : String}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      ps.str_rev(rest, SCon{Sv.Dig.chr(d), acc})

# raising the text of digits is the text of the next number's digits
def ps.raise_inc(ds: List<&2, Sv.Dig>) -> {Laws.dec_raise(ps.lsf(ds)) == ps.lsf(Sv.Num.inc(ds)) : String}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Sv.D0{}:
          {==}
        case Sv.D1{}:
          {==}
        case Sv.D2{}:
          {==}
        case Sv.D3{}:
          {==}
        case Sv.D4{}:
          {==}
        case Sv.D5{}:
          {==}
        case Sv.D6{}:
          {==}
        case Sv.D7{}:
          {==}
        case Sv.D8{}:
          {==}
        case Sv.D9{}:
          Equal.cong(String, String, s => SCon{'0', s}, Laws.dec_raise(ps.lsf(rest)), ps.lsf(Sv.Num.inc(rest)), ps.raise_inc(rest))

# the spec's decimal text of n is the text Num.str writes for n's digits
def ps.dec_spec_str(n: Nat) -> {Laws.dec_spec(n) == Sv.Num.str(Sv.Num.dec(n), SNil{}) : String}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(String, Laws.dec_spec(p), Sv.Num.str(Sv.Num.dec(p), SNil{}), ps.dec_spec_str(p)) : {String.reverse(Laws.dec_raise(String.reverse(_))) == Sv.Num.str(Sv.Num.inc(Sv.Num.dec(p)), SNil{}) : String}
      %Equal.sym(String, Sv.Num.str(Sv.Num.dec(p), SNil{}), String.reverse.go(ps.lsf(Sv.Num.dec(p)), SNil{}), ps.str_rev(Sv.Num.dec(p), SNil{})) : {String.reverse(Laws.dec_raise(String.reverse(_))) == Sv.Num.str(Sv.Num.inc(Sv.Num.dec(p)), SNil{}) : String}
      %Equal.sym(String, String.reverse.go(String.reverse.go(ps.lsf(Sv.Num.dec(p)), SNil{}), SNil{}), String.reverse.go(SNil{}, ps.lsf(Sv.Num.dec(p))), ps.rev_rev(ps.lsf(Sv.Num.dec(p)), SNil{})) : {String.reverse(Laws.dec_raise(_)) == Sv.Num.str(Sv.Num.inc(Sv.Num.dec(p)), SNil{}) : String}
      %Equal.sym(String, Laws.dec_raise(ps.lsf(Sv.Num.dec(p))), ps.lsf(Sv.Num.inc(Sv.Num.dec(p))), ps.raise_inc(Sv.Num.dec(p))) : {String.reverse(_) == Sv.Num.str(Sv.Num.inc(Sv.Num.dec(p)), SNil{}) : String}
      Equal.sym(String, Sv.Num.str(Sv.Num.inc(Sv.Num.dec(p)), SNil{}), String.reverse.go(ps.lsf(Sv.Num.inc(Sv.Num.dec(p))), SNil{}), ps.str_rev(Sv.Num.inc(Sv.Num.dec(p)), SNil{}))

# a version is written as its three numbers in decimal, joined by dots
def ps.show_decimal(+a: Nat, +b: Nat, +c: Nat) -> {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(Laws.dec_spec(a), SCon{'.', String.append(Laws.dec_spec(b), SCon{'.', Laws.dec_spec(c)})}) : String}:
  %Equal.sym(String, Laws.dec_spec(a), Sv.Num.str(Sv.Num.dec(a), SNil{}), ps.dec_spec_str(a)) : {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(_, SCon{'.', String.append(Laws.dec_spec(b), SCon{'.', Laws.dec_spec(c)})}) : String}
  %Equal.sym(String, Laws.dec_spec(b), Sv.Num.str(Sv.Num.dec(b), SNil{}), ps.dec_spec_str(b)) : {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(Sv.Num.str(Sv.Num.dec(a), SNil{}), SCon{'.', String.append(_, SCon{'.', Laws.dec_spec(c)})}) : String}
  %Equal.sym(String, Laws.dec_spec(c), Sv.Num.str(Sv.Num.dec(c), SNil{}), ps.dec_spec_str(c)) : {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(Sv.Num.str(Sv.Num.dec(a), SNil{}), SCon{'.', String.append(Sv.Num.str(Sv.Num.dec(b), SNil{}), SCon{'.', _})}) : String}
  %ps.str_app(Sv.Num.dec(b), SNil{}, SCon{'.', Sv.Num.str(Sv.Num.dec(c), SNil{})}) : {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(Sv.Num.str(Sv.Num.dec(a), SNil{}), SCon{'.', _}) : String}
  ps.str_app(Sv.Num.dec(a), SNil{}, SCon{'.', Sv.Num.str(Sv.Num.dec(b), SCon{'.', Sv.Num.str(Sv.Num.dec(c), SNil{})})})

def Laws.semver_show_decimal(a, b, c):
  ps.show_decimal(a, b, c)
