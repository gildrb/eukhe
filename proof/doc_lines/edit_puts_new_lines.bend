# eukhe: the proof of LAW edit_puts_new_lines
#
# PROOF: the edit persists as the bytes up to the s-th `\n`, the new pieces
# with the carry after the first s pieces, then the bytes after the
# (s+k)-th `\n` (pdl.edit_eq of proof/doc_lines/edit_keeps_untouched_bytes
# .bend). A new piece owns no ending, so each takes that carry
# (epn.fresh). After no piece the carry is the file's first ending, the
# first ending scanned byte by byte (LAWS lines_carry_is_first and
# lines_carry_is_first_end); after s = 1+m pieces it is the own ending of
# piece m (epn.carry_take), the first ending of the lines after the m-th
# `\n`, which are the lines of the bytes after it (epn.split_from), whose
# first ending is again scanned byte by byte.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines
import ./base.bend as LA
import ./edit_keeps_untouched_bytes.bend as PEK
import ./lines_carry_is_first.bend as PLinesCarryIsFirst
import ./lines_carry_is_first_end.bend as PLinesCarryIsFirstEnd

# new pieces persist as their texts, each followed by the carry
def epn.fresh(xs: List<&2, List<&2, Dl.B>>, c: Dl.End) -> {PEK.pdl.pre(Dl.fresh(xs), c, Nil{}) == DocLines.lines.Each(xs, DocLines.lines.EndBytes(c)) : List<&2, Dl.B>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      match c:
        case Dl.Lf{}:
          %epn.fresh(rest, Dl.Lf{}) : {List.append(&2, Dl.B, x, Dl.N{} <> PEK.pdl.pre(Dl.fresh(rest), Dl.Lf{}, Nil{})) == List.append(&2, Dl.B, x, Dl.N{} <> _) : List<&2, Dl.B>}
          {==}
        case Dl.CrLf{}:
          %epn.fresh(rest, Dl.CrLf{}) : {List.append(&2, Dl.B, x, Dl.R{} <> (Dl.N{} <> PEK.pdl.pre(Dl.fresh(rest), Dl.CrLf{}, Nil{}))) == List.append(&2, Dl.B, x, Dl.R{} <> (Dl.N{} <> _)) : List<&2, Dl.B>}
          {==}

# no piece is taken from lines
def epn.take0(ls: Dl.Lines) -> {Nil{} == List.take(&2, Dl.Piece, Dl.pieces(ls), 0n) : List<&2, Dl.Piece>}:
  match ls:
    case Dl.More{t, e, r}:
      {==}
    case Dl.Last{t}:
      {==}

# the carry after the first 1+m pieces of lines is the own ending of piece
# m, the first ending of the lines after the first m
def epn.carry_take(ls: Dl.Lines, m: Nat, +c: Dl.End, h: {Nat.is_le(1n+m, PEK.pdl.count(ls)) == True{} : Bool}) -> {PEK.pdl.carry(List.take(&2, Dl.Piece, Dl.pieces(ls), 1n+m), c) == Dl.first(PEK.pdl.drop(ls, m)) : Dl.End}:
  match ls:
    case Dl.More{t, +e, +r}:
      match m:
        case 0n:
          %epn.take0(r) : {PEK.pdl.carry(_, e) == e : Dl.End}
          {==}
        case 1n+p:
          epn.carry_take(r, p, e, h)
    case Dl.Last{t}:
      LA.pdl.absurd({PEK.pdl.carry(List.take(&2, Dl.Piece, Dl.pieces(Dl.Last{t}), 1n+m), c) == Dl.first(PEK.pdl.drop(Dl.Last{t}, m)) : Dl.End}, Equal.sym(Bool, False{}, True{}, h))

# the lines of the bytes after the j-th `\n` are the lines after the
# first j
def epn.split_from(bs: List<&2, Dl.B>, +j: Nat) -> {Dl.split(Dl.from(bs, j)) == PEK.pdl.drop(Dl.split(bs), j) : Dl.Lines}:
  match bs:
    case Nil{}:
      match j:
        case 0n:
          {==}
        case 1n+m:
          {==}
    case b <> +rest:
      match b:
        case Dl.A{}:
          match j:
            case 0n:
              PEK.pdl.drop0(Dl.split(Dl.A{} <> rest))
            case 1n++m:
              %PEK.pdl.push_drop(Dl.A{}, Dl.split(rest), m) : {Dl.split(Dl.from(rest, 1n+m)) == _ : Dl.Lines}
              epn.split_from(rest, 1n+m)
        case Dl.R{}:
          match j:
            case 0n:
              PEK.pdl.drop0(Dl.split(Dl.R{} <> rest))
            case 1n++m:
              %PEK.pdl.consR_drop(Dl.split(rest), m) : {Dl.split(Dl.from(rest, 1n+m)) == _ : Dl.Lines}
              epn.split_from(rest, 1n+m)
        case Dl.N{}:
          match j:
            case 0n:
              PEK.pdl.drop0(Dl.split(Dl.N{} <> rest))
            case 1n+m:
              epn.split_from(rest, m)

# the first ending of the lines of a body is its first ending scanned
# byte by byte (LAWS lines_carry_is_first, lines_carry_is_first_end)
def epn.first(+bs: List<&2, Dl.B>) -> {Dl.first(Dl.split(bs)) == DocLines.lines.OrLf(DocLines.lines.FirstEnd(bs, False{})) : Dl.End}:
  Equal.trans(Dl.End, Dl.first(Dl.split(bs)), Dl.carry(Dl.proj(Dl.Doc{False{}, bs})), DocLines.lines.OrLf(DocLines.lines.FirstEnd(bs, False{})), Equal.sym(Dl.End, Dl.carry(Dl.proj(Dl.Doc{False{}, bs})), Dl.first(Dl.split(bs)), DocLines.lines_carry_is_first(False{}, bs)), DocLines.lines_carry_is_first_end(False{}, bs))

# the carry after the first s pieces of a file is the ending written
# right before line s
def epn.before(+bs: List<&2, Dl.B>, s: Nat, h: {Nat.is_le(s, PEK.pdl.count(Dl.split(bs))) == True{} : Bool}) -> {PEK.pdl.carry(List.take(&2, Dl.Piece, Dl.pieces(Dl.split(bs)), s), Dl.first(Dl.split(bs))) == DocLines.lines.Before(bs, s) : Dl.End}:
  match s:
    case 0n:
      %epn.take0(Dl.split(bs)) : {PEK.pdl.carry(_, Dl.first(Dl.split(bs))) == DocLines.lines.OrLf(DocLines.lines.FirstEnd(bs, False{})) : Dl.End}
      epn.first(bs)
    case 1n++m:
      +L = Dl.split(bs)
      +F = Dl.from(bs, m)
      +dm = Dl.first(PEK.pdl.drop(L, m))
      +rhs = DocLines.lines.OrLf(DocLines.lines.FirstEnd(F, False{}))
      +sf = Equal.sym(Dl.End, Dl.first(Dl.split(F)), dm, Equal.cong(Dl.Lines, Dl.End, l => Dl.first(l), Dl.split(F), PEK.pdl.drop(L, m), epn.split_from(bs, m)))
      Equal.trans(Dl.End, PEK.pdl.carry(List.take(&2, Dl.Piece, Dl.pieces(L), 1n+m), Dl.first(L)), dm, rhs, epn.carry_take(L, m, Dl.first(L), h), Equal.trans(Dl.End, dm, Dl.first(Dl.split(F)), rhs, sf, epn.first(F)))

def DocLines.edit_puts_new_lines(bom, bs, s, k, xs, fits):
  +hj = PEK.pdl.fits(bs, Nat.add(s, k), fits)
  +hs = PEK.pdl.le_add(s, k, PEK.pdl.count(Dl.split(bs)), hj)
  +L = Dl.split(bs)
  +cc = PEK.pdl.carry(List.take(&2, Dl.Piece, Dl.pieces(L), s), Dl.first(L))
  +E = DocLines.lines.Before(bs, s)
  +x = PEK.pdl.pre(Dl.fresh(xs), cc, Nil{})
  +y = DocLines.lines.Each(xs, DocLines.lines.EndBytes(E))
  +ex = Equal.trans(List<&2, Dl.B>, x, DocLines.lines.Each(xs, DocLines.lines.EndBytes(cc)), y, epn.fresh(xs, cc), Equal.cong(Dl.End, List<&2, Dl.B>, c => DocLines.lines.Each(xs, DocLines.lines.EndBytes(c)), cc, E, epn.before(bs, s, hs)))
  +j = Nat.add(s, k)
  Equal.trans(Dl.Doc, Dl.persist(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)), Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, x, Dl.from(bs, j)))}, Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, y, Dl.from(bs, j)))}, PEK.pdl.edit_eq(bom, bs, s, k, xs, hs, hj), Equal.cong(List<&2, Dl.B>, Dl.Doc, z => Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, z, Dl.from(bs, j)))}, x, y, ex))
