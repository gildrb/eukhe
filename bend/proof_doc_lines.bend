# proof_doc_lines: the line laws of laws/documents.bend (F4): a file
# loaded and persisted is the same bytes; an edit keeps every byte outside
# the lines it replaces; grep and read show the same rows.

import Base
import ./doc_lines.bend as Dl

# Logic and lists
# ---------------

def pdl.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pdl.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pdl.BD(_, Unit, A)
  Unit{}

def pdl.app_assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      %pdl.app_assoc(A, t, ys, zs) : {h <> List.append(&2, A, List.append(&2, A, t, ys), zs) == h <> _ : List<&2, A>}
      {==}

def pdl.le_add(s: Nat, +k: Nat, n: Nat, h: {Nat.is_le(Nat.add(s, k), n) == True{} : Bool}) -> {Nat.is_le(s, n) == True{} : Bool}:
  match s n:
    case 0n 0n:
      {==}
    case 0n 1n+m:
      {==}
    case 1n+p 0n:
      pdl.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+m:
      pdl.le_add(p, k, m, h)

# Lines: the proof-side views
# ---------------------------

# the bytes of the lines
def pdl.cat(ls: Dl.Lines) -> List<&2, Dl.B>:
  match ls:
    case Dl.More{t, e, r}:
      List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(e), pdl.cat(r)))
    case Dl.Last{t}:
      t

# the number of lines with an ending
def pdl.count(ls: Dl.Lines) -> Nat:
  match ls:
    case Dl.More{t, e, r}:
      1n+pdl.count(r)
    case Dl.Last{t}:
      0n

# the bytes of the first s lines (with their endings), then z
def pdl.head(ls: Dl.Lines, s: Nat, z: List<&2, Dl.B>) -> List<&2, Dl.B>:
  match ls:
    case Dl.More{t, e, r}:
      match s:
        case 0n:
          z
        case 1n+m:
          List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(e), pdl.head(r, m, z)))
    case Dl.Last{t}:
      match s:
        case 0n:
          z
        case 1n+m:
          List.append(&2, Dl.B, t, z)

# the lines after the first j
def pdl.drop(ls: Dl.Lines, j: Nat) -> Dl.Lines:
  match ls:
    case Dl.More{t, e, r}:
      match j:
        case 0n:
          Dl.More{t, e, r}
        case 1n+m:
          pdl.drop(r, m)
    case Dl.Last{t}:
      match j:
        case 0n:
          Dl.Last{t}
        case 1n+m:
          Dl.Last{[]}

# the bytes of pieces, each with its separator, then z
def pdl.pre(ps: List<&2, Dl.Piece>, c: Dl.End, z: List<&2, Dl.B>) -> List<&2, Dl.B>:
  match ps:
    case Nil{}:
      z
    case p <> m:
      match p:
        case Dl.Piece{t, en}:
          +s = Dl.sep(en, c)
          List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(s), pdl.pre(m, s, z)))

# the carry after pieces
def pdl.carry(ps: List<&2, Dl.Piece>, c: Dl.End) -> Dl.End:
  match ps:
    case Nil{}:
      c
    case p <> m:
      match p:
        case Dl.Piece{t, en}:
          pdl.carry(m, Dl.sep(en, c))

# Load and persist
# ----------------

# a byte put before the body puts it before the bytes of its lines
def pdl.cons_cat(b: Dl.B, ls: Dl.Lines) -> {pdl.cat(Dl.cons(b, ls)) == b <> pdl.cat(ls) : List<&2, Dl.B>}:
  match b:
    case Dl.A{}:
      match ls:
        case Dl.More{t, e, r}:
          {==}
        case Dl.Last{t}:
          {==}
    case Dl.N{}:
      {==}
    case Dl.R{}:
      match ls:
        case Dl.More{t, e, r}:
          match t:
            case Nil{}:
              match e:
                case Dl.Lf{}:
                  {==}
                case Dl.CrLf{}:
                  {==}
            case h <> tt:
              {==}
        case Dl.Last{t}:
          {==}

# the lines of a body are its bytes
def pdl.split_cat(bs: List<&2, Dl.B>) -> {pdl.cat(Dl.split(bs)) == bs : List<&2, Dl.B>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      %Equal.sym(List<&2, Dl.B>, pdl.cat(Dl.cons(b, Dl.split(rest))), b <> pdl.cat(Dl.split(rest)), pdl.cons_cat(b, Dl.split(rest))) : {_ == b <> rest : List<&2, Dl.B>}
      %pdl.split_cat(rest) : {b <> pdl.cat(Dl.split(rest)) == b <> _ : List<&2, Dl.B>}
      {==}

def pdl.emit_more(+t: List<&2, Dl.B>, +e: Dl.End, r: Dl.Lines, +c: Dl.End, ih: {pdl.cat(r) == Dl.start(Dl.pieces(r), e) : List<&2, Dl.B>}) -> {pdl.cat(Dl.More{t, e, r}) == Dl.start(Dl.pieces(Dl.More{t, e, r}), c) : List<&2, Dl.B>}:
  match r:
    case Dl.Last{t2}:
      {==}
    case Dl.More{+t2, +e2, +r2}:
      %Equal.sym(List<&2, Dl.B>, pdl.cat(Dl.More{t2, e2, r2}), Dl.start(Dl.pieces(Dl.More{t2, e2, r2}), e), ih) : {List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(e), _)) == Dl.start(Dl.pieces(Dl.More{t, e, Dl.More{t2, e2, r2}}), c) : List<&2, Dl.B>}
      {==}

# the lines of a loaded file persist as their bytes, with any carry
def pdl.start_cat(ls: Dl.Lines, +c: Dl.End) -> {pdl.cat(ls) == Dl.start(Dl.pieces(ls), c) : List<&2, Dl.B>}:
  match ls:
    case Dl.More{+t, +e, +r}:
      pdl.emit_more(t, e, r, c, pdl.start_cat(r, e))
    case Dl.Last{t}:
      {==}

# the law load_persist_roundtrip
def pdl.roundtrip(+f: Dl.Doc) -> {Dl.persist(Dl.load(f)) == f : Dl.Doc}:
  match f:
    case Dl.Doc{+bom, +bs}:
      %pdl.start_cat(Dl.split(bs), Dl.first(Dl.split(bs))) : {Dl.Doc{bom, _} == Dl.Doc{bom, bs} : Dl.Doc}
      %pdl.split_cat(bs) : {Dl.Doc{bom, pdl.cat(Dl.split(bs))} == Dl.Doc{bom, _} : Dl.Doc}
      {==}

# Counting, taking and dropping lines
# -----------------------------------

def pdl.push_count(b: Dl.B, ls: Dl.Lines) -> {pdl.count(ls) == pdl.count(Dl.push(b, ls)) : Nat}:
  match ls:
    case Dl.More{t, e, r}:
      {==}
    case Dl.Last{t}:
      {==}

def pdl.consR_count(ls: Dl.Lines) -> {pdl.count(ls) == pdl.count(Dl.cons(Dl.R{}, ls)) : Nat}:
  match ls:
    case Dl.More{t, e, r}:
      match t:
        case Nil{}:
          match e:
            case Dl.Lf{}:
              {==}
            case Dl.CrLf{}:
              {==}
        case h <> tt:
          {==}
    case Dl.Last{t}:
      {==}

# a body has one line with an ending for each `\n`
def pdl.count_lfs(bs: List<&2, Dl.B>) -> {Dl.lfs(bs) == pdl.count(Dl.split(bs)) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case Dl.A{}:
          %pdl.push_count(Dl.A{}, Dl.split(rest)) : {Dl.lfs(rest) == _ : Nat}
          pdl.count_lfs(rest)
        case Dl.R{}:
          %pdl.consR_count(Dl.split(rest)) : {Dl.lfs(rest) == _ : Nat}
          pdl.count_lfs(rest)
        case Dl.N{}:
          %pdl.count_lfs(rest) : {1n+Dl.lfs(rest) == 1n+_ : Nat}
          {==}

def pdl.fits(+bs: List<&2, Dl.B>, +n: Nat, h: {Nat.is_le(n, Dl.lfs(bs)) == True{} : Bool}) -> {Nat.is_le(n, pdl.count(Dl.split(bs))) == True{} : Bool}:
  %pdl.count_lfs(bs) : {Nat.is_le(n, _) == True{} : Bool}
  h

# dropping whole lines drops their pieces
def pdl.drop_pieces(ls: Dl.Lines, j: Nat, h: {Nat.is_le(j, pdl.count(ls)) == True{} : Bool}) -> {Dl.pieces(pdl.drop(ls, j)) == List.drop(&2, Dl.Piece, Dl.pieces(ls), j) : List<&2, Dl.Piece>}:
  match ls:
    case Dl.More{t, e, r}:
      match j:
        case 0n:
          {==}
        case 1n+m:
          pdl.drop_pieces(r, m, h)
    case Dl.Last{t}:
      match j:
        case 0n:
          {==}
        case 1n+m:
          pdl.absurd({Dl.pieces(pdl.drop(Dl.Last{t}, 1n+m)) == List.drop(&2, Dl.Piece, Dl.pieces(Dl.Last{t}), 1n+m) : List<&2, Dl.Piece>}, Equal.sym(Bool, False{}, True{}, h))

# the first s pieces persist as the bytes of the first s lines, with any
# carry
def pdl.take_head(ls: Dl.Lines, s: Nat, +c: Dl.End, +z: List<&2, Dl.B>, h: {Nat.is_le(s, pdl.count(ls)) == True{} : Bool}) -> {pdl.head(ls, s, z) == pdl.pre(List.take(&2, Dl.Piece, Dl.pieces(ls), s), c, z) : List<&2, Dl.B>}:
  match ls:
    case Dl.More{+t, +e, +r}:
      match s:
        case 0n:
          {==}
        case 1n+m:
          %pdl.take_head(r, m, e, z, h) : {List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(e), pdl.head(r, m, z))) == List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(e), _)) : List<&2, Dl.B>}
          {==}
    case Dl.Last{t}:
      match s:
        case 0n:
          {==}
        case 1n+m:
          pdl.absurd({pdl.head(Dl.Last{t}, 1n+m, z) == pdl.pre(List.take(&2, Dl.Piece, Dl.pieces(Dl.Last{t}), 1n+m), c, z) : List<&2, Dl.B>}, Equal.sym(Bool, False{}, True{}, h))

def pdl.head0(ls: Dl.Lines, +z: List<&2, Dl.B>) -> {z == pdl.head(ls, 0n, z) : List<&2, Dl.B>}:
  match ls:
    case Dl.More{t, e, r}:
      {==}
    case Dl.Last{t}:
      {==}

def pdl.push_head(+b: Dl.B, ls: Dl.Lines, +m: Nat, +z: List<&2, Dl.B>) -> {b <> pdl.head(ls, 1n+m, z) == pdl.head(Dl.push(b, ls), 1n+m, z) : List<&2, Dl.B>}:
  match ls:
    case Dl.More{t, e, r}:
      {==}
    case Dl.Last{t}:
      {==}

def pdl.consR_head(ls: Dl.Lines, +m: Nat, +z: List<&2, Dl.B>) -> {Dl.R{} <> pdl.head(ls, 1n+m, z) == pdl.head(Dl.cons(Dl.R{}, ls), 1n+m, z) : List<&2, Dl.B>}:
  match ls:
    case Dl.More{t, e, r}:
      match t:
        case Nil{}:
          match e:
            case Dl.Lf{}:
              {==}
            case Dl.CrLf{}:
              {==}
        case h <> tt:
          {==}
    case Dl.Last{t}:
      {==}

# the bytes of the first s lines are the bytes up to the s-th `\n`
def pdl.upto_head(bs: List<&2, Dl.B>, +s: Nat, +z: List<&2, Dl.B>) -> {List.append(&2, Dl.B, Dl.upto(bs, s), z) == pdl.head(Dl.split(bs), s, z) : List<&2, Dl.B>}:
  match bs:
    case Nil{}:
      match s:
        case 0n:
          {==}
        case 1n+m:
          {==}
    case b <> +rest:
      match b:
        case Dl.A{}:
          match s:
            case 0n:
              %pdl.head0(Dl.split(Dl.A{} <> rest), z) : {z == _ : List<&2, Dl.B>}
              {==}
            case 1n+m:
              %pdl.push_head(Dl.A{}, Dl.split(rest), m, z) : {Dl.A{} <> List.append(&2, Dl.B, Dl.upto(rest, 1n+m), z) == _ : List<&2, Dl.B>}
              %pdl.upto_head(rest, 1n+m, z) : {Dl.A{} <> List.append(&2, Dl.B, Dl.upto(rest, 1n+m), z) == Dl.A{} <> _ : List<&2, Dl.B>}
              {==}
        case Dl.R{}:
          match s:
            case 0n:
              %pdl.head0(Dl.split(Dl.R{} <> rest), z) : {z == _ : List<&2, Dl.B>}
              {==}
            case 1n+m:
              %pdl.consR_head(Dl.split(rest), m, z) : {Dl.R{} <> List.append(&2, Dl.B, Dl.upto(rest, 1n+m), z) == _ : List<&2, Dl.B>}
              %pdl.upto_head(rest, 1n+m, z) : {Dl.R{} <> List.append(&2, Dl.B, Dl.upto(rest, 1n+m), z) == Dl.R{} <> _ : List<&2, Dl.B>}
              {==}
        case Dl.N{}:
          match s:
            case 0n:
              {==}
            case 1n+m:
              %pdl.upto_head(rest, m, z) : {Dl.N{} <> List.append(&2, Dl.B, Dl.upto(rest, m), z) == Dl.N{} <> _ : List<&2, Dl.B>}
              {==}

def pdl.drop0(ls: Dl.Lines) -> {ls == pdl.drop(ls, 0n) : Dl.Lines}:
  match ls:
    case Dl.More{t, e, r}:
      {==}
    case Dl.Last{t}:
      {==}

def pdl.from0(+bs: List<&2, Dl.B>) -> {bs == pdl.cat(pdl.drop(Dl.split(bs), 0n)) : List<&2, Dl.B>}:
  %pdl.drop0(Dl.split(bs)) : {bs == pdl.cat(_) : List<&2, Dl.B>}
  Equal.sym(List<&2, Dl.B>, pdl.cat(Dl.split(bs)), bs, pdl.split_cat(bs))

def pdl.push_drop(b: Dl.B, ls: Dl.Lines, +m: Nat) -> {pdl.drop(ls, 1n+m) == pdl.drop(Dl.push(b, ls), 1n+m) : Dl.Lines}:
  match ls:
    case Dl.More{t, e, r}:
      {==}
    case Dl.Last{t}:
      {==}

def pdl.consR_drop(ls: Dl.Lines, +m: Nat) -> {pdl.drop(ls, 1n+m) == pdl.drop(Dl.cons(Dl.R{}, ls), 1n+m) : Dl.Lines}:
  match ls:
    case Dl.More{t, e, r}:
      match t:
        case Nil{}:
          match e:
            case Dl.Lf{}:
              {==}
            case Dl.CrLf{}:
              {==}
        case h <> tt:
          {==}
    case Dl.Last{t}:
      {==}

# the bytes after the j-th `\n` are the bytes of the lines after the
# first j
def pdl.from_drop(bs: List<&2, Dl.B>, +j: Nat) -> {Dl.from(bs, j) == pdl.cat(pdl.drop(Dl.split(bs), j)) : List<&2, Dl.B>}:
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
              pdl.from0(Dl.A{} <> rest)
            case 1n+m:
              %pdl.push_drop(Dl.A{}, Dl.split(rest), m) : {Dl.from(rest, 1n+m) == pdl.cat(_) : List<&2, Dl.B>}
              pdl.from_drop(rest, 1n+m)
        case Dl.R{}:
          match j:
            case 0n:
              pdl.from0(Dl.R{} <> rest)
            case 1n+m:
              %pdl.consR_drop(Dl.split(rest), m) : {Dl.from(rest, 1n+m) == pdl.cat(_) : List<&2, Dl.B>}
              pdl.from_drop(rest, 1n+m)
        case Dl.N{}:
          match j:
            case 0n:
              pdl.from0(Dl.N{} <> rest)
            case 1n+m:
              pdl.from_drop(rest, m)

# Persisting a run of pieces
# --------------------------

def pdl.emit_split(P: List<&2, Dl.Piece>, +t: List<&2, Dl.B>, +en: Maybe<&2, Dl.End>, +q: Dl.Piece, +more: List<&2, Dl.Piece>, +c: Dl.End) -> {List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(Dl.sep(en, c)), pdl.pre(P, Dl.sep(en, c), Dl.start(q <> more, pdl.carry(P, Dl.sep(en, c)))))) == Dl.emit(List.append(&2, Dl.Piece, P, q <> more), c, Dl.Piece{t, en}) : List<&2, Dl.B>}:
  match P:
    case Nil{}:
      {==}
    case p2 <> +P2:
      match p2:
        case Dl.Piece{+t2, +en2}:
          +s = Dl.sep(en, c)
          %pdl.emit_split(P2, t2, en2, q, more, s) : {List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(s), pdl.pre(Dl.Piece{t2, en2} <> P2, s, Dl.start(q <> more, pdl.carry(Dl.Piece{t2, en2} <> P2, s))))) == List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(s), _)) : List<&2, Dl.B>}
          {==}

# persisting P then a run that is not empty: the bytes of P with their
# separators, then the run persisted with the carry after P
def pdl.start_split(P: List<&2, Dl.Piece>, +q: Dl.Piece, +more: List<&2, Dl.Piece>, +c: Dl.End) -> {pdl.pre(P, c, Dl.start(q <> more, pdl.carry(P, c))) == Dl.start(List.append(&2, Dl.Piece, P, q <> more), c) : List<&2, Dl.B>}:
  match P:
    case Nil{}:
      {==}
    case p <> +P2:
      match p:
        case Dl.Piece{+t, +en}:
          pdl.emit_split(P2, t, en, q, more, c)

def pdl.start_lines(+P: List<&2, Dl.Piece>, ls: Dl.Lines, +c: Dl.End) -> {pdl.pre(P, c, Dl.start(Dl.pieces(ls), pdl.carry(P, c))) == Dl.start(List.append(&2, Dl.Piece, P, Dl.pieces(ls)), c) : List<&2, Dl.B>}:
  match ls:
    case Dl.More{t, e, r}:
      pdl.start_split(P, Dl.Piece{t, Some{e}}, Dl.pieces(r), c)
    case Dl.Last{t}:
      pdl.start_split(P, Dl.Piece{t, None{}}, Nil{}, c)

def pdl.pre_app(P: List<&2, Dl.Piece>, +F: List<&2, Dl.Piece>, +c: Dl.End, +y: List<&2, Dl.B>) -> {pdl.pre(P, c, pdl.pre(F, pdl.carry(P, c), y)) == pdl.pre(List.append(&2, Dl.Piece, P, F), c, y) : List<&2, Dl.B>}:
  match P:
    case Nil{}:
      {==}
    case p <> +P2:
      match p:
        case Dl.Piece{+t, +en}:
          +s = Dl.sep(en, c)
          %pdl.pre_app(P2, F, s, y) : {List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(s), pdl.pre(P2, s, pdl.pre(F, pdl.carry(P2, s), y)))) == List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(s), _)) : List<&2, Dl.B>}
          {==}

def pdl.pre_nil(F: List<&2, Dl.Piece>, +c: Dl.End, +y: List<&2, Dl.B>) -> {List.append(&2, Dl.B, pdl.pre(F, c, Nil{}), y) == pdl.pre(F, c, y) : List<&2, Dl.B>}:
  match F:
    case Nil{}:
      {==}
    case p <> +F2:
      match p:
        case Dl.Piece{+t, +en}:
          +s = Dl.sep(en, c)
          +w = pdl.pre(F2, s, Nil{})
          +E = Dl.ebytes(s)
          %pdl.pre_nil(F2, s, y) : {List.append(&2, Dl.B, List.append(&2, Dl.B, t, List.append(&2, Dl.B, E, w)), y) == List.append(&2, Dl.B, t, List.append(&2, Dl.B, E, _)) : List<&2, Dl.B>}
          %pdl.app_assoc(Dl.B, E, w, y) : {List.append(&2, Dl.B, List.append(&2, Dl.B, t, List.append(&2, Dl.B, E, w)), y) == List.append(&2, Dl.B, t, _) : List<&2, Dl.B>}
          pdl.app_assoc(Dl.B, t, List.append(&2, Dl.B, E, w), y)

# The edit law
# ------------

def pdl.edit_eq(+bom: Bool, +bs: List<&2, Dl.B>, +s: Nat, +k: Nat, +xs: List<&2, List<&2, Dl.B>>, hs: {Nat.is_le(s, pdl.count(Dl.split(bs))) == True{} : Bool}, hj: {Nat.is_le(Nat.add(s, k), pdl.count(Dl.split(bs))) == True{} : Bool}) -> {Dl.persist(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, pdl.pre(Dl.fresh(xs), pdl.carry(List.take(&2, Dl.Piece, Dl.pieces(Dl.split(bs)), s), Dl.first(Dl.split(bs))), Nil{}), Dl.from(bs, Nat.add(s, k))))} : Dl.Doc}:
  +L = Dl.split(bs)
  +c0 = Dl.first(L)
  +T = List.take(&2, Dl.Piece, Dl.pieces(L), s)
  +F = Dl.fresh(xs)
  +j = Nat.add(s, k)
  +L2 = pdl.drop(L, j)
  +cc = pdl.carry(T, c0)
  +x = pdl.pre(F, cc, Nil{})
  +rhs = {Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, x, Dl.from(bs, j)))} : Dl.Doc}
  %pdl.drop_pieces(L, j, hj) : {Dl.Doc{bom, Dl.start(List.append(&2, Dl.Piece, T, List.append(&2, Dl.Piece, F, _)), c0)} == rhs : Dl.Doc}
  %pdl.app_assoc(Dl.Piece, T, F, Dl.pieces(L2)) : {Dl.Doc{bom, Dl.start(_, c0)} == rhs : Dl.Doc}
  %pdl.start_lines(List.append(&2, Dl.Piece, T, F), L2, c0) : {Dl.Doc{bom, _} == rhs : Dl.Doc}
  %pdl.start_cat(L2, pdl.carry(List.append(&2, Dl.Piece, T, F), c0)) : {Dl.Doc{bom, pdl.pre(List.append(&2, Dl.Piece, T, F), c0, _)} == rhs : Dl.Doc}
  %pdl.pre_app(T, F, c0, pdl.cat(L2)) : {Dl.Doc{bom, _} == rhs : Dl.Doc}
  %pdl.take_head(L, s, c0, pdl.pre(F, cc, pdl.cat(L2)), hs) : {Dl.Doc{bom, _} == rhs : Dl.Doc}
  %pdl.upto_head(bs, s, pdl.pre(F, cc, pdl.cat(L2))) : {Dl.Doc{bom, _} == rhs : Dl.Doc}
  %pdl.pre_nil(F, cc, pdl.cat(L2)) : {Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), _)} == rhs : Dl.Doc}
  %pdl.from_drop(bs, j) : {Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, x, _))} == rhs : Dl.Doc}
  {==}

# the law edit_keeps_untouched_bytes
def pdl.edit_keeps(+bom: Bool, +bs: List<&2, Dl.B>, +s: Nat, +k: Nat, +xs: List<&2, List<&2, Dl.B>>, fits: {Nat.is_le(Nat.add(s, k), Dl.lfs(bs)) == True{} : Bool}) -> &x: List<&2, Dl.B> -> {Dl.persist(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, x, Dl.from(bs, Nat.add(s, k))))} : Dl.Doc}:
  +hj = pdl.fits(bs, Nat.add(s, k), fits)
  +hs = pdl.le_add(s, k, pdl.count(Dl.split(bs)), hj)
  (pdl.pre(Dl.fresh(xs), pdl.carry(List.take(&2, Dl.Piece, Dl.pieces(Dl.split(bs)), s), Dl.first(Dl.split(bs))), Nil{}), pdl.edit_eq(bom, bs, s, k, xs, hs, hj))

# Rows of read and grep
# ---------------------

def pdl.pushN_ne(+b: Dl.B, ps: List<&2, List<&2, Dl.B>>) -> {List.is_empty(&2, List<&2, Dl.B>, Dl.pushN(b, ps)) == False{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case q <> m:
      {==}

# a body splits into one piece at least
def pdl.split_ne(bs: List<&2, Dl.B>) -> {List.is_empty(&2, List<&2, Dl.B>, Dl.splitN(bs)) == False{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case Dl.A{}:
          pdl.pushN_ne(Dl.A{}, Dl.splitN(rest))
        case Dl.R{}:
          pdl.pushN_ne(Dl.R{}, Dl.splitN(rest))
        case Dl.N{}:
          {==}

def pdl.lines_x(+x: List<&2, Dl.B>, ps: List<&2, List<&2, Dl.B>>, h: {List.is_empty(&2, List<&2, Dl.B>, ps) == False{} : Bool}) -> {Dl.stripR(x) <> Dl.lines(ps) == Dl.lines(x <> ps) : List<&2, List<&2, Dl.B>>}:
  match ps:
    case Nil{}:
      pdl.absurd({Dl.stripR(x) <> Dl.lines(Nil{}) == Dl.lines(x <> Nil{}) : List<&2, List<&2, Dl.B>>}, h)
    case q <> m:
      {==}

def pdl.lines_pushA(ps: List<&2, List<&2, Dl.B>>) -> {Dl.pushN(Dl.A{}, Dl.lines(ps)) == Dl.lines(Dl.pushN(Dl.A{}, ps)) : List<&2, List<&2, Dl.B>>}:
  match ps:
    case Nil{}:
      {==}
    case q <> m:
      match q:
        case Nil{}:
          match m:
            case Nil{}:
              {==}
            case q2 <> m2:
              {==}
        case c <> cs:
          match m:
            case Nil{}:
              {==}
            case q2 <> m2:
              {==}

def pdl.lines_pushR(c: Dl.B, ps: List<&2, List<&2, Dl.B>>) -> {Dl.pushN(Dl.R{}, Dl.lines(Dl.pushN(c, ps))) == Dl.lines(Dl.pushN(Dl.R{}, Dl.pushN(c, ps))) : List<&2, List<&2, Dl.B>>}:
  match ps:
    case Nil{}:
      {==}
    case q <> m:
      match m:
        case Nil{}:
          {==}
        case q2 <> m2:
          {==}

# splitting the normalized body is splitting the body and stripping each
# `\r\n` terminator; p: a `\r` comes before bs
def pdl.norm_lines(bs: List<&2, Dl.B>, p: Bool) -> {Dl.splitN(Dl.nm(bs, p)) == Dl.lines(Dl.splitN(Dl.lead(p, bs))) : List<&2, List<&2, Dl.B>>}:
  match bs:
    case Nil{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case b <> +rest:
      match b:
        case Dl.A{}:
          match p:
            case True{}:
              %pdl.lines_pushR(Dl.A{}, Dl.splitN(rest)) : {Dl.pushN(Dl.R{}, Dl.pushN(Dl.A{}, Dl.splitN(Dl.nm(rest, False{})))) == _ : List<&2, List<&2, Dl.B>>}
              %pdl.lines_pushA(Dl.splitN(rest)) : {Dl.pushN(Dl.R{}, Dl.pushN(Dl.A{}, Dl.splitN(Dl.nm(rest, False{})))) == Dl.pushN(Dl.R{}, _) : List<&2, List<&2, Dl.B>>}
              %pdl.norm_lines(rest, False{}) : {Dl.pushN(Dl.R{}, Dl.pushN(Dl.A{}, Dl.splitN(Dl.nm(rest, False{})))) == Dl.pushN(Dl.R{}, Dl.pushN(Dl.A{}, _)) : List<&2, List<&2, Dl.B>>}
              {==}
            case False{}:
              %pdl.lines_pushA(Dl.splitN(rest)) : {Dl.pushN(Dl.A{}, Dl.splitN(Dl.nm(rest, False{}))) == _ : List<&2, List<&2, Dl.B>>}
              %pdl.norm_lines(rest, False{}) : {Dl.pushN(Dl.A{}, Dl.splitN(Dl.nm(rest, False{}))) == Dl.pushN(Dl.A{}, _) : List<&2, List<&2, Dl.B>>}
              {==}
        case Dl.R{}:
          match p:
            case True{}:
              %pdl.lines_pushR(Dl.R{}, Dl.splitN(rest)) : {Dl.pushN(Dl.R{}, Dl.splitN(Dl.nm(rest, True{}))) == _ : List<&2, List<&2, Dl.B>>}
              %pdl.norm_lines(rest, True{}) : {Dl.pushN(Dl.R{}, Dl.splitN(Dl.nm(rest, True{}))) == Dl.pushN(Dl.R{}, _) : List<&2, List<&2, Dl.B>>}
              {==}
            case False{}:
              pdl.norm_lines(rest, True{})
        case Dl.N{}:
          match p:
            case True{}:
              %pdl.lines_x([Dl.R{}], Dl.splitN(rest), pdl.split_ne(rest)) : {Nil{} <> Dl.splitN(Dl.nm(rest, False{})) == _ : List<&2, List<&2, Dl.B>>}
              %pdl.norm_lines(rest, False{}) : {Nil{} <> Dl.splitN(Dl.nm(rest, False{})) == Nil{} <> _ : List<&2, List<&2, Dl.B>>}
              {==}
            case False{}:
              %pdl.lines_x([], Dl.splitN(rest), pdl.split_ne(rest)) : {Nil{} <> Dl.splitN(Dl.nm(rest, False{})) == _ : List<&2, List<&2, Dl.B>>}
              %pdl.norm_lines(rest, False{}) : {Nil{} <> Dl.splitN(Dl.nm(rest, False{})) == Nil{} <> _ : List<&2, List<&2, Dl.B>>}
              {==}

# the rows of the text y <> t (proof side): every piece, but no row
# after a final `\n`
def pdl.rows(t: List<&2, Dl.B>, y: Dl.B) -> List<&2, List<&2, Dl.B>>:
  match t:
    case Nil{}:
      match y:
        case Dl.A{}:
          [[Dl.A{}]]
        case Dl.R{}:
          [[Dl.R{}]]
        case Dl.N{}:
          [[]]
    case c <> more:
      Dl.step(y, pdl.rows(more, c))

def pdl.lr_step(y: Dl.B, ps: List<&2, List<&2, Dl.B>>, h: {List.is_empty(&2, List<&2, Dl.B>, ps) == False{} : Bool}) -> {Dl.step(y, Dl.lastrow(ps)) == Dl.lastrow(Dl.step(y, ps)) : List<&2, List<&2, Dl.B>>}:
  match y:
    case Dl.A{}:
      match ps:
        case Nil{}:
          pdl.absurd({Dl.step(Dl.A{}, Dl.lastrow(Nil{})) == Dl.lastrow(Dl.step(Dl.A{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
        case q <> m:
          match q:
            case Nil{}:
              match m:
                case Nil{}:
                  {==}
                case q2 <> m2:
                  {==}
            case c <> cs:
              match m:
                case Nil{}:
                  {==}
                case q2 <> m2:
                  {==}
    case Dl.R{}:
      match ps:
        case Nil{}:
          pdl.absurd({Dl.step(Dl.R{}, Dl.lastrow(Nil{})) == Dl.lastrow(Dl.step(Dl.R{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
        case q <> m:
          match q:
            case Nil{}:
              match m:
                case Nil{}:
                  {==}
                case q2 <> m2:
                  {==}
            case c <> cs:
              match m:
                case Nil{}:
                  {==}
                case q2 <> m2:
                  {==}
    case Dl.N{}:
      match ps:
        case Nil{}:
          pdl.absurd({Dl.step(Dl.N{}, Dl.lastrow(Nil{})) == Dl.lastrow(Dl.step(Dl.N{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
        case q <> m:
          {==}

# grep's rows of y <> t
def pdl.grep_rows(t: List<&2, Dl.B>, +y: Dl.B) -> {pdl.rows(t, y) == Dl.lastrow(Dl.splitN(y <> t)) : List<&2, List<&2, Dl.B>>}:
  match t:
    case Nil{}:
      match y:
        case Dl.A{}:
          {==}
        case Dl.R{}:
          {==}
        case Dl.N{}:
          {==}
    case +c <> +more:
      %pdl.lr_step(y, Dl.splitN(c <> more), pdl.split_ne(c <> more)) : {Dl.step(y, pdl.rows(more, c)) == _ : List<&2, List<&2, Dl.B>>}
      %pdl.grep_rows(more, c) : {Dl.step(y, pdl.rows(more, c)) == Dl.step(y, _) : List<&2, List<&2, Dl.B>>}
      {==}

def pdl.two(ps: List<&2, List<&2, Dl.B>>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> m:
      match m:
        case Nil{}:
          False{}
        case q <> r:
          True{}

def pdl.two_step(c: Dl.B, ps: List<&2, List<&2, Dl.B>>, h: {pdl.two(ps) == True{} : Bool}) -> {pdl.two(Dl.step(c, ps)) == True{} : Bool}:
  match c:
    case Dl.A{}:
      match ps:
        case Nil{}:
          pdl.absurd({pdl.two(Dl.step(Dl.A{}, Nil{})) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
        case p <> m:
          match m:
            case Nil{}:
              pdl.absurd({pdl.two(Dl.step(Dl.A{}, p <> Nil{})) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
            case q <> r:
              {==}
    case Dl.R{}:
      match ps:
        case Nil{}:
          pdl.absurd({pdl.two(Dl.step(Dl.R{}, Nil{})) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
        case p <> m:
          match m:
            case Nil{}:
              pdl.absurd({pdl.two(Dl.step(Dl.R{}, p <> Nil{})) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
            case q <> r:
              {==}
    case Dl.N{}:
      match ps:
        case Nil{}:
          pdl.absurd({pdl.two(Dl.step(Dl.N{}, Nil{})) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
        case p <> m:
          {==}

# a body that ends with `\n` splits into two pieces at least
def pdl.ends_two(more: List<&2, Dl.B>, c: Dl.B, h: {Dl.endsN.go(more, c) == True{} : Bool}) -> {pdl.two(Dl.splitN(c <> more)) == True{} : Bool}:
  match more:
    case Nil{}:
      match c:
        case Dl.A{}:
          pdl.absurd({pdl.two(Dl.splitN([Dl.A{}])) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
        case Dl.R{}:
          pdl.absurd({pdl.two(Dl.splitN([Dl.R{}])) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
        case Dl.N{}:
          {==}
    case +d <> +m:
      pdl.two_step(c, Dl.splitN(d <> m), pdl.ends_two(m, d, h))

def pdl.fin_step(y: Dl.B, e: Bool, ps: List<&2, List<&2, Dl.B>>, h: {List.is_empty(&2, List<&2, Dl.B>, ps) == False{} : Bool}, tw: {e == True{} : Bool} -> {pdl.two(ps) == True{} : Bool}) -> {Dl.step(y, Dl.fin(e, ps)) == Dl.fin(e, Dl.step(y, ps)) : List<&2, List<&2, Dl.B>>}:
  match y:
    case Dl.A{}:
      match e:
        case False{}:
          {==}
        case True{}:
          match ps:
            case Nil{}:
              pdl.absurd({Dl.step(Dl.A{}, Dl.fin(True{}, Nil{})) == Dl.fin(True{}, Dl.step(Dl.A{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
            case q <> m:
              match m:
                case Nil{}:
                  pdl.absurd({Dl.step(Dl.A{}, Dl.fin(True{}, q <> Nil{})) == Dl.fin(True{}, Dl.step(Dl.A{}, q <> Nil{})) : List<&2, List<&2, Dl.B>>}, Equal.sym(Bool, False{}, True{}, tw({==})))
                case q2 <> m2:
                  {==}
    case Dl.R{}:
      match e:
        case False{}:
          {==}
        case True{}:
          match ps:
            case Nil{}:
              pdl.absurd({Dl.step(Dl.R{}, Dl.fin(True{}, Nil{})) == Dl.fin(True{}, Dl.step(Dl.R{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
            case q <> m:
              match m:
                case Nil{}:
                  pdl.absurd({Dl.step(Dl.R{}, Dl.fin(True{}, q <> Nil{})) == Dl.fin(True{}, Dl.step(Dl.R{}, q <> Nil{})) : List<&2, List<&2, Dl.B>>}, Equal.sym(Bool, False{}, True{}, tw({==})))
                case q2 <> m2:
                  {==}
    case Dl.N{}:
      match e:
        case False{}:
          {==}
        case True{}:
          match ps:
            case Nil{}:
              pdl.absurd({Dl.step(Dl.N{}, Dl.fin(True{}, Nil{})) == Dl.fin(True{}, Dl.step(Dl.N{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
            case q <> m:
              {==}

# read's rows of y <> t
def pdl.read_rows(t: List<&2, Dl.B>, +y: Dl.B) -> {pdl.rows(t, y) == Dl.fin(Dl.endsN(y <> t), Dl.splitN(y <> t)) : List<&2, List<&2, Dl.B>>}:
  match t:
    case Nil{}:
      match y:
        case Dl.A{}:
          {==}
        case Dl.R{}:
          {==}
        case Dl.N{}:
          {==}
    case +c <> +more:
      %pdl.fin_step(y, Dl.endsN.go(more, c), Dl.splitN(c <> more), pdl.split_ne(c <> more), h => pdl.ends_two(more, c, h)) : {Dl.step(y, pdl.rows(more, c)) == _ : List<&2, List<&2, Dl.B>>}
      %pdl.read_rows(more, c) : {Dl.step(y, pdl.rows(more, c)) == Dl.step(y, _) : List<&2, List<&2, Dl.B>>}
      {==}

def pdl.rows_same(ys: List<&2, Dl.B>, h: {List.is_empty(&2, Dl.B, ys) == False{} : Bool}) -> {Dl.lastrow(Dl.splitN(ys)) == Dl.fin(Dl.endsN(ys), Dl.splitN(ys)) : List<&2, List<&2, Dl.B>>}:
  match ys:
    case Nil{}:
      pdl.absurd({Dl.lastrow(Dl.splitN(Nil{})) == Dl.fin(Dl.endsN(Nil{}), Dl.splitN(Nil{})) : List<&2, List<&2, Dl.B>>}, h)
    case +y <> +t:
      Equal.trans(List<&2, List<&2, Dl.B>>, Dl.lastrow(Dl.splitN(y <> t)), pdl.rows(t, y), Dl.fin(Dl.endsN(y <> t), Dl.splitN(y <> t)), Equal.sym(List<&2, List<&2, Dl.B>>, pdl.rows(t, y), Dl.lastrow(Dl.splitN(y <> t)), pdl.grep_rows(t, y)), pdl.read_rows(t, y))

def pdl.nm_ne(bs: List<&2, Dl.B>, b: Dl.B, p: Bool) -> {List.is_empty(&2, Dl.B, Dl.nm(b <> bs, p)) == False{} : Bool}:
  match bs:
    case Nil{}:
      match b:
        case Dl.A{}:
          match p:
            case True{}:
              {==}
            case False{}:
              {==}
        case Dl.N{}:
          {==}
        case Dl.R{}:
          match p:
            case True{}:
              {==}
            case False{}:
              {==}
    case c <> more:
      match b:
        case Dl.A{}:
          match p:
            case True{}:
              {==}
            case False{}:
              {==}
        case Dl.N{}:
          {==}
        case Dl.R{}:
          match p:
            case True{}:
              {==}
            case False{}:
              pdl.nm_ne(more, c, True{})

# the law grep_line_is_read_line
def pdl.grep_is_read(+b: Dl.B, +bs: List<&2, Dl.B>) -> {Dl.grep_rows(b <> bs) == Dl.read_rows(b <> bs) : List<&2, List<&2, Dl.B>>}:
  %pdl.norm_lines(b <> bs, False{}) : {Dl.lastrow(_) == Dl.read_rows(b <> bs) : List<&2, List<&2, Dl.B>>}
  pdl.rows_same(Dl.norm(b <> bs), pdl.nm_ne(bs, b, False{}))
