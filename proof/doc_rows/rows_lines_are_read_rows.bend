# eukhe: the proof of LAW rows_lines_are_read_rows

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_rows.bend as DocRows
import ../base/doc_lines/proj.bend as LProj

# Logic
# -----

# a Bool as a choice of types
def rlr.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# a false premise proves anything
def rlr.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : rlr.BD(_, A, Unit)
  Unit{}

# Lengths: the lines a read counts
# --------------------------------

# the items after x (x is past the first item), without the last one when
# it is 0
def rlr.cut.go(m: List<&2, Nat>, x: Nat) -> List<&2, Nat>:
  match m:
    case Nil{}:
      match x:
        case 0n:
          Nil{}
        case 1n+p:
          [1n+p]
    case y <> more:
      x <> rlr.cut.go(more, y)

# a list without its last item when it has two or more and the last is 0
def rlr.cut(ns: List<&2, Nat>) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case x <> m:
      match m:
        case Nil{}:
          [x]
        case y <> more:
          x <> rlr.cut.go(more, y)

# a successor taken out of both branches
def rlr.if_succ(b: Bool, a: Nat, c: Nat) -> {1n+DocRows.rows.If(Nat, b, a, c) == DocRows.rows.If(Nat, b, 1n+a, 1n+c) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the count of x <> more, less the line before x
def rlr.cnt(x: Dl.Line, +more: List<&2, Dl.Line>) -> Nat:
  DocRows.rows.If(Nat, DocRows.rows.LastEmpty(x <> more), List.length(&2, Dl.Line, more), 1n+List.length(&2, Dl.Line, more))

# the count of l <> y <> more is one line more than the count of y <> more
def rlr.count(l: Dl.Line, y: Dl.Line, more: List<&2, Dl.Line>) -> {1n+rlr.cnt(y, more) == DocRows.rows.Count(l <> y <> more) : Nat}:
  match more:
    case Nil{}:
      rlr.if_succ(DocRows.rows.LastEmpty([y]), 0n, 1n)
    case +z <> +more2:
      rlr.if_succ(DocRows.rows.LastEmpty(z <> more2), 1n+List.length(&2, Dl.Line, more2), 1n+1n+List.length(&2, Dl.Line, more2))

# the lines counted from a line past the first
def rlr.take_go(more: List<&2, Dl.Line>, n: Nat, en: Maybe<&2, Dl.End>) -> {DocRows.rows.Lens(List.take(&2, Dl.Line, Dl.Line{n, en} <> more, rlr.cnt(Dl.Line{n, en}, more))) == rlr.cut.go(DocRows.rows.Lens(more), n) : List<&2, Nat>}:
  match more:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case y <> +m2:
      match y:
        case Dl.Line{+n2, +en2}:
          %rlr.if_succ(DocRows.rows.LastEmpty(Dl.Line{n2, en2} <> m2), List.length(&2, Dl.Line, m2), 1n+List.length(&2, Dl.Line, m2)) : {DocRows.rows.Lens(List.take(&2, Dl.Line, Dl.Line{n, en} <> Dl.Line{n2, en2} <> m2, _)) == rlr.cut.go(DocRows.rows.Lens(Dl.Line{n2, en2} <> m2), n) : List<&2, Nat>}
          %rlr.take_go(m2, n2, en2) : {n <> DocRows.rows.Lens(List.take(&2, Dl.Line, Dl.Line{n2, en2} <> m2, rlr.cnt(Dl.Line{n2, en2}, m2))) == n <> _ : List<&2, Nat>}
          {==}

# the lengths of the lines a read counts
def rlr.take_count(ls: List<&2, Dl.Line>) -> {DocRows.rows.Lens(List.take(&2, Dl.Line, ls, DocRows.rows.Count(ls))) == rlr.cut(DocRows.rows.Lens(ls)) : List<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case l <> m:
      match l:
        case Dl.Line{+n, +en}:
          match m:
            case Nil{}:
              {==}
            case y <> +more:
              match y:
                case Dl.Line{+n2, +en2}:
                  %rlr.count(Dl.Line{n, en}, Dl.Line{n2, en2}, more) : {DocRows.rows.Lens(List.take(&2, Dl.Line, Dl.Line{n, en} <> Dl.Line{n2, en2} <> more, _)) == rlr.cut(DocRows.rows.Lens(Dl.Line{n, en} <> Dl.Line{n2, en2} <> more)) : List<&2, Nat>}
                  %rlr.take_go(more, n2, en2) : {n <> DocRows.rows.Lens(List.take(&2, Dl.Line, Dl.Line{n2, en2} <> more, rlr.cnt(Dl.Line{n2, en2}, more))) == n <> _ : List<&2, Nat>}
                  {==}

# Lengths: the rows of read
# -------------------------

# the last item (x is past the first item) is 0
def rlr.lastz.go(m: List<&2, Nat>, x: Nat) -> Bool:
  match m:
    case Nil{}:
      match x:
        case 0n:
          True{}
        case 1n+p:
          False{}
    case y <> more:
      rlr.lastz.go(more, y)

# two items or more, and the last is 0
def rlr.cond(ns: List<&2, Nat>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case x <> m:
      match m:
        case Nil{}:
          False{}
        case y <> more:
          rlr.lastz.go(more, y)

# the items from x on (x is past the first item), but the last
def rlr.init.go(m: List<&2, Nat>, x: Nat) -> List<&2, Nat>:
  match m:
    case Nil{}:
      Nil{}
    case y <> more:
      x <> rlr.init.go(more, y)

# every item but the last
def rlr.init(ns: List<&2, Nat>) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case x <> m:
      rlr.init.go(m, x)

# every item but the last when e holds
def rlr.fin(e: Bool, ns: List<&2, Nat>) -> List<&2, Nat>:
  match e:
    case True{}:
      rlr.init(ns)
    case False{}:
      ns

# the last item dropped or not, past a first item
def rlr.fin_cons(e: Bool, x: Nat, y: Nat, rest: List<&2, Nat>) -> {x <> rlr.fin(e, y <> rest) == rlr.fin(e, x <> y <> rest) : List<&2, Nat>}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

# cutting from a later item is fin by lastz
def rlr.cut_go(more: List<&2, Nat>, +y: Nat, +x: Nat) -> {x <> rlr.cut.go(more, y) == rlr.fin(rlr.lastz.go(more, y), x <> y <> more) : List<&2, Nat>}:
  match more:
    case Nil{}:
      match y:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case +z <> +m2:
      %rlr.fin_cons(rlr.lastz.go(m2, z), x, y, z <> m2) : {x <> y <> rlr.cut.go(m2, z) == _ : List<&2, Nat>}
      %rlr.cut_go(m2, z, y) : {x <> y <> rlr.cut.go(m2, z) == x <> _ : List<&2, Nat>}
      {==}

# cutting is dropping the last item exactly when cond holds
def rlr.cut_fin(ns: List<&2, Nat>) -> {rlr.cut(ns) == rlr.fin(rlr.cond(ns), ns) : List<&2, Nat>}:
  match ns:
    case Nil{}:
      {==}
    case +x <> m:
      match m:
        case Nil{}:
          {==}
        case +y <> +more:
          rlr.cut_go(more, y, x)

# the lengths of init are init of the lengths
def rlr.init_lens(m: List<&2, List<&2, Dl.B>>, +p: List<&2, Dl.B>) -> {rlr.init.go(DocRows.rows.LensB(m), List.length(&2, Dl.B, p)) == DocRows.rows.LensB(Dl.init.go(m, p)) : List<&2, Nat>}:
  match m:
    case Nil{}:
      {==}
    case +q <> +more:
      %rlr.init_lens(more, q) : {List.length(&2, Dl.B, p) <> rlr.init.go(DocRows.rows.LensB(more), List.length(&2, Dl.B, q)) == List.length(&2, Dl.B, p) <> _ : List<&2, Nat>}
      {==}

# the lengths of fin are fin of the lengths
def rlr.fin_lens(e: Bool, ps: List<&2, List<&2, Dl.B>>) -> {rlr.fin(e, DocRows.rows.LensB(ps)) == DocRows.rows.LensB(Dl.fin(e, ps)) : List<&2, Nat>}:
  match e:
    case True{}:
      match ps:
        case Nil{}:
          {==}
        case p <> m:
          rlr.init_lens(m, p)
    case False{}:
      {==}

# the pieces are not a single empty piece
def rlr.ok(ps: List<&2, List<&2, Dl.B>>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> m:
      match p:
        case Nil{}:
          match m:
            case Nil{}:
              False{}
            case q <> r:
              True{}
        case c <> cs:
          True{}

# a byte put on the pieces leaves one piece at least
def rlr.pushN_ne(+b: Dl.B, ps: List<&2, List<&2, Dl.B>>) -> {List.is_empty(&2, List<&2, Dl.B>, Dl.pushN(b, ps)) == False{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case q <> m:
      {==}

# a body splits into one piece at least
def rlr.split_ne(bs: List<&2, Dl.B>) -> {List.is_empty(&2, List<&2, Dl.B>, Dl.splitN(bs)) == False{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case Dl.A{}:
          rlr.pushN_ne(Dl.A{}, Dl.splitN(rest))
        case Dl.R{}:
          rlr.pushN_ne(Dl.R{}, Dl.splitN(rest))
        case Dl.N{}:
          {==}

# a byte put on the first piece makes it not empty
def rlr.ok_push(b: Dl.B, ps: List<&2, List<&2, Dl.B>>) -> {rlr.ok(Dl.pushN(b, ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case q <> m:
      match m:
        case Nil{}:
          {==}
        case q2 <> m2:
          {==}

# an empty piece before one piece or more is not a single empty piece
def rlr.ok_nil(ps: List<&2, List<&2, Dl.B>>, h: {List.is_empty(&2, List<&2, Dl.B>, ps) == False{} : Bool}) -> {rlr.ok(Nil{} <> ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      rlr.absurd({rlr.ok([Nil{}]) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case q <> m:
      {==}

# a body that is not empty does not split into one empty piece
def rlr.ok_split(+more: List<&2, Dl.B>, c: Dl.B) -> {rlr.ok(Dl.splitN(c <> more)) == True{} : Bool}:
  match c:
    case Dl.A{}:
      rlr.ok_push(Dl.A{}, Dl.splitN(more))
    case Dl.R{}:
      rlr.ok_push(Dl.R{}, Dl.splitN(more))
    case Dl.N{}:
      rlr.ok_nil(Dl.splitN(more), rlr.split_ne(more))

# a byte put before a body that is not empty keeps cond
def rlr.cond_step(y: Dl.B, ps: List<&2, List<&2, Dl.B>>, h: {rlr.ok(ps) == True{} : Bool}) -> {rlr.cond(DocRows.rows.LensB(ps)) == rlr.cond(DocRows.rows.LensB(Dl.step(y, ps))) : Bool}:
  match y:
    case Dl.A{}:
      match ps:
        case Nil{}:
          {==}
        case p <> m:
          match m:
            case Nil{}:
              {==}
            case q <> r:
              {==}
    case Dl.R{}:
      match ps:
        case Nil{}:
          {==}
        case p <> m:
          match m:
            case Nil{}:
              {==}
            case q <> r:
              {==}
    case Dl.N{}:
      match ps:
        case Nil{}:
          {==}
        case p <> m:
          match p:
            case Nil{}:
              match m:
                case Nil{}:
                  rlr.absurd({rlr.cond(DocRows.rows.LensB([Nil{}])) == rlr.cond(DocRows.rows.LensB(Dl.step(Dl.N{}, [Nil{}]))) : Bool}, h)
                case q <> r:
                  {==}
            case c <> cs:
              match m:
                case Nil{}:
                  {==}
                case q <> r:
                  {==}

# y <> t ends with `\n` exactly when cond holds of its pieces' lengths
def rlr.ends_go(t: List<&2, Dl.B>, +y: Dl.B) -> {rlr.cond(DocRows.rows.LensB(Dl.splitN(y <> t))) == Dl.endsN.go(t, y) : Bool}:
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
      %rlr.ends_go(more, c) : {rlr.cond(DocRows.rows.LensB(Dl.step(y, Dl.splitN(c <> more)))) == _ : Bool}
      %rlr.cond_step(y, Dl.splitN(c <> more), rlr.ok_split(more, c)) : {_ == rlr.cond(DocRows.rows.LensB(Dl.splitN(c <> more))) : Bool}
      {==}

# a text ends with `\n` exactly when cond holds of its pieces' lengths
def rlr.ends(ys: List<&2, Dl.B>) -> {rlr.cond(DocRows.rows.LensB(Dl.splitN(ys))) == Dl.endsN(ys) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      rlr.ends_go(t, y)

def DocRows.rows_lines_are_read_rows(bs):
  %rlr.fin_lens(Dl.endsN(Dl.norm(bs)), Dl.splitN(Dl.norm(bs))) : {DocRows.rows.Lens(List.take(&2, Dl.Line, DocRows.rows.Pieces(bs), DocRows.rows.Count(DocRows.rows.Pieces(bs)))) == _ : List<&2, Nat>}
  %rlr.ends(Dl.norm(bs)) : {DocRows.rows.Lens(List.take(&2, Dl.Line, DocRows.rows.Pieces(bs), DocRows.rows.Count(DocRows.rows.Pieces(bs)))) == rlr.fin(_, DocRows.rows.LensB(Dl.splitN(Dl.norm(bs)))) : List<&2, Nat>}
  %rlr.cut_fin(DocRows.rows.LensB(Dl.splitN(Dl.norm(bs)))) : {DocRows.rows.Lens(List.take(&2, Dl.Line, DocRows.rows.Pieces(bs), DocRows.rows.Count(DocRows.rows.Pieces(bs)))) == _ : List<&2, Nat>}
  %LProj.dlp.raw(bs) : {DocRows.rows.Lens(List.take(&2, Dl.Line, DocRows.rows.Pieces(bs), DocRows.rows.Count(DocRows.rows.Pieces(bs)))) == rlr.cut(_) : List<&2, Nat>}
  rlr.take_count(DocRows.rows.Pieces(bs))
