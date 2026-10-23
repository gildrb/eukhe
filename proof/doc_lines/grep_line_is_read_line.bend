# eukhe: the proof of LAW grep_line_is_read_line

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines
import ./base.bend as LA

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
      LA.pdl.absurd({Dl.stripR(x) <> Dl.lines(Nil{}) == Dl.lines(x <> Nil{}) : List<&2, List<&2, Dl.B>>}, h)
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
          LA.pdl.absurd({Dl.step(Dl.A{}, Dl.lastrow(Nil{})) == Dl.lastrow(Dl.step(Dl.A{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
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
          LA.pdl.absurd({Dl.step(Dl.R{}, Dl.lastrow(Nil{})) == Dl.lastrow(Dl.step(Dl.R{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
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
          LA.pdl.absurd({Dl.step(Dl.N{}, Dl.lastrow(Nil{})) == Dl.lastrow(Dl.step(Dl.N{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
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
          LA.pdl.absurd({pdl.two(Dl.step(Dl.A{}, Nil{})) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
        case p <> m:
          match m:
            case Nil{}:
              LA.pdl.absurd({pdl.two(Dl.step(Dl.A{}, p <> Nil{})) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
            case q <> r:
              {==}
    case Dl.R{}:
      match ps:
        case Nil{}:
          LA.pdl.absurd({pdl.two(Dl.step(Dl.R{}, Nil{})) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
        case p <> m:
          match m:
            case Nil{}:
              LA.pdl.absurd({pdl.two(Dl.step(Dl.R{}, p <> Nil{})) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
            case q <> r:
              {==}
    case Dl.N{}:
      match ps:
        case Nil{}:
          LA.pdl.absurd({pdl.two(Dl.step(Dl.N{}, Nil{})) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
        case p <> m:
          {==}

# a body that ends with `\n` splits into two pieces at least
def pdl.ends_two(more: List<&2, Dl.B>, c: Dl.B, h: {Dl.endsN.go(more, c) == True{} : Bool}) -> {pdl.two(Dl.splitN(c <> more)) == True{} : Bool}:
  match more:
    case Nil{}:
      match c:
        case Dl.A{}:
          LA.pdl.absurd({pdl.two(Dl.splitN([Dl.A{}])) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
        case Dl.R{}:
          LA.pdl.absurd({pdl.two(Dl.splitN([Dl.R{}])) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
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
              LA.pdl.absurd({Dl.step(Dl.A{}, Dl.fin(True{}, Nil{})) == Dl.fin(True{}, Dl.step(Dl.A{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
            case q <> m:
              match m:
                case Nil{}:
                  LA.pdl.absurd({Dl.step(Dl.A{}, Dl.fin(True{}, q <> Nil{})) == Dl.fin(True{}, Dl.step(Dl.A{}, q <> Nil{})) : List<&2, List<&2, Dl.B>>}, Equal.sym(Bool, False{}, True{}, tw({==})))
                case q2 <> m2:
                  {==}
    case Dl.R{}:
      match e:
        case False{}:
          {==}
        case True{}:
          match ps:
            case Nil{}:
              LA.pdl.absurd({Dl.step(Dl.R{}, Dl.fin(True{}, Nil{})) == Dl.fin(True{}, Dl.step(Dl.R{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
            case q <> m:
              match m:
                case Nil{}:
                  LA.pdl.absurd({Dl.step(Dl.R{}, Dl.fin(True{}, q <> Nil{})) == Dl.fin(True{}, Dl.step(Dl.R{}, q <> Nil{})) : List<&2, List<&2, Dl.B>>}, Equal.sym(Bool, False{}, True{}, tw({==})))
                case q2 <> m2:
                  {==}
    case Dl.N{}:
      match e:
        case False{}:
          {==}
        case True{}:
          match ps:
            case Nil{}:
              LA.pdl.absurd({Dl.step(Dl.N{}, Dl.fin(True{}, Nil{})) == Dl.fin(True{}, Dl.step(Dl.N{}, Nil{})) : List<&2, List<&2, Dl.B>>}, h)
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
      LA.pdl.absurd({Dl.lastrow(Dl.splitN(Nil{})) == Dl.fin(Dl.endsN(Nil{}), Dl.splitN(Nil{})) : List<&2, List<&2, Dl.B>>}, h)
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

def DocLines.grep_line_is_read_line(b, bs):
  pdl.grep_is_read(b, bs)
