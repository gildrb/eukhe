# eukhe: lemmas the proofs of area log share

import Base
import ../../bend/log.bend as Lg

# ---- log ----

# proof_log: the commit log laws of LAWS.bend section storage (D2): open reads
# exactly the complete lines, and after any epoch (any commits, any crash
# point, any torn tail, any lost entries) the log is the old log, then the
# acknowledged commits, then maybe more, and only a prefix of the commits.
#
# A helper lemma {s == t} has the simpler side s first: `%lemma : P`
# turns the t in the goal into s.

# Lists
# -----

def pl.app_nil(-A: Data, xs: List<&2, A>) -> {xs == List.append(&2, A, xs, Nil{}) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %pl.app_nil(A, rest) : {x <> rest == x <> _ : List<&2, A>}
      {==}

def pl.assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, xs, List.append(&2, A, ys, zs)) == List.append(&2, A, List.append(&2, A, xs, ys), zs) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %pl.assoc(A, rest, ys, zs) : {x <> List.append(&2, A, rest, List.append(&2, A, ys, zs)) == x <> _ : List<&2, A>}
      {==}

def pl.byte0(p: Lg.P) -> {Lg.P{Nil{} <> Lg.P.ls(p), Lg.P.tl(p)} == Lg.byte(0n, p) : Lg.P}:
  match p:
    case Lg.P{ls, t}:
      {==}

def pl.eta(p: Lg.P) -> {Lg.P{Lg.P.ls(p), Lg.P.tl(p)} == p : Lg.P}:
  match p:
    case Lg.P{ls, t}:
      {==}

# a line, its newline, and the bytes y after it
def pl.parse_line(l: List<&2, Nat>, +y: List<&2, Nat>) -> {Lg.P{l <> Lg.P.ls(Lg.parse(y)), Lg.P.tl(Lg.parse(y))} == Lg.parse(List.append(&2, Nat, Lg.data(l), 0n <> y)) : Lg.P}:
  match l:
    case Nil{}:
      pl.byte0(Lg.parse(y))
    case +x <> rest:
      %pl.parse_line(rest, y) : {Lg.P{(x <> rest) <> Lg.P.ls(Lg.parse(y)), Lg.P.tl(Lg.parse(y))} == Lg.byte(1n+x, _) : Lg.P}
      {==}

def pl.parse_render(ls: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Lg.P{List.append(&2, List<&2, Nat>, ls, Lg.P.ls(Lg.parse(x))), Lg.P.tl(Lg.parse(x))} == Lg.parse(List.append(&2, Nat, Lg.render(ls), x)) : Lg.P}:
  match ls:
    case Nil{}:
      pl.eta(Lg.parse(x))
    case +l <> +rest:
      +y = List.append(&2, Nat, Lg.render(rest), x)
      %pl.assoc(Nat, Lg.line(l), Lg.render(rest), x) : {Lg.P{l <> List.append(&2, List<&2, Nat>, rest, Lg.P.ls(Lg.parse(x))), Lg.P.tl(Lg.parse(x))} == Lg.parse(_) : Lg.P}
      %pl.assoc(Nat, Lg.data(l), [0n], y) : {Lg.P{l <> List.append(&2, List<&2, Nat>, rest, Lg.P.ls(Lg.parse(x))), Lg.P.tl(Lg.parse(x))} == Lg.parse(_) : Lg.P}
      %pl.parse_line(l, y) : {Lg.P{l <> List.append(&2, List<&2, Nat>, rest, Lg.P.ls(Lg.parse(x))), Lg.P.tl(Lg.parse(x))} == _ : Lg.P}
      %pl.parse_render(rest, x) : {Lg.P{l <> List.append(&2, List<&2, Nat>, rest, Lg.P.ls(Lg.parse(x))), Lg.P.tl(Lg.parse(x))} == Lg.P{l <> Lg.P.ls(_), Lg.P.tl(_)} : Lg.P}
      {==}

# open reads the lines of render(ls) and then those of x
def pl.recover_render(+ls: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {List.append(&2, List<&2, Nat>, ls, Lg.recover(x)) == Lg.recover(List.append(&2, Nat, Lg.render(ls), x)) : List<&2, List<&2, Nat>>}:
  %pl.parse_render(ls, x) : {List.append(&2, List<&2, Nat>, ls, Lg.recover(x)) == Lg.P.ls(_) : List<&2, List<&2, Nat>>}
  {==}

# A torn line
# -----------

# the data byte x before the first line, if any
def pl.head(x: Nat, ls: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      (x <> l) <> rest

# the lines the first k bytes of the line c give: none, or c
def log.pl.keep(k: Nat, c: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      match c:
        case Nil{}:
          [Nil{}]
        case x <> rest:
          pl.head(x, log.pl.keep(j, rest))

def pl.byte_s(x: Nat, p: Lg.P) -> {pl.head(x, Lg.P.ls(p)) == Lg.P.ls(Lg.byte(1n+x, p)) : List<&2, List<&2, Nat>>}:
  match p:
    case Lg.P{ls, t}:
      match ls:
        case Nil{}:
          {==}
        case l <> rest:
          {==}

def pl.torn(+k: Nat, c: List<&2, Nat>) -> {log.pl.keep(k, c) == Lg.recover(List.take(&2, Nat, Lg.line(c), k)) : List<&2, List<&2, Nat>>}:
  match k:
    case 0n:
      match c:
        case Nil{}:
          {==}
        case x <> rest:
          {==}
    case 1n+j:
      match c:
        case Nil{}:
          {==}
        case +x <> +rest:
          %pl.byte_s(x, Lg.parse(List.take(&2, Nat, Lg.line(rest), j))) : {pl.head(x, log.pl.keep(j, rest)) == _ : List<&2, List<&2, Nat>>}
          %pl.torn(j, rest) : {pl.head(x, log.pl.keep(j, rest)) == pl.head(x, _) : List<&2, List<&2, Nat>>}
          {==}

# The state
# ---------

def pl.de(s: Lg.St) -> Bool:
  match s:
    case Lg.St{de, fe, log, pend, acked}:
      de

def pl.fe(s: Lg.St) -> Bool:
  match s:
    case Lg.St{de, fe, log, pend, acked}:
      fe

# what an open after a crash that keeps the file reads
def pl.fin(k: Nat, s: Lg.St) -> List<&2, List<&2, Nat>>:
  match s:
    case Lg.St{de, fe, log, pend, acked}:
      Lg.recover(List.append(&2, Nat, Lg.render(log), Lg.cut(k, pend)))

def pl.pick(b: Bool, xs: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match b:
    case True{}:
      xs
    case False{}:
      Nil{}

def pl.rl(+xs: List<&2, List<&2, Nat>>) -> {xs == Lg.recover(List.append(&2, Nat, Lg.render(xs), Nil{})) : List<&2, List<&2, Nat>>}:
  Equal.trans(List<&2, List<&2, Nat>>, xs, List.append(&2, List<&2, Nat>, xs, Nil{}), Lg.recover(List.append(&2, Nat, Lg.render(xs), Nil{})), pl.app_nil(List<&2, Nat>, xs), pl.recover_render(xs, Nil{}))

def pl.stays(b: Bool, +bytes: List<&2, Nat>) -> {pl.pick(b, Lg.recover(bytes)) == Lg.Disk.log(Lg.stays(b, bytes)) : List<&2, List<&2, Nat>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pl.cr(+k: Nat, +drop: Bool, s: Lg.St) -> {pl.pick(Lg.keeps(drop, pl.de(s), pl.fe(s)), pl.fin(k, s)) == Lg.Disk.log(Lg.crash(k, drop, s)) : List<&2, List<&2, Nat>>}:
  match s:
    case Lg.St{+de, +fe, +log, +pend, acked}:
      pl.stays(Lg.keeps(drop, de, fe), List.append(&2, Nat, Lg.render(log), Lg.cut(k, pend)))

# a crash that keeps the file: the disk reads fin
def pl.surv(+k: Nat, +drop: Bool, +s: Lg.St, h: {True{} == Lg.keeps(drop, pl.de(s), pl.fe(s)) : Bool}) -> {pl.fin(k, s) == Lg.Disk.log(Lg.crash(k, drop, s)) : List<&2, List<&2, Nat>>}:
  +f = pl.fin(k, s)
  Equal.trans(List<&2, List<&2, Nat>>, f, pl.pick(Lg.keeps(drop, pl.de(s), pl.fe(s)), f), Lg.Disk.log(Lg.crash(k, drop, s)), (%h : {f == pl.pick(_, f) : List<&2, List<&2, Nat>>}; {==}), pl.cr(k, drop, s))

def pl.kt(drop: Bool) -> {True{} == Lg.keeps(drop, True{}, True{}) : Bool}:
  match drop:
    case True{}:
      {==}
    case False{}:
      {==}

# the commits after the first keep the flags
def pl.md(cs: List<&2, List<&2, Nat>>, +p: Nat, +de: Bool, +fe: Bool, +l: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>) -> {de == pl.de(Lg.more(cs, p, Lg.St{de, fe, l, None{}, a})) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match p:
        case 0n:
          {==}
        case 1n+p1:
          match p1:
            case 0n:
              {==}
            case 1n+p2:
              pl.md(rest, p2, de, fe, List.append(&2, List<&2, Nat>, l, [c]), List.append(&2, List<&2, Nat>, a, [c]))

def pl.me(cs: List<&2, List<&2, Nat>>, +p: Nat, +de: Bool, +fe: Bool, +l: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>) -> {fe == pl.fe(Lg.more(cs, p, Lg.St{de, fe, l, None{}, a})) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match p:
        case 0n:
          {==}
        case 1n+p1:
          match p1:
            case 0n:
              {==}
            case 1n+p2:
              pl.me(rest, p2, de, fe, List.append(&2, List<&2, Nat>, l, [c]), List.append(&2, List<&2, Nat>, a, [c]))

def pl.fd(cs: List<&2, List<&2, Nat>>, +q: Nat, +fe: Bool, +l: List<&2, List<&2, Nat>>) -> {True{} == pl.de(Lg.first(cs, q, Lg.St{True{}, fe, l, None{}, Nil{}})) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match q:
        case 0n:
          {==}
        case 1n+q1:
          match q1:
            case 0n:
              {==}
            case 1n+q2:
              match q2:
                case 0n:
                  {==}
                case 1n+q3:
                  pl.md(rest, q3, True{}, True{}, List.append(&2, List<&2, Nat>, l, [c]), [c])

def pl.ffe(cs: List<&2, List<&2, Nat>>, +q: Nat, +de: Bool, +l: List<&2, List<&2, Nat>>) -> {True{} == pl.fe(Lg.first(cs, q, Lg.St{de, True{}, l, None{}, Nil{}})) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match q:
        case 0n:
          {==}
        case 1n+q1:
          match q1:
            case 0n:
              {==}
            case 1n+q2:
              match q2:
                case 0n:
                  {==}
                case 1n+q3:
                  pl.me(rest, q3, de, True{}, List.append(&2, List<&2, Nat>, l, [c]), [c])

# both flags of the more commits after an absent file's first commit
def pl.mt(+drop: Bool, +rest: List<&2, List<&2, Nat>>, +q: Nat, +l: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>) -> {True{} == Lg.keeps(drop, pl.de(Lg.more(rest, q, Lg.St{True{}, True{}, l, None{}, a})), pl.fe(Lg.more(rest, q, Lg.St{True{}, True{}, l, None{}, a}))) : Bool}:
  +m = Lg.more(rest, q, Lg.St{True{}, True{}, l, None{}, a})
  %pl.md(rest, q, True{}, True{}, l, a) : {True{} == Lg.keeps(drop, _, pl.fe(m)) : Bool}
  %pl.me(rest, q, True{}, True{}, l, a) : {True{} == Lg.keeps(drop, True{}, _) : Bool}
  pl.kt(drop)

# both flags after a present file's commits
def pl.ft(+drop: Bool, +cs: List<&2, List<&2, Nat>>, +q: Nat, +l: List<&2, List<&2, Nat>>) -> {True{} == Lg.keeps(drop, pl.de(Lg.first(cs, q, Lg.St{True{}, True{}, l, None{}, Nil{}})), pl.fe(Lg.first(cs, q, Lg.St{True{}, True{}, l, None{}, Nil{}}))) : Bool}:
  +m = Lg.first(cs, q, Lg.St{True{}, True{}, l, None{}, Nil{}})
  %pl.fd(cs, q, True{}, l) : {True{} == Lg.keeps(drop, _, pl.fe(m)) : Bool}
  %pl.ffe(cs, q, True{}, l) : {True{} == Lg.keeps(drop, True{}, _) : Bool}
  pl.kt(drop)
