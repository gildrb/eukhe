# proof_log: the commit log laws of laws/storage.bend (D2): open reads
# exactly the complete lines, and after any epoch (any commits, any crash
# point, any torn tail, any lost entries) the log is the old log, then the
# acknowledged commits, then maybe more, and only a prefix of the commits.
#
# A helper lemma {s == t} has the simpler side s first: `%lemma : P`
# turns the t in the goal into s.

import Base
import ./log.bend as Lg

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

def pl.take0(-A: Data, xs: List<&2, A>) -> {Nil{} == List.take(&2, A, xs, 0n) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

# Parsing
# -------

def pl.parse_data(t: List<&2, Nat>) -> {Lg.P{Nil{}, t} == Lg.parse(Lg.data(t)) : Lg.P}:
  match t:
    case Nil{}:
      {==}
    case +x <> rest:
      %pl.parse_data(rest) : {Lg.P{Nil{}, x <> rest} == Lg.byte(1n+x, _) : Lg.P}
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

# the law log_reads_lines
def pl.reads_lines(+ls: List<&2, List<&2, Nat>>, +t: List<&2, Nat>) -> {Lg.recover(List.append(&2, Nat, Lg.render(ls), Lg.data(t))) == ls : List<&2, List<&2, Nat>>}:
  %pl.recover_render(ls, Lg.data(t)) : {_ == ls : List<&2, List<&2, Nat>>}
  %pl.parse_data(t) : {List.append(&2, List<&2, Nat>, ls, Lg.P.ls(_)) == ls : List<&2, List<&2, Nat>>}
  %pl.app_nil(List<&2, Nat>, ls) : {_ == ls : List<&2, List<&2, Nat>>}
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
def pl.keep(k: Nat, c: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      match c:
        case Nil{}:
          [Nil{}]
        case x <> rest:
          pl.head(x, pl.keep(j, rest))

def pl.byte_s(x: Nat, p: Lg.P) -> {pl.head(x, Lg.P.ls(p)) == Lg.P.ls(Lg.byte(1n+x, p)) : List<&2, List<&2, Nat>>}:
  match p:
    case Lg.P{ls, t}:
      match ls:
        case Nil{}:
          {==}
        case l <> rest:
          {==}

def pl.torn(+k: Nat, c: List<&2, Nat>) -> {pl.keep(k, c) == Lg.recover(List.take(&2, Nat, Lg.line(c), k)) : List<&2, List<&2, Nat>>}:
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
          %pl.byte_s(x, Lg.parse(List.take(&2, Nat, Lg.line(rest), j))) : {pl.head(x, pl.keep(j, rest)) == _ : List<&2, List<&2, Nat>>}
          %pl.torn(j, rest) : {pl.head(x, pl.keep(j, rest)) == pl.head(x, _) : List<&2, List<&2, Nat>>}
          {==}

# the head x before a cut of the commits
def pl.head_take(x: Nat, c: List<&2, Nat>, rest: List<&2, List<&2, Nat>>, n: Nat) -> {pl.head(x, List.take(&2, List<&2, Nat>, c <> rest, n)) == List.take(&2, List<&2, Nat>, (x <> c) <> rest, n) : List<&2, List<&2, Nat>>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def pl.head_pair(+x: Nat, +cs: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, -K: List<&2, List<&2, Nat>>, r: &n: Nat -> {K == List.take(&2, List<&2, Nat>, cs <> rest, n) : List<&2, List<&2, Nat>>}) -> &n: Nat -> {pl.head(x, K) == List.take(&2, List<&2, Nat>, (x <> cs) <> rest, n) : List<&2, List<&2, Nat>>}:
  match r:
    case (+m, e):
      (m, (%Equal.sym(List<&2, List<&2, Nat>>, K, List.take(&2, List<&2, Nat>, cs <> rest, m), e) : {pl.head(x, _) == List.take(&2, List<&2, Nat>, (x <> cs) <> rest, m) : List<&2, List<&2, Nat>>}; pl.head_take(x, cs, rest, m)))

# a torn line is a prefix of the commits from it
def pl.keep_take(k: Nat, c: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>) -> &n: Nat -> {pl.keep(k, c) == List.take(&2, List<&2, Nat>, c <> rest, n) : List<&2, List<&2, Nat>>}:
  match k:
    case 0n:
      (0n, {==})
    case 1n+j:
      match c:
        case Nil{}:
          (1n, (%pl.take0(List<&2, Nat>, rest) : {[Nil{}] == Nil{} <> _ : List<&2, List<&2, Nat>>}; {==}))
        case +x <> +cs:
          pl.head_pair(x, cs, rest, pl.keep(j, cs), pl.keep_take(j, cs, rest))

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

# Only a prefix of the commits
# ---------------------------

def pl.ml1_torn(+l: List<&2, List<&2, Nat>>, +c: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +k: Nat, r: &n: Nat -> {pl.keep(k, c) == List.take(&2, List<&2, Nat>, c <> rest, n) : List<&2, List<&2, Nat>>}) -> &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, c <> rest, n)) == Lg.recover(List.append(&2, Nat, Lg.render(l), List.take(&2, Nat, Lg.line(c), k))) : List<&2, List<&2, Nat>>}:
  match r:
    case (+n, e):
      (n, (%pl.recover_render(l, List.take(&2, Nat, Lg.line(c), k)) : {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, c <> rest, n)) == _ : List<&2, List<&2, Nat>>}; %pl.torn(k, c) : {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, c <> rest, n)) == List.append(&2, List<&2, Nat>, l, _) : List<&2, List<&2, Nat>>}; %e : {List.append(&2, List<&2, Nat>, l, _) == List.append(&2, List<&2, Nat>, l, pl.keep(k, c)) : List<&2, List<&2, Nat>>}; {==}))

def pl.ml1_step(+l: List<&2, List<&2, Nat>>, +c: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, -f: List<&2, List<&2, Nat>>, r: &n: Nat -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, [c]), List.take(&2, List<&2, Nat>, rest, n)) == f : List<&2, List<&2, Nat>>}) -> &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, c <> rest, n)) == f : List<&2, List<&2, Nat>>}:
  match r:
    case (+n, e):
      (1n+n, Equal.trans(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, l, c <> List.take(&2, List<&2, Nat>, rest, n)), List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, [c]), List.take(&2, List<&2, Nat>, rest, n)), f, pl.assoc(List<&2, Nat>, l, [c], List.take(&2, List<&2, Nat>, rest, n)), e))

def pl.ml1(cs: List<&2, List<&2, Nat>>, +p: Nat, +k: Nat, +de: Bool, +fe: Bool, +l: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>) -> &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, cs, n)) == pl.fin(k, Lg.more(cs, p, Lg.St{de, fe, l, None{}, a})) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      (0n, pl.recover_render(l, Nil{}))
    case +c <> +rest:
      match p:
        case 0n:
          (0n, pl.recover_render(l, Nil{}))
        case 1n+p1:
          match p1:
            case 0n:
              pl.ml1_torn(l, c, rest, k, pl.keep_take(k, c, rest))
            case 1n+p2:
              +l2 = List.append(&2, List<&2, Nat>, l, [c])
              +a2 = List.append(&2, List<&2, Nat>, a, [c])
              pl.ml1_step(l, c, rest, pl.fin(k, Lg.more(rest, p2, Lg.St{de, fe, l2, None{}, a2})), pl.ml1(rest, p2, k, de, fe, l2, a2))

def pl.f1(cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat, +fe: Bool, +l: List<&2, List<&2, Nat>>) -> &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, cs, n)) == pl.fin(k, Lg.first(cs, q, Lg.St{True{}, fe, l, None{}, Nil{}})) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      (0n, pl.recover_render(l, Nil{}))
    case +c <> +rest:
      match q:
        case 0n:
          (0n, pl.recover_render(l, Nil{}))
        case 1n+q1:
          match q1:
            case 0n:
              pl.ml1_torn(l, c, rest, k, pl.keep_take(k, c, rest))
            case 1n+q2:
              match q2:
                case 0n:
                  +l2 = List.append(&2, List<&2, Nat>, l, [c])
                  (1n, (%pl.take0(List<&2, Nat>, rest) : {List.append(&2, List<&2, Nat>, l, c <> _) == Lg.recover(List.append(&2, Nat, Lg.render(l2), Nil{})) : List<&2, List<&2, Nat>>}; pl.rl(l2)))
                case 1n+q3:
                  +l2 = List.append(&2, List<&2, Nat>, l, [c])
                  pl.ml1_step(l, c, rest, pl.fin(k, Lg.more(rest, q3, Lg.St{True{}, True{}, l2, None{}, [c]})), pl.ml1(rest, q3, k, True{}, True{}, l2, [c]))

# The acknowledged commits are kept
# ---------------------------------

def pl.ml2(cs: List<&2, List<&2, Nat>>, +p: Nat, +k: Nat, +de: Bool, +fe: Bool, +l0: List<&2, List<&2, Nat>>, +l: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>, h: {l == List.append(&2, List<&2, Nat>, l0, a) : List<&2, List<&2, Nat>>}) -> &r: List<&2, List<&2, Nat>> -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l0, Lg.St.acked(Lg.more(cs, p, Lg.St{de, fe, l, None{}, a}))), r) == pl.fin(k, Lg.more(cs, p, Lg.St{de, fe, l, None{}, a})) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      +la = List.append(&2, List<&2, Nat>, l0, a)
      (Nil{}, (%pl.recover_render(l, Nil{}) : {List.append(&2, List<&2, Nat>, la, Nil{}) == _ : List<&2, List<&2, Nat>>}; %h : {List.append(&2, List<&2, Nat>, _, Nil{}) == List.append(&2, List<&2, Nat>, l, Nil{}) : List<&2, List<&2, Nat>>}; {==}))
    case +c <> +rest:
      match p:
        case 0n:
          +la = List.append(&2, List<&2, Nat>, l0, a)
          (Nil{}, (%pl.recover_render(l, Nil{}) : {List.append(&2, List<&2, Nat>, la, Nil{}) == _ : List<&2, List<&2, Nat>>}; %h : {List.append(&2, List<&2, Nat>, _, Nil{}) == List.append(&2, List<&2, Nat>, l, Nil{}) : List<&2, List<&2, Nat>>}; {==}))
        case 1n+p1:
          match p1:
            case 0n:
              +la = List.append(&2, List<&2, Nat>, l0, a)
              (pl.keep(k, c), (%pl.recover_render(l, List.take(&2, Nat, Lg.line(c), k)) : {List.append(&2, List<&2, Nat>, la, pl.keep(k, c)) == _ : List<&2, List<&2, Nat>>}; %pl.torn(k, c) : {List.append(&2, List<&2, Nat>, la, pl.keep(k, c)) == List.append(&2, List<&2, Nat>, l, _) : List<&2, List<&2, Nat>>}; %h : {List.append(&2, List<&2, Nat>, _, pl.keep(k, c)) == List.append(&2, List<&2, Nat>, l, pl.keep(k, c)) : List<&2, List<&2, Nat>>}; {==}))
            case 1n+p2:
              +la = List.append(&2, List<&2, Nat>, l0, a)
              +a2 = List.append(&2, List<&2, Nat>, a, [c])
              pl.ml2(rest, p2, k, de, fe, l0, List.append(&2, List<&2, Nat>, l, [c]), a2, (%Equal.sym(List<&2, List<&2, Nat>>, l, la, h) : {List.append(&2, List<&2, Nat>, _, [c]) == List.append(&2, List<&2, Nat>, l0, a2) : List<&2, List<&2, Nat>>}; Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, l0, a2), List.append(&2, List<&2, Nat>, la, [c]), pl.assoc(List<&2, Nat>, l0, a, [c]))))

def pl.fa(cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat, +fe: Bool, +l: List<&2, List<&2, Nat>>) -> &r: List<&2, List<&2, Nat>> -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, Lg.St.acked(Lg.first(cs, q, Lg.St{True{}, fe, l, None{}, Nil{}}))), r) == pl.fin(k, Lg.first(cs, q, Lg.St{True{}, fe, l, None{}, Nil{}})) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      pl.ml2(Nil{}, 0n, k, True{}, fe, l, l, Nil{}, pl.app_nil(List<&2, Nat>, l))
    case +c <> +rest:
      match q:
        case 0n:
          pl.ml2(Nil{}, 0n, k, True{}, fe, l, l, Nil{}, pl.app_nil(List<&2, Nat>, l))
        case 1n+q1:
          match q1:
            case 0n:
              pl.ml2([c], 1n, k, True{}, fe, l, l, Nil{}, pl.app_nil(List<&2, Nat>, l))
            case 1n+q2:
              match q2:
                case 0n:
                  +l2 = List.append(&2, List<&2, Nat>, l, [c])
                  ([c], (%pl.app_nil(List<&2, Nat>, l) : {List.append(&2, List<&2, Nat>, _, [c]) == Lg.recover(List.append(&2, Nat, Lg.render(l2), Nil{})) : List<&2, List<&2, Nat>>}; pl.rl(l2)))
                case 1n+q3:
                  +l2 = List.append(&2, List<&2, Nat>, l, [c])
                  pl.ml2(rest, q3, k, True{}, True{}, l, l2, [c], {==})

# The laws
# --------

def pl.oc_lift(-l0: List<&2, List<&2, Nat>>, -cs: List<&2, List<&2, Nat>>, -f: List<&2, List<&2, Nat>>, -d: List<&2, List<&2, Nat>>, r: &n: Nat -> {List.append(&2, List<&2, Nat>, l0, List.take(&2, List<&2, Nat>, cs, n)) == f : List<&2, List<&2, Nat>>}, s: {f == d : List<&2, List<&2, Nat>>}) -> &n: Nat -> {d == List.append(&2, List<&2, Nat>, l0, List.take(&2, List<&2, Nat>, cs, n)) : List<&2, List<&2, Nat>>}:
  match r:
    case (+n, e):
      (n, Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, l0, List.take(&2, List<&2, Nat>, cs, n)), d, Equal.trans(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, l0, List.take(&2, List<&2, Nat>, cs, n)), f, d, e, s)))

def pl.ad_lift(-l0: List<&2, List<&2, Nat>>, -a: List<&2, List<&2, Nat>>, -f: List<&2, List<&2, Nat>>, -d: List<&2, List<&2, Nat>>, r: &x: List<&2, List<&2, Nat>> -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l0, a), x) == f : List<&2, List<&2, Nat>>}, s: {f == d : List<&2, List<&2, Nat>>}) -> &x: List<&2, List<&2, Nat>> -> {d == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l0, a), x) : List<&2, List<&2, Nat>>}:
  match r:
    case (+x, e):
      (x, Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l0, a), x), d, Equal.trans(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l0, a), x), f, d, e, s)))

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

# an absent file, a crash that drops the entries
def pl.only_drop(cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat) -> &n: Nat -> {Lg.Disk.log(Lg.crash(k, True{}, Lg.first(cs, q, Lg.St{True{}, False{}, Nil{}, None{}, Nil{}}))) == List.take(&2, List<&2, Nat>, cs, n) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      (0n, {==})
    case +c <> +rest:
      match q:
        case 0n:
          (0n, {==})
        case 1n+q1:
          match q1:
            case 0n:
              (0n, {==})
            case 1n+q2:
              match q2:
                case 0n:
                  (0n, {==})
                case 1n+q3:
                  +m = Lg.more(rest, q3, Lg.St{True{}, True{}, [c], None{}, [c]})
                  pl.oc_lift(Nil{}, c <> rest, pl.fin(k, m), Lg.Disk.log(Lg.crash(k, True{}, m)), pl.ml1_step(Nil{}, c, rest, pl.fin(k, m), pl.ml1(rest, q3, k, True{}, True{}, [c], [c])), pl.surv(k, True{}, m, pl.mt(True{}, rest, q3, [c], [c])))

def pl.ack_drop(cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat) -> &r: List<&2, List<&2, Nat>> -> {Lg.Disk.log(Lg.crash(k, True{}, Lg.first(cs, q, Lg.St{True{}, False{}, Nil{}, None{}, Nil{}}))) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, Nil{}, Lg.St.acked(Lg.first(cs, q, Lg.St{True{}, False{}, Nil{}, None{}, Nil{}}))), r) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      (Nil{}, {==})
    case +c <> +rest:
      match q:
        case 0n:
          (Nil{}, {==})
        case 1n+q1:
          match q1:
            case 0n:
              (Nil{}, {==})
            case 1n+q2:
              match q2:
                case 0n:
                  (Nil{}, {==})
                case 1n+q3:
                  +m = Lg.more(rest, q3, Lg.St{True{}, True{}, [c], None{}, [c]})
                  pl.ad_lift(Nil{}, Lg.St.acked(m), pl.fin(k, m), Lg.Disk.log(Lg.crash(k, True{}, m)), pl.ml2(rest, q3, k, True{}, True{}, Nil{}, [c], [c], {==}), pl.surv(k, True{}, m, pl.mt(True{}, rest, q3, [c], [c])))

# the law log_only_commits
def pl.only(d: Lg.Disk, e: Lg.Epoch) -> &n: Nat -> {Lg.Disk.log(Lg.after(d, e)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), List.take(&2, List<&2, Nat>, Lg.Epoch.cs(e), n)) : List<&2, List<&2, Nat>>}:
  match d:
    case Lg.Absent{}:
      match e:
        case Lg.Epoch{+cs, +p, +k, drop}:
          match p:
            case 0n:
              match drop:
                case True{}:
                  (0n, pl.take0(List<&2, Nat>, cs))
                case False{}:
                  (0n, pl.take0(List<&2, Nat>, cs))
            case 1n+q:
              match drop:
                case True{}:
                  pl.only_drop(cs, q, k)
                case False{}:
                  +m = Lg.first(cs, q, Lg.St{True{}, False{}, Nil{}, None{}, Nil{}})
                  pl.oc_lift(Nil{}, cs, pl.fin(k, m), Lg.Disk.log(Lg.crash(k, False{}, m)), pl.f1(cs, q, k, False{}, Nil{}), pl.surv(k, False{}, m, {==}))
    case Lg.Present{+b}:
      match e:
        case Lg.Epoch{+cs, +p, +k, +drop}:
          match p:
            case 0n:
              +r = Lg.recover(b)
              +s = {Lg.St{True{}, True{}, r, None{}, Nil{}} : Lg.St}
              pl.oc_lift(r, cs, pl.fin(k, s), Lg.Disk.log(Lg.crash(k, drop, s)), (0n, (%pl.take0(List<&2, Nat>, cs) : {List.append(&2, List<&2, Nat>, r, _) == pl.fin(k, s) : List<&2, List<&2, Nat>>}; pl.recover_render(r, Nil{}))), pl.surv(k, drop, s, pl.kt(drop)))
            case 1n+q:
              +r = Lg.recover(b)
              +m = Lg.first(cs, q, Lg.St{True{}, True{}, r, None{}, Nil{}})
              pl.oc_lift(r, cs, pl.fin(k, m), Lg.Disk.log(Lg.crash(k, drop, m)), pl.f1(cs, q, k, True{}, r), pl.surv(k, drop, m, pl.ft(drop, cs, q, r)))

# the law log_ack_durable
def pl.ack(d: Lg.Disk, e: Lg.Epoch) -> &x: List<&2, List<&2, Nat>> -> {Lg.Disk.log(Lg.after(d, e)) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Lg.acked(d, e)), x) : List<&2, List<&2, Nat>>}:
  match d:
    case Lg.Absent{}:
      match e:
        case Lg.Epoch{+cs, +p, +k, drop}:
          match p:
            case 0n:
              match drop:
                case True{}:
                  (Nil{}, {==})
                case False{}:
                  (Nil{}, {==})
            case 1n+q:
              match drop:
                case True{}:
                  pl.ack_drop(cs, q, k)
                case False{}:
                  +m = Lg.first(cs, q, Lg.St{True{}, False{}, Nil{}, None{}, Nil{}})
                  pl.ad_lift(Nil{}, Lg.St.acked(m), pl.fin(k, m), Lg.Disk.log(Lg.crash(k, False{}, m)), pl.fa(cs, q, k, False{}, Nil{}), pl.surv(k, False{}, m, {==}))
    case Lg.Present{+b}:
      match e:
        case Lg.Epoch{+cs, +p, +k, +drop}:
          match p:
            case 0n:
              +r = Lg.recover(b)
              +s = {Lg.St{True{}, True{}, r, None{}, Nil{}} : Lg.St}
              pl.ad_lift(r, Nil{}, pl.fin(k, s), Lg.Disk.log(Lg.crash(k, drop, s)), pl.ml2(Nil{}, 0n, k, True{}, True{}, r, r, Nil{}, pl.app_nil(List<&2, Nat>, r)), pl.surv(k, drop, s, pl.kt(drop)))
            case 1n+q:
              +r = Lg.recover(b)
              +m = Lg.first(cs, q, Lg.St{True{}, True{}, r, None{}, Nil{}})
              pl.ad_lift(r, Lg.St.acked(m), pl.fin(k, m), Lg.Disk.log(Lg.crash(k, drop, m)), pl.fa(cs, q, k, True{}, r), pl.surv(k, drop, m, pl.ft(drop, cs, q, r)))
