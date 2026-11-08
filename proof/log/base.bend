# eukhe: lemmas the proofs of area log share

import Base
import ../../spec/durable/log.bend as Lg
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../base/wire.bend as LWire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/logic/bool.bend as LLogicBool

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

# The open of a file
# ------------------

# a file's last newline and its length, read off its parse

def pl.pre(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      k

# the last newline of the bytes of the lines ls (and any tail after them)
def pl.lastof(ls: List<&2, List<&2, Nat>>) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case l <> r:
      Some{pl.pre(List.length(&2, Nat, Lg.render(l <> r)))}

# the length of the bytes of a parse
def pl.vlen(p: Lg.P) -> Nat:
  match p:
    case Lg.P{ls, t}:
      Nat.add(List.length(&2, Nat, Lg.render(ls)), List.length(&2, Nat, t))

# lines that are not none have bytes
def pl.pre_len(l: List<&2, Nat>, r: List<&2, List<&2, Nat>>) -> {1n+pl.pre(List.length(&2, Nat, Lg.render(l <> r))) == List.length(&2, Nat, Lg.render(l <> r)) : Nat}:
  match l:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

def pl.last_byte(b: Nat, p: Lg.P) -> {Log.log_last.at(b, pl.lastof(Lg.P.ls(p))) == pl.lastof(Lg.P.ls(Lg.byte(b, p))) : Maybe<&2, Nat>}:
  match b:
    case 0n:
      match p:
        case Lg.P{ls, t}:
          match ls:
            case Nil{}:
              {==}
            case +l <> +r:
              %pl.pre_len(l, r) : {Some{1n+pl.pre(List.length(&2, Nat, Lg.render(l <> r)))} == Some{_} : Maybe<&2, Nat>}
              {==}
    case 1n+c:
      match p:
        case Lg.P{ls, t}:
          match ls:
            case Nil{}:
              {==}
            case +l <> +r:
              %pl.pre_len(l, r) : {Some{1n+pl.pre(List.length(&2, Nat, Lg.render(l <> r)))} == Some{_} : Maybe<&2, Nat>}
              {==}

# the last newline of a file is the one of its parse
def pl.last_parse(f: List<&2, Nat>) -> {pl.lastof(Lg.P.ls(Lg.parse(f))) == Log.log_last(f) : Maybe<&2, Nat>}:
  match f:
    case Nil{}:
      {==}
    case +b <> +rest:
      %pl.last_parse(rest) : {pl.lastof(Lg.P.ls(Lg.byte(b, Lg.parse(rest)))) == Log.log_last.at(b, _) : Maybe<&2, Nat>}
      Equal.sym(Maybe<&2, Nat>, Log.log_last.at(b, pl.lastof(Lg.P.ls(Lg.parse(rest)))), pl.lastof(Lg.P.ls(Lg.byte(b, Lg.parse(rest)))), pl.last_byte(b, Lg.parse(rest)))

def pl.len_byte(b: Nat, p: Lg.P) -> {1n+pl.vlen(p) == pl.vlen(Lg.byte(b, p)) : Nat}:
  match b:
    case 0n:
      match p:
        case Lg.P{ls, t}:
          {==}
    case 1n+c:
      match p:
        case Lg.P{ls, t}:
          match ls:
            case Nil{}:
              {==}
            case l <> r:
              {==}

# the length of a file is the one of its parse
def pl.len_parse(f: List<&2, Nat>) -> {pl.vlen(Lg.parse(f)) == List.length(&2, Nat, f) : Nat}:
  match f:
    case Nil{}:
      {==}
    case +b <> +rest:
      %pl.len_parse(rest) : {pl.vlen(Lg.byte(b, Lg.parse(rest))) == 1n+_ : Nat}
      Equal.sym(Nat, 1n+pl.vlen(Lg.parse(rest)), pl.vlen(Lg.byte(b, Lg.parse(rest))), pl.len_byte(b, Lg.parse(rest)))

def pl.le_add(k: Nat, n: Nat) -> {True{} == Nat.is_le(k, Nat.add(k, n)) : Bool}:
  match k:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+m:
          {==}
    case 1n+j:
      pl.le_add(j, n)

def pl.eq_add(k: Nat, n: Nat) -> {Nat.is_eq(0n, n) == Nat.is_eq(k, Nat.add(k, n)) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      pl.eq_add(j, n)

# the open of a parse's facts: the rule against its spec, for the lines
# l <> r whose bytes are 1 + k long
def pl.tail_lines(+k: Nat, t: List<&2, Nat>, l: List<&2, Nat>, r: List<&2, List<&2, Nat>>, e: {1n+k == List.length(&2, Nat, Lg.render(l <> r)) : Nat}) -> {Lr.tail(Nat.add(1n+k, List.length(&2, Nat, t)), Some{k}) == Log.log_tail_spec.of(l <> r, t) : Lr.Tail}:
  match t:
    case Nil{}:
      %pl.le_add(k, 0n) : {Lr.tail.in(_, Nat.add(1n+k, 0n), 1n+k) == Lr.Whole{} : Lr.Tail}
      %pl.eq_add(k, 0n) : {Lr.tail.at(_, 1n+k) == Lr.Whole{} : Lr.Tail}
      {==}
    case +x <> +rest:
      %pl.le_add(k, 1n+List.length(&2, Nat, rest)) : {Lr.tail.in(_, Nat.add(1n+k, 1n+List.length(&2, Nat, rest)), 1n+k) == Lr.Torn{List.length(&2, Nat, Lg.render(l <> r))} : Lr.Tail}
      %pl.eq_add(k, 1n+List.length(&2, Nat, rest)) : {Lr.tail.at(_, 1n+k) == Lr.Torn{List.length(&2, Nat, Lg.render(l <> r))} : Lr.Tail}
      %e : {Lr.Torn{1n+k} == Lr.Torn{_} : Lr.Tail}
      {==}

# the open of a parse's facts is the spec's
def pl.tail_p(p: Lg.P) -> {Lr.tail(pl.vlen(p), pl.lastof(Lg.P.ls(p))) == Log.log_tail_spec.p(p) : Lr.Tail}:
  match p:
    case Lg.P{ls, t}:
      match ls:
        case Nil{}:
          match t:
            case Nil{}:
              {==}
            case x <> rest:
              {==}
        case +l <> +r:
          +n = List.length(&2, Nat, Lg.render(l <> r))
          %pl.pre_len(l, r) : {Lr.tail(Nat.add(_, List.length(&2, Nat, t)), Some{pl.pre(n)}) == Log.log_tail_spec.of(l <> r, t) : Lr.Tail}
          pl.tail_lines(pl.pre(n), t, l, r, pl.pre_len(l, r))

# The entry
# ---------

# A list of Bools on the wire: its count, then its items (pe.put_list);
# it reads back (pe.rt), and a decoded one is exactly an encoding
# (pe.bools_exact), item by item as laws/wire.bend's list of Nats.

# the items of a list of Bools, then rest
def pe.bools(ds: List<&2, Bool>, rest: String) -> String:
  match ds:
    case Nil{}:
      rest
    case d <> t:
      Wr.put_bool(d, pe.bools(t, rest))

def pe.put_go(ds: List<&2, Bool>, -rest: String) -> {Wr.put_list.go(~Bool, ~Wr.put_bool, ds, rest) == (List.length(&2, Bool, ds), pe.bools(ds, rest)) : Nat & String}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Bool, ~Wr.put_bool, t, rest), (List.length(&2, Bool, t), pe.bools(t, rest)), pe.put_go(t, rest)) : {Wr.put_list.step(~Bool, ~Wr.put_bool, d, _) == (1n+List.length(&2, Bool, t), Wr.put_bool(d, pe.bools(t, rest))) : Nat & String}
      {==}

def pe.put_list(+ds: List<&2, Bool>, -rest: String) -> {Wr.put_list(~Bool, ~Wr.put_bool, ds, rest) == Wr.put_nat(List.length(&2, Bool, ds), pe.bools(ds, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Bool, ~Wr.put_bool, ds, rest), (List.length(&2, Bool, ds), pe.bools(ds, rest)), pe.put_go(ds, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Bool, ds), pe.bools(ds, rest)) : String}
  {==}

# the item loop reads back x, then t
def pe.go_rt(+t: List<&2, Bool>, x: Bool, +rest: String) -> {Wr.get_list.go(~Bool, ~Wr.get_bool, List.length(&2, Bool, t), Wr.get_bool(Wr.put_bool(x, pe.bools(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Bool>>}:
  match t:
    case Nil{}:
      match x:
        case True{}:
          {==}
        case False{}:
          {==}
    case +y <> +u:
      match x:
        case True{}:
          +g = Wr.get_list.go(~Bool, ~Wr.get_bool, List.length(&2, Bool, u), Wr.get_bool(Wr.put_bool(y, pe.bools(u, rest))))
          %Equal.sym(Wr.Dec<List<&2, Bool>>, g, Wr.Got{y <> u, rest}, pe.go_rt(u, y, rest)) : {Wr.get_list.cons(Bool, True{}, _) == Wr.Got{True{} <> y <> u, rest} : Wr.Dec<List<&2, Bool>>}
          {==}
        case False{}:
          +g = Wr.get_list.go(~Bool, ~Wr.get_bool, List.length(&2, Bool, u), Wr.get_bool(Wr.put_bool(y, pe.bools(u, rest))))
          %Equal.sym(Wr.Dec<List<&2, Bool>>, g, Wr.Got{y <> u, rest}, pe.go_rt(u, y, rest)) : {Wr.get_list.cons(Bool, False{}, _) == Wr.Got{False{} <> y <> u, rest} : Wr.Dec<List<&2, Bool>>}
          {==}

# a list of Bools whose count fits reads back
def pe.rt(ds: List<&2, Bool>, +rest: String, h: {LawsBase.wire_fits(List.length(&2, Bool, ds)) == True{} : Bool}) -> {Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_list(~Bool, ~Wr.put_bool, ds, rest)) == Wr.Got{ds, rest} : Wr.Dec<List<&2, Bool>>}:
  match ds:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(String, Wr.put_list(~Bool, ~Wr.put_bool, x <> t, rest), Wr.put_nat(1n+List.length(&2, Bool, t), pe.bools(x <> t, rest)), pe.put_list(x <> t, rest)) : {Wr.get_list(~Bool, ~Wr.get_bool, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Bool>>}
      %LWire.pc.nat(1n+List.length(&2, Bool, t), pe.bools(x <> t, rest), h) : {Wr.get_list.start(~Bool, ~Wr.get_bool, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Bool>>}
      pe.go_rt(t, x, rest)

# what the item loop's answer says about its input s (m + 1 items)
def pe.pl(s: String, m: Nat, d: Wr.Dec<List<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == pe.bools(xs, r) : String} & {List.length(&2, Bool, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def pe.list_step(-s: String, +x: Bool, +s3: String, -k: Nat, ex: {s == Wr.put_bool(x, s3) : String}, d: Wr.Dec<List<&2, Bool>>, ih: pe.pl(s3, k, d)) -> pe.pl(s, 1n+k, Wr.get_list.cons(Bool, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, Wr.put_bool(x, s3), Wr.put_bool(x, pe.bools(ys, r)), ex, Equal.cong(String, String, z => Wr.put_bool(x, z), s3, pe.bools(ys, r), e1)), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Bool, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only items that are encodings
def pe.list_spec(m: Nat, cur: Wr.Dec<Bool>, +s: String, er: {Wr.get_bool(s) == cur : Wr.Dec<Bool>}) -> pe.pl(s, m, Wr.get_list.go(~Bool, ~Wr.get_bool, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (Wire.wire_bool_exact(s, x, s3, er), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      pe.list_step(s, x, s3, k, Wire.wire_bool_exact(s, x, s3, er), Wr.get_list.go(~Bool, ~Wr.get_bool, k, Wr.get_bool(s3)), pe.list_spec(k, Wr.get_bool(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def pe.pls(s: String, d: Wr.Dec<List<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~Bool, ~Wr.put_bool, xs, r) : String}
    case Wr.Bad{}:
      Unit

def pe.list_conv(+s: String, +s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, d: Wr.Dec<List<&2, Bool>>, pl: pe.pl(s2, m, d)) -> pe.pls(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = pl
      %Equal.sym(String, Wr.put_list(~Bool, ~Wr.put_bool, xs, r), Wr.put_nat(List.length(&2, Bool, xs), pe.bools(xs, r)), pe.put_list(xs, r)) : {s == _ : String}
      %Equal.sym(Nat, List.length(&2, Bool, xs), 1n+m, e2) : {s == Wr.put_nat(_, pe.bools(xs, r)) : String}
      %e1 : {s == Wr.put_nat(1n+m, _) : String}
      en
    case Wr.Bad{}:
      Unit{}

def pe.list_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}) -> pe.pls(s, Wr.get_list.start(~Bool, ~Wr.get_bool, Wr.Got{n, s2})):
  match n:
    case 0n:
      en
    case 1n++m:
      pe.list_conv(s, s2, m, en, Wr.get_list.go(~Bool, ~Wr.get_bool, m, Wr.get_bool(s2)), pe.list_spec(m, Wr.get_bool(s2), s2, {==}))

def pe.list_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> pe.pls(s, Wr.get_list.start(~Bool, ~Wr.get_bool, r)):
  match r:
    case Wr.Got{+n, +s2}:
      pe.list_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

# a decoded list of Bools is exactly an encoding
def pe.bools_exact(+s: String, -ds: List<&2, Bool>, -rest: String, h: {Wr.get_list(~Bool, ~Wr.get_bool, s) == Wr.Got{ds, rest} : Wr.Dec<List<&2, Bool>>}) -> {s == Wr.put_list(~Bool, ~Wr.put_bool, ds, rest) : String}:
  %h : pe.pls(s, _)
  pe.list_top(s, Wr.get_nat(s), {==})

# the reply of a list is no error form
def pe.fin_ok(r: Nat & String) -> {LawsBase.wire_opens_err(Wr.put_list.fin(r)) == False{} : Bool}:
  (n, s) = r
  Wire.wire_nat_not_err(n, s)

# a plan's reply is no error form
def pe.reply_ok(p: Lr.Plan) -> {LawsBase.wire_opens_err(Log.log_reply(FLg.reply(p))) == False{} : Bool}:
  match p:
    case Lr.Plan{s, acts}:
      pe.fin_ok(Wr.put_list.go(~Lr.Act, ~FLg.put_act, acts, ""))
