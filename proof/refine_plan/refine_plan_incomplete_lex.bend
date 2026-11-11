# eukhe: the proof of LAW refine_plan_incomplete_lex
#
# PROOF: from each spec mode (outside a string, in one, after a backslash
# in one) and counts o and k, the code's scan of a text answers the spec's
# lexed text with o and k added (rpi.go, by induction on the text); a char
# opens or closes a bracket, never both (rpi.excl).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/walk.bend as RefinePlanWalk
import ./base/chars.bend as LCh

def rpi.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, rpi.add_zero(p))

def rpi.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), rpi.add_succ(p, b))

# the code's scan state of a spec mode, with o brackets opened and k closed
def rpi.st(m: RefinePlanWalk.RsMode, o: Nat, k: Nat) -> Rp.Scan:
  match m:
    case RefinePlanWalk.RsOut{}:
      Rp.Scan{False{}, False{}, o, k}
    case RefinePlanWalk.RsStr{}:
      Rp.Scan{True{}, False{}, o, k}
    case RefinePlanWalk.RsEsc{}:
      Rp.Scan{True{}, True{}, o, k}

# the spec's answer of a lexed text with o openers and k closers before it
def rpi.cut(l: RefinePlanWalk.RsLex, o: Nat, k: Nat) -> Bool:
  match l:
    case RefinePlanWalk.RsLex{+out, op}:
      Bool.or(op, Nat.is_gt(Nat.add(RefinePlanWalk.rs_count(out, '{', '['), o), Nat.add(RefinePlanWalk.rs_count(out, '}', ']'), k)))

def rpi.excl.b(+x: U32, b: Bool, eb: {U32.is_eq(x, 91) == b : Bool}) -> {Bool.and(Bool.or(False{}, U32.is_eq(x, 91)), Bool.or(U32.is_eq(x, 125), U32.is_eq(x, 93))) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, x, 91, LCh.sound_fin(x, 91, U32.cmp(x, 91), {==}, eb)) : {Bool.and(Bool.or(False{}, U32.is_eq(_, 91)), Bool.or(U32.is_eq(_, 125), U32.is_eq(_, 93))) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(x, 91), False{}, eb) : {Bool.and(Bool.or(False{}, _), Bool.or(U32.is_eq(x, 125), U32.is_eq(x, 93))) == False{} : Bool}
      {==}

def rpi.excl.a(+x: U32, a: Bool, ea: {U32.is_eq(x, 123) == a : Bool}) -> {Bool.and(Bool.or(U32.is_eq(x, 123), U32.is_eq(x, 91)), Bool.or(U32.is_eq(x, 125), U32.is_eq(x, 93))) == False{} : Bool}:
  match a:
    case True{}:
      %Equal.sym(U32, x, 123, LCh.sound_fin(x, 123, U32.cmp(x, 123), {==}, ea)) : {Bool.and(Bool.or(U32.is_eq(_, 123), U32.is_eq(_, 91)), Bool.or(U32.is_eq(_, 125), U32.is_eq(_, 93))) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(x, 123), False{}, ea) : {Bool.and(Bool.or(_, U32.is_eq(x, 91)), Bool.or(U32.is_eq(x, 125), U32.is_eq(x, 93))) == False{} : Bool}
      rpi.excl.b(x, U32.is_eq(x, 91), {==})

# a char opens a bracket or closes one, never both
def rpi.excl(+x: U32) -> {Bool.and(Bool.or(U32.is_eq(x, 123), U32.is_eq(x, 91)), Bool.or(U32.is_eq(x, 125), U32.is_eq(x, 93))) == False{} : Bool}:
  rpi.excl.a(x, U32.is_eq(x, 123), {==})

# a char kept outside strings: an opener counts on the opened side, a
# closer on the closed side
def rpi.kept(op: Bool, cl: Bool, -bs: Bool, ex: {Bool.and(op, cl) == False{} : Bool}, +t: String, +o: Nat, +k: Nat, +C1: Nat, +C2: Nat, +opn: Bool, ih: {Rp.scan.done(Rp.scan(t, Rp.Scan{False{}, False{}, o, k})) == Bool.or(opn, Nat.is_gt(Nat.add(C1, o), Nat.add(C2, k))) : Bool}, ih_o: {Rp.scan.done(Rp.scan(t, Rp.Scan{False{}, False{}, 1n+o, k})) == Bool.or(opn, Nat.is_gt(Nat.add(C1, 1n+o), Nat.add(C2, k))) : Bool}, ih_k: {Rp.scan.done(Rp.scan(t, Rp.Scan{False{}, False{}, o, 1n+k})) == Bool.or(opn, Nat.is_gt(Nat.add(C1, o), Nat.add(C2, 1n+k))) : Bool}) -> {Rp.scan.done(Rp.scan(t, Rp.scan.out(False{}, bs, False{}, op, cl, o, k))) == Bool.or(opn, Nat.is_gt(Nat.add(RefinePlanWalk.rs_count.at(op, C1), o), Nat.add(RefinePlanWalk.rs_count.at(cl, C2), k))) : Bool}:
  match op:
    case True{}:
      match cl:
        case True{}:
          LCh.absurd({Rp.scan.done(Rp.scan(t, Rp.scan.out(False{}, bs, False{}, True{}, True{}, o, k))) == Bool.or(opn, Nat.is_gt(Nat.add(RefinePlanWalk.rs_count.at(True{}, C1), o), Nat.add(RefinePlanWalk.rs_count.at(True{}, C2), k))) : Bool}, ex)
        case False{}:
          %rpi.add_succ(C1, o) : {Rp.scan.done(Rp.scan(t, Rp.Scan{False{}, False{}, 1n+o, k})) == Bool.or(opn, Nat.is_gt(_, Nat.add(C2, k))) : Bool}
          ih_o
    case False{}:
      match cl:
        case True{}:
          %rpi.add_succ(C2, k) : {Rp.scan.done(Rp.scan(t, Rp.Scan{False{}, False{}, o, 1n+k})) == Bool.or(opn, Nat.is_gt(Nat.add(C1, o), _)) : Bool}
          ih_k
        case False{}:
          ih

def rpi.out.kept(l: RefinePlanWalk.RsLex, +x: U32, -bs: Bool, +t: String, +o: Nat, +k: Nat, ih: {Rp.scan.done(Rp.scan(t, rpi.st(RefinePlanWalk.RsOut{}, o, k))) == rpi.cut(l, o, k) : Bool}, ih_o: {Rp.scan.done(Rp.scan(t, rpi.st(RefinePlanWalk.RsOut{}, 1n+o, k))) == rpi.cut(l, 1n+o, k) : Bool}, ih_k: {Rp.scan.done(Rp.scan(t, rpi.st(RefinePlanWalk.RsOut{}, o, 1n+k))) == rpi.cut(l, o, 1n+k) : Bool}) -> {Rp.scan.done(Rp.scan(t, Rp.scan.out(False{}, bs, False{}, Bool.or(U32.is_eq(x, 123), U32.is_eq(x, 91)), Bool.or(U32.is_eq(x, 125), U32.is_eq(x, 93)), o, k))) == rpi.cut(RefinePlanWalk.rs_lex.keep(True{}, Chr{x}, l), o, k) : Bool}:
  match l:
    case RefinePlanWalk.RsLex{+out, +opn}:
      rpi.kept(Bool.or(U32.is_eq(x, 123), U32.is_eq(x, 91)), Bool.or(U32.is_eq(x, 125), U32.is_eq(x, 93)), bs, rpi.excl(x), t, o, k, RefinePlanWalk.rs_count(out, '{', '['), RefinePlanWalk.rs_count(out, '}', ']'), opn, ih, ih_o, ih_k)

# outside a string: a `"` opens one, any other char is kept
def rpi.out(q: Bool, +x: U32, +t: String, +o: Nat, +k: Nat, ih_s: {Rp.scan.done(Rp.scan(t, rpi.st(RefinePlanWalk.RsStr{}, o, k))) == rpi.cut(RefinePlanWalk.rs_lex(t, RefinePlanWalk.RsStr{}), o, k) : Bool}, ih: {Rp.scan.done(Rp.scan(t, rpi.st(RefinePlanWalk.RsOut{}, o, k))) == rpi.cut(RefinePlanWalk.rs_lex(t, RefinePlanWalk.RsOut{}), o, k) : Bool}, ih_o: {Rp.scan.done(Rp.scan(t, rpi.st(RefinePlanWalk.RsOut{}, 1n+o, k))) == rpi.cut(RefinePlanWalk.rs_lex(t, RefinePlanWalk.RsOut{}), 1n+o, k) : Bool}, ih_k: {Rp.scan.done(Rp.scan(t, rpi.st(RefinePlanWalk.RsOut{}, o, 1n+k))) == rpi.cut(RefinePlanWalk.rs_lex(t, RefinePlanWalk.RsOut{}), o, 1n+k) : Bool}) -> {Rp.scan.done(Rp.scan(t, Rp.scan.out(False{}, U32.is_eq(x, 92), q, Bool.or(U32.is_eq(x, 123), U32.is_eq(x, 91)), Bool.or(U32.is_eq(x, 125), U32.is_eq(x, 93)), o, k))) == rpi.cut(RefinePlanWalk.rs_lex.keep(Bool.not(q), Chr{x}, RefinePlanWalk.rs_lex(t, RefinePlanWalk.rs_lex.next(RefinePlanWalk.RsOut{}, U32.is_eq(x, 92), q))), o, k) : Bool}:
  match q:
    case True{}:
      ih_s
    case False{}:
      rpi.out.kept(RefinePlanWalk.rs_lex(t, RefinePlanWalk.RsOut{}), x, U32.is_eq(x, 92), t, o, k, ih, ih_o, ih_k)

# in a string: a `\` escapes the next char, an unescaped `"` closes it
def rpi.str(bs: Bool, q: Bool, +t: String, +o: Nat, +k: Nat, -op: Bool, -cl: Bool, ih_e: {Rp.scan.done(Rp.scan(t, rpi.st(RefinePlanWalk.RsEsc{}, o, k))) == rpi.cut(RefinePlanWalk.rs_lex(t, RefinePlanWalk.RsEsc{}), o, k) : Bool}, ih_o: {Rp.scan.done(Rp.scan(t, rpi.st(RefinePlanWalk.RsOut{}, o, k))) == rpi.cut(RefinePlanWalk.rs_lex(t, RefinePlanWalk.RsOut{}), o, k) : Bool}, ih_s: {Rp.scan.done(Rp.scan(t, rpi.st(RefinePlanWalk.RsStr{}, o, k))) == rpi.cut(RefinePlanWalk.rs_lex(t, RefinePlanWalk.RsStr{}), o, k) : Bool}) -> {Rp.scan.done(Rp.scan(t, Rp.scan.out(True{}, bs, q, op, cl, o, k))) == rpi.cut(RefinePlanWalk.rs_lex(t, RefinePlanWalk.rs_lex.next(RefinePlanWalk.RsStr{}, bs, q)), o, k) : Bool}:
  match bs:
    case True{}:
      ih_e
    case False{}:
      match q:
        case True{}:
          ih_o
        case False{}:
          ih_s

# from a spec mode m with o and k counted, the code's scan answers the
# spec's lexed text with o and k added
def rpi.go(s: String, +m: RefinePlanWalk.RsMode, +o: Nat, +k: Nat) -> {Rp.scan.done(Rp.scan(s, rpi.st(m, o, k))) == rpi.cut(RefinePlanWalk.rs_lex(s, m), o, k) : Bool}:
  match s:
    case SNil{}:
      match m:
        case RefinePlanWalk.RsOut{}:
          {==}
        case RefinePlanWalk.RsStr{}:
          {==}
        case RefinePlanWalk.RsEsc{}:
          {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          match m:
            case RefinePlanWalk.RsOut{}:
              rpi.out(U32.is_eq(x, 34), x, t, o, k, rpi.go(t, RefinePlanWalk.RsStr{}, o, k), rpi.go(t, RefinePlanWalk.RsOut{}, o, k), rpi.go(t, RefinePlanWalk.RsOut{}, 1n+o, k), rpi.go(t, RefinePlanWalk.RsOut{}, o, 1n+k))
            case RefinePlanWalk.RsStr{}:
              rpi.str(U32.is_eq(x, 92), U32.is_eq(x, 34), t, o, k, Bool.or(U32.is_eq(x, 123), U32.is_eq(x, 91)), Bool.or(U32.is_eq(x, 125), U32.is_eq(x, 93)), rpi.go(t, RefinePlanWalk.RsEsc{}, o, k), rpi.go(t, RefinePlanWalk.RsOut{}, o, k), rpi.go(t, RefinePlanWalk.RsStr{}, o, k))
            case RefinePlanWalk.RsEsc{}:
              rpi.go(t, RefinePlanWalk.RsStr{}, o, k)

def rpi.zero(l: RefinePlanWalk.RsLex) -> {rpi.cut(l, 0n, 0n) == RefinePlanWalk.rs_cut(l) : Bool}:
  match l:
    case RefinePlanWalk.RsLex{+out, op}:
      %Equal.sym(Nat, Nat.add(RefinePlanWalk.rs_count(out, '{', '['), 0n), RefinePlanWalk.rs_count(out, '{', '['), rpi.add_zero(RefinePlanWalk.rs_count(out, '{', '['))) : {Bool.or(op, Nat.is_gt(_, Nat.add(RefinePlanWalk.rs_count(out, '}', ']'), 0n))) == RefinePlanWalk.rs_cut(RefinePlanWalk.RsLex{out, op}) : Bool}
      %Equal.sym(Nat, Nat.add(RefinePlanWalk.rs_count(out, '}', ']'), 0n), RefinePlanWalk.rs_count(out, '}', ']'), rpi.add_zero(RefinePlanWalk.rs_count(out, '}', ']'))) : {Bool.or(op, Nat.is_gt(RefinePlanWalk.rs_count(out, '{', '['), _)) == RefinePlanWalk.rs_cut(RefinePlanWalk.RsLex{out, op}) : Bool}
      {==}

def rpi.incomplete(+text: String) -> {Rp.incomplete(text) == RefinePlanWalk.rs_incomplete(text) : Bool}:
  Equal.trans(Bool, Rp.incomplete(text), rpi.cut(RefinePlanWalk.rs_lex(text, RefinePlanWalk.RsOut{}), 0n, 0n), RefinePlanWalk.rs_incomplete(text), rpi.go(text, RefinePlanWalk.RsOut{}, 0n, 0n), rpi.zero(RefinePlanWalk.rs_lex(text, RefinePlanWalk.RsOut{})))

def RefinePlanWalk.refine_plan_incomplete_lex(text):
  rpi.incomplete(text)
