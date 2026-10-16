# proof_compactor: the laws of a compactor call (H1) and of the wait for
# a settled view (H2), for bend/compactor.bend and the need-first queue of
# bend/optchat.bend. Every proof is by induction: on the tries of a line,
# on the outcomes of the settle, on the view of the queue.

import Base
import ./optchat.bend as O
import ./spec.bend as S
import ./compactor.bend as C
import ./proof_fit.bend as Fit
import ./proof_cover.bend as Cover
import ./proof_agree.bend as Agree

# Logic
# -----

def pc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pc.absurd_ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pc.BD(_, A, Unit)
  Unit{}

def pc.absurd_tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pc.BD(_, Unit, A)
  Unit{}

def pc.NZ(n: Nat, A: Type) -> Type:
  match n:
    case 0n:
      A
    case 1n+p:
      Unit

# 1+n is not 0
def pc.succ_zero(-A: Type, -n: Nat, e: {1n+n == 0n : Nat}) -> A:
  %e : pc.NZ(_, A)
  Unit{}

def pc.or_true(a: Bool) -> {Bool.or(True{}, a) == True{} : Bool}:
  {==}

# Numbers
# -------

def pc.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pc.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pc.le_refl(p)

def pc.lt_not_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      pc.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pc.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      pc.lt_not_le(p, q, e)

def pc.le_not_lt(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pc.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_not_lt(p, q, e)

# nothing is below 0
def pc.lt_zero(-A: Type, a: Nat, e: {Nat.is_lt(a, 0n) == True{} : Bool}) -> A:
  match a:
    case 0n:
      pc.absurd_ft(A, e)
    case 1n+p:
      pc.absurd_ft(A, e)

def pc.lt_le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      pc.absurd_ft({Nat.is_lt(0n, c) == True{} : Bool}, ab)
    case 1n+p 0n _:
      pc.absurd_ft({Nat.is_lt(1n+p, c) == True{} : Bool}, ab)
    case 0n 1n+q 0n:
      pc.absurd_ft({False{} == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      pc.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pc.lt_le_trans(p, q, r, ab, bc)

def pc.le_succ_r(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      pc.absurd_ft({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_succ_r(p, q, e)

def pc.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n q r:
      pc.le_zero(r)
    case 1n+p 0n r:
      pc.absurd_ft({Nat.is_le(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      pc.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pc.le_trans(p, q, r, ab, bc)

def pc.lt_succ_of_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      pc.absurd_ft({Nat.is_lt(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.lt_succ_of_le(p, q, e)

def pc.le_succ_of_lt(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      pc.lt_zero({Nat.is_le(1n+p, 0n) == True{} : Bool}, p, e)
    case 0n 1n+q:
      pc.le_zero(q)
    case 1n+p 1n+q:
      pc.le_succ_of_lt(p, q, e)

# m <= n + m
def pc.le_add(n: Nat, +m: Nat) -> {Nat.is_le(m, Nat.add(n, m)) == True{} : Bool}:
  match n:
    case 0n:
      pc.le_refl(m)
    case 1n+p:
      +q = p
      pc.le_succ_r(m, Nat.add(q, m), pc.le_add(q, m))

def pc.lt_add_l(c: Nat, -x: Nat, -y: Nat, e: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+p:
      pc.lt_add_l(p, x, y, e)

def pc.le_add_l(c: Nat, -x: Nat, -y: Nat, e: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+p:
      pc.le_add_l(p, x, y, e)

def pc.and_true(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      pc.absurd_ft({False{} == True{} : Bool}, ea)

# (H1) A line
# -----------

def pc.calls_next(fit: Bool, less: Bool, -ws: List<&2, C.W>, -node: Nat, -best: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>, rec: C.Line, p: Nat, ih: {Nat.is_le(C.Line.calls(rec), p) == True{} : Bool}) -> {Nat.is_le(C.Line.calls(C.line.next(fit, less, ws, node, best, input, rec)), 1n+p) == True{} : Bool}:
  match fit less:
    case True{} l:
      pc.le_zero(p)
    case False{} False{}:
      pc.le_zero(p)
    case False{} True{}:
      match rec:
        case C.Line{c, l}:
          ih

def pc.calls_go(tries: Nat, +node: Nat, +best: Maybe<&2, List<&2, C.W>>, +bl: Nat, rs: List<&2, C.Reply>, +input: List<&2, C.W>) -> {Nat.is_le(C.Line.calls(C.line.go(tries, node, best, bl, rs, input)), tries) == True{} : Bool}:
  match tries:
    case 0n:
      {==}
    case 1n+p:
      match rs:
        case Nil{}:
          pc.le_zero(p)
        case r <> +rest:
          match r:
            case C.Erred{}:
              pc.le_zero(p)
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  pc.le_zero(p)
                case +w <> +t:
                  +q = p
                  +len = C.Text.len(w <> t)
                  pc.calls_next(Nat.is_le(len, node), C.shorter(len, best, bl), w <> t, node, best, input, C.line.go(q, node, Some{w <> t}, len, rest, input), q, pc.calls_go(q, node, Some{w <> t}, len, rest, input))

def pc.line_calls_at_most_tries(+tries: Nat, +node: Nat, +input: List<&2, C.W>, rs: List<&2, C.Reply>) -> {Nat.is_le(C.Line.calls(C.line(tries, node, input, rs)), tries) == True{} : Bool}:
  pc.calls_go(tries, node, None{}, 0n, rs, input)

# a cut fits its room
def pc.cut_le(t: List<&2, C.W>, room: Nat) -> {Nat.is_le(C.Text.len(C.cut(t, room)), room) == True{} : Bool}:
  match t:
    case Nil{}:
      pc.le_zero(room)
    case c <> rest:
      match c room:
        case C.W1{} 0n:
          {==}
        case C.W1{} 1n+r:
          pc.cut_le(rest, r)
        case C.W2{} 0n:
          {==}
        case C.W2{} 1n:
          {==}
        case C.W2{} 2n+r:
          pc.cut_le(rest, r)
        case C.W3{} 0n:
          {==}
        case C.W3{} 1n:
          {==}
        case C.W3{} 2n:
          {==}
        case C.W3{} 3n+r:
          pc.cut_le(rest, r)
        case C.W4{} 0n:
          {==}
        case C.W4{} 1n:
          {==}
        case C.W4{} 2n:
          {==}
        case C.W4{} 3n:
          {==}
        case C.W4{} 4n+r:
          pc.cut_le(rest, r)

# a text that is not empty, cut to at least 4 bytes, keeps its first
# character: 1 to 4+k bytes
def pc.cut_fits(c: C.W, t: List<&2, C.W>, k: Nat) -> {C.line.fits(4n+k, Some{C.cut(c <> t, 4n+k)}) == True{} : Bool}:
  match c:
    case C.W1{}:
      pc.cut_le(t, 3n+k)
    case C.W2{}:
      pc.cut_le(t, 2n+k)
    case C.W3{}:
      pc.cut_le(t, 1n+k)
    case C.W4{}:
      pc.cut_le(t, k)

# the best reply so far is never empty
def pc.NE(m: Maybe<&2, List<&2, C.W>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{t}:
      match t:
        case Nil{}:
          Empty
        case h <> r:
          Unit

def pc.end_fits(best: Maybe<&2, List<&2, C.W>>, nb: pc.NE(best), c: C.W, rest: List<&2, C.W>, k: Nat) -> {C.line.fits(4n+k, Some{C.line.end(4n+k, best, c <> rest)}) == True{} : Bool}:
  match best:
    case None{}:
      pc.cut_fits(c, rest, k)
    case Some{b}:
      match b:
        case Nil{}:
          match nb:
        case x <> y:
          pc.cut_fits(x, y, k)

def pc.pos_len(w: C.W, -t: List<&2, C.W>) -> {O.Nat.is_pos(C.Text.len(w <> t)) == True{} : Bool}:
  match w:
    case C.W1{}:
      {==}
    case C.W2{}:
      {==}
    case C.W3{}:
      {==}
    case C.W4{}:
      {==}

def pc.fits_next(fit: Bool, less: Bool, +w: C.W, +t: List<&2, C.W>, +k: Nat, best: Maybe<&2, List<&2, C.W>>, nb: pc.NE(best), c: C.W, rest: List<&2, C.W>, rec: C.Line, efit: {Nat.is_le(C.Text.len(w <> t), 4n+k) == fit : Bool}, ih: {C.line.fits(4n+k, C.Line.line(rec)) == True{} : Bool}) -> {C.line.fits(4n+k, C.Line.line(C.line.next(fit, less, w <> t, 4n+k, best, c <> rest, rec))) == True{} : Bool}:
  match fit less:
    case True{} l:
      pc.and_true(O.Nat.is_pos(C.Text.len(w <> t)), Nat.is_le(C.Text.len(w <> t), 4n+k), pc.pos_len(w, t), efit)
    case False{} False{}:
      pc.end_fits(best, nb, c, rest, k)
    case False{} True{}:
      match rec:
        case C.Line{n, l}:
          ih

def pc.fits_go(tries: Nat, +k: Nat, +best: Maybe<&2, List<&2, C.W>>, +bl: Nat, nb: pc.NE(best), rs: List<&2, C.Reply>, +c: C.W, +rest: List<&2, C.W>) -> {C.line.fits(4n+k, C.Line.line(C.line.go(tries, 4n+k, best, bl, rs, c <> rest))) == True{} : Bool}:
  match tries:
    case 0n:
      pc.end_fits(best, nb, c, rest, k)
    case 1n+p:
      match rs:
        case Nil{}:
          {==}
        case r <> +more:
          match r:
            case C.Erred{}:
              {==}
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  pc.end_fits(best, nb, c, rest, k)
                case +w <> +t:
                  +q = p
                  +len = C.Text.len(w <> t)
                  pc.fits_next(Nat.is_le(len, 4n+k), C.shorter(len, best, bl), w, t, k, best, nb, c, rest, C.line.go(q, 4n+k, Some{w <> t}, len, more, c <> rest), {==}, pc.fits_go(q, k, Some{w <> t}, len, Unit{}, more, c, rest))

def pc.line_fits(+tries: Nat, +k: Nat, +c: C.W, +rest: List<&2, C.W>, +rs: List<&2, C.Reply>) -> {C.line.fits(4n+k, C.Line.line(C.line(tries, 4n+k, c <> rest, rs))) == True{} : Bool}:
  pc.fits_go(tries, k, None{}, 0n, Unit{}, rs, c, rest)

def pc.text_eq_refl(t: List<&2, C.W>) -> {C.Text.eq(t, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case w <> r:
      match w:
        case C.W1{}:
          pc.text_eq_refl(r)
        case C.W2{}:
          pc.text_eq_refl(r)
        case C.W3{}:
          pc.text_eq_refl(r)
        case C.W4{}:
          pc.text_eq_refl(r)

def pc.first_next(fit: Bool, less: Bool, +w: C.W, +t: List<&2, C.W>, +node: Nat, -best: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>, -rest: List<&2, C.Reply>, rec: C.Line, efit: {fit == Nat.is_le(C.Text.len(w <> t), node) : Bool}, ih: {C.line.first(C.first_fit(node, C.read(C.Line.calls(rec), rest)), C.Line.line(rec)) == True{} : Bool}) -> {C.line.first(C.first_fit(node, C.read(C.Line.calls(C.line.next(fit, less, w <> t, node, best, input, rec)), C.Says{w <> t} <> rest)), C.Line.line(C.line.next(fit, less, w <> t, node, best, input, rec))) == True{} : Bool}:
  match fit less:
    case True{} l:
      %efit : {C.line.first(C.first_fit.pick(_, w <> t, None{}), Some{w <> t}) == True{} : Bool}
      pc.text_eq_refl(w <> t)
    case False{} False{}:
      %efit : {C.line.first(C.first_fit.pick(_, w <> t, None{}), Some{C.line.end(node, best, input)}) == True{} : Bool}
      {==}
    case False{} True{}:
      match rec:
        case C.Line{n, l}:
          %efit : {C.line.first(C.first_fit.pick(_, w <> t, C.first_fit(node, C.read(n, rest))), l) == True{} : Bool}
          ih

def pc.first_go(tries: Nat, +node: Nat, +best: Maybe<&2, List<&2, C.W>>, +bl: Nat, rs: List<&2, C.Reply>, +input: List<&2, C.W>) -> {C.line.first(C.first_fit(node, C.read(C.Line.calls(C.line.go(tries, node, best, bl, rs, input)), rs)), C.Line.line(C.line.go(tries, node, best, bl, rs, input))) == True{} : Bool}:
  match tries:
    case 0n:
      {==}
    case 1n+p:
      match rs:
        case Nil{}:
          {==}
        case r <> +rest:
          match r:
            case C.Erred{}:
              {==}
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  {==}
                case +w <> +t:
                  +q = p
                  +len = C.Text.len(w <> t)
                  pc.first_next(Nat.is_le(len, node), C.shorter(len, best, bl), w, t, node, best, input, rest, C.line.go(q, node, Some{w <> t}, len, rest, input), {==}, pc.first_go(q, node, Some{w <> t}, len, rest, input))

def pc.line_takes_first_fit(+tries: Nat, +node: Nat, +input: List<&2, C.W>, +rs: List<&2, C.Reply>) -> {C.line.first(C.first_fit(node, C.read(C.Line.calls(C.line(tries, node, input, rs)), rs)), C.Line.line(C.line(tries, node, input, rs))) == True{} : Bool}:
  pc.first_go(tries, node, None{}, 0n, rs, input)

def pc.stop_next(fa: Bool, fb: Bool, lb: Bool, -a: List<&2, C.W>, -b: List<&2, C.W>, -node: Nat, -input: List<&2, C.W>, -rec: C.Line, ea: {fa == False{} : Bool}, eb: {fb == False{} : Bool}, el: {lb == False{} : Bool}) -> {C.line.next(fa, True{}, a, node, None{}, input, C.line.next(fb, lb, b, node, Some{a}, input, rec)) == C.Line{2n, Some{C.cut(a, node)}} : C.Line}:
  match fa fb lb:
    case True{} y z:
      pc.absurd_tf({C.Line{1n, Some{a}} == C.Line{2n, Some{C.cut(a, node)}} : C.Line}, ea)
    case False{} True{} z:
      pc.absurd_tf({C.Line{2n, Some{b}} == C.Line{2n, Some{C.cut(a, node)}} : C.Line}, eb)
    case False{} False{} True{}:
      pc.absurd_tf({C.Line.more(C.Line.more(rec)) == C.Line{2n, Some{C.cut(a, node)}} : C.Line}, el)
    case False{} False{} False{}:
      {==}

def pc.line_stops_when_not_shorter(+t: Nat, +node: Nat, +input: List<&2, C.W>, +a: List<&2, C.W>, +b: List<&2, C.W>, +rest: List<&2, C.Reply>, +over: {Nat.is_lt(node, C.Text.len(a)) == True{} : Bool}, +longer: {Nat.is_le(C.Text.len(a), C.Text.len(b)) == True{} : Bool}) -> {C.line(2n+t, node, input, C.Says{a} <> C.Says{b} <> rest) == C.Line{2n, Some{C.cut(a, node)}} : C.Line}:
  match a:
    case Nil{}:
      pc.lt_zero({C.line(2n+t, node, input, C.Says{Nil{}} <> C.Says{b} <> rest) == C.Line{2n, Some{C.cut(Nil{}, node)}} : C.Line}, node, over)
    case +x <> +y:
      match b:
        case Nil{}:
          pc.lt_zero({C.line(2n+t, node, input, C.Says{x <> y} <> C.Says{Nil{}} <> rest) == C.Line{2n, Some{C.cut(x <> y, node)}} : C.Line}, node, pc.lt_le_trans(node, C.Text.len(x <> y), 0n, over, longer))
        case +u <> +v:
          pc.stop_next(Nat.is_le(C.Text.len(x <> y), node), Nat.is_le(C.Text.len(u <> v), node), Nat.is_lt(C.Text.len(u <> v), C.Text.len(x <> y)), x <> y, u <> v, node, input, C.line.go(t, node, Some{u <> v}, C.Text.len(u <> v), rest, input), pc.lt_not_le(node, C.Text.len(x <> y), over), pc.lt_not_le(node, C.Text.len(u <> v), pc.lt_le_trans(node, C.Text.len(x <> y), C.Text.len(u <> v), over, longer)), pc.le_not_lt(C.Text.len(x <> y), C.Text.len(u <> v), longer))

def pc.line_empty_is_a_try(-t: Nat, -node: Nat, -input: List<&2, C.W>, -rest: List<&2, C.Reply>) -> {C.line(1n+t, node, input, C.Says{Nil{}} <> rest) == C.Line{1n, Some{C.cut(input, node)}} : C.Line}:
  {==}

def pc.line_error_fails(-t: Nat, -node: Nat, -input: List<&2, C.W>, -rest: List<&2, C.Reply>) -> {C.line(1n+t, node, input, C.Erred{} <> rest) == C.Line{1n, None{}} : C.Line}:
  {==}

# a built line stays built
def pc.run_made(os: List<&2, C.Outcome>) -> {C.Pend.run(os, C.Made{}) == C.Made{} : C.Pend}:
  match os:
    case Nil{}:
      {==}
    case o <> rest:
      match o:
        case C.Built{}:
          pc.run_made(rest)
        case C.Failed{}:
          pc.run_made(rest)
        case C.Disk{}:
          pc.run_made(rest)
        case C.Stopped{}:
          pc.run_made(rest)

def pc.fail_cap_builds(os: List<&2, C.Outcome>, n: Nat, many: {Nat.is_le(1n+n, C.failures(os)) == True{} : Bool}) -> {C.Pend.run(os, C.Owed{n}) == C.Made{} : C.Pend}:
  match os:
    case Nil{}:
      pc.absurd_ft({C.Owed{n} == C.Made{} : C.Pend}, many)
    case o <> rest:
      match o:
        case C.Built{}:
          pc.run_made(rest)
        case C.Failed{}:
          match n:
            case 0n:
              pc.run_made(rest)
            case 1n+m:
              pc.fail_cap_builds(rest, m, many)
        case C.Disk{}:
          pc.fail_cap_builds(rest, n, many)
        case C.Stopped{}:
          pc.fail_cap_builds(rest, n, many)

# (H2) The settle
# ---------------

def pc.lt_to_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      pc.lt_zero({Nat.is_le(p, 0n) == True{} : Bool}, p, e)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pc.lt_to_le(p, q, e)

def pc.le_lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case p q 0n:
      pc.lt_zero({Nat.is_lt(p, 0n) == True{} : Bool}, q, bc)
    case 0n q 1n+r:
      {==}
    case 1n+p 0n 1n+r:
      pc.absurd_ft({Nat.is_lt(1n+p, 1n+r) == True{} : Bool}, ab)
    case 1n+p 1n+q 1n+r:
      pc.le_lt_trans(p, q, r, ab, bc)

def pc.lt_self(+x: Nat) -> {Nat.is_lt(x, 1n+x) == True{} : Bool}:
  pc.lt_succ_of_le(x, x, pc.le_refl(x))

# an outcome that counts lowers a pending line's weight
def pc.after_falls(n: Nat, o: C.Outcome, +m: Nat, lands: {C.Outcome.lands(o) == True{} : Bool}) -> {Nat.is_lt(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{n}, o)), m), Nat.add(1n+n, m)) == True{} : Bool}:
  match n o:
    case +p C.Built{}:
      pc.lt_succ_of_le(m, Nat.add(p, m), pc.le_add(p, m))
    case 0n C.Failed{}:
      pc.lt_self(m)
    case 1n+p C.Failed{}:
      pc.lt_self(Nat.add(p, m))
    case p C.Disk{}:
      pc.absurd_ft({Nat.is_lt(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Disk{})), m), Nat.add(1n+p, m)) == True{} : Bool}, lands)
    case p C.Stopped{}:
      pc.absurd_ft({Nat.is_lt(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Stopped{})), m), Nat.add(1n+p, m)) == True{} : Bool}, lands)

# and no outcome raises it
def pc.after_holds(n: Nat, o: C.Outcome, +m: Nat) -> {Nat.is_le(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{n}, o)), m), Nat.add(1n+n, m)) == True{} : Bool}:
  match n o:
    case +p C.Built{}:
      pc.lt_to_le(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Built{})), m), Nat.add(1n+p, m), pc.after_falls(p, C.Built{}, m, {==}))
    case +p C.Failed{}:
      pc.lt_to_le(Nat.add(C.Pend.weight(C.Pend.after(C.Owed{p}, C.Failed{})), m), Nat.add(1n+p, m), pc.after_falls(p, C.Failed{}, m, {==}))
    case 0n C.Disk{}:
      pc.le_refl(1n+m)
    case 1n+p C.Disk{}:
      pc.le_refl(Nat.add(2n+p, m))
    case 0n C.Stopped{}:
      pc.le_refl(1n+m)
    case 1n+p C.Stopped{}:
      pc.le_refl(Nat.add(2n+p, m))

def pc.settle_falls(ps: List<&2, C.Pend>, k: Nat, o: C.Outcome, due: {C.pending_at(ps, k) == True{} : Bool}, lands: {C.Outcome.lands(o) == True{} : Bool}) -> {Nat.is_lt(C.measure(C.hit(ps, k, o)), C.measure(ps)) == True{} : Bool}:
  match ps k:
    case Nil{} j:
      pc.absurd_ft({Nat.is_lt(0n, 0n) == True{} : Bool}, due)
    case C.Made{} <> rest 0n:
      pc.absurd_ft({Nat.is_lt(C.measure(rest), C.measure(rest)) == True{} : Bool}, due)
    case C.Owed{n} <> rest 0n:
      pc.after_falls(n, o, C.measure(rest), lands)
    case p <> rest 1n+j:
      pc.lt_add_l(C.Pend.weight(p), C.measure(C.hit(rest, j, o)), C.measure(rest), pc.settle_falls(rest, j, o, due, lands))

def pc.settle_holds(ps: List<&2, C.Pend>, k: Nat, +o: C.Outcome) -> {Nat.is_le(C.measure(C.hit(ps, k, o)), C.measure(ps)) == True{} : Bool}:
  match ps k:
    case Nil{} j:
      {==}
    case C.Made{} <> rest 0n:
      pc.le_refl(C.measure(rest))
    case C.Owed{+n} <> rest 0n:
      pc.after_holds(n, o, C.measure(rest))
    case +p <> rest 1n+j:
      pc.le_add_l(C.Pend.weight(p), C.measure(C.hit(rest, j, o)), C.measure(rest), pc.settle_holds(rest, j, o))

def pc.bounded_step(b: Bool, +h: Nat, +x: Nat, +m1: Nat, +m0: Nat, +ih: {Nat.is_le(Nat.add(h, x), m1) == True{} : Bool}, holds: {Nat.is_le(m1, m0) == True{} : Bool}, falls: {b == True{} : Bool} -> {Nat.is_lt(m1, m0) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(O.bit(b, 0n), h), x), m0) == True{} : Bool}:
  match b:
    case False{}:
      pc.le_trans(Nat.add(h, x), m1, m0, ih, holds)
    case True{}:
      pc.le_succ_of_lt(Nat.add(h, x), m0, pc.le_lt_trans(Nat.add(h, x), m1, m0, ih, falls({==})))

def pc.settle_bounded(es: List<&2, C.End>, +ps: List<&2, C.Pend>) -> {Nat.is_le(Nat.add(C.hits(es, ps), C.measure(C.run(es, ps))), C.measure(ps)) == True{} : Bool}:
  match es:
    case Nil{}:
      pc.le_refl(C.measure(ps))
    case C.End{+k, +o} <> +rest:
      +next = C.hit(ps, k, o)
      +due = C.pending_at(ps, k)
      +lands = C.Outcome.lands(o)
      pc.bounded_step(Bool.and(due, lands), C.hits(rest, next), C.measure(C.run(rest, next)), C.measure(next), C.measure(ps), pc.settle_bounded(rest, next), pc.settle_holds(ps, k, o), +both => pc.settle_falls(ps, k, o, Fit.pf.and_l(due, lands, both), Fit.pf.and_r(due, lands, both)))

def pc.le_zero_eq(x: Nat, e: {Nat.is_le(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      pc.absurd_ft({1n+p == 0n : Nat}, e)

# h + x <= m <= h leaves x = 0
def pc.rest_zero(h: Nat, x: Nat, m: Nat, e1: {Nat.is_le(Nat.add(h, x), m) == True{} : Bool}, e2: {Nat.is_le(m, h) == True{} : Bool}) -> {x == 0n : Nat}:
  match h m:
    case 0n 0n:
      pc.le_zero_eq(x, e1)
    case 0n 1n+q:
      pc.absurd_ft({x == 0n : Nat}, e2)
    case 1n+p 0n:
      pc.absurd_ft({x == 0n : Nat}, e1)
    case 1n+p 1n+q:
      pc.rest_zero(p, x, q, e1, e2)

def pc.zero_settled(ps: List<&2, C.Pend>, e: {C.measure(ps) == 0n : Nat}) -> {C.settled(ps) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case C.Made{}:
          pc.zero_settled(rest, e)
        case C.Owed{n}:
          pc.succ_zero({Bool.and(False{}, C.settled(rest)) == True{} : Bool}, Nat.add(n, C.measure(rest)), e)

def pc.settle_reached(+es: List<&2, C.End>, +ps: List<&2, C.Pend>, enough: {Nat.is_le(C.measure(ps), C.hits(es, ps)) == True{} : Bool}) -> {C.settled(C.run(es, ps)) == True{} : Bool}:
  pc.zero_settled(C.run(es, ps), pc.rest_zero(C.hits(es, ps), C.measure(C.run(es, ps)), C.measure(ps), pc.settle_bounded(es, ps), enough))

def pc.start_step(b: Bool, +p: Nat, -m: Nat, -u: Nat, ih: {m == Nat.mul(u, 1n+p) : Nat}) -> {Nat.add(C.Pend.weight(C.settle.line(b, p)), m) == Nat.mul(Nat.add(O.bit(Bool.not(b), 0n), u), 1n+p) : Nat}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Nat, m, Nat.mul(u, 1n+p), ih) : {Nat.add(1n+p, _) == Nat.add(1n+p, Nat.mul(u, 1n+p)) : Nat}
      {==}

def pc.settle_start(+p: Nat, +info: O.Info, v: List<&2, O.Node>) -> {C.measure(C.settle.start(p, info, v)) == Nat.mul(C.unbuilt(info, v), 1n+p) : Nat}:
  match v:
    case Nil{}:
      {==}
    case +h <> +rest:
      pc.start_step(O.Info.built(info, h), p, C.measure(C.settle.start(p, info, rest)), C.unbuilt(info, rest), pc.settle_start(p, info, rest))

# (H2) Need first
# ---------------

def pc.needed_cons(+info: O.Info, +h: O.Node, +v: List<&2, O.Node>, ns: List<&2, O.Node>, +e: {C.needed(info, v, ns) == True{} : Bool}) -> {C.needed(info, h <> v, ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> rest:
      +a = Bool.and(O.Nodes.has(v, n), Bool.not(O.Info.built(info, n)))
      +ea = Fit.pf.and_l(a, C.needed(info, v, rest), e)
      pc.and_true(Bool.and(Bool.or(O.Node.eq(h, n), O.Nodes.has(v, n)), Bool.not(O.Info.built(info, n))), C.needed(info, h <> v, rest), pc.and_true(Bool.or(O.Node.eq(h, n), O.Nodes.has(v, n)), Bool.not(O.Info.built(info, n)), Fit.pf.or_r(O.Node.eq(h, n), O.Nodes.has(v, n), Fit.pf.and_l(O.Nodes.has(v, n), Bool.not(O.Info.built(info, n)), ea)), Fit.pf.and_r(O.Nodes.has(v, n), Bool.not(O.Info.built(info, n)), ea)), pc.needed_cons(info, h, v, rest, Fit.pf.and_r(a, C.needed(info, v, rest), e)))

def pc.emit_ok(stop: Bool, b: Bool, free: Bool, +info: O.Info, +h: O.Node, +rest: List<&2, O.Node>, +rec: List<&2, O.Node>, eb: {b == O.Info.built(info, h) : Bool}, +ih: {C.needed(info, rest, rec) == True{} : Bool}) -> {C.needed(info, h <> rest, O.cand.emit(stop, b, free, h, rec)) == True{} : Bool}:
  match stop b free:
    case True{} y z:
      {==}
    case False{} True{} z:
      pc.needed_cons(info, h, rest, rec, ih)
    case False{} False{} True{}:
      %eb : {Bool.and(Bool.and(Bool.or(O.Node.eq(h, h), O.Nodes.has(rest, h)), Bool.not(_)), C.needed(info, h <> rest, rec)) == True{} : Bool}
      %Fit.pf.node_eq_refl(h) : {Bool.and(Bool.and(Bool.or(_, O.Nodes.has(rest, h)), True{}), C.needed(info, h <> rest, rec)) == True{} : Bool}
      pc.needed_cons(info, h, rest, rec, ih)
    case False{} False{} False{}:
      pc.needed_cons(info, h, rest, rec, ih)

def pc.cand_ok(v: List<&2, O.Node>, +info: O.Info, +busy: List<&2, O.Node>, +jobs: Nat, +unb: Nat, room: Nat) -> {C.needed(info, v, O.cand.view(v, info, busy, jobs, unb, room)) == True{} : Bool}:
  match v room:
    case Nil{} r:
      {==}
    case h <> rest 0n:
      {==}
    case +h <> +rest 1n+r:
      +unb2 = Nat.add(unb, O.bit(Bool.not(O.Info.built(info, h)), 0n))
      +room2 = Nat.sub(1n+r, O.bit(Bool.and(Bool.not(O.Info.built(info, h)), Bool.not(O.Nodes.has(busy, h))), 0n))
      pc.emit_ok(Nat.is_ge(unb, jobs), O.Info.built(info, h), Bool.not(O.Nodes.has(busy, h)), info, h, rest, O.cand.view(rest, info, busy, jobs, unb2, room2), {==}, pc.cand_ok(rest, info, busy, jobs, unb2, room2))

def pc.need_first(+cfg: O.Cfg, +s: O.St) -> {C.needed(O.St.info(s), O.St.view(s), O.cands.need(cfg, s)) == True{} : Bool}:
  pc.cand_ok(O.St.view(s), O.St.info(s), O.St.busy(s), O.Cfg.jobs(cfg), 0n, Nat.sub(O.Cfg.jobs(cfg), List.length(&2, O.Node, O.St.busy(s))))

# a waiting turn stops every call it does not need
def pc.keep_need(c: Bool, +info: O.Info, +v: List<&2, O.Node>, +b: O.Node, +rest: List<&2, O.Node>, ec: {c == Bool.and(O.Nodes.has(v, b), Bool.not(O.Info.built(info, b))) : Bool}, +ih: {C.needed(info, v, rest) == True{} : Bool}) -> {C.needed(info, v, O.Nodes.keep(c, b, rest)) == True{} : Bool}:
  match c:
    case True{}:
      %ec : {Bool.and(_, C.needed(info, v, rest)) == True{} : Bool}
      ih
    case False{}:
      ih

def pc.busy_need(+info: O.Info, +v: List<&2, O.Node>, bs: List<&2, O.Node>) -> {C.needed(info, v, O.busy.need(info, v, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      pc.keep_need(Bool.and(O.Nodes.has(v, b), Bool.not(O.Info.built(info, b))), info, v, b, O.busy.need(info, v, rest), {==}, pc.busy_need(info, v, rest))

def pc.needed_app(+info: O.Info, +v: List<&2, O.Node>, xs: List<&2, O.Node>, -ys: List<&2, O.Node>, +ex: {C.needed(info, v, xs) == True{} : Bool}, +ey: {C.needed(info, v, ys) == True{} : Bool}) -> {C.needed(info, v, List.append(&2, O.Node, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ey
    case +x <> +rest:
      +a = Bool.and(O.Nodes.has(v, x), Bool.not(O.Info.built(info, x)))
      pc.and_true(a, C.needed(info, v, List.append(&2, O.Node, rest, ys)), Fit.pf.and_l(a, C.needed(info, v, rest), ex), pc.needed_app(info, v, rest, ys, Fit.pf.and_r(a, C.needed(info, v, rest), ex), ey))

def pc.need_first_running(+cfg: O.Cfg, +s: O.St) -> {C.needed(O.St.info(s), O.St.view(s), List.append(&2, O.Node, O.St.busy(O.St.wait(s)), O.cands.need(cfg, O.St.wait(s)))) == True{} : Bool}:
  match s:
    case O.St{t, info, view, shrink, cview, ready, busy}:
      +w = {O.St{t, info, view, shrink, cview, ready, O.busy.need(info, view, busy)} : O.St}
      pc.needed_app(info, view, O.busy.need(info, view, busy), O.cands.need(cfg, w), pc.busy_need(info, view, busy), pc.need_first(cfg, w))

# a waiting turn stops no call it needs
def pc.implies_or(c: Bool, d: Bool, -y: Bool, e: {O.Bool.implies(c, y) == True{} : Bool}) -> {O.Bool.implies(c, Bool.or(d, y)) == True{} : Bool}:
  match c d:
    case False{} z:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      e

def pc.kept_cons(+info: O.Info, +v: List<&2, O.Node>, bs: List<&2, O.Node>, +x: O.Node, +ws: List<&2, O.Node>, +e: {C.kept(info, v, bs, ws) == True{} : Bool}) -> {C.kept(info, v, bs, x <> ws) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      +c = Bool.and(O.Nodes.has(v, b), Bool.not(O.Info.built(info, b)))
      +y = O.Nodes.has(ws, b)
      pc.and_true(O.Bool.implies(c, Bool.or(O.Node.eq(x, b), y)), C.kept(info, v, rest, x <> ws), pc.implies_or(c, O.Node.eq(x, b), y, Fit.pf.and_l(O.Bool.implies(c, y), C.kept(info, v, rest, ws), e)), pc.kept_cons(info, v, rest, x, ws, Fit.pf.and_r(O.Bool.implies(c, y), C.kept(info, v, rest, ws), e)))

def pc.kept_step(c: Bool, +info: O.Info, +v: List<&2, O.Node>, +b: O.Node, +rest: List<&2, O.Node>, +ns: List<&2, O.Node>, ih: {C.kept(info, v, rest, ns) == True{} : Bool}) -> {Bool.and(O.Bool.implies(c, O.Nodes.has(O.Nodes.keep(c, b, ns), b)), C.kept(info, v, rest, O.Nodes.keep(c, b, ns))) == True{} : Bool}:
  match c:
    case True{}:
      %Fit.pf.node_eq_refl(b) : {Bool.and(Bool.or(_, O.Nodes.has(ns, b)), C.kept(info, v, rest, b <> ns)) == True{} : Bool}
      pc.kept_cons(info, v, rest, b, ns, ih)
    case False{}:
      ih

def pc.kept_need(+info: O.Info, +v: List<&2, O.Node>, bs: List<&2, O.Node>) -> {C.kept(info, v, bs, O.busy.need(info, v, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      pc.kept_step(Bool.and(O.Nodes.has(v, b), Bool.not(O.Info.built(info, b))), info, v, b, rest, O.busy.need(info, v, rest), pc.kept_need(info, v, rest))

def pc.wait_keeps_needed(+s: O.St) -> {C.kept(O.St.info(s), O.St.view(s), O.St.busy(s), O.St.busy(O.St.wait(s))) == True{} : Bool}:
  match s:
    case O.St{t, +info, +view, shrink, cview, ready, +busy}:
      pc.kept_need(info, view, busy)

# (H2) Progress
# -------------
# The queue scans the view oldest first and stops after jobs unbuilt
# lines. A line the scan passes is built, or busy: then a call of the
# busy list starts at it, and the view's lines start in order, so that
# call starts before every later line. pc.ahead(s, busy), the busy calls
# that start at s or later, plus the unbuilt lines passed stays below
# jobs: the scan reaches a line that is neither built nor busy.

def pc.add_zero(n: Nat) -> {n == Nat.add(n, 0n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %pc.add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def pc.le_add_r(a: Nat, c: Nat) -> {Nat.is_le(a, Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      pc.le_zero(c)
    case 1n+p:
      pc.le_add_r(p, c)

def pc.lt_add_pos(a: Nat, c: Nat, pos: {O.Nat.is_pos(c) == True{} : Bool}) -> {Nat.is_lt(a, Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      match c:
        case 0n:
          pos
        case 1n+q:
          {==}
    case 1n+p:
      pc.lt_add_pos(p, c, pos)

def pc.double_pos(x: Nat, e: {O.Nat.is_pos(x) == True{} : Bool}) -> {O.Nat.is_pos(Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      e
    case 1n+p:
      {==}

def pc.pow2_pos(+l: Nat) -> {O.Nat.is_pos(O.pow2(l)) == True{} : Bool}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      pc.double_pos(O.pow2(p), pc.pow2_pos(p))

# every line covers a message
def pc.count_pos(n: O.Node) -> {O.Nat.is_pos(O.Node.count(n)) == True{} : Bool}:
  match n:
    case O.Node{l, i}:
      pc.pow2_pos(l)

def pc.le_add_both(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, cd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  match a b:
    case 0n q:
      pc.le_trans(c, d, Nat.add(q, d), cd, pc.le_add(q, d))
    case 1n+p 0n:
      pc.absurd_ft({Nat.is_le(Nat.add(1n+p, c), d) == True{} : Bool}, ab)
    case 1n+p 1n+q:
      pc.le_add_both(p, q, c, d, ab, cd)

def pc.bit_le(x: Bool, y: Bool, imp: {x == True{} : Bool} -> {y == True{} : Bool}) -> {Nat.is_le(O.bit(x, 0n), O.bit(y, 0n)) == True{} : Bool}:
  match x y:
    case False{} z:
      pc.le_zero(O.bit(z, 0n))
    case True{} True{}:
      {==}
    case True{} False{}:
      pc.absurd_ft({Nat.is_le(1n, 0n) == True{} : Bool}, imp({==}))

def pc.bit_le_one(x: Bool) -> {Nat.is_le(O.bit(x, 0n), 1n) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def pc.not_false(x: Bool, e: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      pc.absurd_tf({False{} == True{} : Bool}, e)

def pc.lt_not_ge(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_ge(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      pc.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      pc.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      pc.lt_not_ge(p, q, e)

def pc.sub_pos(b: Nat, j: Nat, e: {Nat.is_lt(b, j) == True{} : Bool}) -> {O.Nat.is_pos(Nat.sub(j, b)) == True{} : Bool}:
  match b j:
    case p 0n:
      pc.lt_zero({O.Nat.is_pos(Nat.sub(0n, p)) == True{} : Bool}, p, e)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pc.sub_pos(p, q, e)

# equal nodes start together
def pc.same_eq(+xs: List<&2, Bool>, +ys: List<&2, Bool>, e: {O.Bits.same(xs, ys) == True{} : Bool}) -> {Nat.is_eq(O.Bits.val(xs), O.Bits.val(ys)) == True{} : Bool}:
  %Agree.pa.cmp_val(xs, ys) : {Cmp.is_eq(_) == True{} : Bool}
  e

def pc.eq_start(a: O.Node, b: O.Node, +e: {O.Node.eq(a, b) == True{} : Bool}) -> {O.Node.start(a) == O.Node.start(b) : Nat}:
  match a b:
    case O.Node{+la, +ia} O.Node{+lb, +ib}:
      %Cover.cover.eq_of_is_eq(la, lb, Fit.pf.and_l(Nat.is_eq(la, lb), O.Bits.same(ia, ib), e)) : {O.shl(la, O.Bits.val(ia)) == O.shl(_, O.Bits.val(ib)) : Nat}
      %Cover.cover.eq_of_is_eq(O.Bits.val(ia), O.Bits.val(ib), pc.same_eq(ia, ib, Fit.pf.and_r(Nat.is_eq(la, lb), O.Bits.same(ia, ib), e))) : {O.shl(la, O.Bits.val(ia)) == O.shl(la, _) : Nat}
      {==}

# the busy calls that start at s or later
def pc.ahead(+s: Nat, bs: List<&2, O.Node>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case b <> rest:
      Nat.add(O.bit(Nat.is_le(s, O.Node.start(b)), 0n), pc.ahead(s, rest))

def pc.ahead_len(+s: Nat, bs: List<&2, O.Node>) -> {Nat.is_le(pc.ahead(s, bs), List.length(&2, O.Node, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      pc.le_add_both(O.bit(Nat.is_le(s, O.Node.start(b)), 0n), 1n, pc.ahead(s, rest), List.length(&2, O.Node, rest), pc.bit_le_one(Nat.is_le(s, O.Node.start(b))), pc.ahead_len(s, rest))

def pc.ahead_mono(bs: List<&2, O.Node>, +s: Nat, +s2: Nat, +le: {Nat.is_le(s, s2) == True{} : Bool}) -> {Nat.is_le(pc.ahead(s2, bs), pc.ahead(s, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      +sb = O.Node.start(b)
      pc.le_add_both(O.bit(Nat.is_le(s2, sb), 0n), O.bit(Nat.is_le(s, sb), 0n), pc.ahead(s2, rest), pc.ahead(s, rest), pc.bit_le(Nat.is_le(s2, sb), Nat.is_le(s, sb), z => pc.le_trans(s, s2, sb, le, z)), pc.ahead_mono(rest, s, s2, le))

def pc.drop_step(x: Bool, -y: Bool, +s: Nat, +s2: Nat, +sb: Nat, +a1: Nat, +a2: Nat, lt: {Nat.is_lt(s, s2) == True{} : Bool}, has: {Bool.or(x, y) == True{} : Bool}, at: {x == True{} : Bool} -> {s == sb : Nat}, mono: {Nat.is_le(a2, a1) == True{} : Bool}, ih: {y == True{} : Bool} -> {Nat.is_le(1n+a2, a1) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(O.bit(Nat.is_le(s2, sb), 0n), a2), Nat.add(O.bit(Nat.is_le(s, sb), 0n), a1)) == True{} : Bool}:
  match x:
    case True{}:
      %at({==}) : {Nat.is_le(1n+Nat.add(O.bit(Nat.is_le(s2, _), 0n), a2), Nat.add(O.bit(Nat.is_le(s, _), 0n), a1)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(s2, s), False{}, pc.lt_not_le(s, s2, lt)) : {Nat.is_le(1n+Nat.add(O.bit(_, 0n), a2), Nat.add(O.bit(Nat.is_le(s, s), 0n), a1)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(s, s), True{}, pc.le_refl(s)) : {Nat.is_le(1n+Nat.add(O.bit(False{}, 0n), a2), Nat.add(O.bit(_, 0n), a1)) == True{} : Bool}
      mono
    case False{}:
      +x2 = O.bit(Nat.is_le(s2, sb), 0n)
      +x1 = O.bit(Nat.is_le(s, sb), 0n)
      %Equal.sym(Nat, 1n+Nat.add(x2, a2), Nat.add(x2, 1n+a2), Cover.cover.add_succ(x2, a2)) : {Nat.is_le(_, Nat.add(x1, a1)) == True{} : Bool}
      pc.le_add_both(x2, x1, 1n+a2, a1, pc.bit_le(Nat.is_le(s2, sb), Nat.is_le(s, sb), z => pc.le_trans(s, s2, sb, pc.lt_to_le(s, s2, lt), z)), ih(has))

# a busy call at s drops out of the calls ahead once the scan is past s
def pc.ahead_drop(bs: List<&2, O.Node>, +h: O.Node, +s: Nat, +s2: Nat, +lt: {Nat.is_lt(s, s2) == True{} : Bool}, +st: {O.Node.start(h) == s : Nat}, has: {O.Nodes.has(bs, h) == True{} : Bool}) -> {Nat.is_le(1n+pc.ahead(s2, bs), pc.ahead(s, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      pc.absurd_ft({Nat.is_le(1n, 0n) == True{} : Bool}, has)
    case +b <> +rest:
      pc.drop_step(O.Node.eq(b, h), O.Nodes.has(rest, h), s, s2, O.Node.start(b), pc.ahead(s, rest), pc.ahead(s2, rest), lt, has, e => Equal.sym(Nat, O.Node.start(b), s, Equal.trans(Nat, O.Node.start(b), O.Node.start(h), s, pc.eq_start(b, h, e), st)), pc.ahead_mono(rest, s, s2, pc.lt_to_le(s, s2, lt)), hr => pc.ahead_drop(rest, h, s, s2, lt, st, hr))

def pc.under_built(+a1: Nat, +a2: Nat, +unb: Nat, +jobs: Nat, under: {Nat.is_lt(Nat.add(a1, unb), jobs) == True{} : Bool}, mono: {Nat.is_le(a2, a1) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a2, Nat.add(unb, 0n)), jobs) == True{} : Bool}:
  %pc.add_zero(unb) : {Nat.is_lt(Nat.add(a2, _), jobs) == True{} : Bool}
  pc.le_lt_trans(Nat.add(a2, unb), Nat.add(a1, unb), jobs, pc.le_add_both(a2, a1, unb, unb, mono, pc.le_refl(unb)), under)

def pc.under_busy(+a1: Nat, +a2: Nat, +unb: Nat, +jobs: Nat, under: {Nat.is_lt(Nat.add(a1, unb), jobs) == True{} : Bool}, drop: {Nat.is_le(1n+a2, a1) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a2, Nat.add(unb, 1n)), jobs) == True{} : Bool}:
  %Cover.cover.add_one(unb) : {Nat.is_lt(Nat.add(a2, _), jobs) == True{} : Bool}
  %Cover.cover.add_succ(a2, unb) : {Nat.is_lt(_, jobs) == True{} : Bool}
  pc.le_lt_trans(1n+Nat.add(a2, unb), Nat.add(a1, unb), jobs, pc.le_add_both(1n+a2, a1, unb, unb, drop, pc.le_refl(unb)), under)

# one line of the scan: a built line passes, a free one starts, a busy
# one passes and its call drops out of the calls ahead
def pc.scan_step(stop: Bool, b: Bool, f: Bool, +info: O.Info, +h: O.Node, +rest: List<&2, O.Node>, +busy: List<&2, O.Node>, +jobs: Nat, +unb: Nat, +r: Nat, +a1: Nat, +a2: Nat, estop: {stop == False{} : Bool}, idle: {Bool.or(Bool.and(Bool.not(b), f), C.idle(info, rest, busy)) == True{} : Bool}, under: {Nat.is_lt(Nat.add(a1, unb), jobs) == True{} : Bool}, mono: {Nat.is_le(a2, a1) == True{} : Bool}, drop: {f == False{} : Bool} -> {Nat.is_le(1n+a2, a1) == True{} : Bool}, ih: {C.idle(info, rest, busy) == True{} : Bool} -> {Nat.is_lt(Nat.add(a2, Nat.add(unb, O.bit(Bool.not(b), 0n))), jobs) == True{} : Bool} -> {O.Nat.is_pos(List.length(&2, O.Node, O.cand.view(rest, info, busy, jobs, Nat.add(unb, O.bit(Bool.not(b), 0n)), 1n+r))) == True{} : Bool}) -> {O.Nat.is_pos(List.length(&2, O.Node, O.cand.emit(stop, b, f, h, O.cand.view(rest, info, busy, jobs, Nat.add(unb, O.bit(Bool.not(b), 0n)), Nat.sub(1n+r, O.bit(Bool.and(Bool.not(b), f), 0n)))))) == True{} : Bool}:
  match stop b f:
    case True{} y z:
      pc.absurd_tf({False{} == True{} : Bool}, estop)
    case False{} True{} z:
      ih(idle, pc.under_built(a1, a2, unb, jobs, under, mono))
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      ih(idle, pc.under_busy(a1, a2, unb, jobs, under, drop({==})))

def pc.scan(v: List<&2, O.Node>, +room: Nat, +info: O.Info, +busy: List<&2, O.Node>, +jobs: Nat, +unb: Nat, +s: Nat, -e: Nat, tiles: S.Tiles(s, v, e), idle: {C.idle(info, v, busy) == True{} : Bool}, pos: {O.Nat.is_pos(room) == True{} : Bool}, +under: {Nat.is_lt(Nat.add(pc.ahead(s, busy), unb), jobs) == True{} : Bool}) -> {O.Nat.is_pos(List.length(&2, O.Node, O.cand.view(v, info, busy, jobs, unb, room))) == True{} : Bool}:
  match v room:
    case Nil{} k:
      idle
    case h <> rest 0n:
      pos
    case +h <> +rest 1n+r:
      (st, tl) = tiles
      +s2 = Nat.add(s, O.Node.count(h))
      +a1 = pc.ahead(s, busy)
      +a2 = pc.ahead(s2, busy)
      pc.scan_step(Nat.is_ge(unb, jobs), O.Info.built(info, h), Bool.not(O.Nodes.has(busy, h)), info, h, rest, busy, jobs, unb, r, a1, a2, pc.lt_not_ge(unb, jobs, pc.le_lt_trans(unb, Nat.add(a1, unb), jobs, pc.le_add(a1, unb), under)), idle, under, pc.ahead_mono(busy, s, s2, pc.le_add_r(s, O.Node.count(h))), nf => pc.ahead_drop(busy, h, s, s2, pc.lt_add_pos(s, O.Node.count(h), pc.count_pos(h)), st, pc.not_false(O.Nodes.has(busy, h), nf)), i => u => pc.scan(rest, 1n+r, info, busy, jobs, Nat.add(unb, O.bit(Bool.not(O.Info.built(info, h)), 0n)), s2, e, tl, i, {==}, u))

def pc.under0(+jobs: Nat, +busy: List<&2, O.Node>, room: {Nat.is_lt(List.length(&2, O.Node, busy), jobs) == True{} : Bool}) -> {Nat.is_lt(Nat.add(pc.ahead(0n, busy), 0n), jobs) == True{} : Bool}:
  %pc.add_zero(pc.ahead(0n, busy)) : {Nat.is_lt(_, jobs) == True{} : Bool}
  pc.le_lt_trans(pc.ahead(0n, busy), List.length(&2, O.Node, busy), jobs, pc.ahead_len(0n, busy), room)

def pc.need_progress(+cfg: O.Cfg, +evs: List<&2, O.Ev>, +room: {Nat.is_lt(List.length(&2, O.Node, O.St.busy(O.run(cfg, evs))), O.Cfg.jobs(cfg)) == True{} : Bool}, idle: {C.idle(O.St.info(O.run(cfg, evs)), O.St.view(O.run(cfg, evs)), O.St.busy(O.run(cfg, evs))) == True{} : Bool}) -> {O.Nat.is_pos(List.length(&2, O.Node, O.cands.need(cfg, O.run(cfg, evs)))) == True{} : Bool}:
  +s = O.run(cfg, evs)
  +jobs = O.Cfg.jobs(cfg)
  +busy = O.St.busy(s)
  pc.scan(O.St.view(s), Nat.sub(jobs, List.length(&2, O.Node, busy)), O.St.info(s), busy, jobs, 0n, 0n, S.total.of(cfg, evs), Cover.view_covers(cfg, evs), idle, pc.sub_pos(List.length(&2, O.Node, busy), jobs, room), pc.under0(jobs, busy, room))
