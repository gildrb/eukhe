# eukhe: lemmas of the proofs of area redirect_input: a paste of an
# address with a query (rq.paste: cleaning trims and drops in the address
# only, and the query is what follows its first `?`), values (rq.*: a
# value is a plain text that holds a char).

import Base
import ../../../bend/redirect_input.bend as Ri
import ../../../laws/redirect_input.bend as RedirectInput
import ./text.bend as LT
import ./parse.bend as LP

# a value is plain
def rq.plain(c: String, h: {RedirectInput.ri_value(c) == True{} : Bool}) -> {RedirectInput.ri_plain(c) == True{} : Bool}:
  match c:
    case SNil{}:
      LT.rt.absurdF({RedirectInput.ri_plain(SNil{}) == True{} : Bool}, h)
    case SCon{x, t}:
      h

# a value holds a char
def rq.ne(c: String, h: {RedirectInput.ri_value(c) == True{} : Bool}) -> {String.is_empty(c) == False{} : Bool}:
  match c:
    case SNil{}:
      LT.rt.absurdF({String.is_empty(SNil{}) == False{} : Bool}, h)
    case SCon{x, t}:
      {==}

# a value is calm
def rq.calm(+c: String, h: {RedirectInput.ri_value(c) == True{} : Bool}) -> {LT.rt.calm(c) == True{} : Bool}:
  LT.rt.plain_calm(c, rq.plain(c, h))

# a value lacks the mark n
def rq.lacks(+c: String, +n: Nat, h: {RedirectInput.ri_value(c) == True{} : Bool}) -> {LT.rt.lacks(c, LT.rt.mark(n)) == True{} : Bool}:
  LT.rt.plain_lacks(c, n, rq.plain(c, h))

# a value decodes to itself
def rq.dec(+c: String, h: {RedirectInput.ri_value(c) == True{} : Bool}) -> {Ri.decode(c) == c : String}:
  LP.rp.dec(c, rq.plain(c, h))

# slashes lack every char but `/`
def rq.sl_lacks(n: Nat, +k: Char, +hk: {Char.is_eq('/', k) == False{} : Bool}) -> {LT.rt.lacks(RedirectInput.ri_slashes(n), k) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      LT.rt.and_t(Bool.not(Char.is_eq('/', k)), LT.rt.lacks(RedirectInput.ri_slashes(m), k), LT.rt.not_f(Char.is_eq('/', k), hk), rq.sl_lacks(m, k, hk))

def rq.rev_ne(y: String, ne: {String.is_empty(y) == False{} : Bool}) -> {String.is_empty(String.reverse(y)) == False{} : Bool}:
  match y:
    case SNil{}:
      LT.rt.absurd({String.is_empty(SNil{}) == False{} : Bool}, ne)
    case SCon{+c, +t}:
      LT.rt.rev_ne(c, t)

# a text x then y, y ending with no `/`, ends with no `/`
def rq.nofs_tail(+x: String, +y: String, h: {LP.rp.nofs(String.reverse(y)) == True{} : Bool}, ne: {String.is_empty(y) == False{} : Bool}) -> {LP.rp.nofs(String.reverse(String.append(x, y))) == True{} : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(x, y), SNil{}), String.reverse.go(y, String.reverse(x)), LT.rt.rev_app(x, y, SNil{})) : {LP.rp.nofs(_) == True{} : Bool}
  %Equal.sym(String, String.reverse.go(y, String.reverse(x)), String.append(String.reverse(y), String.reverse(x)), LT.rt.rev_acc(y, String.reverse(x))) : {LP.rp.nofs(_) == True{} : Bool}
  LP.rp.nofs_app(String.reverse(y), String.reverse(x), h, rq.rev_ne(y, ne))

# a value ends with no `/`
def rq.nofs(+c: String, h: {RedirectInput.ri_value(c) == True{} : Bool}) -> {LP.rp.nofs(String.reverse(c)) == True{} : Bool}:
  LP.rp.nofs_end(SNil{}, c, h)

# The query
# ---------

# the address b without `?`, then `?` and a calm text q: q is the query
def rq.paste(+b: String, +q: String, nq: {RedirectInput.ri_lacks(b, 63) == True{} : Bool}, hc: {LT.rt.calm(q) == True{} : Bool}) -> {Ri.parse(String.append(b, SCon{'?', q})) == Ri.parse.query(Ri.split(q, '#'), q) : Ri.Answer}:
  +Y = Ri.unwrap(Ri.compact(b))
  +lk = LP.rp.lk_unwrap(Ri.compact(b), '?', LP.rp.lk_compact(b, '?', LT.rt.lacks_code(b, 63, nq)))
  %Equal.sym(String, Ri.clean(String.append(b, SCon{'?', q})), String.append(Y, SCon{'?', q}), LT.rt.clean_tail(b, '?', q, hc)) : {Ri.parse.at(Ri.split(_, '?'), _) == Ri.parse.query(Ri.split(q, '#'), q) : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(String.append(Y, SCon{'?', q}), '?'), Some{Ri.Cut{Y, q}}, LP.rp.split_hit(Y, '?', q, {==}, lk)) : {Ri.parse.at(_, String.append(Y, SCon{'?', q})) == Ri.parse.query(Ri.split(q, '#'), q) : Ri.Answer}
  {==}

# ... and a query q without `#` gives its parameters, trailing slashes dropped
def rq.query(+b: String, +q: String, nq: {RedirectInput.ri_lacks(b, 63) == True{} : Bool}, hc: {LT.rt.calm(q) == True{} : Bool}, nh: {LT.rt.lacks(q, '#') == True{} : Bool}) -> {Ri.parse(String.append(b, SCon{'?', q})) == Ri.from_params([Ri.unslash(q), SNil{}]) : Ri.Answer}:
  %Equal.sym(Ri.Answer, Ri.parse(String.append(b, SCon{'?', q})), Ri.parse.query(Ri.split(q, '#'), q), rq.paste(b, q, nq, hc)) : {_ == Ri.from_params([Ri.unslash(q), SNil{}]) : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(q, '#'), None{}, LP.rp.split_none(q, '#', nh)) : {Ri.parse.query(_, q) == Ri.from_params([Ri.unslash(q), SNil{}]) : Ri.Answer}
  {==}
