# eukhe: lemmas of the cut proofs of area rlm_query. Both the code's flat
# loop (qc.code) and the spec's longest prefix (qc.spec) are the reference
# cut qc.R, which takes a char while its bytes fit the room left; the cut
# of R keeps at most the room (qc.within) and R cuts a ++ b as a, then b
# (qc.app).

import Base
import ../../../bend/rlm_query.bend as Rq
import ../../../spec/rlm/query.bend as QSpec
import ../../../laws/rlm_query.bend as RlmQuery
import ./nat.bend as LN

# The reference cut
# -----------------

def qc.pick(fit: Bool, +w: Nat, x: Rq.Trim) -> Rq.Trim:
  match fit:
    case True{}:
      RlmQuery.rq_shift(w, x)
    case False{}:
      Rq.CutAt{0n}

# the cut of t under room bytes: a char that fits is kept, then the rest
# cuts in the room left; a char that does not fit cuts before it
def qc.R(t: String, +room: Nat) -> Rq.Trim:
  match t:
    case SNil{}:
      Rq.Fits{}
    case SCon{c, r}:
      +w = Rq.bytes(c)
      qc.pick(Nat.is_le(w, room), w, qc.R(r, Nat.sub(room, w)))

def qc.shift0(x: Rq.Trim) -> {RlmQuery.rq_shift(0n, x) == x : Rq.Trim}:
  match x:
    case Rq.Fits{}:
      {==}
    case Rq.CutAt{k}:
      {==}

def qc.shift2(+a: Nat, +w: Nat, x: Rq.Trim) -> {RlmQuery.rq_shift(Nat.add(a, w), x) == RlmQuery.rq_shift(a, RlmQuery.rq_shift(w, x)) : Rq.Trim}:
  match x:
    case Rq.Fits{}:
      {==}
    case Rq.CutAt{+k}:
      Equal.cong(Nat, Rq.Trim, z => Rq.CutAt{z}, Nat.add(Nat.add(a, w), k), Nat.add(a, Nat.add(w, k)), LN.rq.add_assoc(a, w, k))

# The code is the reference
# -------------------------

# the loop at a char c with the chars s after it, at bytes before c
def qc.go(s: String, f: Bool, +c: Char, +room: Nat, +at: Nat, +hf: {Nat.is_le(Rq.bytes(c), room) == f : Bool}) -> {Rq.cut.go(s, f, Rq.bytes(c), room, at) == RlmQuery.rq_shift(at, qc.R(SCon{c, s}, room)) : Rq.Trim}:
  match s:
    case SNil{}:
      match f:
        case True{}:
          %Equal.sym(Bool, Nat.is_le(Rq.bytes(c), room), True{}, hf) : {Rq.Fits{} == RlmQuery.rq_shift(at, qc.pick(_, Rq.bytes(c), Rq.Fits{})) : Rq.Trim}
          {==}
        case False{}:
          %Equal.sym(Bool, Nat.is_le(Rq.bytes(c), room), False{}, hf) : {Rq.CutAt{at} == RlmQuery.rq_shift(at, qc.pick(_, Rq.bytes(c), Rq.Fits{})) : Rq.Trim}
          Equal.cong(Nat, Rq.Trim, z => Rq.CutAt{z}, at, Nat.add(at, 0n), Equal.sym(Nat, Nat.add(at, 0n), at, LN.rq.add_zero(at)))
    case SCon{+c2, +s2}:
      match f:
        case True{}:
          %Equal.sym(Bool, Nat.is_le(Rq.bytes(c), room), True{}, hf) : {Rq.cut.go(SCon{c2, s2}, True{}, Rq.bytes(c), room, at) == RlmQuery.rq_shift(at, qc.pick(_, Rq.bytes(c), qc.R(SCon{c2, s2}, Nat.sub(room, Rq.bytes(c))))) : Rq.Trim}
          Equal.trans(Rq.Trim, Rq.cut.go(s2, Nat.is_le(Rq.bytes(c2), Nat.sub(room, Rq.bytes(c))), Rq.bytes(c2), Nat.sub(room, Rq.bytes(c)), Nat.add(at, Rq.bytes(c))), RlmQuery.rq_shift(Nat.add(at, Rq.bytes(c)), qc.R(SCon{c2, s2}, Nat.sub(room, Rq.bytes(c)))), RlmQuery.rq_shift(at, RlmQuery.rq_shift(Rq.bytes(c), qc.R(SCon{c2, s2}, Nat.sub(room, Rq.bytes(c))))), qc.go(s2, Nat.is_le(Rq.bytes(c2), Nat.sub(room, Rq.bytes(c))), c2, Nat.sub(room, Rq.bytes(c)), Nat.add(at, Rq.bytes(c)), {==}), qc.shift2(at, Rq.bytes(c), qc.R(SCon{c2, s2}, Nat.sub(room, Rq.bytes(c)))))
        case False{}:
          %Equal.sym(Bool, Nat.is_le(Rq.bytes(c), room), False{}, hf) : {Rq.CutAt{at} == RlmQuery.rq_shift(at, qc.pick(_, Rq.bytes(c), qc.R(SCon{c2, s2}, Nat.sub(room, Rq.bytes(c))))) : Rq.Trim}
          Equal.cong(Nat, Rq.Trim, z => Rq.CutAt{z}, at, Nat.add(at, 0n), Equal.sym(Nat, Nat.add(at, 0n), at, LN.rq.add_zero(at)))

# the code's cut is the reference
def qc.code(t: String, +m: Nat) -> {Rq.cut(m, t) == qc.R(t, m) : Rq.Trim}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      Equal.trans(Rq.Trim, Rq.cut.go(r, Nat.is_le(Rq.bytes(c), m), Rq.bytes(c), m, 0n), RlmQuery.rq_shift(0n, qc.R(SCon{c, r}, m)), qc.R(SCon{c, r}, m), qc.go(r, Nat.is_le(Rq.bytes(c), m), c, m, 0n, {==}), qc.shift0(qc.R(SCon{c, r}, m)))

# The spec is the reference
# -------------------------

def qc.width.of(a: Bool, b: Bool, c: Bool) -> {QSpec.width.of(a, b, c) == Rq.bytes.of(a, b, c) : Nat}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}

# the spec's width of a char is the code's
def qc.width(c: Char) -> {QSpec.width(c) == Rq.bytes(c) : Nat}:
  match c:
    case Chr{+x}:
      qc.width.of(U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))

def qc.pick_same(b: Bool, +x: Nat) -> {QSpec.longest.pick(b, x, x) == x : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def qc.pick_add(b: Bool, +w: Nat, +x: Nat, +y: Nat) -> {QSpec.longest.pick(b, Nat.add(w, x), Nat.add(w, y)) == Nat.add(w, QSpec.longest.pick(b, x, y)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the prefixes after a char c that fits: c's bytes on top of the prefixes
# in the room c leaves
def qc.heads(ps: List<&2, String>, +c: Char, +m: Nat, +b: Nat, +hw: {Nat.is_le(Rq.bytes(c), m) == True{} : Bool}) -> {QSpec.longest(m, QSpec.heads(c, ps), Nat.add(Rq.bytes(c), b)) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), ps, b)) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +q}:
      %Equal.sym(Nat, QSpec.width(c), Rq.bytes(c), qc.width(c)) : {QSpec.longest(m, QSpec.heads(c, q), QSpec.longest.pick(Nat.is_le(Nat.add(_, QSpec.utf8(p)), m), Nat.add(_, QSpec.utf8(p)), Nat.add(Rq.bytes(c), b))) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), q, QSpec.longest.pick(Nat.is_le(QSpec.utf8(p), Nat.sub(m, Rq.bytes(c))), QSpec.utf8(p), b))) : Nat}
      %Equal.sym(Bool, Nat.is_le(Nat.add(Rq.bytes(c), QSpec.utf8(p)), m), Nat.is_le(QSpec.utf8(p), Nat.sub(m, Rq.bytes(c))), LN.rq.le_shift(Rq.bytes(c), m, QSpec.utf8(p), hw)) : {QSpec.longest(m, QSpec.heads(c, q), QSpec.longest.pick(_, Nat.add(Rq.bytes(c), QSpec.utf8(p)), Nat.add(Rq.bytes(c), b))) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), q, QSpec.longest.pick(Nat.is_le(QSpec.utf8(p), Nat.sub(m, Rq.bytes(c))), QSpec.utf8(p), b))) : Nat}
      %Equal.sym(Nat, QSpec.longest.pick(Nat.is_le(QSpec.utf8(p), Nat.sub(m, Rq.bytes(c))), Nat.add(Rq.bytes(c), QSpec.utf8(p)), Nat.add(Rq.bytes(c), b)), Nat.add(Rq.bytes(c), QSpec.longest.pick(Nat.is_le(QSpec.utf8(p), Nat.sub(m, Rq.bytes(c))), QSpec.utf8(p), b)), qc.pick_add(Nat.is_le(QSpec.utf8(p), Nat.sub(m, Rq.bytes(c))), Rq.bytes(c), QSpec.utf8(p), b)) : {QSpec.longest(m, QSpec.heads(c, q), _) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), q, QSpec.longest.pick(Nat.is_le(QSpec.utf8(p), Nat.sub(m, Rq.bytes(c))), QSpec.utf8(p), b))) : Nat}
      qc.heads(q, c, m, QSpec.longest.pick(Nat.is_le(QSpec.utf8(p), Nat.sub(m, Rq.bytes(c))), QSpec.utf8(p), b), hw)

# the prefixes after a char c that does not fit: none fits
def qc.past(ps: List<&2, String>, +c: Char, +m: Nat, +b: Nat, +hw: {Nat.is_le(Rq.bytes(c), m) == False{} : Bool}) -> {QSpec.longest(m, QSpec.heads(c, ps), b) == b : Nat}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +q}:
      %Equal.sym(Nat, QSpec.width(c), Rq.bytes(c), qc.width(c)) : {QSpec.longest(m, QSpec.heads(c, q), QSpec.longest.pick(Nat.is_le(Nat.add(_, QSpec.utf8(p)), m), Nat.add(_, QSpec.utf8(p)), b)) == b : Nat}
      %Equal.sym(Bool, Nat.is_le(Nat.add(Rq.bytes(c), QSpec.utf8(p)), m), False{}, LN.rq.le_past(Rq.bytes(c), m, QSpec.utf8(p), hw)) : {QSpec.longest(m, QSpec.heads(c, q), QSpec.longest.pick(_, Nat.add(Rq.bytes(c), QSpec.utf8(p)), b)) == b : Nat}
      qc.past(q, c, m, b, hw)

def qc.fit.of(ps: List<&2, String>, +c: Char, +m: Nat, +hw: {Nat.is_le(Rq.bytes(c), m) == True{} : Bool}) -> {QSpec.longest(m, QSpec.heads(c, "" <> ps), QSpec.longest.pick(Nat.is_le(0n, m), 0n, 0n)) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), "" <> ps, 0n)) : Nat}:
  %Equal.sym(Nat, QSpec.longest.pick(Nat.is_le(0n, m), 0n, 0n), 0n, qc.pick_same(Nat.is_le(0n, m), 0n)) : {QSpec.longest(m, QSpec.heads(c, "" <> ps), _) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), "" <> ps, 0n)) : Nat}
  %Equal.sym(Nat, QSpec.width(c), Rq.bytes(c), qc.width(c)) : {QSpec.longest(m, QSpec.heads(c, ps), QSpec.longest.pick(Nat.is_le(Nat.add(_, 0n), m), Nat.add(_, 0n), 0n)) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), "" <> ps, 0n)) : Nat}
  %Equal.sym(Nat, Nat.add(Rq.bytes(c), 0n), Rq.bytes(c), LN.rq.add_zero(Rq.bytes(c))) : {QSpec.longest(m, QSpec.heads(c, ps), QSpec.longest.pick(Nat.is_le(_, m), _, 0n)) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), "" <> ps, 0n)) : Nat}
  %Equal.sym(Bool, Nat.is_le(Rq.bytes(c), m), True{}, hw) : {QSpec.longest(m, QSpec.heads(c, ps), QSpec.longest.pick(_, Rq.bytes(c), 0n)) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), "" <> ps, 0n)) : Nat}
  %Equal.sym(Nat, QSpec.longest.pick(Nat.is_le(0n, Nat.sub(m, Rq.bytes(c))), 0n, 0n), 0n, qc.pick_same(Nat.is_le(0n, Nat.sub(m, Rq.bytes(c))), 0n)) : {QSpec.longest(m, QSpec.heads(c, ps), Rq.bytes(c)) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), ps, _)) : Nat}
  %LN.rq.add_zero(Rq.bytes(c)) : {QSpec.longest(m, QSpec.heads(c, ps), _) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), ps, 0n)) : Nat}
  qc.heads(ps, c, m, 0n, hw)

# a char c that fits: the longest prefix of c ++ r is c's bytes on top of
# the longest prefix of r in the room c leaves
def qc.fit(r: String, +c: Char, +m: Nat, +hw: {Nat.is_le(Rq.bytes(c), m) == True{} : Bool}) -> {QSpec.longest(m, QSpec.prefixes(SCon{c, r}), 0n) == Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), QSpec.prefixes(r), 0n)) : Nat}:
  match r:
    case SNil{}:
      qc.fit.of(Nil{}, c, m, hw)
    case SCon{c2, r2}:
      qc.fit.of(QSpec.heads(c2, QSpec.prefixes(r2)), c, m, hw)

# a char c that does not fit: the longest prefix is the empty one
def qc.nofit(r: String, +c: Char, +m: Nat, +hw: {Nat.is_le(Rq.bytes(c), m) == False{} : Bool}) -> {QSpec.longest(m, QSpec.prefixes(SCon{c, r}), 0n) == 0n : Nat}:
  %Equal.sym(Nat, QSpec.longest.pick(Nat.is_le(0n, m), 0n, 0n), 0n, qc.pick_same(Nat.is_le(0n, m), 0n)) : {QSpec.longest(m, QSpec.heads(c, QSpec.prefixes(r)), _) == 0n : Nat}
  qc.past(QSpec.prefixes(r), c, m, 0n, hw)

def qc.step(g: Bool, +c: Char, +r: String, +m: Nat, +hw: {Nat.is_le(Rq.bytes(c), m) == True{} : Bool}) -> {QSpec.cut.of(g, m, SCon{c, r}) == RlmQuery.rq_shift(Rq.bytes(c), QSpec.cut.of(g, Nat.sub(m, Rq.bytes(c)), r)) : Rq.Trim}:
  match g:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Nat, Rq.Trim, z => Rq.CutAt{z}, QSpec.longest(m, QSpec.prefixes(SCon{c, r}), 0n), Nat.add(Rq.bytes(c), QSpec.longest(Nat.sub(m, Rq.bytes(c)), QSpec.prefixes(r), 0n)), qc.fit(r, c, m, hw))

def qc.spec.c(f: Bool, +c: Char, +r: String, +m: Nat, +hf: {Nat.is_le(Rq.bytes(c), m) == f : Bool}, ih: {QSpec.cut(Nat.sub(m, Rq.bytes(c)), r) == qc.R(r, Nat.sub(m, Rq.bytes(c))) : Rq.Trim}) -> {QSpec.cut(m, SCon{c, r}) == qc.R(SCon{c, r}, m) : Rq.Trim}:
  match f:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(Rq.bytes(c), m), True{}, hf) : {QSpec.cut(m, SCon{c, r}) == qc.pick(_, Rq.bytes(c), qc.R(r, Nat.sub(m, Rq.bytes(c)))) : Rq.Trim}
      %ih : {QSpec.cut(m, SCon{c, r}) == RlmQuery.rq_shift(Rq.bytes(c), _) : Rq.Trim}
      %Equal.sym(Nat, QSpec.width(c), Rq.bytes(c), qc.width(c)) : {QSpec.cut.of(Nat.is_le(Nat.add(_, QSpec.utf8(r)), m), m, SCon{c, r}) == RlmQuery.rq_shift(Rq.bytes(c), QSpec.cut(Nat.sub(m, Rq.bytes(c)), r)) : Rq.Trim}
      %Equal.sym(Bool, Nat.is_le(Nat.add(Rq.bytes(c), QSpec.utf8(r)), m), Nat.is_le(QSpec.utf8(r), Nat.sub(m, Rq.bytes(c))), LN.rq.le_shift(Rq.bytes(c), m, QSpec.utf8(r), hf)) : {QSpec.cut.of(_, m, SCon{c, r}) == RlmQuery.rq_shift(Rq.bytes(c), QSpec.cut(Nat.sub(m, Rq.bytes(c)), r)) : Rq.Trim}
      qc.step(Nat.is_le(QSpec.utf8(r), Nat.sub(m, Rq.bytes(c))), c, r, m, hf)
    case False{}:
      %Equal.sym(Bool, Nat.is_le(Rq.bytes(c), m), False{}, hf) : {QSpec.cut(m, SCon{c, r}) == qc.pick(_, Rq.bytes(c), qc.R(r, Nat.sub(m, Rq.bytes(c)))) : Rq.Trim}
      %Equal.sym(Nat, QSpec.width(c), Rq.bytes(c), qc.width(c)) : {QSpec.cut.of(Nat.is_le(Nat.add(_, QSpec.utf8(r)), m), m, SCon{c, r}) == Rq.CutAt{0n} : Rq.Trim}
      %Equal.sym(Bool, Nat.is_le(Nat.add(Rq.bytes(c), QSpec.utf8(r)), m), False{}, LN.rq.le_past(Rq.bytes(c), m, QSpec.utf8(r), hf)) : {QSpec.cut.of(_, m, SCon{c, r}) == Rq.CutAt{0n} : Rq.Trim}
      Equal.cong(Nat, Rq.Trim, z => Rq.CutAt{z}, QSpec.longest(m, QSpec.prefixes(SCon{c, r}), 0n), 0n, qc.nofit(r, c, m, hf))

# the spec's cut is the reference
def qc.spec(t: String, +m: Nat) -> {QSpec.cut(m, t) == qc.R(t, m) : Rq.Trim}:
  match t:
    case SNil{}:
      %Equal.sym(Bool, Nat.is_le(0n, m), True{}, LN.rq.le_zero(m)) : {QSpec.cut.of(_, m, SNil{}) == Rq.Fits{} : Rq.Trim}
      {==}
    case SCon{+c, +r}:
      qc.spec.c(Nat.is_le(Rq.bytes(c), m), c, r, m, {==}, qc.spec(r, Nat.sub(m, Rq.bytes(c))))

# The reference's cuts
# --------------------

def qc.W(x: Rq.Trim, +room: Nat) -> Type:
  match x:
    case Rq.Fits{}:
      Unit
    case Rq.CutAt{k}:
      {Nat.is_le(k, room) == True{} : Bool}

def qc.within.c(f: Bool, +w: Nat, +room: Nat, hf: {Nat.is_le(w, room) == f : Bool}, x: Rq.Trim, ih: qc.W(x, Nat.sub(room, w))) -> qc.W(qc.pick(f, w, x), room):
  match f:
    case True{}:
      match x:
        case Rq.Fits{}:
          Unit{}
        case Rq.CutAt{+j}:
          LN.rq.sub_add_le(w, room, j, ih, hf)
    case False{}:
      LN.rq.le_zero(room)

# a cut keeps at most the room
def qc.within(t: String, +room: Nat) -> qc.W(qc.R(t, room), room):
  match t:
    case SNil{}:
      Unit{}
    case SCon{+c, +r}:
      qc.within.c(Nat.is_le(Rq.bytes(c), room), Rq.bytes(c), room, {==}, qc.R(r, Nat.sub(room, Rq.bytes(c))), qc.within(r, Nat.sub(room, Rq.bytes(c))))

# the reference's cut of a ++ b from the cut of a
def qc.then(x: Rq.Trim, +m: Nat, +a: String, b: String) -> Rq.Trim:
  match x:
    case Rq.Fits{}:
      RlmQuery.rq_shift(QSpec.utf8(a), qc.R(b, Nat.sub(m, QSpec.utf8(a))))
    case Rq.CutAt{k}:
      Rq.CutAt{k}

def qc.app.c(f: Bool, +c: Char, +a2: String, +m: Nat, +b: String, x: Rq.Trim) -> {qc.pick(f, Rq.bytes(c), qc.then(x, Nat.sub(m, Rq.bytes(c)), a2, b)) == qc.then(qc.pick(f, Rq.bytes(c), x), m, SCon{c, a2}, b) : Rq.Trim}:
  match f:
    case True{}:
      match x:
        case Rq.Fits{}:
          %Equal.sym(Nat, QSpec.width(c), Rq.bytes(c), qc.width(c)) : {RlmQuery.rq_shift(Rq.bytes(c), RlmQuery.rq_shift(QSpec.utf8(a2), qc.R(b, Nat.sub(Nat.sub(m, Rq.bytes(c)), QSpec.utf8(a2))))) == RlmQuery.rq_shift(Nat.add(_, QSpec.utf8(a2)), qc.R(b, Nat.sub(m, Nat.add(_, QSpec.utf8(a2))))) : Rq.Trim}
          %Equal.sym(Nat, Nat.sub(m, Nat.add(Rq.bytes(c), QSpec.utf8(a2))), Nat.sub(Nat.sub(m, Rq.bytes(c)), QSpec.utf8(a2)), LN.rq.sub_sub(m, Rq.bytes(c), QSpec.utf8(a2))) : {RlmQuery.rq_shift(Rq.bytes(c), RlmQuery.rq_shift(QSpec.utf8(a2), qc.R(b, Nat.sub(Nat.sub(m, Rq.bytes(c)), QSpec.utf8(a2))))) == RlmQuery.rq_shift(Nat.add(Rq.bytes(c), QSpec.utf8(a2)), qc.R(b, _)) : Rq.Trim}
          Equal.sym(Rq.Trim, RlmQuery.rq_shift(Nat.add(Rq.bytes(c), QSpec.utf8(a2)), qc.R(b, Nat.sub(Nat.sub(m, Rq.bytes(c)), QSpec.utf8(a2)))), RlmQuery.rq_shift(Rq.bytes(c), RlmQuery.rq_shift(QSpec.utf8(a2), qc.R(b, Nat.sub(Nat.sub(m, Rq.bytes(c)), QSpec.utf8(a2))))), qc.shift2(Rq.bytes(c), QSpec.utf8(a2), qc.R(b, Nat.sub(Nat.sub(m, Rq.bytes(c)), QSpec.utf8(a2)))))
        case Rq.CutAt{j}:
          {==}
    case False{}:
      {==}

# the reference cuts a ++ b as a, then b in the room a leaves
def qc.app(a: String, +m: Nat, +b: String) -> {qc.R(String.append(a, b), m) == qc.then(qc.R(a, m), m, a, b) : Rq.Trim}:
  match a:
    case SNil{}:
      Equal.sym(Rq.Trim, RlmQuery.rq_shift(0n, qc.R(b, Nat.sub(m, 0n))), qc.R(b, m), Equal.trans(Rq.Trim, RlmQuery.rq_shift(0n, qc.R(b, Nat.sub(m, 0n))), qc.R(b, Nat.sub(m, 0n)), qc.R(b, m), qc.shift0(qc.R(b, Nat.sub(m, 0n))), Equal.cong(Nat, Rq.Trim, z => qc.R(b, z), Nat.sub(m, 0n), m, LN.rq.sub_zero(m))))
    case SCon{+c, +a2}:
      Equal.trans(Rq.Trim, qc.pick(Nat.is_le(Rq.bytes(c), m), Rq.bytes(c), qc.R(String.append(a2, b), Nat.sub(m, Rq.bytes(c)))), qc.pick(Nat.is_le(Rq.bytes(c), m), Rq.bytes(c), qc.then(qc.R(a2, Nat.sub(m, Rq.bytes(c))), Nat.sub(m, Rq.bytes(c)), a2, b)), qc.then(qc.pick(Nat.is_le(Rq.bytes(c), m), Rq.bytes(c), qc.R(a2, Nat.sub(m, Rq.bytes(c)))), m, SCon{c, a2}, b), Equal.cong(Rq.Trim, Rq.Trim, z => qc.pick(Nat.is_le(Rq.bytes(c), m), Rq.bytes(c), z), qc.R(String.append(a2, b), Nat.sub(m, Rq.bytes(c))), qc.then(qc.R(a2, Nat.sub(m, Rq.bytes(c))), Nat.sub(m, Rq.bytes(c)), a2, b), qc.app(a2, Nat.sub(m, Rq.bytes(c)), b)), qc.app.c(Nat.is_le(Rq.bytes(c), m), c, a2, m, b, qc.R(a2, Nat.sub(m, Rq.bytes(c)))))

# the law's continuation is the reference's
def qc.then_eq(x: Rq.Trim, +m: Nat, +a: String, +b: String) -> {RlmQuery.rq_cut_then(x, m, a, b) == qc.then(x, m, a, b) : Rq.Trim}:
  match x:
    case Rq.Fits{}:
      Equal.cong(Rq.Trim, Rq.Trim, z => RlmQuery.rq_shift(QSpec.utf8(a), z), Rq.cut(Nat.sub(m, QSpec.utf8(a)), b), qc.R(b, Nat.sub(m, QSpec.utf8(a))), qc.code(b, Nat.sub(m, QSpec.utf8(a))))
    case Rq.CutAt{k}:
      {==}
