# eukhe: lemmas shared by the proofs of area slash_args

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg

# Bool
# ----

def sab.not_t(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LStg.stg.absurdF({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def sab.or_fl(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LStg.stg.absurd({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def sab.or_fr(a: Bool, b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LStg.stg.absurd({b == False{} : Bool}, e)
    case False{}:
      e

def sab.or_tl(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

def sab.or_ff(a: Bool, b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ea) : {Bool.or(_, b) == False{} : Bool}
  eb

# Strings: String.eq is equality
# ------------------------------

def sab.CI(c: Cmp, G: Type) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      G
    case GT{}:
      Unit

def sab.lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  %e : sab.CI(_, G)
  Unit{}

def sab.gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  %e : sab.CI(_, G)
  Unit{}

def sab.fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def sab.cmp_eq_fin(-p: Nat, -at: Word(p), -bt: Word(p), t: Cmp, +ab: Bool, +bb: Bool,
  et: {Word.cmp(p, at, bt) == t : Cmp},
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match t:
    case LT{}:
      sab.lt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case GT{}:
      sab.gt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt, rec(et))
        case False{} True{}:
          sab.lt_eq({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, e)
        case True{} False{}:
          sab.gt_eq({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, e)
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt, rec(et))

def sab.word_eq(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e => sab.cmp_eq_fin(p, at, bt, Word.cmp(p, at, bt), ab, bb, {==}, sab.word_eq(p, at, bt), e)

def sab.u32_eq(+a: U32, +b: U32) -> {U32.cmp(a, b) == EQ{} : Cmp} -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      e => Equal.cong(Word(32n), U32, w => U32{w}, x, y, sab.word_eq(32n, x, y)(e))

def sab.str_cons(+x: U32, +y: U32, +t1: String, -t2: String, r: {t1 == t2 : String} & {U32.cmp(x, y) == EQ{} : Cmp}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {EQ{} == EQ{} : Cmp}:
  (p, q) = r
  %p : {SCon{Chr{x}, t1} == SCon{Chr{y}, _} : String} & {EQ{} == EQ{} : Cmp}
  %sab.u32_eq(x, y)(q) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t1} : String} & {EQ{} == EQ{} : Cmp}
  ({==}, {==})

def sab.str_sound(+a: String, +b: String, c: Cmp, e: {Cmp.is_eq(String.order.go(a, b, c)) == True{} : Bool}) -> {a == b : String} & {c == EQ{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      match c:
        case LT{}:
          LStg.stg.absurdF({SNil{} == SNil{} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          ({==}, {==})
        case GT{}:
          LStg.stg.absurdF({SNil{} == SNil{} : String} & {GT{} == EQ{} : Cmp}, e)
    case SNil{} SCon{h, t}:
      match c:
        case LT{}:
          LStg.stg.absurdF({SNil{} == SCon{h, t} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          LStg.stg.absurdF({SNil{} == SCon{h, t} : String} & {EQ{} == EQ{} : Cmp}, e)
        case GT{}:
          LStg.stg.absurdF({SNil{} == SCon{h, t} : String} & {GT{} == EQ{} : Cmp}, e)
    case SCon{h, t} SNil{}:
      match c:
        case LT{}:
          LStg.stg.absurdF({SCon{h, t} == SNil{} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          LStg.stg.absurdF({SCon{h, t} == SNil{} : String} & {EQ{} == EQ{} : Cmp}, e)
        case GT{}:
          LStg.stg.absurdF({SCon{h, t} == SNil{} : String} & {GT{} == EQ{} : Cmp}, e)
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          LStg.stg.absurdF({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          sab.str_cons(x, y, t1, t2, sab.str_sound(t1, t2, U32.cmp(x, y), e))
        case GT{}:
          LStg.stg.absurdF({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {GT{} == EQ{} : Cmp}, e)

# String.eq is equality
def sab.str_eq(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  sab.fst({a == b : String}, {EQ{} == EQ{} : Cmp}, sab.str_sound(a, b, EQ{}, e))

# Whitespace
# ----------

# the code's whitespace test is the laws' White_Space table
def sab.white(+c: Char) -> {Ga.space(c) == SlashArgs.sa_white(c) : Bool}:
  {==}

def sab.sp_t(+c: Char, e: {SlashArgs.sa_white(c) == True{} : Bool}) -> {Ga.space(c) == True{} : Bool}:
  Equal.trans(Bool, Ga.space(c), SlashArgs.sa_white(c), True{}, sab.white(c), e)

def sab.sp_f(+c: Char, e: {SlashArgs.sa_white(c) == False{} : Bool}) -> {Ga.space(c) == False{} : Bool}:
  Equal.trans(Bool, Ga.space(c), SlashArgs.sa_white(c), False{}, sab.white(c), e)

# Words
# -----

def sab.lapp_assoc(a: List<&2, String>, -b: List<&2, String>, -c: List<&2, String>) -> {List.append(&2, String, List.append(&2, String, a, b), c) == List.append(&2, String, a, List.append(&2, String, b, c)) : List<&2, String>}:
  match a:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, String>, List<&2, String>, z => h <> z, List.append(&2, String, List.append(&2, String, t, b), c), List.append(&2, String, t, List.append(&2, String, b, c)), sab.lapp_assoc(t, b, c))

def sab.lrev_app(a: List<&2, String>, -b: List<&2, String>, -acc: List<&2, String>) -> {List.reverse.go(&2, String, List.append(&2, String, a, b), acc) == List.reverse.go(&2, String, b, List.reverse.go(&2, String, a, acc)) : List<&2, String>}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      sab.lrev_app(t, b, h <> acc)

def sab.lrev_acc(x: List<&2, String>, -acc: List<&2, String>) -> {List.reverse.go(&2, String, x, acc) == List.append(&2, String, List.reverse.go(&2, String, x, Nil{}), acc) : List<&2, String>}:
  match x:
    case Nil{}:
      {==}
    case +h <> +t:
      +rt = List.reverse.go(&2, String, t, Nil{})
      Equal.trans(List<&2, String>, List.reverse.go(&2, String, t, h <> acc), List.append(&2, String, rt, h <> acc), List.append(&2, String, List.reverse.go(&2, String, t, [h]), acc), sab.lrev_acc(t, h <> acc), Equal.trans(List<&2, String>, List.append(&2, String, rt, h <> acc), List.append(&2, String, List.append(&2, String, rt, [h]), acc), List.append(&2, String, List.reverse.go(&2, String, t, [h]), acc), Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, rt, [h]), acc), List.append(&2, String, rt, h <> acc), sab.lapp_assoc(rt, [h], acc)), Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, acc), List.append(&2, String, rt, [h]), List.reverse.go(&2, String, t, [h]), Equal.sym(List<&2, String>, List.reverse.go(&2, String, t, [h]), List.append(&2, String, rt, [h]), sab.lrev_acc(t, [h])))))

# the tokenizer's state after the chars of s
def sab.run(s: String, st: Sa.Tok) -> Sa.Tok:
  match s:
    case SNil{}:
      st
    case SCon{+c, t}:
      sab.run(t, Sa.tok.step(c, st))

def sab.go_run(s: String, st: Sa.Tok) -> {Sa.tok.go(s, st) == Sa.tok.fin(sab.run(s, st)) : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      sab.go_run(t, Sa.tok.step(c, st))

def sab.go_app(s: String, -u: String, st: Sa.Tok) -> {Sa.tok.go(String.append(s, u), st) == Sa.tok.go(u, sab.run(s, st)) : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      sab.go_app(t, u, Sa.tok.step(c, st))

def sab.q(st: Sa.Tok) -> Maybe<&2, Char>:
  match st:
    case Sa.Tok{q, cur, qd, done}:
      q

def sab.q.in(b: Bool, x: Char, c: Char, cur: String, qd: Bool, done: List<&2, String>) -> {sab.q(Sa.tok.in_quote(b, x, c, cur, qd, done)) == SlashArgs.sa_step.in(b, x) : Maybe<&2, Char>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sab.q.out(o: Bool, wh: Bool, c: Char, cur: String, qd: Bool, done: List<&2, String>) -> {sab.q(Sa.tok.out(o, wh, c, cur, qd, done)) == SlashArgs.sa_step.out(o, c) : Maybe<&2, Char>}:
  match o wh:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the tokenizer's quote after a char is R2's
def sab.q.step(+c: Char, st: Sa.Tok) -> {sab.q(Sa.tok.step(c, st)) == SlashArgs.sa_step(c, sab.q(st)) : Maybe<&2, Char>}:
  match st:
    case Sa.Tok{q, cur, qd, done}:
      match q:
        case Some{+x}:
          sab.q.in(Char.is_eq(c, x), x, c, cur, qd, done)
        case None{}:
          sab.q.out(Bool.or(Char.is_eq(c, '"'), Char.is_eq(c, '\'')), Ga.space(c), c, cur, qd, done)

# the tokenizer's quote after a text is R2's
def sab.q.run(s: String, +st: Sa.Tok) -> {sab.q(sab.run(s, st)) == SlashArgs.sa_end(s, sab.q(st)) : Maybe<&2, Char>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %sab.q.step(c, st) : {sab.q(sab.run(t, Sa.tok.step(c, st))) == SlashArgs.sa_end(t, _) : Maybe<&2, Char>}
      sab.q.run(t, Sa.tok.step(c, st))

# the words so far, then done
def sab.add(st: Sa.Tok, d: List<&2, String>) -> Sa.Tok:
  match st:
    case Sa.Tok{q, cur, qd, e}:
      Sa.Tok{q, cur, qd, List.append(&2, String, e, d)}

def sab.push(cur: String, qd: Bool, -e: List<&2, String>, -d: List<&2, String>) -> {Sa.tok.push(cur, qd, List.append(&2, String, e, d)) == List.append(&2, String, Sa.tok.push(cur, qd, e), d) : List<&2, String>}:
  match cur qd:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{h, t} _:
      {==}

def sab.step_add.in(b: Bool, x: Char, c: Char, cur: String, qd: Bool, e: List<&2, String>, d: List<&2, String>) -> {Sa.tok.in_quote(b, x, c, cur, qd, List.append(&2, String, e, d)) == sab.add(Sa.tok.in_quote(b, x, c, cur, qd, e), d) : Sa.Tok}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sab.step_add.out(o: Bool, wh: Bool, c: Char, +cur: String, +qd: Bool, e: List<&2, String>, d: List<&2, String>) -> {Sa.tok.out(o, wh, c, cur, qd, List.append(&2, String, e, d)) == sab.add(Sa.tok.out(o, wh, c, cur, qd, e), d) : Sa.Tok}:
  match o wh:
    case True{} _:
      {==}
    case False{} True{}:
      Equal.cong(List<&2, String>, Sa.Tok, z => Sa.Tok{None{}, SNil{}, False{}, z}, Sa.tok.push(cur, qd, List.append(&2, String, e, d)), List.append(&2, String, Sa.tok.push(cur, qd, e), d), sab.push(cur, qd, e, d))
    case False{} False{}:
      {==}

def sab.step_add(+c: Char, st: Sa.Tok, d: List<&2, String>) -> {Sa.tok.step(c, sab.add(st, d)) == sab.add(Sa.tok.step(c, st), d) : Sa.Tok}:
  match st:
    case Sa.Tok{q, cur, qd, e}:
      match q:
        case Some{+x}:
          sab.step_add.in(Char.is_eq(c, x), x, c, cur, qd, e, d)
        case None{}:
          sab.step_add.out(Bool.or(Char.is_eq(c, '"'), Char.is_eq(c, '\'')), Ga.space(c), c, cur, qd, e, d)

def sab.fin_add(st: Sa.Tok, -d: List<&2, String>) -> {Sa.tok.fin(sab.add(st, d)) == List.reverse.go(&2, String, d, Sa.tok.fin(st)) : List<&2, String>}:
  match st:
    case Sa.Tok{q, +cur, +qd, +e}:
      +p0 = Sa.tok.push(cur, qd, Nil{})
      %Equal.sym(List<&2, String>, Sa.tok.push(cur, qd, e), List.append(&2, String, p0, e), sab.push(cur, qd, Nil{}, e)) : {List.reverse(&2, String, Sa.tok.push(cur, qd, List.append(&2, String, e, d))) == List.reverse.go(&2, String, d, List.reverse(&2, String, _)) : List<&2, String>}
      %Equal.sym(List<&2, String>, Sa.tok.push(cur, qd, List.append(&2, String, e, d)), List.append(&2, String, p0, List.append(&2, String, e, d)), sab.push(cur, qd, Nil{}, List.append(&2, String, e, d))) : {List.reverse(&2, String, _) == List.reverse.go(&2, String, d, List.reverse(&2, String, List.append(&2, String, p0, e))) : List<&2, String>}
      %Equal.sym(List<&2, String>, List.reverse.go(&2, String, List.append(&2, String, p0, List.append(&2, String, e, d)), Nil{}), List.reverse.go(&2, String, List.append(&2, String, e, d), List.reverse.go(&2, String, p0, Nil{})), sab.lrev_app(p0, List.append(&2, String, e, d), Nil{})) : {_ == List.reverse.go(&2, String, d, List.reverse(&2, String, List.append(&2, String, p0, e))) : List<&2, String>}
      %Equal.sym(List<&2, String>, List.reverse.go(&2, String, List.append(&2, String, e, d), List.reverse.go(&2, String, p0, Nil{})), List.reverse.go(&2, String, d, List.reverse.go(&2, String, e, List.reverse.go(&2, String, p0, Nil{}))), sab.lrev_app(e, d, List.reverse.go(&2, String, p0, Nil{}))) : {_ == List.reverse.go(&2, String, d, List.reverse(&2, String, List.append(&2, String, p0, e))) : List<&2, String>}
      %Equal.sym(List<&2, String>, List.reverse.go(&2, String, List.append(&2, String, p0, e), Nil{}), List.reverse.go(&2, String, e, List.reverse.go(&2, String, p0, Nil{})), sab.lrev_app(p0, e, Nil{})) : {List.reverse.go(&2, String, d, List.reverse.go(&2, String, e, List.reverse.go(&2, String, p0, Nil{}))) == List.reverse.go(&2, String, d, _) : List<&2, String>}
      {==}

# words added before the state: the words of the rest after them
def sab.go_add(u: String, +st: Sa.Tok, +d: List<&2, String>) -> {Sa.tok.go(u, sab.add(st, d)) == List.reverse.go(&2, String, d, Sa.tok.go(u, st)) : List<&2, String>}:
  match u:
    case SNil{}:
      sab.fin_add(st, d)
    case SCon{+c, +t}:
      %Equal.sym(Sa.Tok, Sa.tok.step(c, sab.add(st, d)), sab.add(Sa.tok.step(c, st), d), sab.step_add(c, st, d)) : {Sa.tok.go(t, _) == List.reverse.go(&2, String, d, Sa.tok.go(t, Sa.tok.step(c, st))) : List<&2, String>}
      sab.go_add(t, Sa.tok.step(c, st), d)

def sab.MI(m: Maybe<&2, Char>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def sab.some_none(-G: Type, -x: Char, e: {Some{x} == None{} : Maybe<&2, Char>}) -> G:
  %e : sab.MI(_, G)
  Unit{}

def sab.none_of(m: Maybe<&2, Char>, e: {SlashArgs.sa_none(m) == True{} : Bool}) -> {m == None{} : Maybe<&2, Char>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      LStg.stg.absurdF({Some{x} == None{} : Maybe<&2, Char>}, e)

def sab.nq.at(+c: Char, +y: Char, b: Bool, eb: {Char.is_eq(c, y) == b : Bool}, cw: {SlashArgs.sa_white(c) == True{} : Bool}, ey: {SlashArgs.sa_white(y) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, True{}, SlashArgs.sa_white(c), False{}, Equal.sym(Bool, SlashArgs.sa_white(c), True{}, cw), Equal.trans(Bool, SlashArgs.sa_white(c), SlashArgs.sa_white(y), False{}, Equal.cong(Char, Bool, z => SlashArgs.sa_white(z), c, y, LStg.stg.char_sound(c, y, eb)), ey))

# a White_Space char is not the char y, when y is not White_Space
def sab.nq(+c: Char, +y: Char, cw: {SlashArgs.sa_white(c) == True{} : Bool}, ey: {SlashArgs.sa_white(y) == False{} : Bool}) -> {Char.is_eq(c, y) == False{} : Bool}:
  sab.nq.at(c, y, Char.is_eq(c, y), {==}, cw, ey)

def sab.init() -> Sa.Tok:
  Sa.Tok{None{}, SNil{}, False{}, Nil{}}

# a White_Space char outside a quote ends the words so far
def sab.split.st(st: Sa.Tok, eq: {sab.q(st) == None{} : Maybe<&2, Char>}, +c: Char, +cw: {SlashArgs.sa_white(c) == True{} : Bool}, +t: String) -> {Sa.tok.go(SCon{c, t}, st) == List.append(&2, String, Sa.tok.fin(st), Sa.words(t)) : List<&2, String>}:
  match st:
    case Sa.Tok{q, +cur, +qd, +done}:
      match q:
        case Some{x}:
          sab.some_none({Sa.tok.go(SCon{c, t}, Sa.Tok{Some{x}, cur, qd, done}) == List.append(&2, String, Sa.tok.fin(Sa.Tok{Some{x}, cur, qd, done}), Sa.words(t)) : List<&2, String>}, x, eq)
        case None{}:
          +rhs = List.append(&2, String, Sa.tok.fin(Sa.Tok{None{}, cur, qd, done}), Sa.words(t))
          +p = Sa.tok.push(cur, qd, done)
          %Equal.sym(Bool, Char.is_eq(c, '"'), False{}, sab.nq(c, '"', cw, {==})) : {Sa.tok.go(t, Sa.tok.out(Bool.or(_, Char.is_eq(c, '\'')), Ga.space(c), c, cur, qd, done)) == rhs : List<&2, String>}
          %Equal.sym(Bool, Char.is_eq(c, '\''), False{}, sab.nq(c, '\'', cw, {==})) : {Sa.tok.go(t, Sa.tok.out(Bool.or(False{}, _), Ga.space(c), c, cur, qd, done)) == rhs : List<&2, String>}
          %Equal.sym(Bool, Ga.space(c), True{}, sab.sp_t(c, cw)) : {Sa.tok.go(t, Sa.tok.out(False{}, _, c, cur, qd, done)) == rhs : List<&2, String>}
          Equal.trans(List<&2, String>, Sa.tok.go(t, sab.add(sab.init(), p)), List.reverse.go(&2, String, p, Sa.words(t)), rhs, sab.go_add(t, sab.init(), p), sab.lrev_acc(p, Sa.words(t)))

# Strings
# -------

def sab.app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, z => SCon{h, z}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), sab.app_assoc(t, b, c))

def sab.rev_acc(x: String, -acc: String) -> {String.reverse.go(x, acc) == String.append(String.reverse.go(x, SNil{}), acc) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      +rt = String.reverse.go(t, SNil{})
      Equal.trans(String, String.reverse.go(t, SCon{h, acc}), String.append(rt, SCon{h, acc}), String.append(String.reverse.go(t, SCon{h, SNil{}}), acc), sab.rev_acc(t, SCon{h, acc}), Equal.trans(String, String.append(rt, SCon{h, acc}), String.append(String.append(rt, SCon{h, SNil{}}), acc), String.append(String.reverse.go(t, SCon{h, SNil{}}), acc), Equal.sym(String, String.append(String.append(rt, SCon{h, SNil{}}), acc), String.append(rt, SCon{h, acc}), sab.app_assoc(rt, SCon{h, SNil{}}, acc)), Equal.cong(String, String, z => String.append(z, acc), String.append(rt, SCon{h, SNil{}}), String.reverse.go(t, SCon{h, SNil{}}), Equal.sym(String, String.reverse.go(t, SCon{h, SNil{}}), String.append(rt, SCon{h, SNil{}}), sab.rev_acc(t, SCon{h, SNil{}})))))

def sab.rr(a: String, -acc: String) -> {String.reverse.go(String.reverse.go(a, acc), SNil{}) == String.reverse.go(acc, a) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      sab.rr(t, SCon{h, acc})

# One word
# --------

# R2's quoted flag after c: a quote opened outside sets it
def sab.orq.at(q: Maybe<&2, Char>, +c: Char, qd: Bool) -> Bool:
  match q:
    case None{}:
      Bool.or(SlashArgs.sa_qc(c), qd)
    case Some{x}:
      qd

def sab.orq(s: String, +q: Maybe<&2, Char>, qd: Bool) -> Bool:
  match s:
    case SNil{}:
      qd
    case SCon{+c, t}:
      sab.orq(t, SlashArgs.sa_step(c, q), sab.orq.at(q, c, qd))

def sab.cur1(m: Bool, c: Char, cur: String) -> String:
  match m:
    case True{}:
      cur
    case False{}:
      SCon{c, cur}

def sab.one.out(o: Bool, c: Char, cur: String, qd: Bool) -> {Sa.tok.out(o, False{}, c, cur, qd, Nil{}) == Sa.Tok{SlashArgs.sa_step.out(o, c), sab.cur1(o, c, cur), Bool.or(o, qd), Nil{}} : Sa.Tok}:
  match o:
    case True{}:
      {==}
    case False{}:
      {==}

def sab.one.in(b: Bool, x: Char, c: Char, cur: String, qd: Bool) -> {Sa.tok.in_quote(b, x, c, cur, qd, Nil{}) == Sa.Tok{SlashArgs.sa_step.in(b, x), sab.cur1(b, c, cur), qd, Nil{}} : Sa.Tok}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# one char of a tight text: R2's quote, the char kept unless a quote
# mark, the quoted flag
def sab.one.step(+c: Char, q: Maybe<&2, Char>, +cur: String, +qd: Bool, tq: {SlashArgs.sa_tight.at(q, c) == True{} : Bool}) -> {Sa.tok.step(c, Sa.Tok{q, cur, qd, Nil{}}) == Sa.Tok{SlashArgs.sa_step(c, q), sab.cur1(SlashArgs.sa_mark(c, q), c, cur), sab.orq.at(q, c, qd), Nil{}} : Sa.Tok}:
  match q:
    case None{}:
      %Equal.sym(Bool, Ga.space(c), False{}, sab.sp_f(c, sab.not_t(SlashArgs.sa_white(c), tq))) : {Sa.tok.out(Bool.or(Char.is_eq(c, '"'), Char.is_eq(c, '\'')), _, c, cur, qd, Nil{}) == Sa.Tok{SlashArgs.sa_step(c, None{}), sab.cur1(SlashArgs.sa_mark(c, None{}), c, cur), sab.orq.at(None{}, c, qd), Nil{}} : Sa.Tok}
      sab.one.out(Bool.or(Char.is_eq(c, '"'), Char.is_eq(c, '\'')), c, cur, qd)
    case Some{+x}:
      sab.one.in(Char.is_eq(c, x), x, c, cur, qd)

def sab.cur1.rev(m: Bool, c: Char, x: String, -cur: String) -> {String.reverse.go(SlashArgs.sa_unquote.at(m, c, x), cur) == String.reverse.go(x, sab.cur1(m, c, cur)) : String}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# a tight text read from q: R2's quote after it, its unquoted chars
# (turned around) before cur, the quoted flag
def sab.one(s: String, +q: Maybe<&2, Char>, +cur: String, +qd: Bool, +ti: {SlashArgs.sa_tight(s, q) == True{} : Bool}) -> {sab.run(s, Sa.Tok{q, cur, qd, Nil{}}) == Sa.Tok{SlashArgs.sa_end(s, q), String.reverse.go(SlashArgs.sa_unquote(s, q), cur), sab.orq(s, q, qd), Nil{}} : Sa.Tok}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +q2 = SlashArgs.sa_step(c, q)
      +m = SlashArgs.sa_mark(c, q)
      +cur2 = sab.cur1(m, c, cur)
      +qd2 = sab.orq.at(q, c, qd)
      +u = SlashArgs.sa_unquote(t, q2)
      %Equal.sym(Sa.Tok, Sa.tok.step(c, Sa.Tok{q, cur, qd, Nil{}}), Sa.Tok{q2, cur2, qd2, Nil{}}, sab.one.step(c, q, cur, qd, LStg.stg.and_l(SlashArgs.sa_tight.at(q, c), SlashArgs.sa_tight(t, q2), ti))) : {sab.run(t, _) == Sa.Tok{SlashArgs.sa_end(t, q2), String.reverse.go(SlashArgs.sa_unquote.at(m, c, u), cur), sab.orq(t, q2, qd2), Nil{}} : Sa.Tok}
      Equal.trans(Sa.Tok, sab.run(t, Sa.Tok{q2, cur2, qd2, Nil{}}), Sa.Tok{SlashArgs.sa_end(t, q2), String.reverse.go(u, cur2), sab.orq(t, q2, qd2), Nil{}}, Sa.Tok{SlashArgs.sa_end(t, q2), String.reverse.go(SlashArgs.sa_unquote.at(m, c, u), cur), sab.orq(t, q2, qd2), Nil{}}, sab.one(t, q2, cur2, qd2, LStg.stg.and_r(SlashArgs.sa_tight.at(q, c), SlashArgs.sa_tight(t, q2), ti)), Equal.cong(String, Sa.Tok, z => Sa.Tok{SlashArgs.sa_end(t, q2), z, sab.orq(t, q2, qd2), Nil{}}, String.reverse.go(u, cur2), String.reverse.go(SlashArgs.sa_unquote.at(m, c, u), cur), Equal.sym(String, String.reverse.go(SlashArgs.sa_unquote.at(m, c, u), cur), String.reverse.go(u, cur2), sab.cur1.rev(m, c, u, cur))))

def sab.or_tr(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def sab.orq_t.at(q: Maybe<&2, Char>, +c: Char, -t: String, -q2: Maybe<&2, Char>, ih: {sab.orq(t, q2, True{}) == True{} : Bool}) -> {sab.orq(t, q2, sab.orq.at(q, c, True{})) == True{} : Bool}:
  match q:
    case None{}:
      %Equal.sym(Bool, Bool.or(SlashArgs.sa_qc(c), True{}), True{}, sab.or_tr(SlashArgs.sa_qc(c))) : {sab.orq(t, q2, _) == True{} : Bool}
      ih
    case Some{x}:
      ih

# a quote once opened keeps the flag
def sab.orq_t(s: String, +q: Maybe<&2, Char>) -> {sab.orq(s, q, True{}) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      sab.orq_t.at(q, c, t, SlashArgs.sa_step(c, q), sab.orq_t(t, SlashArgs.sa_step(c, q)))

def sab.push_app(x: String, +u0: Char, q: Bool) -> {Sa.tok.push(String.append(x, SCon{u0, SNil{}}), q, Nil{}) == [String.reverse(String.append(x, SCon{u0, SNil{}}))] : List<&2, String>}:
  match x:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# one word, when it has a char or held a quote
def sab.push_rev(u: String, +q: Bool, ok: {Bool.or(Bool.not(String.is_empty(u)), q) == True{} : Bool}) -> {List.reverse(&2, String, Sa.tok.push(String.reverse.go(u, SNil{}), q, Nil{})) == [u] : List<&2, String>}:
  match u:
    case SNil{}:
      %Equal.sym(Bool, q, True{}, ok) : {List.reverse(&2, String, Sa.tok.push(SNil{}, _, Nil{})) == [SNil{}] : List<&2, String>}
      {==}
    case SCon{+u0, +us}:
      +x = String.reverse.go(us, SNil{})
      %Equal.sym(String, String.reverse.go(us, SCon{u0, SNil{}}), String.append(x, SCon{u0, SNil{}}), sab.rev_acc(us, SCon{u0, SNil{}})) : {List.reverse(&2, String, Sa.tok.push(_, q, Nil{})) == [SCon{u0, us}] : List<&2, String>}
      %Equal.sym(List<&2, String>, Sa.tok.push(String.append(x, SCon{u0, SNil{}}), q, Nil{}), [String.reverse(String.append(x, SCon{u0, SNil{}}))], sab.push_app(x, u0, q)) : {List.reverse(&2, String, _) == [SCon{u0, us}] : List<&2, String>}
      %sab.rev_acc(us, SCon{u0, SNil{}}) : {List.reverse(&2, String, [String.reverse(_)]) == [SCon{u0, us}] : List<&2, String>}
      %Equal.sym(String, String.reverse.go(String.reverse.go(SCon{u0, us}, SNil{}), SNil{}), SCon{u0, us}, sab.rr(SCon{u0, us}, SNil{})) : {List.reverse(&2, String, [_]) == [SCon{u0, us}] : List<&2, String>}
      {==}

def sab.one_ok.at(b: Bool, +c: Char, +t: String) -> {Bool.or(Bool.not(String.is_empty(SlashArgs.sa_unquote.at(b, c, SlashArgs.sa_unquote(t, SlashArgs.sa_step.out(b, c))))), sab.orq(t, SlashArgs.sa_step.out(b, c), Bool.or(b, False{}))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, sab.orq(t, Some{c}, True{}), True{}, sab.orq_t(t, Some{c})) : {Bool.or(Bool.not(String.is_empty(SlashArgs.sa_unquote(t, Some{c}))), _) == True{} : Bool}
      sab.or_tr(Bool.not(String.is_empty(SlashArgs.sa_unquote(t, Some{c}))))
    case False{}:
      {==}

def sab.one_ok(+c: Char, +t: String, b: Bool, eb: {SlashArgs.sa_qc(c) == b : Bool}) -> {Bool.or(Bool.not(String.is_empty(SlashArgs.sa_unquote(SCon{c, t}, None{}))), sab.orq(SCon{c, t}, None{}, False{})) == True{} : Bool}:
  %Equal.sym(Bool, SlashArgs.sa_qc(c), b, eb) : {Bool.or(Bool.not(String.is_empty(SlashArgs.sa_unquote.at(_, c, SlashArgs.sa_unquote(t, SlashArgs.sa_step.out(_, c))))), sab.orq(t, SlashArgs.sa_step.out(_, c), Bool.or(_, False{}))) == True{} : Bool}
  sab.one_ok.at(b, c, t)

# `/auto`
# -------

def sab.auto_ws(+s: String, +ws: List<&2, String>, e: {Sa.words(s) == ws : List<&2, String>}) -> {Sa.auto(s) == Sa.auto.words(ws, s) : Sa.Auto}:
  Equal.cong(List<&2, String>, Sa.Auto, z => Sa.auto.words(z, s), Sa.words(s), ws, e)

def sab.alone.at(st: Bool, on: Bool, off: Bool, s: String) -> {Sa.auto.kw(st, on, off, Nil{}, s) == SlashArgs.sa_alone.at(st, on, off, s) : Sa.Auto}:
  match st on off:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def sab.ne_off.at(+l: String, +x: String, b: Bool, eb: {String.eq(l, x) == b : Bool}, eo: {SlashArgs.sa_off(l) == True{} : Bool}, ex: {SlashArgs.sa_off(x) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, True{}, SlashArgs.sa_off(l), False{}, Equal.sym(Bool, SlashArgs.sa_off(l), True{}, eo), Equal.trans(Bool, SlashArgs.sa_off(l), SlashArgs.sa_off(x), False{}, Equal.cong(String, Bool, z => SlashArgs.sa_off(z), l, x, sab.str_eq(l, x, eb)), ex))

# l is an off word: it is not x, an on word
def sab.ne_off(+l: String, +x: String, eo: {SlashArgs.sa_off(l) == True{} : Bool}, ex: {SlashArgs.sa_off(x) == False{} : Bool}) -> {String.eq(l, x) == False{} : Bool}:
  sab.ne_off.at(l, x, String.eq(l, x), {==}, eo, ex)

def sab.ne_on.at(+l: String, +x: String, b: Bool, eb: {String.eq(l, x) == b : Bool}, eo: {SlashArgs.sa_on(l) == True{} : Bool}, ex: {SlashArgs.sa_on(x) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, True{}, SlashArgs.sa_on(l), False{}, Equal.sym(Bool, SlashArgs.sa_on(l), True{}, eo), Equal.trans(Bool, SlashArgs.sa_on(l), SlashArgs.sa_on(x), False{}, Equal.cong(String, Bool, z => SlashArgs.sa_on(z), l, x, sab.str_eq(l, x, eb)), ex))

# l is an on word: it is not x
def sab.ne_on(+l: String, +x: String, eo: {SlashArgs.sa_on(l) == True{} : Bool}, ex: {SlashArgs.sa_on(x) == False{} : Bool}) -> {String.eq(l, x) == False{} : Bool}:
  sab.ne_on.at(l, x, String.eq(l, x), {==}, eo, ex)

# an off word is no on word
def sab.on_off(+l: String, +eo: {SlashArgs.sa_off(l) == True{} : Bool}) -> {SlashArgs.sa_on(l) == False{} : Bool}:
  sab.or_ff(String.eq(l, "on"), Bool.or(String.eq(l, "enable"), String.eq(l, "enabled")), sab.ne_off(l, "on", eo, {==}), sab.or_ff(String.eq(l, "enable"), String.eq(l, "enabled"), sab.ne_off(l, "enable", eo, {==}), sab.ne_off(l, "enabled", eo, {==})))

def sab.snd(rr: Sa.Read & Sa.Read) -> Sa.Read:
  (a, b) = rr
  b

# the options of x then t: x's step, before the reads of t
def sab.first_word(+x: String, +t: List<&2, String>, rr: Sa.Read & Sa.Read) -> {Sa.options.fst(Sa.reads.of(x, t, rr)) == Sa.step(String.starts_with(x, "--"), x, t, Sa.options.fst(rr), sab.snd(rr)) : Sa.Read}:
  match rr:
    case (a, b):
      {==}

def sab.raw.at(b: Bool, c: Char, r: String) -> {Sa.before_eq.at(b, c, r) == SlashArgs.sa_raw.at(b, c, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's flag of a word is R7's
def sab.raw(s: String) -> {Sa.before_eq(s) == SlashArgs.sa_raw(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Sa.before_eq(t), SlashArgs.sa_raw(t), sab.raw(t)) : {Sa.before_eq.at(Char.is_eq(c, '='), c, _) == SlashArgs.sa_raw(SCon{c, t}) : String}
      sab.raw.at(Char.is_eq(c, '='), c, SlashArgs.sa_raw(t))

def sab.name.d(d: Bool, +f: String) -> {Sa.name.dashes(d, f) == SlashArgs.sa_name.at(False{}, d, f) : String}:
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

def sab.name.at(a: Bool, +f: String) -> {Sa.name.of(a, f) == SlashArgs.sa_name.at(a, String.starts_with(f, "--"), f) : String}:
  match a:
    case True{}:
      {==}
    case False{}:
      sab.name.d(String.starts_with(f, "--"), f)

# the code's name of a flag is R7's
def sab.name(+f: String) -> {Sa.name.of(String.starts_with(f, "--autonomous-"), f) == SlashArgs.sa_name(f) : String}:
  sab.name.at(String.starts_with(f, "--autonomous-"), f)

def sab.idx8(b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, b8: Bool, e: {Bool.or(b1, Bool.or(b2, Bool.or(b3, Bool.or(b4, Bool.or(b5, Bool.or(b6, Bool.or(b7, b8))))))) == False{} : Bool}) -> {Sa.index.at(b1, 0n, Sa.index.at(b2, 1n, Sa.index.at(b3, 2n, Sa.index.at(b4, 3n, Sa.index.at(b5, 4n, Sa.index.at(b6, 5n, Sa.index.at(b7, 6n, Sa.index.at(b8, 7n, None{})))))))) == None{} : Maybe<&2, Nat>}:
  match b1:
    case True{}:
      LStg.stg.absurd({Sa.index.at(True{}, 0n, Sa.index.at(b2, 1n, Sa.index.at(b3, 2n, Sa.index.at(b4, 3n, Sa.index.at(b5, 4n, Sa.index.at(b6, 5n, Sa.index.at(b7, 6n, Sa.index.at(b8, 7n, None{})))))))) == None{} : Maybe<&2, Nat>}, e)
    case False{}:
      match b2:
        case True{}:
          LStg.stg.absurd({Sa.index.at(True{}, 1n, Sa.index.at(b3, 2n, Sa.index.at(b4, 3n, Sa.index.at(b5, 4n, Sa.index.at(b6, 5n, Sa.index.at(b7, 6n, Sa.index.at(b8, 7n, None{}))))))) == None{} : Maybe<&2, Nat>}, e)
        case False{}:
          match b3:
            case True{}:
              LStg.stg.absurd({Sa.index.at(True{}, 2n, Sa.index.at(b4, 3n, Sa.index.at(b5, 4n, Sa.index.at(b6, 5n, Sa.index.at(b7, 6n, Sa.index.at(b8, 7n, None{})))))) == None{} : Maybe<&2, Nat>}, e)
            case False{}:
              match b4:
                case True{}:
                  LStg.stg.absurd({Sa.index.at(True{}, 3n, Sa.index.at(b5, 4n, Sa.index.at(b6, 5n, Sa.index.at(b7, 6n, Sa.index.at(b8, 7n, None{}))))) == None{} : Maybe<&2, Nat>}, e)
                case False{}:
                  match b5:
                    case True{}:
                      LStg.stg.absurd({Sa.index.at(True{}, 4n, Sa.index.at(b6, 5n, Sa.index.at(b7, 6n, Sa.index.at(b8, 7n, None{})))) == None{} : Maybe<&2, Nat>}, e)
                    case False{}:
                      match b6:
                        case True{}:
                          LStg.stg.absurd({Sa.index.at(True{}, 5n, Sa.index.at(b7, 6n, Sa.index.at(b8, 7n, None{}))) == None{} : Maybe<&2, Nat>}, e)
                        case False{}:
                          match b7:
                            case True{}:
                              LStg.stg.absurd({Sa.index.at(True{}, 6n, Sa.index.at(b8, 7n, None{})) == None{} : Maybe<&2, Nat>}, e)
                            case False{}:
                              match b8:
                                case True{}:
                                  LStg.stg.absurd({Sa.index.at(True{}, 7n, None{}) == None{} : Maybe<&2, Nat>}, e)
                                case False{}:
                                  {==}

# a name that is no budget flag: the code finds no flag index
def sab.index_none(+n: String, u: {SlashArgs.sa_known(n) == False{} : Bool}) -> {Sa.index(n, Sa.flags(), 0n) == None{} : Maybe<&2, Nat>}:
  sab.idx8(String.eq(n, "max-continuations"), String.eq(n, "max-turns"), String.eq(n, "max-tokens"), String.eq(n, "timeout-ms"), String.eq(n, "gate"), String.eq(n, "gate-retries"), String.eq(n, "gate-timeout-ms"), String.eq(n, "subagent-keep-alive-ms"), u)

# Digits (R4, R8)
# ---------------

# the code's digits test is R4's
def sab.digits(s: String) -> {Sa.all_digits(s) == SlashArgs.sa_digits(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Sa.all_digits(t), SlashArgs.sa_digits(t), sab.digits(t)) : {Bool.and(Char.is_digit(c), _) == SlashArgs.sa_digits(SCon{c, t}) : Bool}
      {==}

def sab.lead.at(a: Bool, z: Bool, x: Bool) -> {Bool.and(Bool.not(z), Bool.and(a, x)) == Bool.and(Bool.and(a, Bool.not(z)), x) : Bool}:
  match a:
    case True{}:
      match z:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match z:
        case True{}:
          {==}
        case False{}:
          {==}

# the code's positive test is R4's leading digit test, its conjuncts
# reordered
def sab.positive_lead(s: String) -> {Sa.positive(s) == SlashArgs.sa_lead(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Sa.all_digits(t), SlashArgs.sa_digits(t), sab.digits(t)) : {Bool.and(Bool.not(Char.is_eq(c, '0')), Bool.and(Char.is_digit(c), _)) == SlashArgs.sa_lead(SCon{c, t}) : Bool}
      sab.lead.at(Char.is_digit(c), Char.is_eq(c, '0'), SlashArgs.sa_digits(t))
