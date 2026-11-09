# eukhe: lemmas of area privacy, section session: the map a session's
# texts leave (laws/privacy/session.bend) is the spec's map of all their
# pieces scrubbed as one text from the empty map (psn.sess), and what each
# class of a class that maps back holds there is the class's distinct
# values among those pieces, in the order they first appear (psn.tk): a
# value the pieces hold sits at its number, one they do not is absent, and
# the class holds as many values as the pieces have kinds of it. The
# pieces are read last first (psn.rv): one more piece is one more scrub
# step (psn.hstep).

import Base
import ../../../bend/privacy/token.bend as Tk
import ../../../spec/harness/privacy.bend as S
import ../../../spec/harness/privacy_map.bend as Sm
import ../../../laws/privacy/session.bend as Ses
import ./map.bend as LMp
import ./stext.bend as LSt

# Logic
# -----

def psn.IfSome(m: Maybe<&2, String>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# a premise None == Some proves anything
def psn.none_some(-b: String, -G: Type, e: {None{} == Some{b} : Maybe<&2, String>}) -> G:
  %e : psn.IfSome(_, G)
  Unit{}

def psn.some_val(d: String, m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def psn.some_inj(+a: String, +b: String, e: {Some{a} == Some{b} : Maybe<&2, String>}) -> {a == b : String}:
  Equal.cong(Maybe<&2, String>, String, m => psn.some_val(a, m), Some{a}, Some{b}, e)

def psn.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def psn.or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def psn.or_fl(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LMp.pmp.absurd({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, e))
    case False{}:
      {==}

def psn.or_fr(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LMp.pmp.absurd({b == False{} : Bool}, Equal.sym(Bool, True{}, False{}, e))
    case False{}:
      e

def psn.or_keep(p: Bool, -x: Bool, -y: Bool, h: {Bool.or(p, x) == True{} : Bool}, ih: {x == True{} : Bool} -> {y == True{} : Bool}) -> {Bool.or(p, y) == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      ih(h)

# Equal to itself
# ---------------

def psn.scr(c: Tk.Class) -> {Sm.same_class(c, c) == True{} : Bool}:
  match c:
    case Tk.Person{}:
      {==}
    case Tk.Email{}:
      {==}
    case Tk.Phone{}:
      {==}
    case Tk.Ip{}:
      {==}
    case Tk.Id{}:
      {==}
    case Tk.ApiKey{}:
      {==}
    case Tk.Card{}:
      {==}
    case Tk.Iban{}:
      {==}

def psn.nrefl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      psn.nrefl(p)

def psn.word_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case True{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, psn.word_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}
            case False{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, psn.word_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}

def psn.u32_refl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      psn.word_refl(32n, w)

def psn.str_order_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{} : Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, psn.u32_refl(x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
          psn.str_order_refl(t)

def psn.str_refl(a: String) -> {String.eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, String.order.go(a, a, EQ{}), EQ{}, psn.str_order_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def psn.ecf(b: Bool, +u: String, +w: String, eb: {String.eq(w, u) == b : Bool}, e: {String.eq(u, w) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, True{}, String.eq(u, u), False{}, Equal.sym(Bool, String.eq(u, u), True{}, psn.str_refl(u)), Equal.trans(Bool, String.eq(u, u), String.eq(u, w), False{}, Equal.cong(String, Bool, z => String.eq(u, z), u, w, Equal.sym(String, w, u, LMp.pmp.str_eq(w, u, eb))), e))

# u is not w, so w is not u
def psn.eq_comm_f(+u: String, +w: String, e: {String.eq(u, w) == False{} : Bool}) -> {String.eq(w, u) == False{} : Bool}:
  psn.ecf(String.eq(w, u), u, w, {==}, e)

# Lists
# -----

def psn.app_nil(xs: List<&2, Tk.Piece>) -> {List.append(&2, Tk.Piece, xs, Nil{}) == xs : List<&2, Tk.Piece>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      %psn.app_nil(rest) : {x <> List.append(&2, Tk.Piece, rest, Nil{}) == x <> _ : List<&2, Tk.Piece>}
      {==}

def psn.app_assoc(a: List<&2, Tk.Piece>, +b: List<&2, Tk.Piece>, +c: List<&2, Tk.Piece>) -> {List.append(&2, Tk.Piece, List.append(&2, Tk.Piece, a, b), c) == List.append(&2, Tk.Piece, a, List.append(&2, Tk.Piece, b, c)) : List<&2, Tk.Piece>}:
  match a:
    case Nil{}:
      {==}
    case x <> rest:
      %psn.app_assoc(rest, b, c) : {x <> List.append(&2, Tk.Piece, List.append(&2, Tk.Piece, rest, b), c) == x <> _ : List<&2, Tk.Piece>}
      {==}

# the pieces xs, last first
def psn.rv(xs: List<&2, Tk.Piece>) -> List<&2, Tk.Piece>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      List.append(&2, Tk.Piece, psn.rv(rest), [x])

def psn.rv_app(a: List<&2, Tk.Piece>, +b: List<&2, Tk.Piece>) -> {psn.rv(List.append(&2, Tk.Piece, a, b)) == List.append(&2, Tk.Piece, psn.rv(b), psn.rv(a)) : List<&2, Tk.Piece>}:
  match a:
    case Nil{}:
      Equal.sym(List<&2, Tk.Piece>, List.append(&2, Tk.Piece, psn.rv(b), Nil{}), psn.rv(b), psn.app_nil(psn.rv(b)))
    case +x <> +rest:
      %Equal.sym(List<&2, Tk.Piece>, psn.rv(List.append(&2, Tk.Piece, rest, b)), List.append(&2, Tk.Piece, psn.rv(b), psn.rv(rest)), psn.rv_app(rest, b)) : {List.append(&2, Tk.Piece, _, [x]) == List.append(&2, Tk.Piece, psn.rv(b), List.append(&2, Tk.Piece, psn.rv(rest), [x])) : List<&2, Tk.Piece>}
      psn.app_assoc(psn.rv(b), psn.rv(rest), [x])

def psn.rv_rv(xs: List<&2, Tk.Piece>) -> {psn.rv(psn.rv(xs)) == xs : List<&2, Tk.Piece>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      %Equal.sym(List<&2, Tk.Piece>, psn.rv(List.append(&2, Tk.Piece, psn.rv(r), [x])), List.append(&2, Tk.Piece, psn.rv([x]), psn.rv(psn.rv(r))), psn.rv_app(psn.rv(r), [x])) : {_ == x <> r : List<&2, Tk.Piece>}
      %psn.rv_rv(r) : {x <> psn.rv(psn.rv(r)) == x <> _ : List<&2, Tk.Piece>}
      {==}

# The map of a history
# --------------------

# the spec's map after the pieces K scrubbed as one text from the empty map
def psn.B(K: List<&2, Tk.Piece>) -> Tk.Book:
  Sm.toks_book(Sm.scrub_vals(Sm.vals(K), Tk.Book.empty()))

# the values class c holds in that map, oldest first
def psn.hb(K: List<&2, Tk.Piece>, c: Tk.Class) -> List<&2, String>:
  Sm.held(Tk.Book.es(psn.B(K)), c)

# the values class c holds after one more piece x, from those before
def psn.step(+acc: List<&2, String>, x: Tk.Piece, +c: Tk.Class) -> List<&2, String>:
  match x:
    case Tk.Plain{s}:
      acc
    case Tk.Value{+d, +w}:
      Sm.held.add(Bool.and(Sm.same_class(c, d), Bool.and(S.reversible(d), Sm.fresh(Sm.place(acc, w)))), acc, w)

def psn.vals_app(a: List<&2, Tk.Piece>, +b: List<&2, Tk.Piece>) -> {List.append(&2, Tk.Val, Sm.vals(a), Sm.vals(b)) == Sm.vals(List.append(&2, Tk.Piece, a, b)) : List<&2, Tk.Val>}:
  match a:
    case Nil{}:
      {==}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          psn.vals_app(rest, b)
        case Tk.Value{c, v}:
          %psn.vals_app(rest, b) : {Tk.Val{c, v} <> List.append(&2, Tk.Val, Sm.vals(rest), Sm.vals(b)) == Tk.Val{c, v} <> _ : List<&2, Tk.Val>}
          {==}

def psn.tb(-t: Tk.Tok, r: Tk.Toks) -> {Sm.toks_book(r) == Sm.toks_book(Sm.push(t, r)) : Tk.Book}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

# values scrubbed one list after another: the map after both
def psn.book_app(vs: List<&2, Tk.Val>, +ws: List<&2, Tk.Val>, +b: Tk.Book) -> {Sm.toks_book(Sm.scrub_vals(List.append(&2, Tk.Val, vs, ws), b)) == Sm.toks_book(Sm.scrub_vals(ws, Sm.toks_book(Sm.scrub_vals(vs, b)))) : Tk.Book}:
  match vs:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Tk.Val{+c, +v}:
          %psn.tb(Sm.step_tok(Sm.scrub1(b, c, v)), Sm.scrub_vals(List.append(&2, Tk.Val, rest, ws), Sm.step_book(Sm.scrub1(b, c, v)))) : {_ == Sm.toks_book(Sm.scrub_vals(ws, Sm.toks_book(Sm.push(Sm.step_tok(Sm.scrub1(b, c, v)), Sm.scrub_vals(rest, Sm.step_book(Sm.scrub1(b, c, v))))))) : Tk.Book}
          %psn.tb(Sm.step_tok(Sm.scrub1(b, c, v)), Sm.scrub_vals(rest, Sm.step_book(Sm.scrub1(b, c, v)))) : {Sm.toks_book(Sm.scrub_vals(List.append(&2, Tk.Val, rest, ws), Sm.step_book(Sm.scrub1(b, c, v)))) == Sm.toks_book(Sm.scrub_vals(ws, _)) : Tk.Book}
          psn.book_app(rest, ws, Sm.step_book(Sm.scrub1(b, c, v)))

# one more piece: one more scrub step from the map before it
def psn.bsnoc(+K: List<&2, Tk.Piece>, +x: Tk.Piece) -> {psn.B(List.append(&2, Tk.Piece, K, [x])) == Sm.toks_book(Sm.scrub_vals(Sm.vals([x]), psn.B(K))) : Tk.Book}:
  %psn.vals_app(K, [x]) : {Sm.toks_book(Sm.scrub_vals(_, Tk.Book.empty())) == Sm.toks_book(Sm.scrub_vals(Sm.vals([x]), psn.B(K))) : Tk.Book}
  psn.book_app(Sm.vals(K), Sm.vals([x]), Tk.Book.empty())

def psn.add_f(s: Bool, xs: List<&2, String>, w: String) -> {xs == Sm.held.add(Bool.and(s, False{}), xs, w) : List<&2, String>}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

def psn.l1_m(m: Maybe<&2, Nat>, +es: List<&2, Tk.Ent>, +c: Tk.Class, +w: String) -> {Sm.held(Tk.Book.es(Sm.step_book(Sm.scrub1.place(m, es, c, w))), c) == Sm.held.add(Sm.fresh(m), Sm.held(es, c), w) : List<&2, String>}:
  match m:
    case Some{i}:
      {==}
    case None{}:
      %Equal.sym(Bool, Sm.same_class(c, c), True{}, psn.scr(c)) : {Sm.held.add(_, Sm.held(es, c), w) == Sm.held.add(True{}, Sm.held(es, c), w) : List<&2, String>}
      {==}

def psn.l1_f(m: Maybe<&2, Nat>, +es: List<&2, Tk.Ent>, +c: Tk.Class, +d: Tk.Class, +w: String, e: {Sm.same_class(c, d) == False{} : Bool}) -> {Sm.held(Tk.Book.es(Sm.step_book(Sm.scrub1.place(m, es, d, w))), c) == Sm.held(es, c) : List<&2, String>}:
  match m:
    case Some{i}:
      {==}
    case None{}:
      %Equal.sym(Bool, Sm.same_class(c, d), False{}, e) : {Sm.held.add(_, Sm.held(es, c), w) == Sm.held(es, c) : List<&2, String>}
      {==}

def psn.l1_t(sc: Bool, +es: List<&2, Tk.Ent>, +c: Tk.Class, +d: Tk.Class, +w: String, e: {Sm.same_class(c, d) == sc : Bool}) -> {Sm.held(Tk.Book.es(Sm.step_book(Sm.scrub1.place(Sm.place(Sm.held(es, d), w), es, d, w))), c) == Sm.held.add(Bool.and(sc, Sm.fresh(Sm.place(Sm.held(es, c), w))), Sm.held(es, c), w) : List<&2, String>}:
  match sc:
    case True{}:
      %LMp.pmp.class_eq(c, d, e) : {Sm.held(Tk.Book.es(Sm.step_book(Sm.scrub1.place(Sm.place(Sm.held(es, _), w), es, _, w))), c) == Sm.held.add(Sm.fresh(Sm.place(Sm.held(es, c), w)), Sm.held(es, c), w) : List<&2, String>}
      psn.l1_m(Sm.place(Sm.held(es, c), w), es, c, w)
    case False{}:
      psn.l1_f(Sm.place(Sm.held(es, d), w), es, c, d, w, e)

def psn.l1_of(r: Bool, +es: List<&2, Tk.Ent>, +c: Tk.Class, +d: Tk.Class, +w: String) -> {Sm.held(Tk.Book.es(Sm.step_book(Sm.scrub1.of(r, Tk.Book{es}, d, w))), c) == Sm.held.add(Bool.and(Sm.same_class(c, d), Bool.and(r, Sm.fresh(Sm.place(Sm.held(es, c), w)))), Sm.held(es, c), w) : List<&2, String>}:
  match r:
    case True{}:
      psn.l1_t(Sm.same_class(c, d), es, c, d, w, {==})
    case False{}:
      psn.add_f(Sm.same_class(c, d), Sm.held(es, c), w)

# what a class holds after the spec scrubs one value
def psn.l1(b: Tk.Book, +c: Tk.Class, +d: Tk.Class, +w: String) -> {Sm.held(Tk.Book.es(Sm.step_book(Sm.scrub1(b, d, w))), c) == psn.step(Sm.held(Tk.Book.es(b), c), Tk.Value{d, w}, c) : List<&2, String>}:
  match b:
    case Tk.Book{es}:
      psn.l1_of(S.reversible(d), es, c, d, w)

# what a class holds after one more piece of history
def psn.hstep(+K: List<&2, Tk.Piece>, x: Tk.Piece, +c: Tk.Class) -> {psn.hb(List.append(&2, Tk.Piece, K, [x]), c) == psn.step(psn.hb(K, c), x, c) : List<&2, String>}:
  match x:
    case Tk.Plain{+s}:
      %Equal.sym(Tk.Book, psn.B(List.append(&2, Tk.Piece, K, [Tk.Plain{s}])), Sm.toks_book(Sm.scrub_vals(Sm.vals([Tk.Plain{s}]), psn.B(K))), psn.bsnoc(K, Tk.Plain{s})) : {Sm.held(Tk.Book.es(_), c) == psn.hb(K, c) : List<&2, String>}
      {==}
    case Tk.Value{+d, +w}:
      %Equal.sym(Tk.Book, psn.B(List.append(&2, Tk.Piece, K, [Tk.Value{d, w}])), Sm.toks_book(Sm.scrub_vals(Sm.vals([Tk.Value{d, w}]), psn.B(K))), psn.bsnoc(K, Tk.Value{d, w})) : {Sm.held(Tk.Book.es(_), c) == psn.step(psn.hb(K, c), Tk.Value{d, w}, c) : List<&2, String>}
      psn.l1(psn.B(K), c, d, w)

# A session is that map
# ---------------------

def psn.out_m(-xs: List<&2, Tk.Piece>, r: Tk.Toks) -> {Sm.toks_book(r) == Tk.Out.m(Sm.text(xs, r)) : Tk.Book}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

def psn.sess_go(xss: List<&2, List<&2, Tk.Piece>>, +m: Tk.Book, +ok: {Sm.book_distinct(m) == True{} : Bool}) -> {Ses.session.go(xss, m) == Sm.toks_book(Sm.scrub_vals(Sm.vals(List.concat(&2, Tk.Piece, xss)), m)) : Tk.Book}:
  match xss:
    case Nil{}:
      {==}
    case +xs <> +rest:
      %Equal.sym(Tk.Out, Tk.scrub(m, xs), Sm.scrub_text(xs, m), LSt.pst.scrub(m, xs, ok)) : {Ses.session.go(rest, Tk.Out.m(_)) == Sm.toks_book(Sm.scrub_vals(Sm.vals(List.append(&2, Tk.Piece, xs, List.concat(&2, Tk.Piece, rest))), m)) : Tk.Book}
      %psn.out_m(xs, Sm.scrub_vals(Sm.vals(xs), m)) : {Ses.session.go(rest, _) == Sm.toks_book(Sm.scrub_vals(Sm.vals(List.append(&2, Tk.Piece, xs, List.concat(&2, Tk.Piece, rest))), m)) : Tk.Book}
      %psn.vals_app(xs, List.concat(&2, Tk.Piece, rest)) : {Ses.session.go(rest, Sm.toks_book(Sm.scrub_vals(Sm.vals(xs), m))) == Sm.toks_book(Sm.scrub_vals(_, m)) : Tk.Book}
      %Equal.sym(Tk.Book, Sm.toks_book(Sm.scrub_vals(List.append(&2, Tk.Val, Sm.vals(xs), Sm.vals(List.concat(&2, Tk.Piece, rest))), m)), Sm.toks_book(Sm.scrub_vals(Sm.vals(List.concat(&2, Tk.Piece, rest)), Sm.toks_book(Sm.scrub_vals(Sm.vals(xs), m)))), psn.book_app(Sm.vals(xs), Sm.vals(List.concat(&2, Tk.Piece, rest)), m)) : {Ses.session.go(rest, Sm.toks_book(Sm.scrub_vals(Sm.vals(xs), m))) == _ : Tk.Book}
      psn.sess_go(rest, Sm.toks_book(Sm.scrub_vals(Sm.vals(xs), m)), LMp.pmp.dk(Sm.vals(xs), m, ok))

# a session's map is the spec's map of its history
def psn.sess(+xss: List<&2, List<&2, Tk.Piece>>) -> {Ses.session(xss) == psn.B(Ses.history(xss)) : Tk.Book}:
  psn.sess_go(xss, Tk.Book.empty(), {==})

# The history
# -----------

def psn.hy0(+c: Tk.Class, +d: Tk.Class, +v: String, +w: String, e: {Sm.same_class(c, d) == False{} : Bool}) -> {Ses.has([Tk.Value{d, w}], c, v) == False{} : Bool}:
  Equal.cong(Bool, Bool, s => Bool.or(Bool.and(s, String.eq(v, w)), False{}), Sm.same_class(c, d), False{}, e)

def psn.hy1(+c: Tk.Class, +d: Tk.Class, +v: String, +w: String, e: {String.eq(v, w) == False{} : Bool}) -> {Ses.has([Tk.Value{d, w}], c, v) == False{} : Bool}:
  %Equal.sym(Bool, String.eq(v, w), False{}, e) : {Bool.or(Bool.and(Sm.same_class(c, d), _), False{}) == False{} : Bool}
  %Equal.sym(Bool, Bool.and(Sm.same_class(c, d), False{}), False{}, psn.and_f(Sm.same_class(c, d))) : {Bool.or(_, False{}) == False{} : Bool}
  {==}

# pieces that hold no v of class c change nothing about it
def psn.has_app_f(K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, hy: {Ses.has(Y, c, v) == False{} : Bool}) -> {Ses.has(K, c, v) == Ses.has(List.append(&2, Tk.Piece, K, Y), c, v) : Bool}:
  match K:
    case Nil{}:
      Equal.sym(Bool, Ses.has(Y, c, v), False{}, hy)
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          psn.has_app_f(rest, Y, c, v, hy)
        case Tk.Value{d, w}:
          %psn.has_app_f(rest, Y, c, v, hy) : {Bool.or(Bool.and(Sm.same_class(c, d), String.eq(v, w)), Ses.has(rest, c, v)) == Bool.or(Bool.and(Sm.same_class(c, d), String.eq(v, w)), _) : Bool}
          {==}

def psn.has_app_t(K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String) -> {Ses.has(K, c, v) == True{} : Bool} -> {Ses.has(List.append(&2, Tk.Piece, K, Y), c, v) == True{} : Bool}:
  match K:
    case Nil{}:
      h => LMp.pmp.absurd({Ses.has(Y, c, v) == True{} : Bool}, h)
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          h => psn.has_app_t(rest, Y, c, v)(h)
        case Tk.Value{+d, +w}:
          h => psn.or_keep(Bool.and(Sm.same_class(c, d), String.eq(v, w)), Ses.has(rest, c, v), Ses.has(List.append(&2, Tk.Piece, rest, Y), c, v), h, psn.has_app_t(rest, Y, c, v))

def psn.has_snoc_self(K: List<&2, Tk.Piece>, +c: Tk.Class, +w: String) -> {Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w) == True{} : Bool}:
  match K:
    case Nil{}:
      %Equal.sym(Bool, Sm.same_class(c, c), True{}, psn.scr(c)) : {Bool.or(Bool.and(_, String.eq(w, w)), False{}) == True{} : Bool}
      %Equal.sym(Bool, String.eq(w, w), True{}, psn.str_refl(w)) : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          psn.has_snoc_self(rest, c, w)
        case Tk.Value{+d, +u}:
          %Equal.sym(Bool, Ses.has(List.append(&2, Tk.Piece, rest, [Tk.Value{c, w}]), c, w), True{}, psn.has_snoc_self(rest, c, w)) : {Bool.or(Bool.and(Sm.same_class(c, d), String.eq(w, u)), _) == True{} : Bool}
          psn.or_t(Bool.and(Sm.same_class(c, d), String.eq(w, u)))

def psn.bt_at(hit: Bool, d: Tk.Class, w: String, -rest: List<&2, Tk.Piece>, -Y: List<&2, Tk.Piece>, -c: Tk.Class, -v: String, h: {Bool.or(hit, Ses.has(rest, c, v)) == True{} : Bool}, ih: {Ses.has(rest, c, v) == True{} : Bool} -> {Ses.before(rest, c, v) == Ses.before(List.append(&2, Tk.Piece, rest, Y), c, v) : List<&2, Tk.Piece>}) -> {Ses.before.at(hit, d, w, Ses.before(rest, c, v)) == Ses.before.at(hit, d, w, Ses.before(List.append(&2, Tk.Piece, rest, Y), c, v)) : List<&2, Tk.Piece>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      Equal.cong(List<&2, Tk.Piece>, List<&2, Tk.Piece>, z => Tk.Value{d, w} <> z, Ses.before(rest, c, v), Ses.before(List.append(&2, Tk.Piece, rest, Y), c, v), ih(h))

# pieces after the first v change nothing before it
def psn.bs_t(K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String) -> {Ses.has(K, c, v) == True{} : Bool} -> {Ses.before(K, c, v) == Ses.before(List.append(&2, Tk.Piece, K, Y), c, v) : List<&2, Tk.Piece>}:
  match K:
    case Nil{}:
      h => LMp.pmp.absurd({Nil{} == Ses.before(Y, c, v) : List<&2, Tk.Piece>}, h)
    case x <> rest:
      match x:
        case Tk.Plain{+s}:
          h => Equal.cong(List<&2, Tk.Piece>, List<&2, Tk.Piece>, z => Tk.Plain{s} <> z, Ses.before(rest, c, v), Ses.before(List.append(&2, Tk.Piece, rest, Y), c, v), psn.bs_t(rest, Y, c, v)(h))
        case Tk.Value{+d, +w}:
          h => psn.bt_at(Bool.and(Sm.same_class(c, d), String.eq(v, w)), d, w, rest, Y, c, v, h, psn.bs_t(rest, Y, c, v))

# pieces with no v: all of them come before the first v after them
def psn.bs_f(K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, +h: {Ses.has(K, c, v) == False{} : Bool}) -> {List.append(&2, Tk.Piece, K, Ses.before(Y, c, v)) == Ses.before(List.append(&2, Tk.Piece, K, Y), c, v) : List<&2, Tk.Piece>}:
  match K:
    case Nil{}:
      {==}
    case x <> rest:
      match x:
        case Tk.Plain{+s}:
          Equal.cong(List<&2, Tk.Piece>, List<&2, Tk.Piece>, z => Tk.Plain{s} <> z, List.append(&2, Tk.Piece, rest, Ses.before(Y, c, v)), Ses.before(List.append(&2, Tk.Piece, rest, Y), c, v), psn.bs_f(rest, Y, c, v, h))
        case Tk.Value{+d, +w}:
          %Equal.sym(Bool, Bool.and(Sm.same_class(c, d), String.eq(v, w)), False{}, psn.or_fl(Bool.and(Sm.same_class(c, d), String.eq(v, w)), Ses.has(rest, c, v), h)) : {Tk.Value{d, w} <> List.append(&2, Tk.Piece, rest, Ses.before(Y, c, v)) == Ses.before.at(_, d, w, Ses.before(List.append(&2, Tk.Piece, rest, Y), c, v)) : List<&2, Tk.Piece>}
          Equal.cong(List<&2, Tk.Piece>, List<&2, Tk.Piece>, z => Tk.Value{d, w} <> z, List.append(&2, Tk.Piece, rest, Ses.before(Y, c, v)), Ses.before(List.append(&2, Tk.Piece, rest, Y), c, v), psn.bs_f(rest, Y, c, v, psn.or_fr(Bool.and(Sm.same_class(c, d), String.eq(v, w)), Ses.has(rest, c, v), h)))

# a value the history holds keeps its number after more pieces
def psn.number_old(+K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, h: {Ses.has(K, c, v) == True{} : Bool}) -> {Ses.number(K, c, v) == Ses.number(List.append(&2, Tk.Piece, K, Y), c, v) : Nat}:
  Equal.cong(List<&2, Tk.Piece>, Nat, z => 1n+Ses.kinds(z, c), Ses.before(K, c, v), Ses.before(List.append(&2, Tk.Piece, K, Y), c, v), psn.bs_t(K, Y, c, v)(h))

# a value new to the history, next: one more than its kinds
def psn.number_new(+K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, +h: {Ses.has(K, c, v) == False{} : Bool}) -> {1n+Ses.kinds(K, c) == Ses.number(List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> Y), c, v) : Nat}:
  %psn.bs_f(K, Tk.Value{c, v} <> Y, c, v, h) : {1n+Ses.kinds(K, c) == 1n+Ses.kinds(_, c) : Nat}
  %Equal.sym(Bool, Sm.same_class(c, c), True{}, psn.scr(c)) : {1n+Ses.kinds(K, c) == 1n+Ses.kinds(List.append(&2, Tk.Piece, K, Ses.before.at(Bool.and(_, String.eq(v, v)), c, v, Ses.before(Y, c, v))), c) : Nat}
  %Equal.sym(Bool, String.eq(v, v), True{}, psn.str_refl(v)) : {1n+Ses.kinds(K, c) == 1n+Ses.kinds(List.append(&2, Tk.Piece, K, Ses.before.at(_, c, v, Ses.before(Y, c, v))), c) : Nat}
  %Equal.sym(List<&2, Tk.Piece>, List.append(&2, Tk.Piece, K, Nil{}), K, psn.app_nil(K)) : {1n+Ses.kinds(K, c) == 1n+Ses.kinds(_, c) : Nat}
  {==}

# Kinds
# -----

def psn.kat_add(b: Bool, -n: Nat) -> {Ses.kinds.at(b, n) == Nat.add(Tk.bit(b), n) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psn.kat_comm(p: Bool, q: Bool, -n: Nat) -> {Nat.add(Tk.bit(q), Ses.kinds.at(p, n)) == Ses.kinds.at(p, Nat.add(Tk.bit(q), n)) : Nat}:
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def psn.ks_plain(K: List<&2, Tk.Piece>, +s: String, +c: Tk.Class) -> {Ses.kinds(K, c) == Ses.kinds(List.append(&2, Tk.Piece, K, [Tk.Plain{s}]), c) : Nat}:
  match K:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Tk.Plain{t}:
          psn.ks_plain(rest, s, c)
        case Tk.Value{d, +u}:
          %psn.has_app_f(rest, [Tk.Plain{s}], c, u, {==}) : {Ses.kinds.at(Bool.and(Sm.same_class(c, d), Bool.not(Ses.has(rest, c, u))), Ses.kinds(rest, c)) == Ses.kinds.at(Bool.and(Sm.same_class(c, d), Bool.not(_)), Ses.kinds(List.append(&2, Tk.Piece, rest, [Tk.Plain{s}]), c)) : Nat}
          %psn.ks_plain(rest, s, c) : {Ses.kinds.at(Bool.and(Sm.same_class(c, d), Bool.not(Ses.has(rest, c, u))), Ses.kinds(rest, c)) == Ses.kinds.at(Bool.and(Sm.same_class(c, d), Bool.not(Ses.has(rest, c, u))), _) : Nat}
          {==}

def psn.ks0(K: List<&2, Tk.Piece>, +d: Tk.Class, +w: String, +c: Tk.Class, +es: {Sm.same_class(c, d) == False{} : Bool}) -> {Ses.kinds(K, c) == Ses.kinds(List.append(&2, Tk.Piece, K, [Tk.Value{d, w}]), c) : Nat}:
  match K:
    case Nil{}:
      %Equal.sym(Bool, Sm.same_class(c, d), False{}, es) : {0n == Ses.kinds.at(Bool.and(_, True{}), 0n) : Nat}
      {==}
    case x <> +rest:
      match x:
        case Tk.Plain{t}:
          psn.ks0(rest, d, w, c, es)
        case Tk.Value{e, +u}:
          %psn.has_app_f(rest, [Tk.Value{d, w}], c, u, psn.hy0(c, d, u, w, es)) : {Ses.kinds.at(Bool.and(Sm.same_class(c, e), Bool.not(Ses.has(rest, c, u))), Ses.kinds(rest, c)) == Ses.kinds.at(Bool.and(Sm.same_class(c, e), Bool.not(_)), Ses.kinds(List.append(&2, Tk.Piece, rest, [Tk.Value{d, w}]), c)) : Nat}
          %psn.ks0(rest, d, w, c, es) : {Ses.kinds.at(Bool.and(Sm.same_class(c, e), Bool.not(Ses.has(rest, c, u))), Ses.kinds(rest, c)) == Ses.kinds.at(Bool.and(Sm.same_class(c, e), Bool.not(Ses.has(rest, c, u))), _) : Nat}
          {==}

def psn.ks1_q(q: Bool, +rest: List<&2, Tk.Piece>, +c: Tk.Class, +u: String, +w: String, +eq: {String.eq(u, w) == q : Bool}) -> {Nat.add(Tk.bit(Bool.not(Bool.or(String.eq(w, u), Ses.has(rest, c, w)))), Ses.kinds.at(Bool.not(Ses.has(rest, c, u)), Ses.kinds(rest, c))) == Ses.kinds.at(Bool.not(Ses.has(List.append(&2, Tk.Piece, rest, [Tk.Value{c, w}]), c, u)), Nat.add(Tk.bit(Bool.not(Ses.has(rest, c, w))), Ses.kinds(rest, c))) : Nat}:
  match q:
    case True{}:
      %LMp.pmp.str_eq(u, w, eq) : {Nat.add(Tk.bit(Bool.not(Bool.or(String.eq(_, u), Ses.has(rest, c, _)))), Ses.kinds.at(Bool.not(Ses.has(rest, c, u)), Ses.kinds(rest, c))) == Ses.kinds.at(Bool.not(Ses.has(List.append(&2, Tk.Piece, rest, [Tk.Value{c, _}]), c, u)), Nat.add(Tk.bit(Bool.not(Ses.has(rest, c, _))), Ses.kinds(rest, c))) : Nat}
      %Equal.sym(Bool, String.eq(u, u), True{}, psn.str_refl(u)) : {Nat.add(Tk.bit(Bool.not(Bool.or(_, Ses.has(rest, c, u)))), Ses.kinds.at(Bool.not(Ses.has(rest, c, u)), Ses.kinds(rest, c))) == Ses.kinds.at(Bool.not(Ses.has(List.append(&2, Tk.Piece, rest, [Tk.Value{c, u}]), c, u)), Nat.add(Tk.bit(Bool.not(Ses.has(rest, c, u))), Ses.kinds(rest, c))) : Nat}
      %Equal.sym(Bool, Ses.has(List.append(&2, Tk.Piece, rest, [Tk.Value{c, u}]), c, u), True{}, psn.has_snoc_self(rest, c, u)) : {Ses.kinds.at(Bool.not(Ses.has(rest, c, u)), Ses.kinds(rest, c)) == Ses.kinds.at(Bool.not(_), Nat.add(Tk.bit(Bool.not(Ses.has(rest, c, u))), Ses.kinds(rest, c))) : Nat}
      psn.kat_add(Bool.not(Ses.has(rest, c, u)), Ses.kinds(rest, c))
    case False{}:
      %psn.has_app_f(rest, [Tk.Value{c, w}], c, u, psn.hy1(c, c, u, w, eq)) : {Nat.add(Tk.bit(Bool.not(Bool.or(String.eq(w, u), Ses.has(rest, c, w)))), Ses.kinds.at(Bool.not(Ses.has(rest, c, u)), Ses.kinds(rest, c))) == Ses.kinds.at(Bool.not(_), Nat.add(Tk.bit(Bool.not(Ses.has(rest, c, w))), Ses.kinds(rest, c))) : Nat}
      %Equal.sym(Bool, String.eq(w, u), False{}, psn.eq_comm_f(u, w, eq)) : {Nat.add(Tk.bit(Bool.not(Bool.or(_, Ses.has(rest, c, w)))), Ses.kinds.at(Bool.not(Ses.has(rest, c, u)), Ses.kinds(rest, c))) == Ses.kinds.at(Bool.not(Ses.has(rest, c, u)), Nat.add(Tk.bit(Bool.not(Ses.has(rest, c, w))), Ses.kinds(rest, c))) : Nat}
      psn.kat_comm(Bool.not(Ses.has(rest, c, u)), Bool.not(Ses.has(rest, c, w)), Ses.kinds(rest, c))

def psn.ks1_v(a: Bool, +rest: List<&2, Tk.Piece>, +c: Tk.Class, +u: String, +w: String) -> {Nat.add(Tk.bit(Bool.not(Bool.or(Bool.and(a, String.eq(w, u)), Ses.has(rest, c, w)))), Ses.kinds.at(Bool.and(a, Bool.not(Ses.has(rest, c, u))), Ses.kinds(rest, c))) == Ses.kinds.at(Bool.and(a, Bool.not(Ses.has(List.append(&2, Tk.Piece, rest, [Tk.Value{c, w}]), c, u))), Nat.add(Tk.bit(Bool.not(Ses.has(rest, c, w))), Ses.kinds(rest, c))) : Nat}:
  match a:
    case True{}:
      psn.ks1_q(String.eq(u, w), rest, c, u, w, {==})
    case False{}:
      {==}

# a value of class c next: one more kind when the history lacks it
def psn.ks1(K: List<&2, Tk.Piece>, +c: Tk.Class, +w: String) -> {Nat.add(Tk.bit(Bool.not(Ses.has(K, c, w))), Ses.kinds(K, c)) == Ses.kinds(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c) : Nat}:
  match K:
    case Nil{}:
      %Equal.sym(Bool, Sm.same_class(c, c), True{}, psn.scr(c)) : {1n == Ses.kinds.at(Bool.and(_, True{}), 0n) : Nat}
      {==}
    case x <> +rest:
      match x:
        case Tk.Plain{s}:
          psn.ks1(rest, c, w)
        case Tk.Value{+e, +u}:
          %psn.ks1(rest, c, w) : {Nat.add(Tk.bit(Bool.not(Bool.or(Bool.and(Sm.same_class(c, e), String.eq(w, u)), Ses.has(rest, c, w)))), Ses.kinds.at(Bool.and(Sm.same_class(c, e), Bool.not(Ses.has(rest, c, u))), Ses.kinds(rest, c))) == Ses.kinds.at(Bool.and(Sm.same_class(c, e), Bool.not(Ses.has(List.append(&2, Tk.Piece, rest, [Tk.Value{c, w}]), c, u))), _) : Nat}
          psn.ks1_v(Sm.same_class(c, e), rest, c, u, w)

# What a class holds
# ------------------

# the place a history gives v of class c: its number when it holds v
def psn.want(hit: Bool, K: List<&2, Tk.Piece>, c: Tk.Class, v: String) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{Ses.number(K, c, v)}
    case False{}:
      None{}

def psn.want_at(h: Bool, +K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, eh: {Ses.has(K, c, v) == h : Bool}) -> {psn.want(h, K, c, v) == psn.want(h, List.append(&2, Tk.Piece, K, Y), c, v) : Maybe<&2, Nat>}:
  match h:
    case True{}:
      Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, Ses.number(K, c, v), Ses.number(List.append(&2, Tk.Piece, K, Y), c, v), psn.number_old(K, Y, c, v, eh))
    case False{}:
      {==}

# pieces with no v of class c leave its place
def psn.want_keep(+K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, hy: {Ses.has(Y, c, v) == False{} : Bool}) -> {psn.want(Ses.has(K, c, v), K, c, v) == psn.want(Ses.has(List.append(&2, Tk.Piece, K, Y), c, v), List.append(&2, Tk.Piece, K, Y), c, v) : Maybe<&2, Nat>}:
  %psn.has_app_f(K, Y, c, v, hy) : {psn.want(Ses.has(K, c, v), K, c, v) == psn.want(_, List.append(&2, Tk.Piece, K, Y), c, v) : Maybe<&2, Nat>}
  psn.want_at(Ses.has(K, c, v), K, Y, c, v, {==})

# a value the history holds keeps its place
def psn.want_grow(+K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, +h: {Ses.has(K, c, v) == True{} : Bool}) -> {psn.want(Ses.has(K, c, v), K, c, v) == psn.want(Ses.has(List.append(&2, Tk.Piece, K, Y), c, v), List.append(&2, Tk.Piece, K, Y), c, v) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Ses.has(List.append(&2, Tk.Piece, K, Y), c, v), True{}, psn.has_app_t(K, Y, c, v)(h)) : {psn.want(Ses.has(K, c, v), K, c, v) == psn.want(_, List.append(&2, Tk.Piece, K, Y), c, v) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Ses.has(K, c, v), True{}, h) : {psn.want(_, K, c, v) == psn.want(True{}, List.append(&2, Tk.Piece, K, Y), c, v) : Maybe<&2, Nat>}
  psn.want_at(True{}, K, Y, c, v, h)

# A holds the values of class c of the history K: v at its place, and as
# many as K's kinds
def psn.TT(A: List<&2, String>, K: List<&2, Tk.Piece>, c: Tk.Class, v: String) -> Type:
  {psn.want(Ses.has(K, c, v), K, c, v) == Sm.place(A, v) : Maybe<&2, Nat>} & {List.length(&2, String, A) == Ses.kinds(K, c) : Nat}

def psn.vtw(-A: List<&2, String>, -K: List<&2, Tk.Piece>, -c: Tk.Class, -v: String, -w: String, vw: {v == w : String}, v1: {psn.want(Ses.has(K, c, v), K, c, v) == Sm.place(A, v) : Maybe<&2, Nat>}) -> {psn.want(Ses.has(K, c, w), K, c, w) == Sm.place(A, w) : Maybe<&2, Nat>}:
  %vw : {psn.want(Ses.has(K, c, _), K, c, _) == Sm.place(A, _) : Maybe<&2, Nat>}
  v1

def psn.len_old(-A: List<&2, String>, +K: List<&2, Tk.Piece>, +c: Tk.Class, +w: String, ehw: {Ses.has(K, c, w) == True{} : Bool}, l: {List.length(&2, String, A) == Ses.kinds(K, c) : Nat}) -> {List.length(&2, String, A) == Ses.kinds(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c) : Nat}:
  %psn.ks1(K, c, w) : {List.length(&2, String, A) == _ : Nat}
  %Equal.sym(Bool, Ses.has(K, c, w), True{}, ehw) : {List.length(&2, String, A) == Nat.add(Tk.bit(Bool.not(_)), Ses.kinds(K, c)) : Nat}
  l

def psn.len_new(+A: List<&2, String>, +K: List<&2, Tk.Piece>, +c: Tk.Class, +w: String, ehw: {Ses.has(K, c, w) == False{} : Bool}, l: {List.length(&2, String, A) == Ses.kinds(K, c) : Nat}) -> {List.length(&2, String, List.append(&2, String, A, [w])) == Ses.kinds(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c) : Nat}:
  %psn.ks1(K, c, w) : {List.length(&2, String, List.append(&2, String, A, [w])) == _ : Nat}
  %Equal.sym(Bool, Ses.has(K, c, w), False{}, ehw) : {List.length(&2, String, List.append(&2, String, A, [w])) == Nat.add(Tk.bit(Bool.not(_)), Ses.kinds(K, c)) : Nat}
  %Equal.sym(Nat, List.length(&2, String, List.append(&2, String, A, [w])), 1n+List.length(&2, String, A), LMp.pmp.len_snoc(A, w)) : {_ == 1n+Ses.kinds(K, c) : Nat}
  Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, A), Ses.kinds(K, c), l)

# v after a held value w of class c next: its place stays
def psn.c1_old(q: Bool, -A: List<&2, String>, +K: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, +w: String, +eq: {String.eq(v, w) == q : Bool}, ehw: {Ses.has(K, c, w) == True{} : Bool}, v1: {psn.want(Ses.has(K, c, v), K, c, v) == Sm.place(A, v) : Maybe<&2, Nat>}) -> {psn.want(Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v) == Sm.place(A, v) : Maybe<&2, Nat>}:
  match q:
    case True{}:
      %psn.want_grow(K, [Tk.Value{c, w}], c, v, Equal.trans(Bool, Ses.has(K, c, v), Ses.has(K, c, w), True{}, Equal.cong(String, Bool, z => Ses.has(K, c, z), v, w, LMp.pmp.str_eq(v, w, eq)), ehw)) : {_ == Sm.place(A, v) : Maybe<&2, Nat>}
      v1
    case False{}:
      %psn.want_keep(K, [Tk.Value{c, w}], c, v, psn.hy1(c, c, v, w, eq)) : {_ == Sm.place(A, v) : Maybe<&2, Nat>}
      v1

# v after a new value w of class c next: w takes the next place
def psn.c1_new(q: Bool, +A: List<&2, String>, +K: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, +w: String, +eq: {String.eq(v, w) == q : Bool}, +ehw: {Ses.has(K, c, w) == False{} : Bool}, v1: {psn.want(Ses.has(K, c, v), K, c, v) == Sm.place(A, v) : Maybe<&2, Nat>}, l: {List.length(&2, String, A) == Ses.kinds(K, c) : Nat}) -> {psn.want(Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v) == Sm.place(List.append(&2, String, A, [w]), v) : Maybe<&2, Nat>}:
  match q:
    case True{}:
      +vw = LMp.pmp.str_eq(v, w, eq)
      %Equal.sym(String, v, w, vw) : {psn.want(Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, _), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, _) == Sm.place(List.append(&2, String, A, [w]), _) : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, Sm.place(List.append(&2, String, A, [w]), w), LMp.pmp.psnoc(Sm.place(A, w), String.eq(w, w), List.length(&2, String, A)), LMp.pmp.place_snoc(A, w, w)) : {psn.want(Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w) == _ : Maybe<&2, Nat>}
      %Equal.sym(Bool, String.eq(w, w), True{}, psn.str_refl(w)) : {psn.want(Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w) == LMp.pmp.psnoc(Sm.place(A, w), _, List.length(&2, String, A)) : Maybe<&2, Nat>}
      %psn.vtw(A, K, c, v, w, vw, v1) : {psn.want(Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w) == LMp.pmp.psnoc(_, True{}, List.length(&2, String, A)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Ses.has(K, c, w), False{}, ehw) : {psn.want(Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w) == LMp.pmp.psnoc(psn.want(_, K, c, w), True{}, List.length(&2, String, A)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w), True{}, psn.has_snoc_self(K, c, w)) : {psn.want(_, List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, w) == Some{1n+List.length(&2, String, A)} : Maybe<&2, Nat>}
      %psn.number_new(K, Nil{}, c, w, ehw) : {Some{_} == Some{1n+List.length(&2, String, A)} : Maybe<&2, Nat>}
      %l : {Some{1n+_} == Some{1n+List.length(&2, String, A)} : Maybe<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Nat>, Sm.place(List.append(&2, String, A, [w]), v), LMp.pmp.psnoc(Sm.place(A, v), String.eq(v, w), List.length(&2, String, A)), LMp.pmp.place_snoc(A, w, v)) : {psn.want(Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v) == _ : Maybe<&2, Nat>}
      %Equal.sym(Bool, String.eq(v, w), False{}, eq) : {psn.want(Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v) == LMp.pmp.psnoc(Sm.place(A, v), _, List.length(&2, String, A)) : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, LMp.pmp.psnoc(Sm.place(A, v), False{}, List.length(&2, String, A)), Sm.place(A, v), LMp.pmp.psnoc_f(Sm.place(A, v), List.length(&2, String, A))) : {psn.want(Ses.has(List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v) == _ : Maybe<&2, Nat>}
      %psn.want_keep(K, [Tk.Value{c, w}], c, v, psn.hy1(c, c, v, w, eq)) : {_ == Sm.place(A, v) : Maybe<&2, Nat>}
      v1

# a value w of class c next
def psn.t_same(hw: Bool, +A: List<&2, String>, +K: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, +w: String, +ehw: {Ses.has(K, c, w) == hw : Bool}, ihv: psn.TT(A, K, c, v), ihw: psn.TT(A, K, c, w)) -> psn.TT(Sm.held.add(Sm.fresh(Sm.place(A, w)), A, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v):
  match hw:
    case True{}:
      (v1, v2) = ihv
      (w1, w2) = ihw
      %w1 : psn.TT(Sm.held.add(Sm.fresh(_), A, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v)
      %Equal.sym(Bool, Ses.has(K, c, w), True{}, ehw) : psn.TT(Sm.held.add(Sm.fresh(psn.want(_, K, c, w)), A, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v)
      (psn.c1_old(String.eq(v, w), A, K, c, v, w, {==}, ehw, v1), psn.len_old(A, K, c, w, ehw, v2))
    case False{}:
      (v1, v2) = ihv
      (w1, w2) = ihw
      +l = v2
      %w1 : psn.TT(Sm.held.add(Sm.fresh(_), A, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v)
      %Equal.sym(Bool, Ses.has(K, c, w), False{}, ehw) : psn.TT(Sm.held.add(Sm.fresh(psn.want(_, K, c, w)), A, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v)
      (psn.c1_new(String.eq(v, w), A, K, c, v, w, {==}, ehw, v1, l), psn.len_new(A, K, c, w, ehw, l))

# a value of class d next
def psn.t_val(sc: Bool, +A: List<&2, String>, +K: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, +d: Tk.Class, +w: String, +rc: {S.reversible(c) == True{} : Bool}, +es: {Sm.same_class(c, d) == sc : Bool}, ihv: psn.TT(A, K, c, v), ihw: psn.TT(A, K, c, w)) -> psn.TT(psn.step(A, Tk.Value{d, w}, c), List.append(&2, Tk.Piece, K, [Tk.Value{d, w}]), c, v):
  match sc:
    case True{}:
      %LMp.pmp.class_eq(c, d, es) : psn.TT(psn.step(A, Tk.Value{_, w}, c), List.append(&2, Tk.Piece, K, [Tk.Value{_, w}]), c, v)
      %Equal.sym(Bool, Sm.same_class(c, c), True{}, psn.scr(c)) : psn.TT(Sm.held.add(Bool.and(_, Bool.and(S.reversible(c), Sm.fresh(Sm.place(A, w)))), A, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v)
      %Equal.sym(Bool, S.reversible(c), True{}, rc) : psn.TT(Sm.held.add(Bool.and(True{}, Bool.and(_, Sm.fresh(Sm.place(A, w)))), A, w), List.append(&2, Tk.Piece, K, [Tk.Value{c, w}]), c, v)
      psn.t_same(Ses.has(K, c, w), A, K, c, v, w, {==}, ihv, ihw)
    case False{}:
      %Equal.sym(Bool, Sm.same_class(c, d), False{}, es) : psn.TT(Sm.held.add(Bool.and(_, Bool.and(S.reversible(d), Sm.fresh(Sm.place(A, w)))), A, w), List.append(&2, Tk.Piece, K, [Tk.Value{d, w}]), c, v)
      %psn.want_keep(K, [Tk.Value{d, w}], c, v, psn.hy0(c, d, v, w, es)) : {_ == Sm.place(A, v) : Maybe<&2, Nat>} & {List.length(&2, String, A) == Ses.kinds(List.append(&2, Tk.Piece, K, [Tk.Value{d, w}]), c) : Nat}
      %psn.ks0(K, d, w, c, es) : {psn.want(Ses.has(K, c, v), K, c, v) == Sm.place(A, v) : Maybe<&2, Nat>} & {List.length(&2, String, A) == _ : Nat}
      ihv

# a plain piece next
def psn.t_plain(A: List<&2, String>, +K: List<&2, Tk.Piece>, +s: String, +c: Tk.Class, +v: String, ih: psn.TT(A, K, c, v)) -> psn.TT(A, List.append(&2, Tk.Piece, K, [Tk.Plain{s}]), c, v):
  %psn.want_keep(K, [Tk.Plain{s}], c, v, {==}) : {_ == Sm.place(A, v) : Maybe<&2, Nat>} & {List.length(&2, String, A) == Ses.kinds(List.append(&2, Tk.Piece, K, [Tk.Plain{s}]), c) : Nat}
  %psn.ks_plain(K, s, c) : {psn.want(Ses.has(K, c, v), K, c, v) == Sm.place(A, v) : Maybe<&2, Nat>} & {List.length(&2, String, A) == _ : Nat}
  ih

# induction on the history read last first: each piece one scrub step
def psn.tr(rk: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, +rc: {S.reversible(c) == True{} : Bool}) -> psn.TT(psn.hb(psn.rv(rk), c), psn.rv(rk), c, v):
  match rk:
    case Nil{}:
      ({==}, {==})
    case x <> +r:
      match x:
        case Tk.Plain{+s}:
          %Equal.sym(List<&2, String>, psn.hb(List.append(&2, Tk.Piece, psn.rv(r), [Tk.Plain{s}]), c), psn.hb(psn.rv(r), c), psn.hstep(psn.rv(r), Tk.Plain{s}, c)) : psn.TT(_, List.append(&2, Tk.Piece, psn.rv(r), [Tk.Plain{s}]), c, v)
          psn.t_plain(psn.hb(psn.rv(r), c), psn.rv(r), s, c, v, psn.tr(r, c, v, rc))
        case Tk.Value{+d, +w}:
          %Equal.sym(List<&2, String>, psn.hb(List.append(&2, Tk.Piece, psn.rv(r), [Tk.Value{d, w}]), c), psn.step(psn.hb(psn.rv(r), c), Tk.Value{d, w}, c), psn.hstep(psn.rv(r), Tk.Value{d, w}, c)) : psn.TT(_, List.append(&2, Tk.Piece, psn.rv(r), [Tk.Value{d, w}]), c, v)
          psn.t_val(Sm.same_class(c, d), psn.hb(psn.rv(r), c), psn.rv(r), c, v, d, w, rc, {==}, psn.tr(r, c, v, rc), psn.tr(r, c, w, rc))

# for every history K and class c that maps back, what c holds in the map
# of K: each value at its number when K holds it, else absent, and as many
# as K's kinds of c
def psn.tk(+K: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, +rc: {S.reversible(c) == True{} : Bool}) -> psn.TT(psn.hb(K, c), K, c, v):
  %psn.rv_rv(K) : psn.TT(psn.hb(_, c), _, c, v)
  psn.tr(psn.rv(K), c, v, rc)

# Restores
# --------

def psn.fa(q: Bool, m: Maybe<&2, Nat>, h: {Sm.fresh(m) == False{} : Bool}) -> {Sm.fresh(Sm.place.at(q, m)) == False{} : Bool}:
  match q:
    case True{}:
      {==}
    case False{}:
      match m:
        case None{}:
          h
        case Some{i}:
          {==}

# a value at some place of xs has a place there
def psn.at_held(xs: List<&2, String>, i: Nat, +v: String, h: {Sm.at(xs, i) == Some{v} : Maybe<&2, String>}) -> {Sm.fresh(Sm.place(xs, v)) == False{} : Bool}:
  match xs:
    case Nil{}:
      psn.none_some(v, {True{} == False{} : Bool}, h)
    case +x <> +rest:
      match i:
        case 0n:
          psn.none_some(v, {Sm.fresh(Sm.place(x <> rest, v)) == False{} : Bool}, h)
        case 1n+j:
          match j:
            case 0n:
              %Equal.sym(String, x, v, psn.some_inj(x, v, h)) : {Sm.fresh(Sm.place.at(String.eq(v, _), Sm.place(rest, v))) == False{} : Bool}
              %Equal.sym(Bool, String.eq(v, v), True{}, psn.str_refl(v)) : {Sm.fresh(Sm.place.at(_, Sm.place(rest, v))) == False{} : Bool}
              {==}
            case 1n+k:
              psn.fa(String.eq(v, x), Sm.place(rest, v), psn.at_held(rest, 1n+k, v, h))

def psn.r1_of(r: Bool, b: Tk.Book, +c: Tk.Class, +i: Nat, +v: String, ef: {Sm.restore1.of(r, b, c, i) == Some{v} : Maybe<&2, String>}) -> {r == True{} : Bool} & {Sm.fresh(Sm.place(Sm.held(Tk.Book.es(b), c), v)) == False{} : Bool}:
  match r:
    case True{}:
      match b:
        case Tk.Book{es}:
          ({==}, psn.at_held(Sm.held(es, c), i, v, ef))
    case False{}:
      psn.none_some(v, {False{} == True{} : Bool} & {Sm.fresh(Sm.place(Sm.held(Tk.Book.es(b), c), v)) == False{} : Bool}, ef)

# a token the map restores is of a class that maps back, and its value has
# a place in its class
def psn.r1(b: Tk.Book, +c: Tk.Class, +i: Nat, +v: String, ef: {Sm.restore1(b, c, i) == Some{v} : Maybe<&2, String>}) -> {S.reversible(c) == True{} : Bool} & {Sm.fresh(Sm.place(Sm.held(Tk.Book.es(b), c), v)) == False{} : Bool}:
  psn.r1_of(S.reversible(c), b, c, i, v, ef)

def psn.fresh_hb(+H: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, eh: {Ses.has(H, c, v) == False{} : Bool}, t: psn.TT(psn.hb(H, c), H, c, v)) -> {Sm.fresh(Sm.place(psn.hb(H, c), v)) == True{} : Bool}:
  (t1, t2) = t
  %t1 : {Sm.fresh(_) == True{} : Bool}
  %Equal.sym(Bool, Ses.has(H, c, v), False{}, eh) : {Sm.fresh(psn.want(_, H, c, v)) == True{} : Bool}
  {==}

def psn.has_of_at(h: Bool, +H: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, eh: {Ses.has(H, c, v) == h : Bool}, rc: {S.reversible(c) == True{} : Bool}, hf: {Sm.fresh(Sm.place(psn.hb(H, c), v)) == False{} : Bool}) -> {h == True{} : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, False{}, Sm.fresh(Sm.place(psn.hb(H, c), v)), True{}, Equal.sym(Bool, Sm.fresh(Sm.place(psn.hb(H, c), v)), False{}, hf), psn.fresh_hb(H, c, v, eh, psn.tk(H, c, v, rc)))

# a value of a class that maps back with a place in the map of H: H holds it
def psn.has_of(+H: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, rc: {S.reversible(c) == True{} : Bool}, hf: {Sm.fresh(Sm.place(psn.hb(H, c), v)) == False{} : Bool}) -> {Ses.has(H, c, v) == True{} : Bool}:
  psn.has_of_at(Ses.has(H, c, v), H, c, v, {==}, rc, hf)

def psn.ptok_s(+H: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, p: {S.reversible(c) == True{} : Bool} & {Sm.fresh(Sm.place(Sm.held(Tk.Book.es(psn.B(H)), c), v)) == False{} : Bool}) -> {Bool.and(Bool.and(Sm.same_class(c, c), S.reversible(c)), Ses.has(H, c, v)) == True{} : Bool}:
  (rc0, hf) = p
  +rc = rc0
  %Equal.sym(Bool, Sm.same_class(c, c), True{}, psn.scr(c)) : {Bool.and(Bool.and(_, S.reversible(c)), Ses.has(H, c, v)) == True{} : Bool}
  %Equal.sym(Bool, S.reversible(c), True{}, rc) : {Bool.and(Bool.and(True{}, _), Ses.has(H, c, v)) == True{} : Bool}
  psn.has_of(H, c, v, rc, hf)

def psn.ptok(f: Maybe<&2, String>, +H: List<&2, Tk.Piece>, +c: Tk.Class, +i: Nat, ef: {Sm.restore1(psn.B(H), c, i) == f : Maybe<&2, String>}) -> {Bool.or(Ses.same_seg(Tk.Tok{c, i}, Sm.restore_seg.tok(c, i, f)), Ses.brought(H, Tk.Tok{c, i}, Sm.restore_seg.tok(c, i, f))) == True{} : Bool}:
  match f:
    case None{}:
      %Equal.sym(Bool, Sm.same_class(c, c), True{}, psn.scr(c)) : {Bool.or(Bool.and(_, Nat.is_eq(i, i)), False{}) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(i, i), True{}, psn.nrefl(i)) : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case Some{+v}:
      psn.ptok_s(H, c, v, psn.r1(psn.B(H), c, i, v, ef))

# a piece of an answer restored against the map of H: kept, or a token
# brought into clear as a value of its class H holds
def psn.piece(+H: List<&2, Tk.Piece>, y: Tk.Seg) -> {Bool.or(Ses.same_seg(y, Sm.restore_seg(psn.B(H), y)), Ses.brought(H, y, Sm.restore_seg(psn.B(H), y))) == True{} : Bool}:
  match y:
    case Tk.Txt{+s}:
      %Equal.sym(Bool, String.eq(s, s), True{}, psn.str_refl(s)) : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case Tk.Clear{+c, +v}:
      %Equal.sym(Bool, Sm.same_class(c, c), True{}, psn.scr(c)) : {Bool.or(Bool.and(_, String.eq(v, v)), False{}) == True{} : Bool}
      %Equal.sym(Bool, String.eq(v, v), True{}, psn.str_refl(v)) : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case Tk.Tok{+c, +i}:
      psn.ptok(Sm.restore1(psn.B(H), c, i), H, c, i, {==})
    case Tk.Hash{+c, +v}:
      %Equal.sym(Bool, Sm.same_class(c, c), True{}, psn.scr(c)) : {Bool.or(Bool.and(_, String.eq(v, v)), False{}) == True{} : Bool}
      %Equal.sym(Bool, String.eq(v, v), True{}, psn.str_refl(v)) : {Bool.or(_, False{}) == True{} : Bool}
      {==}

# an answer restored against the map of H: every piece kept or brought
# into clear as a value H holds
def psn.came(+H: List<&2, Tk.Piece>, ys: List<&2, Tk.Seg>) -> {Ses.all_came(H, ys, Sm.restore_text(ys, psn.B(H))) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> rest:
      %Equal.sym(Bool, Bool.or(Ses.same_seg(y, Sm.restore_seg(psn.B(H), y)), Ses.brought(H, y, Sm.restore_seg(psn.B(H), y))), True{}, psn.piece(H, y)) : {Bool.and(_, Ses.all_came(H, rest, Sm.restore_text(rest, psn.B(H)))) == True{} : Bool}
      psn.came(H, rest)

# Numbers
# -------

def psn.ts_push(-t: Tk.Tok, r: Tk.Toks) -> {t <> Tk.Toks.ts(r) == Tk.Toks.ts(Sm.push(t, r)) : List<&2, Tk.Tok>}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

def psn.out_ys(-xs: List<&2, Tk.Piece>, r: Tk.Toks) -> {Sm.fill(xs, Tk.Toks.ts(r)) == Tk.Out.ys(Sm.text(xs, r)) : List<&2, Tk.Seg>}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

def psn.head_h(h: Bool, +es: List<&2, Tk.Ent>, +K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, eh: {Ses.has(K, c, v) == h : Bool}, hl: {List.length(&2, String, Sm.held(es, c)) == Ses.kinds(K, c) : Nat}) -> {Sm.seg(c, v, Sm.step_tok(Sm.scrub1.place(psn.want(h, K, c, v), es, c, v))) == Tk.Tok{c, Ses.number(List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> Y), c, v)} : Tk.Seg}:
  match h:
    case True{}:
      %psn.number_old(K, Tk.Value{c, v} <> Y, c, v, eh) : {Tk.Tok{c, Ses.number(K, c, v)} == Tk.Tok{c, _} : Tk.Seg}
      {==}
    case False{}:
      %psn.number_new(K, Y, c, v, eh) : {Tk.Tok{c, 1n+List.length(&2, String, Sm.held(es, c))} == Tk.Tok{c, _} : Tk.Seg}
      %hl : {Tk.Tok{c, 1n+List.length(&2, String, Sm.held(es, c))} == Tk.Tok{c, 1n+_} : Tk.Seg}
      {==}

def psn.head_t(b: Tk.Book, +K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, t: psn.TT(Sm.held(Tk.Book.es(b), c), K, c, v)) -> {Sm.seg(c, v, Sm.step_tok(Sm.scrub1.of(True{}, b, c, v))) == Tk.Tok{c, Ses.number(List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> Y), c, v)} : Tk.Seg}:
  match b:
    case Tk.Book{+es}:
      (t1, t2) = t
      %t1 : {Sm.seg(c, v, Sm.step_tok(Sm.scrub1.place(_, es, c, v))) == Tk.Tok{c, Ses.number(List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> Y), c, v)} : Tk.Seg}
      psn.head_h(Ses.has(K, c, v), es, K, Y, c, v, {==}, t2)

def psn.head_of(r: Bool, +K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String, er: {S.reversible(c) == r : Bool}) -> {Sm.seg(c, v, Sm.step_tok(Sm.scrub1.of(r, psn.B(K), c, v))) == Ses.numbered.of(r, List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> Y), c, v) : Tk.Seg}:
  match r:
    case True{}:
      psn.head_t(psn.B(K), K, Y, c, v, psn.tk(K, c, v, er))
    case False{}:
      {==}

# a value next after the history K: the token its number in K and the text
def psn.head(+K: List<&2, Tk.Piece>, +Y: List<&2, Tk.Piece>, +c: Tk.Class, +v: String) -> {Sm.seg(c, v, Sm.step_tok(Sm.scrub1(psn.B(K), c, v))) == Ses.numbered.of(S.reversible(c), List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> Y), c, v) : Tk.Seg}:
  psn.head_of(S.reversible(c), K, Y, c, v, {==})

# the text xs scrubbed from the map of the history K: numbered in K and xs
def psn.num(xs: List<&2, Tk.Piece>, +K: List<&2, Tk.Piece>) -> {Sm.fill(xs, Tk.Toks.ts(Sm.scrub_vals(Sm.vals(xs), psn.B(K)))) == Ses.numbered(List.append(&2, Tk.Piece, K, xs), xs) : List<&2, Tk.Seg>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Tk.Plain{+s}:
          %psn.app_assoc(K, [Tk.Plain{s}], rest) : {Tk.Txt{s} <> Sm.fill(rest, Tk.Toks.ts(Sm.scrub_vals(Sm.vals(rest), psn.B(K)))) == Tk.Txt{s} <> Ses.numbered(_, rest) : List<&2, Tk.Seg>}
          %psn.bsnoc(K, Tk.Plain{s}) : {Tk.Txt{s} <> Sm.fill(rest, Tk.Toks.ts(Sm.scrub_vals(Sm.vals(rest), _))) == Tk.Txt{s} <> Ses.numbered(List.append(&2, Tk.Piece, List.append(&2, Tk.Piece, K, [Tk.Plain{s}]), rest), rest) : List<&2, Tk.Seg>}
          %psn.num(rest, List.append(&2, Tk.Piece, K, [Tk.Plain{s}])) : {Tk.Txt{s} <> Sm.fill(rest, Tk.Toks.ts(Sm.scrub_vals(Sm.vals(rest), psn.B(List.append(&2, Tk.Piece, K, [Tk.Plain{s}]))))) == Tk.Txt{s} <> _ : List<&2, Tk.Seg>}
          {==}
        case Tk.Value{+c, +v}:
          %psn.ts_push(Sm.step_tok(Sm.scrub1(psn.B(K), c, v)), Sm.scrub_vals(Sm.vals(rest), Sm.step_book(Sm.scrub1(psn.B(K), c, v)))) : {Sm.fill(Tk.Value{c, v} <> rest, _) == Ses.numbered.of(S.reversible(c), List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> rest), c, v) <> Ses.numbered(List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> rest), rest) : List<&2, Tk.Seg>}
          %psn.app_assoc(K, [Tk.Value{c, v}], rest) : {Sm.seg(c, v, Sm.step_tok(Sm.scrub1(psn.B(K), c, v))) <> Sm.fill(rest, Tk.Toks.ts(Sm.scrub_vals(Sm.vals(rest), Sm.step_book(Sm.scrub1(psn.B(K), c, v))))) == Ses.numbered.of(S.reversible(c), List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> rest), c, v) <> Ses.numbered(_, rest) : List<&2, Tk.Seg>}
          %psn.bsnoc(K, Tk.Value{c, v}) : {Sm.seg(c, v, Sm.step_tok(Sm.scrub1(psn.B(K), c, v))) <> Sm.fill(rest, Tk.Toks.ts(Sm.scrub_vals(Sm.vals(rest), _))) == Ses.numbered.of(S.reversible(c), List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> rest), c, v) <> Ses.numbered(List.append(&2, Tk.Piece, List.append(&2, Tk.Piece, K, [Tk.Value{c, v}]), rest), rest) : List<&2, Tk.Seg>}
          %psn.num(rest, List.append(&2, Tk.Piece, K, [Tk.Value{c, v}])) : {Sm.seg(c, v, Sm.step_tok(Sm.scrub1(psn.B(K), c, v))) <> Sm.fill(rest, Tk.Toks.ts(Sm.scrub_vals(Sm.vals(rest), psn.B(List.append(&2, Tk.Piece, K, [Tk.Value{c, v}]))))) == Ses.numbered.of(S.reversible(c), List.append(&2, Tk.Piece, K, Tk.Value{c, v} <> rest), c, v) <> _ : List<&2, Tk.Seg>}
          %psn.head(K, rest, c, v) : {Sm.seg(c, v, Sm.step_tok(Sm.scrub1(psn.B(K), c, v))) <> Sm.fill(rest, Tk.Toks.ts(Sm.scrub_vals(Sm.vals(rest), psn.B(List.append(&2, Tk.Piece, K, [Tk.Value{c, v}]))))) == _ <> Sm.fill(rest, Tk.Toks.ts(Sm.scrub_vals(Sm.vals(rest), psn.B(List.append(&2, Tk.Piece, K, [Tk.Value{c, v}]))))) : List<&2, Tk.Seg>}
          {==}
