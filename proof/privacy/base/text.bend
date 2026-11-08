# eukhe: lemmas shared by the proofs of area privacy, section token: the
# values of one text scrubbed in one step (the map after them keeps every
# index, scrubbing them again changes nothing), and a text scrubbed and
# restored piece by piece

import Base
import ../../../bend/privacy/token.bend as Tk
import ../../../spec/harness/privacy.bend as S
import ./token.bend as LTk
import ./scrub.bend as LSc

# Steps
# -----

def ptx.vals_m(-t: Tk.Tok, r: Tk.Toks) -> {Tk.Toks.m(Tk.scrub_vals.cons(t, r)) == Tk.Toks.m(r) : Tk.Book}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

def ptx.vals_ts(-t: Tk.Tok, r: Tk.Toks) -> {Tk.Toks.ts(Tk.scrub_vals.cons(t, r)) == t <> Tk.Toks.ts(r) : List<&2, Tk.Tok>}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

def ptx.vals_eta(r: Tk.Toks) -> {r == Tk.Toks{Tk.Toks.m(r), Tk.Toks.ts(r)} : Tk.Toks}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

def ptx.out_m(-xs: List<&2, Tk.Piece>, r: Tk.Toks) -> {Tk.Out.m(Tk.scrub.fill(xs, r)) == Tk.Toks.m(r) : Tk.Book}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

def ptx.out_ys(-xs: List<&2, Tk.Piece>, r: Tk.Toks) -> {Tk.Out.ys(Tk.scrub.fill(xs, r)) == Tk.fill(xs, Tk.Toks.ts(r)) : List<&2, Tk.Seg>}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

def ptx.out_eta(r: Tk.Out) -> {r == Tk.Out{Tk.Out.m(r), Tk.Out.ys(r)} : Tk.Out}:
  match r:
    case Tk.Out{m, ys}:
      {==}

# the values of one text keep the value of every token the map holds
def ptx.keep(vs: List<&2, Tk.Val>, +m: Tk.Book, +k: Tk.Class, +i: Nat, +x: String, +h: {Tk.restore_tok(m, k, i) == Some{x} : Maybe<&2, String>}) -> {Tk.restore_tok(Tk.Toks.m(Tk.scrub_vals(vs, m)), k, i) == Some{x} : Maybe<&2, String>}:
  match vs:
    case Nil{}:
      h
    case y <> +rest:
      match y:
        case Tk.Val{+c, +v}:
          +r = Tk.scrub_val(m, c, v)
          +e = ptx.vals_m(Tk.Step.t(r), Tk.scrub_vals(rest, Tk.Step.m(r)))
          Equal.trans(Maybe<&2, String>, Tk.restore_tok(Tk.Toks.m(Tk.scrub_vals.cons(Tk.Step.t(r), Tk.scrub_vals(rest, Tk.Step.m(r)))), k, i), Tk.restore_tok(Tk.Toks.m(Tk.scrub_vals(rest, Tk.Step.m(r))), k, i), Some{x}, Equal.cong(Tk.Book, Maybe<&2, String>, z => Tk.restore_tok(z, k, i), Tk.Toks.m(Tk.scrub_vals.cons(Tk.Step.t(r), Tk.scrub_vals(rest, Tk.Step.m(r)))), Tk.Toks.m(Tk.scrub_vals(rest, Tk.Step.m(r))), e), ptx.keep(rest, Tk.Step.m(r), k, i, x, LSc.psc.keep1(m, c, v, k, i, x, h)))

# the values of one text keep the index of every value the map holds
def ptx.find(vs: List<&2, Tk.Val>, +m: Tk.Book, +k: Tk.Class, +x: String, +i: Nat, +h: {Tk.find(Tk.Book.es(m), k, x) == Some{i} : Maybe<&2, Nat>}) -> {Tk.find(Tk.Book.es(Tk.Toks.m(Tk.scrub_vals(vs, m))), k, x) == Some{i} : Maybe<&2, Nat>}:
  match vs:
    case Nil{}:
      h
    case y <> +rest:
      match y:
        case Tk.Val{+c, +v}:
          +r = Tk.scrub_val(m, c, v)
          +e = ptx.vals_m(Tk.Step.t(r), Tk.scrub_vals(rest, Tk.Step.m(r)))
          Equal.trans(Maybe<&2, Nat>, Tk.find(Tk.Book.es(Tk.Toks.m(Tk.scrub_vals.cons(Tk.Step.t(r), Tk.scrub_vals(rest, Tk.Step.m(r))))), k, x), Tk.find(Tk.Book.es(Tk.Toks.m(Tk.scrub_vals(rest, Tk.Step.m(r)))), k, x), Some{i}, Equal.cong(Tk.Book, Maybe<&2, Nat>, z => Tk.find(Tk.Book.es(z), k, x), Tk.Toks.m(Tk.scrub_vals.cons(Tk.Step.t(r), Tk.scrub_vals(rest, Tk.Step.m(r)))), Tk.Toks.m(Tk.scrub_vals(rest, Tk.Step.m(r))), e), ptx.find(rest, Tk.Step.m(r), k, x, i, LSc.psc.find1(m, c, v, k, x, i, h)))

def ptx.stable.s(s: Tk.Step, +c: Tk.Class, +v: String, +m: Tk.Book, +rest: List<&2, Tk.Val>,
  ok: LSc.psc.TokOk(c, v, m, s),
  ih: @m1: Tk.Book -> {Tk.scrub_vals(rest, Tk.Toks.m(Tk.scrub_vals(rest, m1))) == Tk.scrub_vals(rest, m1) : Tk.Toks}) ->
  {Tk.scrub_vals(Tk.Val{c, v} <> rest, Tk.Toks.m(Tk.scrub_vals(rest, Tk.Step.m(s)))) == Tk.scrub_vals.cons(Tk.Step.t(s), Tk.scrub_vals(rest, Tk.Step.m(s))) : Tk.Toks}:
  match s:
    case Tk.Step{+m1, t}:
      match t:
        case Tk.Mapped{+i}:
          (er, (eh, ef)) = ok
          +mm = Tk.Toks.m(Tk.scrub_vals(rest, m1))
          +held = LSc.psc.held(mm, c, v, i, er, ptx.find(rest, m1, c, v, i, ef))
          %Equal.sym(Tk.Step, Tk.scrub_val(mm, c, v), Tk.Step{mm, Tk.Mapped{i}}, held) : {Tk.scrub_vals.cons(Tk.Step.t(_), Tk.scrub_vals(rest, Tk.Step.m(_))) == Tk.scrub_vals.cons(Tk.Mapped{i}, Tk.scrub_vals(rest, m1)) : Tk.Toks}
          %ih(m1) : {Tk.scrub_vals.cons(Tk.Mapped{i}, Tk.scrub_vals(rest, mm)) == Tk.scrub_vals.cons(Tk.Mapped{i}, _) : Tk.Toks}
          {==}
        case Tk.OneWay{}:
          (er, em) = ok
          +mm = Tk.Toks.m(Tk.scrub_vals(rest, m1))
          +one = LSc.psc.oneway(mm, c, v, er)
          %Equal.sym(Tk.Step, Tk.scrub_val(mm, c, v), Tk.Step{mm, Tk.OneWay{}}, one) : {Tk.scrub_vals.cons(Tk.Step.t(_), Tk.scrub_vals(rest, Tk.Step.m(_))) == Tk.scrub_vals.cons(Tk.OneWay{}, Tk.scrub_vals(rest, m1)) : Tk.Toks}
          %ih(m1) : {Tk.scrub_vals.cons(Tk.OneWay{}, Tk.scrub_vals(rest, mm)) == Tk.scrub_vals.cons(Tk.OneWay{}, _) : Tk.Toks}
          {==}

# the values of one text scrubbed again, against the map after them,
# give the same tokens and the same map
def ptx.stable(vs: List<&2, Tk.Val>, +m: Tk.Book) -> {Tk.scrub_vals(vs, Tk.Toks.m(Tk.scrub_vals(vs, m))) == Tk.scrub_vals(vs, m) : Tk.Toks}:
  match vs:
    case Nil{}:
      {==}
    case y <> +rest:
      match y:
        case Tk.Val{+c, +v}:
          +r = Tk.scrub_val(m, c, v)
          +e = ptx.vals_m(Tk.Step.t(r), Tk.scrub_vals(rest, Tk.Step.m(r)))
          %Equal.sym(Tk.Book, Tk.Toks.m(Tk.scrub_vals.cons(Tk.Step.t(r), Tk.scrub_vals(rest, Tk.Step.m(r)))), Tk.Toks.m(Tk.scrub_vals(rest, Tk.Step.m(r))), e) : {Tk.scrub_vals(Tk.Val{c, v} <> rest, _) == Tk.scrub_vals.cons(Tk.Step.t(r), Tk.scrub_vals(rest, Tk.Step.m(r))) : Tk.Toks}
          ptx.stable.s(r, c, v, m, rest, LSc.psc.tok_ok(m, c, v), m1 => ptx.stable(rest, m1))

# Texts
# -----

def ptx.restore1.tok(+c: Tk.Class, +i: Nat, f: Maybe<&2, String>) -> Tk.Seg:
  match f:
    case None{}:
      Tk.Tok{c, i}
    case Some{v}:
      Tk.Clear{c, v}

# a piece restored
def ptx.restore1(+m: Tk.Book, y: Tk.Seg) -> Tk.Seg:
  match y:
    case Tk.Txt{s}:
      Tk.Txt{s}
    case Tk.Clear{c, v}:
      Tk.Clear{c, v}
    case Tk.Tok{+c, +i}:
      ptx.restore1.tok(c, i, Tk.restore_tok(m, c, i))
    case Tk.Hash{c, v}:
      Tk.Hash{c, v}

def ptx.rc_tok(f: Maybe<&2, String>, +c: Tk.Class, +i: Nat, -ys: List<&2, Tk.Seg>, -fs: List<&2, Maybe<&2, String>>) -> {Tk.back(Tk.Tok{c, i} <> ys, f <> fs) == ptx.restore1.tok(c, i, f) <> Tk.back(ys, fs) : List<&2, Tk.Seg>}:
  match f:
    case None{}:
      {==}
    case Some{v}:
      {==}

# a text restores piece by piece
def ptx.restore_cons(+m: Tk.Book, y: Tk.Seg, +ys: List<&2, Tk.Seg>) -> {Tk.restore(m, y <> ys) == ptx.restore1(m, y) <> Tk.restore(m, ys) : List<&2, Tk.Seg>}:
  match y:
    case Tk.Txt{s}:
      {==}
    case Tk.Clear{c, v}:
      {==}
    case Tk.Tok{+c, +i}:
      ptx.rc_tok(Tk.restore_tok(m, c, i), c, i, ys, Tk.restore_toks(Tk.refs(ys), m))
    case Tk.Hash{c, v}:
      {==}

# a text scrubbed from m, restored against the map after it
def ptx.RT(xs: List<&2, Tk.Piece>, m: Tk.Book) -> Type:
  {Tk.restore(Tk.Toks.m(Tk.scrub_vals(Tk.vals(xs), m)), Tk.fill(xs, Tk.Toks.ts(Tk.scrub_vals(Tk.vals(xs), m)))) == S.mask(xs) : List<&2, Tk.Seg>}

def ptx.rt.s(s: Tk.Step, +c: Tk.Class, +v: String, +m: Tk.Book, +xs: List<&2, Tk.Piece>,
  ok: LSc.psc.TokOk(c, v, m, s),
  ih: @m1: Tk.Book -> ptx.RT(xs, m1)) ->
  {Tk.restore(Tk.Toks.m(Tk.scrub_vals(Tk.vals(xs), Tk.Step.m(s))), Tk.fill(Tk.Value{c, v} <> xs, Tk.Step.t(s) <> Tk.Toks.ts(Tk.scrub_vals(Tk.vals(xs), Tk.Step.m(s))))) == S.mask(Tk.Value{c, v} <> xs) : List<&2, Tk.Seg>}:
  match s:
    case Tk.Step{+m1, t}:
      match t:
        case Tk.Mapped{+i}:
          (er, (eh, ef)) = ok
          +mm = Tk.Toks.m(Tk.scrub_vals(Tk.vals(xs), m1))
          +ts = Tk.Toks.ts(Tk.scrub_vals(Tk.vals(xs), m1))
          +kept = ptx.keep(Tk.vals(xs), m1, c, i, v, eh)
          %Equal.sym(List<&2, Tk.Seg>, Tk.restore(mm, Tk.Tok{c, i} <> Tk.fill(xs, ts)), ptx.restore1(mm, Tk.Tok{c, i}) <> Tk.restore(mm, Tk.fill(xs, ts)), ptx.restore_cons(mm, Tk.Tok{c, i}, Tk.fill(xs, ts))) : {_ == S.mask(Tk.Value{c, v} <> xs) : List<&2, Tk.Seg>}
          %Equal.sym(Maybe<&2, String>, Tk.restore_tok(mm, c, i), Some{v}, kept) : {ptx.restore1.tok(c, i, _) <> Tk.restore(mm, Tk.fill(xs, ts)) == S.mask(Tk.Value{c, v} <> xs) : List<&2, Tk.Seg>}
          %Equal.sym(List<&2, Tk.Seg>, Tk.restore(mm, Tk.fill(xs, ts)), S.mask(xs), ih(m1)) : {Tk.Clear{c, v} <> _ == S.mask(Tk.Value{c, v} <> xs) : List<&2, Tk.Seg>}
          %Equal.sym(Bool, S.reversible(c), True{}, LTk.ptk.srev(c, True{}, er)) : {Tk.Clear{c, v} <> S.mask(xs) == S.mask.of(_, c, v) <> S.mask(xs) : List<&2, Tk.Seg>}
          {==}
        case Tk.OneWay{}:
          (er, em) = ok
          +mm = Tk.Toks.m(Tk.scrub_vals(Tk.vals(xs), m1))
          +ts = Tk.Toks.ts(Tk.scrub_vals(Tk.vals(xs), m1))
          %Equal.sym(List<&2, Tk.Seg>, Tk.restore(mm, Tk.fill(xs, ts)), S.mask(xs), ih(m1)) : {Tk.Hash{c, v} <> _ == S.mask(Tk.Value{c, v} <> xs) : List<&2, Tk.Seg>}
          %Equal.sym(Bool, S.reversible(c), False{}, LTk.ptk.srev(c, False{}, er)) : {Tk.Hash{c, v} <> S.mask(xs) == S.mask.of(_, c, v) <> S.mask(xs) : List<&2, Tk.Seg>}
          {==}

def ptx.round_trip(xs: List<&2, Tk.Piece>, +m: Tk.Book) -> ptx.RT(xs, m):
  match xs:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Tk.Plain{+s}:
          %ptx.round_trip(rest, m) : {Tk.Txt{s} <> Tk.restore(Tk.Toks.m(Tk.scrub_vals(Tk.vals(rest), m)), Tk.fill(rest, Tk.Toks.ts(Tk.scrub_vals(Tk.vals(rest), m)))) == Tk.Txt{s} <> _ : List<&2, Tk.Seg>}
          {==}
        case Tk.Value{+c, +v}:
          +r = Tk.scrub_val(m, c, v)
          +rr = Tk.scrub_vals(Tk.vals(rest), Tk.Step.m(r))
          %Equal.sym(Tk.Book, Tk.Toks.m(Tk.scrub_vals.cons(Tk.Step.t(r), rr)), Tk.Toks.m(rr), ptx.vals_m(Tk.Step.t(r), rr)) : {Tk.restore(_, Tk.fill(Tk.Value{c, v} <> rest, Tk.Toks.ts(Tk.scrub_vals.cons(Tk.Step.t(r), rr)))) == S.mask(Tk.Value{c, v} <> rest) : List<&2, Tk.Seg>}
          %Equal.sym(List<&2, Tk.Tok>, Tk.Toks.ts(Tk.scrub_vals.cons(Tk.Step.t(r), rr)), Tk.Step.t(r) <> Tk.Toks.ts(rr), ptx.vals_ts(Tk.Step.t(r), rr)) : {Tk.restore(Tk.Toks.m(rr), Tk.fill(Tk.Value{c, v} <> rest, _)) == S.mask(Tk.Value{c, v} <> rest) : List<&2, Tk.Seg>}
          ptx.rt.s(r, c, v, m, rest, LSc.psc.tok_ok(m, c, v), m1 => ptx.round_trip(rest, m1))

# a text scrubbed from m, indexes erased
def ptx.SH(xs: List<&2, Tk.Piece>, m: Tk.Book) -> Type:
  {S.erase(Tk.fill(xs, Tk.Toks.ts(Tk.scrub_vals(Tk.vals(xs), m)))) == S.shape(xs) : List<&2, Tk.Seg>}

def ptx.sh.s(s: Tk.Step, +c: Tk.Class, +v: String, +m: Tk.Book, +xs: List<&2, Tk.Piece>,
  ok: LSc.psc.TokOk(c, v, m, s),
  ih: @m1: Tk.Book -> ptx.SH(xs, m1)) ->
  {S.erase(Tk.fill(Tk.Value{c, v} <> xs, Tk.Step.t(s) <> Tk.Toks.ts(Tk.scrub_vals(Tk.vals(xs), Tk.Step.m(s))))) == S.shape(Tk.Value{c, v} <> xs) : List<&2, Tk.Seg>}:
  match s:
    case Tk.Step{+m1, t}:
      match t:
        case Tk.Mapped{+i}:
          (er, (eh, ef)) = ok
          %Equal.sym(List<&2, Tk.Seg>, S.erase(Tk.fill(xs, Tk.Toks.ts(Tk.scrub_vals(Tk.vals(xs), m1)))), S.shape(xs), ih(m1)) : {Tk.Tok{c, 0n} <> _ == S.shape(Tk.Value{c, v} <> xs) : List<&2, Tk.Seg>}
          %Equal.sym(Bool, S.reversible(c), True{}, LTk.ptk.srev(c, True{}, er)) : {Tk.Tok{c, 0n} <> S.shape(xs) == S.shape.of(_, c, v) <> S.shape(xs) : List<&2, Tk.Seg>}
          {==}
        case Tk.OneWay{}:
          (er, em) = ok
          %Equal.sym(List<&2, Tk.Seg>, S.erase(Tk.fill(xs, Tk.Toks.ts(Tk.scrub_vals(Tk.vals(xs), m1)))), S.shape(xs), ih(m1)) : {Tk.Hash{c, v} <> _ == S.shape(Tk.Value{c, v} <> xs) : List<&2, Tk.Seg>}
          %Equal.sym(Bool, S.reversible(c), False{}, LTk.ptk.srev(c, False{}, er)) : {Tk.Hash{c, v} <> S.shape(xs) == S.shape.of(_, c, v) <> S.shape(xs) : List<&2, Tk.Seg>}
          {==}

def ptx.shape(xs: List<&2, Tk.Piece>, +m: Tk.Book) -> ptx.SH(xs, m):
  match xs:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Tk.Plain{+s}:
          %ptx.shape(rest, m) : {Tk.Txt{s} <> S.erase(Tk.fill(rest, Tk.Toks.ts(Tk.scrub_vals(Tk.vals(rest), m)))) == Tk.Txt{s} <> _ : List<&2, Tk.Seg>}
          {==}
        case Tk.Value{+c, +v}:
          +r = Tk.scrub_val(m, c, v)
          +rr = Tk.scrub_vals(Tk.vals(rest), Tk.Step.m(r))
          %Equal.sym(List<&2, Tk.Tok>, Tk.Toks.ts(Tk.scrub_vals.cons(Tk.Step.t(r), rr)), Tk.Step.t(r) <> Tk.Toks.ts(rr), ptx.vals_ts(Tk.Step.t(r), rr)) : {S.erase(Tk.fill(Tk.Value{c, v} <> rest, _)) == S.shape(Tk.Value{c, v} <> rest) : List<&2, Tk.Seg>}
          ptx.sh.s(r, c, v, m, rest, LSc.psc.tok_ok(m, c, v), m1 => ptx.shape(rest, m1))

# Credentials
# -----------

def ptx.cr_some.r(r: Bool, +c: Tk.Class, +i: Nat, +v: String, +m: Tk.Book, -x: List<&2, Tk.Seg>,
  +er: {S.reversible(c) == r : Bool},
  +h: {Tk.restore_tok(m, c, i) == Some{v} : Maybe<&2, String>}) ->
  {S.creds.keep(Bool.not(r), Tk.Clear{c, v}, x) == S.creds.keep(Bool.not(r), Tk.Tok{c, i}, x) : List<&2, Tk.Seg>}:
  match r:
    case True{}:
      {==}
    case False{}:
      +ek = Equal.trans(Bool, Tk.reversible(c), S.reversible(c), False{}, LTk.ptk.rev_spec(c), er)
      LTk.ptk.none_some(String, v, {S.creds.keep(True{}, Tk.Clear{c, v}, x) == S.creds.keep(True{}, Tk.Tok{c, i}, x) : List<&2, Tk.Seg>}, Equal.trans(Maybe<&2, String>, None{}, Tk.restore_tok(m, c, i), Some{v}, Equal.sym(Maybe<&2, String>, Tk.restore_tok(m, c, i), None{}, LSc.psc.rt_none(m, c, i, ek)), h))

def ptx.cr_tok(f: Maybe<&2, String>, +c: Tk.Class, +i: Nat, +m: Tk.Book, -x: List<&2, Tk.Seg>,
  +ef: {Tk.restore_tok(m, c, i) == f : Maybe<&2, String>}) ->
  {S.creds.keep(S.secret_seg(ptx.restore1.tok(c, i, f)), ptx.restore1.tok(c, i, f), x) == S.creds.keep(S.secret_seg(Tk.Tok{c, i}), Tk.Tok{c, i}, x) : List<&2, Tk.Seg>}:
  match f:
    case None{}:
      {==}
    case Some{+v}:
      ptx.cr_some.r(S.reversible(c), c, i, v, m, x, {==}, ef)

def ptx.cr1(+m: Tk.Book, y: Tk.Seg, -x: List<&2, Tk.Seg>) -> {S.creds.keep(S.secret_seg(ptx.restore1(m, y)), ptx.restore1(m, y), x) == S.creds.keep(S.secret_seg(y), y, x) : List<&2, Tk.Seg>}:
  match y:
    case Tk.Txt{s}:
      {==}
    case Tk.Clear{c, v}:
      {==}
    case Tk.Tok{+c, +i}:
      ptx.cr_tok(Tk.restore_tok(m, c, i), c, i, m, x, {==})
    case Tk.Hash{c, v}:
      {==}

# restoring keeps every piece of a one-way class
def ptx.creds(+m: Tk.Book, ys: List<&2, Tk.Seg>) -> {S.creds(Tk.restore(m, ys)) == S.creds(ys) : List<&2, Tk.Seg>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      %Equal.sym(List<&2, Tk.Seg>, Tk.restore(m, y <> rest), ptx.restore1(m, y) <> Tk.restore(m, rest), ptx.restore_cons(m, y, rest)) : {S.creds(_) == S.creds(y <> rest) : List<&2, Tk.Seg>}
      %Equal.sym(List<&2, Tk.Seg>, S.creds(Tk.restore(m, rest)), S.creds(rest), ptx.creds(m, rest)) : {S.creds.keep(S.secret_seg(ptx.restore1(m, y)), ptx.restore1(m, y), _) == S.creds(y <> rest) : List<&2, Tk.Seg>}
      ptx.cr1(m, y, S.creds(rest))

# Failover
# --------

def ptx.raw(xs: List<&2, Tk.Piece>) -> {Tk.raw(xs) == S.raw(xs) : List<&2, Tk.Seg>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match x:
        case Tk.Plain{+s}:
          %ptx.raw(rest) : {Tk.Txt{s} <> Tk.raw(rest) == Tk.Txt{s} <> _ : List<&2, Tk.Seg>}
          {==}
        case Tk.Value{+c, +v}:
          %ptx.raw(rest) : {Tk.Clear{c, v} <> Tk.raw(rest) == Tk.Clear{c, v} <> _ : List<&2, Tk.Seg>}
          {==}

def ptx.sent_cons(-y: List<&2, Tk.Seg>, r: Tk.Sent) -> {Tk.Sent.yss(Tk.send.cons(y, r)) == y <> Tk.Sent.yss(r) : List<&2, List<&2, Tk.Seg>>}:
  match r:
    case Tk.Sent{m, yss}:
      {==}

# the same text scrubbed again against the map after it
def ptx.scrub_stable(+m: Tk.Book, +xs: List<&2, Tk.Piece>) -> {Tk.scrub(Tk.Out.m(Tk.scrub(m, xs)), xs) == Tk.scrub(m, xs) : Tk.Out}:
  +r = Tk.scrub_vals(Tk.vals(xs), m)
  %Equal.sym(Tk.Book, Tk.Out.m(Tk.scrub.fill(xs, r)), Tk.Toks.m(r), ptx.out_m(xs, r)) : {Tk.scrub(_, xs) == Tk.scrub(m, xs) : Tk.Out}
  %Equal.sym(Tk.Toks, Tk.scrub_vals(Tk.vals(xs), Tk.Toks.m(r)), r, ptx.stable(Tk.vals(xs), m)) : {Tk.scrub.fill(xs, _) == Tk.scrub(m, xs) : Tk.Out}
  {==}

# from a map the text's scrub does not grow, every attempt sends the one
# scrub y or the raw text
def ptx.sends(ts: List<&2, Bool>, +m: Tk.Book, +xs: List<&2, Tk.Piece>, +y: List<&2, Tk.Seg>, +e: {Tk.scrub(m, xs) == Tk.Out{m, y} : Tk.Out}) -> {Tk.Sent.yss(Tk.send(ts, m, xs)) == S.sends(ts, y, S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case True{}:
          %Equal.sym(List<&2, List<&2, Tk.Seg>>, Tk.Sent.yss(Tk.send.cons(Tk.Out.ys(Tk.scrub(m, xs)), Tk.send(rest, Tk.Out.m(Tk.scrub(m, xs)), xs))), Tk.Out.ys(Tk.scrub(m, xs)) <> Tk.Sent.yss(Tk.send(rest, Tk.Out.m(Tk.scrub(m, xs)), xs)), ptx.sent_cons(Tk.Out.ys(Tk.scrub(m, xs)), Tk.send(rest, Tk.Out.m(Tk.scrub(m, xs)), xs))) : {_ == S.sends(True{} <> rest, y, S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          %Equal.sym(Tk.Out, Tk.scrub(m, xs), Tk.Out{m, y}, e) : {Tk.Out.ys(_) <> Tk.Sent.yss(Tk.send(rest, Tk.Out.m(_), xs)) == S.sends(True{} <> rest, y, S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          %Equal.sym(List<&2, List<&2, Tk.Seg>>, Tk.Sent.yss(Tk.send(rest, m, xs)), S.sends(rest, y, S.raw(xs)), ptx.sends(rest, m, xs, y, e)) : {y <> _ == S.sends(True{} <> rest, y, S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          {==}
        case False{}:
          %Equal.sym(List<&2, List<&2, Tk.Seg>>, Tk.Sent.yss(Tk.send.cons(Tk.raw(xs), Tk.send(rest, m, xs))), Tk.raw(xs) <> Tk.Sent.yss(Tk.send(rest, m, xs)), ptx.sent_cons(Tk.raw(xs), Tk.send(rest, m, xs))) : {_ == S.sends(False{} <> rest, y, S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          %Equal.sym(List<&2, Tk.Seg>, Tk.raw(xs), S.raw(xs), ptx.raw(xs)) : {_ <> Tk.Sent.yss(Tk.send(rest, m, xs)) == S.sends(False{} <> rest, y, S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          %Equal.sym(List<&2, List<&2, Tk.Seg>>, Tk.Sent.yss(Tk.send(rest, m, xs)), S.sends(rest, y, S.raw(xs)), ptx.sends(rest, m, xs, y, e)) : {S.raw(xs) <> _ == S.sends(False{} <> rest, y, S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          {==}

# every attempt sends the one scrub of the raw text, or the raw text
def ptx.failover(ts: List<&2, Bool>, +m: Tk.Book, +xs: List<&2, Tk.Piece>) -> {Tk.Sent.yss(Tk.send(ts, m, xs)) == S.sends(ts, Tk.Out.ys(Tk.scrub(m, xs)), S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case True{}:
          +o = Tk.scrub(m, xs)
          +e = Equal.trans(Tk.Out, Tk.scrub(Tk.Out.m(o), xs), o, Tk.Out{Tk.Out.m(o), Tk.Out.ys(o)}, ptx.scrub_stable(m, xs), ptx.out_eta(o))
          %Equal.sym(List<&2, List<&2, Tk.Seg>>, Tk.Sent.yss(Tk.send.cons(Tk.Out.ys(o), Tk.send(rest, Tk.Out.m(o), xs))), Tk.Out.ys(o) <> Tk.Sent.yss(Tk.send(rest, Tk.Out.m(o), xs)), ptx.sent_cons(Tk.Out.ys(o), Tk.send(rest, Tk.Out.m(o), xs))) : {_ == S.sends(True{} <> rest, Tk.Out.ys(o), S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          %Equal.sym(List<&2, List<&2, Tk.Seg>>, Tk.Sent.yss(Tk.send(rest, Tk.Out.m(o), xs)), S.sends(rest, Tk.Out.ys(o), S.raw(xs)), ptx.sends(rest, Tk.Out.m(o), xs, Tk.Out.ys(o), e)) : {Tk.Out.ys(o) <> _ == S.sends(True{} <> rest, Tk.Out.ys(o), S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          {==}
        case False{}:
          %Equal.sym(List<&2, List<&2, Tk.Seg>>, Tk.Sent.yss(Tk.send.cons(Tk.raw(xs), Tk.send(rest, m, xs))), Tk.raw(xs) <> Tk.Sent.yss(Tk.send(rest, m, xs)), ptx.sent_cons(Tk.raw(xs), Tk.send(rest, m, xs))) : {_ == S.sends(False{} <> rest, Tk.Out.ys(Tk.scrub(m, xs)), S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          %Equal.sym(List<&2, Tk.Seg>, Tk.raw(xs), S.raw(xs), ptx.raw(xs)) : {_ <> Tk.Sent.yss(Tk.send(rest, m, xs)) == S.sends(False{} <> rest, Tk.Out.ys(Tk.scrub(m, xs)), S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          %Equal.sym(List<&2, List<&2, Tk.Seg>>, Tk.Sent.yss(Tk.send(rest, m, xs)), S.sends(rest, Tk.Out.ys(Tk.scrub(m, xs)), S.raw(xs)), ptx.failover(rest, m, xs)) : {S.raw(xs) <> _ == S.sends(False{} <> rest, Tk.Out.ys(Tk.scrub(m, xs)), S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}
          {==}

# a text with no credential is its mask
def ptx.mask_raw(xs: List<&2, Tk.Piece>, +ok: {S.no_secret(xs) == True{} : Bool}) -> {S.mask(xs) == S.raw(xs) : List<&2, Tk.Seg>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Tk.Plain{+s}:
          %ptx.mask_raw(rest, ok) : {Tk.Txt{s} <> S.mask(rest) == Tk.Txt{s} <> _ : List<&2, Tk.Seg>}
          {==}
        case Tk.Value{+c, +v}:
          +er = LTk.ptk.and_l(S.reversible(c), S.no_secret(rest), ok)
          %Equal.sym(Bool, S.reversible(c), True{}, er) : {S.mask.of(_, c, v) <> S.mask(rest) == Tk.Clear{c, v} <> S.raw(rest) : List<&2, Tk.Seg>}
          %ptx.mask_raw(rest, LTk.ptk.and_r(S.reversible(c), S.no_secret(rest), ok)) : {Tk.Clear{c, v} <> S.mask(rest) == Tk.Clear{c, v} <> _ : List<&2, Tk.Seg>}
          {==}
