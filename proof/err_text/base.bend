# eukhe: lemmas shared by the proofs of area err_text: the code's tables
# are found where the phrases read from the Rust regex literals are (the
# same lists, or for the transient table each a pick of the other), the
# code's lazy
# decision is the spec's (text_pat_fold, phrase_any), a spelled request
# reads back (etb.req), the answer is the spelled spec answer (etb.reply),
# and each decoder stage answers Got only for the spelling of what it read
# so far, every count and length within the wire (etb.x.*: the stage
# carries `pre`, the input spelled up to its field).

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/phrase.bend as P
import ../../bend/err_text.bend as E
import ../../bend/ffi_err_text.bend as FE
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/phrase.bend as Phrase
import ../../laws/err_text.bend as ErrText
import ../text_pat/text_pat_fold.bend as PTextPatFold
import ../phrase/phrase_any.bend as PPhraseAny
import ../wire/wire_strs_round_trip.bend as PWireStrsRoundTrip
import ../wire/wire_strs_exact.bend as PWireStrsExact
import ../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ../wire/base/spell.bend as LAWireSpell
import ../base/staging.bend as LStg

# Logic
# -----

def etb.or_lazy(a: Bool, b: Bool) -> {P.pm.or(a, u => b) == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def etb.or_r(y: Bool) -> {Bool.or(y, True{}) == True{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}

# The decision
# ------------

# Tables
# ------

def etb.or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def etb.or_absorb(f: Bool, -t: Bool) -> {Bool.or(Bool.or(f, False{}), Bool.or(f, t)) == Bool.or(f, t) : Bool}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

def etb.or_mid(n: Bool, f: Bool, -t: Bool, ih: {Bool.or(n, t) == t : Bool}) -> {Bool.or(n, Bool.or(f, t)) == Bool.or(f, t) : Bool}:
  match f:
    case True{}:
      etb.or_r(n)
    case False{}:
      ih

# or(a, b) is b and or(b, a) is a: a is b
def etb.or_antisym(a: Bool, b: Bool, h1: {Bool.or(a, b) == b : Bool}, h2: {Bool.or(b, a) == a : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      LStg.stg.absurd({True{} == False{} : Bool}, h1)
    case False{} True{}:
      LStg.stg.absurd({False{} == True{} : Bool}, h2)

# the i-th phrase of xs (0 first), as a list of it; none past the end
def etb.nth(xs: List<&2, P.Ph>, i: Nat) -> List<&2, P.Ph>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      match i:
        case 0n:
          [x]
        case 1n+j:
          etb.nth(t, j)

# the phrases of xs at the indices ix, in order
def etb.pick(+xs: List<&2, P.Ph>, ix: List<&2, Nat>) -> List<&2, P.Ph>:
  match ix:
    case Nil{}:
      Nil{}
    case i <> t:
      List.append(&2, P.Ph, etb.nth(xs, i), etb.pick(xs, t))

# a search of a ++ b is a search of a, then of b
def etb.any_app(+s: String, a: List<&2, P.Ph>, -b: List<&2, P.Ph>) -> {Phrase.sp_any(s, List.append(&2, P.Ph, a, b)) == Bool.or(Phrase.sp_any(s, a), Phrase.sp_any(s, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Bool, Phrase.sp_any(s, List.append(&2, P.Ph, t, b)), Bool.or(Phrase.sp_any(s, t), Phrase.sp_any(s, b)), etb.any_app(s, t, b)) : {Bool.or(P.found(s, x), _) == Bool.or(Bool.or(P.found(s, x), Phrase.sp_any(s, t)), Phrase.sp_any(s, b)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(P.found(s, x), Phrase.sp_any(s, t)), Phrase.sp_any(s, b)), Bool.or(P.found(s, x), Bool.or(Phrase.sp_any(s, t), Phrase.sp_any(s, b))), etb.or_assoc(P.found(s, x), Phrase.sp_any(s, t), Phrase.sp_any(s, b)))

# a phrase of xs found: xs found (as or(.., xs) == xs)
def etb.any_nth(+s: String, xs: List<&2, P.Ph>, i: Nat) -> {Bool.or(Phrase.sp_any(s, etb.nth(xs, i)), Phrase.sp_any(s, xs)) == Phrase.sp_any(s, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match i:
        case 0n:
          etb.or_absorb(P.found(s, x), Phrase.sp_any(s, t))
        case 1n++j:
          etb.or_mid(Phrase.sp_any(s, etb.nth(t, j)), P.found(s, x), Phrase.sp_any(s, t), etb.any_nth(s, t, j))

# phrases of xs picked and found: xs found
def etb.any_pick(+s: String, +xs: List<&2, P.Ph>, ix: List<&2, Nat>) -> {Bool.or(Phrase.sp_any(s, etb.pick(xs, ix)), Phrase.sp_any(s, xs)) == Phrase.sp_any(s, xs) : Bool}:
  match ix:
    case Nil{}:
      {==}
    case +i <> +t:
      +n = Phrase.sp_any(s, etb.nth(xs, i))
      +q = Phrase.sp_any(s, etb.pick(xs, t))
      +b = Phrase.sp_any(s, xs)
      %Equal.sym(Bool, Phrase.sp_any(s, List.append(&2, P.Ph, etb.nth(xs, i), etb.pick(xs, t))), Bool.or(n, q), etb.any_app(s, etb.nth(xs, i), etb.pick(xs, t))) : {Bool.or(_, b) == b : Bool}
      %Equal.sym(Bool, Bool.or(Bool.or(n, q), b), Bool.or(n, Bool.or(q, b)), etb.or_assoc(n, q, b)) : {_ == b : Bool}
      %Equal.sym(Bool, Bool.or(q, b), b, etb.any_pick(s, xs, t)) : {Bool.or(n, _) == b : Bool}
      etb.any_nth(s, xs, i)

# the code's tables are the phrases its regex literal reads to: the same
# list, or (the transient table, written grouped by edges) the same
# phrases in another order, each list a pick of the other
def etb.c_limit() -> {E.limit_phs() == ErrText.sp_table(E.RLimit{}) : List<&2, P.Ph>}:
  {==}

def etb.c_terminal() -> {E.terminal_phs() == ErrText.sp_table(E.RCodexTerminal{}) : List<&2, P.Ph>}:
  {==}

def etb.c_retryable() -> {E.codex_retryable_phs() == ErrText.sp_table(E.RCodexRetryable{}) : List<&2, P.Ph>}:
  {==}

def etb.c_usage() -> {E.codex_usage_phs() == ErrText.sp_table(E.RCodexUsage{}) : List<&2, P.Ph>}:
  {==}

def etb.c_timeout() -> {E.timeout_phs() == ErrText.sp_table(E.RTimeout{}) : List<&2, P.Ph>}:
  {==}

def etb.c_tr_code() -> {E.transient_phs() == etb.pick(ErrText.sp_table(E.RTransient{}), [0n, 5n, 30n, 16n, 17n, 18n, 19n, 21n, 22n, 23n, 24n, 39n, 40n, 1n, 6n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 26n, 27n, 28n, 29n, 32n, 34n, 35n, 36n, 37n, 38n, 41n, 49n, 50n, 51n, 2n, 3n, 4n, 20n, 25n, 31n, 33n, 42n, 43n, 44n, 45n, 46n, 47n, 48n]) : List<&2, P.Ph>}:
  {==}

def etb.c_tr_rx() -> {ErrText.sp_table(E.RTransient{}) == etb.pick(E.transient_phs(), [0n, 13n, 38n, 39n, 40n, 1n, 14n, 15n, 16n, 17n, 18n, 19n, 20n, 21n, 22n, 23n, 3n, 4n, 5n, 6n, 41n, 7n, 8n, 9n, 10n, 42n, 24n, 25n, 26n, 27n, 2n, 43n, 28n, 44n, 29n, 30n, 31n, 32n, 33n, 11n, 12n, 34n, 45n, 46n, 47n, 48n, 49n, 50n, 51n, 35n, 36n, 37n]) : List<&2, P.Ph>}:
  {==}

# the transient search: each table's phrases are the other's
def etb.same_tr(+s: String) -> {Phrase.sp_any(s, E.transient_phs()) == Phrase.sp_any(s, ErrText.sp_table(E.RTransient{})) : Bool}:
  +a = Phrase.sp_any(s, E.transient_phs())
  +b = Phrase.sp_any(s, ErrText.sp_table(E.RTransient{}))
  +h1 = Equal.trans(Bool, Bool.or(a, b), Bool.or(Phrase.sp_any(s, etb.pick(ErrText.sp_table(E.RTransient{}), [0n, 5n, 30n, 16n, 17n, 18n, 19n, 21n, 22n, 23n, 24n, 39n, 40n, 1n, 6n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 26n, 27n, 28n, 29n, 32n, 34n, 35n, 36n, 37n, 38n, 41n, 49n, 50n, 51n, 2n, 3n, 4n, 20n, 25n, 31n, 33n, 42n, 43n, 44n, 45n, 46n, 47n, 48n])), b), b, Equal.cong(List<&2, P.Ph>, Bool, z => Bool.or(Phrase.sp_any(s, z), b), E.transient_phs(), etb.pick(ErrText.sp_table(E.RTransient{}), [0n, 5n, 30n, 16n, 17n, 18n, 19n, 21n, 22n, 23n, 24n, 39n, 40n, 1n, 6n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 26n, 27n, 28n, 29n, 32n, 34n, 35n, 36n, 37n, 38n, 41n, 49n, 50n, 51n, 2n, 3n, 4n, 20n, 25n, 31n, 33n, 42n, 43n, 44n, 45n, 46n, 47n, 48n]), etb.c_tr_code()), etb.any_pick(s, ErrText.sp_table(E.RTransient{}), [0n, 5n, 30n, 16n, 17n, 18n, 19n, 21n, 22n, 23n, 24n, 39n, 40n, 1n, 6n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 26n, 27n, 28n, 29n, 32n, 34n, 35n, 36n, 37n, 38n, 41n, 49n, 50n, 51n, 2n, 3n, 4n, 20n, 25n, 31n, 33n, 42n, 43n, 44n, 45n, 46n, 47n, 48n]))
  +h2 = Equal.trans(Bool, Bool.or(b, a), Bool.or(Phrase.sp_any(s, etb.pick(E.transient_phs(), [0n, 13n, 38n, 39n, 40n, 1n, 14n, 15n, 16n, 17n, 18n, 19n, 20n, 21n, 22n, 23n, 3n, 4n, 5n, 6n, 41n, 7n, 8n, 9n, 10n, 42n, 24n, 25n, 26n, 27n, 2n, 43n, 28n, 44n, 29n, 30n, 31n, 32n, 33n, 11n, 12n, 34n, 45n, 46n, 47n, 48n, 49n, 50n, 51n, 35n, 36n, 37n])), a), a, Equal.cong(List<&2, P.Ph>, Bool, z => Bool.or(Phrase.sp_any(s, z), a), ErrText.sp_table(E.RTransient{}), etb.pick(E.transient_phs(), [0n, 13n, 38n, 39n, 40n, 1n, 14n, 15n, 16n, 17n, 18n, 19n, 20n, 21n, 22n, 23n, 3n, 4n, 5n, 6n, 41n, 7n, 8n, 9n, 10n, 42n, 24n, 25n, 26n, 27n, 2n, 43n, 28n, 44n, 29n, 30n, 31n, 32n, 33n, 11n, 12n, 34n, 45n, 46n, 47n, 48n, 49n, 50n, 51n, 35n, 36n, 37n]), etb.c_tr_rx()), etb.any_pick(s, E.transient_phs(), [0n, 13n, 38n, 39n, 40n, 1n, 14n, 15n, 16n, 17n, 18n, 19n, 20n, 21n, 22n, 23n, 3n, 4n, 5n, 6n, 41n, 7n, 8n, 9n, 10n, 42n, 24n, 25n, 26n, 27n, 2n, 43n, 28n, 44n, 29n, 30n, 31n, 32n, 33n, 11n, 12n, 34n, 45n, 46n, 47n, 48n, 49n, 50n, 51n, 35n, 36n, 37n]))
  etb.or_antisym(a, b, h1, h2)

# the code's table of each rule and the regex's are found alike
def etb.same(+s: String, r: E.Rule) -> {Phrase.sp_any(s, E.table(r)) == Phrase.sp_any(s, ErrText.sp_table(r)) : Bool}:
  match r:
    case E.RLimit{}:
      Equal.cong(List<&2, P.Ph>, Bool, z => Phrase.sp_any(s, z), E.limit_phs(), ErrText.sp_table(E.RLimit{}), etb.c_limit())
    case E.RTransient{}:
      etb.same_tr(s)
    case E.RCodexTerminal{}:
      Equal.cong(List<&2, P.Ph>, Bool, z => Phrase.sp_any(s, z), E.terminal_phs(), ErrText.sp_table(E.RCodexTerminal{}), etb.c_terminal())
    case E.RCodexRetryable{}:
      Equal.cong(List<&2, P.Ph>, Bool, z => Phrase.sp_any(s, z), E.codex_retryable_phs(), ErrText.sp_table(E.RCodexRetryable{}), etb.c_retryable())
    case E.RCodexUsage{}:
      Equal.cong(List<&2, P.Ph>, Bool, z => Phrase.sp_any(s, z), E.codex_usage_phs(), ErrText.sp_table(E.RCodexUsage{}), etb.c_usage())
    case E.RTimeout{}:
      Equal.cong(List<&2, P.Ph>, Bool, z => Phrase.sp_any(s, z), E.timeout_phs(), ErrText.sp_table(E.RTimeout{}), etb.c_timeout())

# one text: the code's test is the spec's
def etb.text(+r: E.Rule, +t: String) -> {E.holds_text(r, t) == ErrText.sp_holds_text(r, t) : Bool}:
  %Equal.sym(String, Tp.fold_str(t), TextPat.sp_fold(t), TextPat.text_pat_fold(t)) : {P.any(_, E.table(r)) == ErrText.sp_holds_text(r, t) : Bool}
  %Equal.sym(Bool, P.any(TextPat.sp_fold(t), E.table(r)), Phrase.sp_any(TextPat.sp_fold(t), E.table(r)), Phrase.phrase_any(TextPat.sp_fold(t), E.table(r))) : {_ == ErrText.sp_holds_text(r, t) : Bool}
  etb.same(TextPat.sp_fold(t), r)

# the code's lazy decision over a list of texts is the spec's
def etb.holds(+r: E.Rule, texts: List<&2, String>) -> {E.holds(r, texts) == ErrText.sp_holds(r, texts) : Bool}:
  match texts:
    case Nil{}:
      {==}
    case +t <> +more:
      %Equal.sym(Bool, E.holds(r, more), ErrText.sp_holds(r, more), etb.holds(r, more)) : {P.pm.or(E.holds_text(r, t), u => _) == ErrText.sp_holds(r, t <> more) : Bool}
      %Equal.sym(Bool, E.holds_text(r, t), ErrText.sp_holds_text(r, t), etb.text(r, t)) : {P.pm.or(_, u => ErrText.sp_holds(r, more)) == ErrText.sp_holds(r, t <> more) : Bool}
      etb.or_lazy(ErrText.sp_holds_text(r, t), ErrText.sp_holds(r, more))

# a phrase found makes a list that holds it found
def etb.any_split(pre: List<&2, P.Ph>, +s: String, +ph: P.Ph, +post: List<&2, P.Ph>, +h: {P.found(s, ph) == True{} : Bool}) -> {Phrase.sp_any(s, List.append(&2, P.Ph, pre, ph <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, P.found(s, ph), True{}, h) : {Bool.or(_, Phrase.sp_any(s, post)) == True{} : Bool}
      {==}
    case p <> more:
      %Equal.sym(Bool, Phrase.sp_any(s, List.append(&2, P.Ph, more, ph <> post)), True{}, etb.any_split(more, s, ph, post, h)) : {Bool.or(P.found(s, p), _) == True{} : Bool}
      etb.or_r(P.found(s, p))

# a text that holds makes a list of texts that holds it hold
def etb.list_split(tp: List<&2, String>, +r: E.Rule, +text: String, +tq: List<&2, String>, +h: {ErrText.sp_holds_text(r, text) == True{} : Bool}) -> {ErrText.sp_holds(r, List.append(&2, String, tp, text <> tq)) == True{} : Bool}:
  match tp:
    case Nil{}:
      %Equal.sym(Bool, ErrText.sp_holds_text(r, text), True{}, h) : {Bool.or(_, ErrText.sp_holds(r, tq)) == True{} : Bool}
      {==}
    case t <> more:
      %Equal.sym(Bool, ErrText.sp_holds(r, List.append(&2, String, more, text <> tq)), True{}, etb.list_split(more, r, text, tq, h)) : {Bool.or(ErrText.sp_holds_text(r, t), _) == True{} : Bool}
      etb.or_r(ErrText.sp_holds_text(r, t))

# The entry: reading and answering
# --------------------------------

# a spelled rule reads back, the rest untouched
def etb.tag(r: E.Rule, x: String) -> {FE.get_rule.tag(Wr.get_nat(ErrText.sp_w_rule(r, x))) == Wr.Got{r, x} : Wr.Dec<E.Rule>}:
  match r:
    case E.RLimit{}:
      {==}
    case E.RTransient{}:
      {==}
    case E.RCodexTerminal{}:
      {==}
    case E.RCodexRetryable{}:
      {==}
    case E.RCodexUsage{}:
      {==}
    case E.RTimeout{}:
      {==}

# a spelled request that fits reads back, the rest untouched
def etb.req(q: FE.Req, +rest: String, h: {ErrText.sp_fit_req(q) == True{} : Bool}) -> {FE.get_req(ErrText.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FE.Req>}:
  match q:
    case FE.Req{+r, +ts}:
      +x = LawsBase.wire_spell_strs(ts, rest)
      %Equal.sym(Wr.Dec<E.Rule>, FE.get_rule.tag(Wr.get_nat(ErrText.sp_w_rule(r, x))), Wr.Got{r, x}, etb.tag(r, x)) : {FE.get_req.rule(_) == Wr.Got{FE.Req{r, ts}, rest} : Wr.Dec<FE.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, x), Wr.Got{ts, rest}, Wire.wire_strs_round_trip(ts, rest, h)) : {FE.get_req.texts(r, _) == Wr.Got{FE.Req{r, ts}, rest} : Wr.Dec<FE.Req>}
      {==}

# the entry's answer to a request is the spelled spec answer
def etb.reply(q: FE.Req) -> {FE.answer(q) == ErrText.sp_w_reply(q) : String}:
  match q:
    case FE.Req{+r, +ts}:
      Equal.cong(Bool, String, z => Wr.put_bool(z, ""), E.holds(r, ts), ErrText.sp_holds(r, ts), etb.holds(r, ts))

# Exactness
# ---------

def etb.RP(s: String, d: Wr.Dec<FE.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ErrText.sp_w_req(q, r) : String} & {ErrText.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def etb.x.texts(+r: E.Rule, -s: String, +s0: String, pre: {s == ErrText.sp_w_rule(r, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s0) == d : Wr.Dec<List<&2, String>>}) -> etb.RP(s, FE.get_req.texts(r, d)):
  match d:
    case Wr.Got{+ts, +rr}:
      +ee = ed
      +e = Wire.wire_strs_exact(s0, ts, rr, ee)
      +f = Wire.wire_strs_decoded_fit(s0, ts, rr, ee)
      (Equal.trans(String, s, ErrText.sp_w_rule(r, s0), ErrText.sp_w_rule(r, LawsBase.wire_spell_strs(ts, rr)), pre, Equal.cong(String, String, z => ErrText.sp_w_rule(r, z), s0, LawsBase.wire_spell_strs(ts, rr), e)), f)
    case Wr.Bad{}:
      Unit{}

def etb.x.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> etb.RP(s, FE.get_req.rule(FE.get_rule.tag(d))):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          etb.x.texts(E.RLimit{}, s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_list(~String, ~Wr.get_str, s0), {==})
        case 1n:
          etb.x.texts(E.RTransient{}, s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_list(~String, ~Wr.get_str, s0), {==})
        case 2n:
          etb.x.texts(E.RCodexTerminal{}, s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_list(~String, ~Wr.get_str, s0), {==})
        case 3n:
          etb.x.texts(E.RCodexRetryable{}, s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), Wr.get_list(~String, ~Wr.get_str, s0), {==})
        case 4n:
          etb.x.texts(E.RCodexUsage{}, s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), Wr.get_list(~String, ~Wr.get_str, s0), {==})
        case 5n:
          etb.x.texts(E.RTimeout{}, s, s0, Wire.wire_nat_exact(s, 5n, s0, ed), Wr.get_list(~String, ~Wr.get_str, s0), {==})
        case 6n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the decoder reads from s is the spelling of what it read, then
# its rest, and fits the wire
def etb.rp_all(+s: String) -> etb.RP(s, FE.get_req(s)):
  etb.x.tag(s, Wr.get_nat(s), {==})

# a request read whole: the input, the fit and the answer are the spec's
def etb.top_eq(+s: String, +q: FE.Req, e: {s == ErrText.sp_w_req(q, "") : String}, f: {ErrText.sp_fit_req(q) == True{} : Bool}) -> {(s, (ErrText.sp_fit_req(q), FE.answer(q))) == (ErrText.sp_w_req(q, ""), (True{}, ErrText.sp_w_reply(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, ErrText.sp_w_req(q, ""), e) : {(_, (ErrText.sp_fit_req(q), FE.answer(q))) == (ErrText.sp_w_req(q, ""), (True{}, ErrText.sp_w_reply(q))) : String & (Bool & String)}
  %Equal.sym(Bool, ErrText.sp_fit_req(q), True{}, f) : {(ErrText.sp_w_req(q, ""), (_, FE.answer(q))) == (ErrText.sp_w_req(q, ""), (True{}, ErrText.sp_w_reply(q))) : String & (Bool & String)}
  %Equal.sym(String, FE.answer(q), ErrText.sp_w_reply(q), etb.reply(q)) : {(ErrText.sp_w_req(q, ""), (True{}, _)) == (ErrText.sp_w_req(q, ""), (True{}, ErrText.sp_w_reply(q))) : String & (Bool & String)}
  {==}

def etb.TopG(s: String, a: String) -> Type:
  Sigma<&1, &1, FE.Req, q => {(s, (ErrText.sp_fit_req(q), a)) == (ErrText.sp_w_req(q, ""), (True{}, ErrText.sp_w_reply(q))) : String & (Bool & String)}>

# an answer that is no error: a request read whole, nothing left
def etb.top(+s: String, d: Wr.Dec<FE.Req>, rp: etb.RP(s, d), ok: {LawsBase.wire_opens_err(FE.ffi.got(d)) == False{} : Bool}) -> etb.TopG(s, FE.ffi.got(d)):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (e, f) = rp
          (q, etb.top_eq(s, q, e, f))
        case SCon{x, y}:
          LAWireSpell.ws_absurd(etb.TopG(s, Wr.err("err_text: malformed request")), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(etb.TopG(s, Wr.err("err_text: malformed request")), ok)

def etb.MuG(s: String) -> Type:
  Sigma<&1, &1, FE.Req, q => Sigma<&1, &1, String, rest => {(s, ErrText.sp_fit_req(q)) == (ErrText.sp_w_req(q, rest), True{}) : String & Bool}>>

def etb.mu_eq(+s: String, +q: FE.Req, +rest: String, e: {s == ErrText.sp_w_req(q, rest) : String}, f: {ErrText.sp_fit_req(q) == True{} : Bool}) -> {(s, ErrText.sp_fit_req(q)) == (ErrText.sp_w_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, ErrText.sp_w_req(q, rest), e) : {(_, ErrText.sp_fit_req(q)) == (ErrText.sp_w_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, ErrText.sp_fit_req(q), True{}, f) : {(ErrText.sp_w_req(q, rest), _) == (ErrText.sp_w_req(q, rest), True{}) : String & Bool}
  {==}

# an answer other than the malformed error: a request read, then its rest
def etb.mu(+s: String, d: Wr.Dec<FE.Req>, rp: etb.RP(s, d), other: {String.eq(FE.ffi.got(d), Wr.err("err_text: malformed request")) == False{} : Bool}) -> etb.MuG(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e, f) = rp
      (q, (rest, etb.mu_eq(s, q, rest, e, f)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(etb.MuG(s), other)
