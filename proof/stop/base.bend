# eukhe: lemmas shared by the proofs of area stop: the code's end of a
# reply is the spec's (stb.drop, stb.heard), its tables are the spec's
# (both compute to the same phrases), its text tests are the spec's
# (text_pat_fold, phrase_any), the walk is the spec's case by case
# (stb.walk), a spelled request reads back (stb.req) and the answer is the
# spelled spec answer (stb.reply).

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/phrase.bend as P
import ../../bend/stop.bend as S
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/phrase.bend as Phrase
import ../../laws/stop.bend as Stop
import ../../spec/harness/stop.bend as StSpec
import ../text_pat/text_pat_fold.bend as PTextPatFold
import ../phrase/phrase_any.bend as PPhraseAny
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../../bend/run/recovery.bend as RnRecovery

# Logic
# -----

def stb.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def stb.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : stb.BD(_, A, Unit)
  Unit{}

def stb.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def stb.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      stb.absurd({b == True{} : Bool}, h)

# The text tests
# --------------

# the code drops the chars the spec drops
def stb.drop(k: Nat, s: String) -> {S.drop(k, s) == StSpec.drop(k, s) : String}:
  match k:
    case 0n:
      match s:
        case SNil{}:
          {==}
        case SCon{c, t}:
          {==}
    case 1n+j:
      match s:
        case SNil{}:
          {==}
        case SCon{c, t}:
          stb.drop(j, t)

# the end of a reply, folded, is the spec's
def stb.heard(+s: String) -> {S.heard(s) == StSpec.heard(s) : String}:
  +n = Nat.sub(String.length(s), 400n)
  %Equal.sym(String, S.drop(n, s), StSpec.drop(n, s), stb.drop(n, s)) : {Tp.fold_str(_) == StSpec.heard(s) : String}
  %Equal.sym(String, Tp.fold_str(StSpec.drop(n, s)), TextPat.sp_fold(StSpec.drop(n, s)), TextPat.text_pat_fold(StSpec.drop(n, s))) : {_ == StSpec.heard(s) : String}
  {==}

def stb.promise_table() -> {S.promise_phs() == StSpec.promise_table() : List<&2, P.Ph>}:
  {==}

def stb.ask_table() -> {S.ask_phs() == StSpec.ask_table() : List<&2, P.Ph>}:
  {==}

# the code's tests are the spec's
def stb.promises(+s: String) -> {S.promises(s) == StSpec.promises(s) : Bool}:
  %Equal.sym(String, S.heard(s), StSpec.heard(s), stb.heard(s)) : {P.any(_, S.promise_phs()) == StSpec.promises(s) : Bool}
  %Equal.sym(List<&2, P.Ph>, S.promise_phs(), StSpec.promise_table(), stb.promise_table()) : {P.any(StSpec.heard(s), _) == StSpec.promises(s) : Bool}
  Phrase.phrase_any(StSpec.heard(s), StSpec.promise_table())

def stb.asks(+s: String) -> {S.asks(s) == StSpec.asks(s) : Bool}:
  %Equal.sym(String, S.heard(s), StSpec.heard(s), stb.heard(s)) : {P.any(_, S.ask_phs()) == StSpec.asks(s) : Bool}
  %Equal.sym(List<&2, P.Ph>, S.ask_phs(), StSpec.ask_table(), stb.ask_table()) : {P.any(StSpec.heard(s), _) == StSpec.asks(s) : Bool}
  Phrase.phrase_any(StSpec.heard(s), StSpec.ask_table())

# The verdicts and the walk
# -------------------------

def stb.on(b: Bool) -> {S.on(b) == StSpec.go_if(b) : S.Verdict}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def stb.unexpected(a: Bool, p: Bool) -> {S.on(Bool.and(p, Bool.not(a))) == StSpec.unexpected(a, p) : S.Verdict}:
  match a p:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the last Director's verdict, its tests rewritten to the spec's
def stb.unexpected_said(+s: String) -> {S.on(Bool.and(S.promises(s), Bool.not(S.asks(s)))) == StSpec.unexpected(StSpec.asks(s), StSpec.promises(s)) : S.Verdict}:
  %Equal.sym(Bool, S.promises(s), StSpec.promises(s), stb.promises(s)) : {S.on(Bool.and(_, Bool.not(S.asks(s)))) == StSpec.unexpected(StSpec.asks(s), StSpec.promises(s)) : S.Verdict}
  %Equal.sym(Bool, S.asks(s), StSpec.asks(s), stb.asks(s)) : {S.on(Bool.and(StSpec.promises(s), Bool.not(_))) == StSpec.unexpected(StSpec.asks(s), StSpec.promises(s)) : S.Verdict}
  stb.unexpected(StSpec.asks(s), StSpec.promises(s))

def stb.verdict(d: S.Dir, f: S.Facts) -> {S.verdict(d, f) == StSpec.verdict(d, f) : S.Verdict}:
  match d:
    case S.LengthStop{}:
      match f:
        case S.Facts{c, t, b, p, s}:
          stb.on(c)
    case S.EmptyStop{}:
      match f:
        case S.Facts{c, t, b, p, s}:
          match t:
            case True{}:
              {==}
            case False{}:
              {==}
    case S.MarkupStop{}:
      match f:
        case S.Facts{c, t, b, p, s}:
          stb.on(b)
    case S.PendingWork{}:
      match f:
        case S.Facts{c, t, b, p, s}:
          match p:
            case True{}:
              {==}
            case False{}:
              {==}
    case S.UnexpectedStop{}:
      match f:
        case S.Facts{c, t, b, p, +s}:
          stb.unexpected_said(s)

# the walk's last step: UnexpectedStop decides, then the stack is empty
def stb.announced(a: Bool, p: Bool) -> {S.pick(S.on(Bool.and(p, Bool.not(a))), S.UnexpectedStop{}, u => S.Stands{}) == StSpec.announced(a, p) : S.Pick}:
  match a p:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def stb.announced_said(+s: String) -> {S.pick(S.on(Bool.and(S.promises(s), Bool.not(S.asks(s)))), S.UnexpectedStop{}, u => S.Stands{}) == StSpec.announced(StSpec.asks(s), StSpec.promises(s)) : S.Pick}:
  %Equal.sym(Bool, S.promises(s), StSpec.promises(s), stb.promises(s)) : {S.pick(S.on(Bool.and(_, Bool.not(S.asks(s)))), S.UnexpectedStop{}, u => S.Stands{}) == StSpec.announced(StSpec.asks(s), StSpec.promises(s)) : S.Pick}
  %Equal.sym(Bool, S.asks(s), StSpec.asks(s), stb.asks(s)) : {S.pick(S.on(Bool.and(StSpec.promises(s), Bool.not(_))), S.UnexpectedStop{}, u => S.Stands{}) == StSpec.announced(StSpec.asks(s), StSpec.promises(s)) : S.Pick}
  stb.announced(StSpec.asks(s), StSpec.promises(s))

def stb.walk(f: S.Facts) -> {S.walk(f) == StSpec.pick(f) : S.Pick}:
  match f:
    case S.Facts{c, t, b, p, +s}:
      match c:
        case True{}:
          {==}
        case False{}:
          match t:
            case False{}:
              {==}
            case True{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  match p:
                    case True{}:
                      {==}
                    case False{}:
                      stb.announced_said(s)

# The entry
# ---------

# a spelled note reads back, the rest untouched
def stb.note(+a: Nat, n: S.Note, +rest: String, +h: {Stop.sp_fit_note(n) == True{} : Bool}) -> {FS.get_note.tag(a, Wr.get_nat(Stop.sp_w_note(n, rest))) == Wr.Got{FS.AskNote{a, n}, rest} : Wr.Dec<FS.Ask>}:
  match n:
    case S.Cut{+t, +r, +k}:
      +h0 = stb.and_l(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)), h)
      +h1 = stb.and_r(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(k)), h)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(t, Wr.put_nat(r, Wr.put_nat(k, rest)))), Wr.Got{t, Wr.put_nat(r, Wr.put_nat(k, rest))}, Wire.wire_nat_round_trip(t, Wr.put_nat(r, Wr.put_nat(k, rest)), h0)) : {FS.get_cut(a, _) == Wr.Got{FS.AskNote{a, S.Cut{t, r, k}}, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(r, Wr.put_nat(k, rest))), Wr.Got{r, Wr.put_nat(k, rest)}, Wire.wire_nat_round_trip(r, Wr.put_nat(k, rest), stb.and_l(LawsBase.wire_fits(r), LawsBase.wire_fits(k), h1))) : {FS.get_cut.row(a, t, _) == Wr.Got{FS.AskNote{a, S.Cut{t, r, k}}, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(k, rest)), Wr.Got{k, rest}, Wire.wire_nat_round_trip(k, rest, stb.and_r(LawsBase.wire_fits(r), LawsBase.wire_fits(k), h1))) : {FS.get_cut.cap(a, t, r, _) == Wr.Got{FS.AskNote{a, S.Cut{t, r, k}}, rest} : Wr.Dec<FS.Ask>}
      {==}
    case S.Promised{+r}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(r, rest)), Wr.Got{r, rest}, Wire.wire_nat_round_trip(r, rest, h)) : {FS.get_promised(a, _) == Wr.Got{FS.AskNote{a, S.Promised{r}}, rest} : Wr.Dec<FS.Ask>}
      {==}

# a spelled request that fits reads back, the rest untouched
def stb.req(q: FS.Ask, +rest: String, +h: {Stop.sp_fit(q) == True{} : Bool}) -> {FS.get_ask(Stop.sp_w_ask(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FS.Ask>}:
  match q:
    case FS.AskWalk{f}:
      match f:
        case S.Facts{+c, +t, +b, +p, +s}:
          %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_str(s, rest)))))), Wr.Got{c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_str(s, rest))))}, Wire.wire_bool_round_trip(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_str(s, rest)))))) : {FS.get_walk(_) == Wr.Got{FS.AskWalk{S.Facts{c, t, b, p, s}}, rest} : Wr.Dec<FS.Ask>}
          %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_str(s, rest))))), Wr.Got{t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_str(s, rest)))}, Wire.wire_bool_round_trip(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_str(s, rest))))) : {FS.get_walk.text(c, _) == Wr.Got{FS.AskWalk{S.Facts{c, t, b, p, s}}, rest} : Wr.Dec<FS.Ask>}
          %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, Wr.put_bool(p, Wr.put_str(s, rest)))), Wr.Got{b, Wr.put_bool(p, Wr.put_str(s, rest))}, Wire.wire_bool_round_trip(b, Wr.put_bool(p, Wr.put_str(s, rest)))) : {FS.get_walk.broken(c, t, _) == Wr.Got{FS.AskWalk{S.Facts{c, t, b, p, s}}, rest} : Wr.Dec<FS.Ask>}
          %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(p, Wr.put_str(s, rest))), Wr.Got{p, Wr.put_str(s, rest)}, Wire.wire_bool_round_trip(p, Wr.put_str(s, rest))) : {FS.get_walk.pending(c, t, b, _) == Wr.Got{FS.AskWalk{S.Facts{c, t, b, p, s}}, rest} : Wr.Dec<FS.Ask>}
          %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(s, rest)), Wr.Got{s, rest}, Wire.wire_str_round_trip(s, rest, h)) : {FS.get_walk.said(c, t, b, p, _) == Wr.Got{FS.AskWalk{S.Facts{c, t, b, p, s}}, rest} : Wr.Dec<FS.Ask>}
          {==}
    case FS.AskNote{+a, +n}:
      +h0 = stb.and_l(LawsBase.wire_fits(a), Stop.sp_fit_note(n), h)
      +h1 = stb.and_r(LawsBase.wire_fits(a), Stop.sp_fit_note(n), h)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(a, Stop.sp_w_note(n, rest))), Wr.Got{a, Stop.sp_w_note(n, rest)}, Wire.wire_nat_round_trip(a, Stop.sp_w_note(n, rest), h0)) : {FS.get_note(_) == Wr.Got{FS.AskNote{a, n}, rest} : Wr.Dec<FS.Ask>}
      stb.note(a, n, rest, h1)
    case FS.AskRounds{+m, +d}:
      +h0 = stb.and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(d), h)
      +h1 = stb.and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(d), h)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(m, Wr.put_nat(d, rest))), Wr.Got{m, Wr.put_nat(d, rest)}, Wire.wire_nat_round_trip(m, Wr.put_nat(d, rest), h0)) : {FS.get_rounds(_) == Wr.Got{FS.AskRounds{m, d}, rest} : Wr.Dec<FS.Ask>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(d, rest)), Wr.Got{d, rest}, Wire.wire_nat_round_trip(d, rest, h1)) : {FS.get_rounds.done(m, _) == Wr.Got{FS.AskRounds{m, d}, rest} : Wr.Dec<FS.Ask>}
      {==}

# the spelled pick of the code's walk is the spelled pick of the spec's
def stb.w_pick(p: S.Pick) -> {FS.put_pick(p, "") == Stop.sp_w_pick(p) : String}:
  match p:
    case S.Stands{}:
      {==}
    case S.Goes{d}:
      match d:
        case S.LengthStop{}:
          {==}
        case S.EmptyStop{}:
          {==}
        case S.MarkupStop{}:
          {==}
        case S.PendingWork{}:
          {==}
        case S.UnexpectedStop{}:
          {==}

def stb.w_round(m: Maybe<&2, String>) -> {FS.put_text(m, "") == Stop.sp_w_round(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      {==}

# The texts
# ---------

# every note is the spec's text, once the reported limit (0, more) is split
def stb.note_text(a: Nat, n: S.Note) -> {S.note(a, n) == StSpec.note(a, n) : String}:
  match n:
    case S.Cut{t, r, k}:
      match t:
        case 0n:
          {==}
        case 1n+u:
          {==}
    case S.Promised{r}:
      {==}

def stb.round_text(left: Nat, +max: Nat) -> {S.rounds.text(left, max) == StSpec.round_text(left, max) : String}:
  match left:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def stb.round_at(near: Bool, +left: Nat, +max: Nat) -> {S.rounds.at(near, left, max) == StSpec.round_at(near, left, max) : Maybe<&2, String>}:
  match near:
    case True{}:
      Equal.cong(String, Maybe<&2, String>, z => Some{z}, S.rounds.text(left, max), StSpec.round_text(left, max), stb.round_text(left, max))
    case False{}:
      {==}

# the round note after any rounds of any cap is the spec's
def stb.rounds(+m: Nat, +d: Nat) -> {S.rounds(m, d) == StSpec.rounds(m, d) : Maybe<&2, String>}:
  +l = Nat.sub(Nat.sub(m, 1n), d)
  stb.round_at(Nat.is_le(l, 10n), l, m)

# the entry's answer to a request is the spelled spec answer
def stb.reply(q: FS.Ask) -> {FS.answer(q) == Stop.sp_w_reply(q) : String}:
  match q:
    case FS.AskWalk{+f}:
      %Equal.sym(S.Pick, S.walk(f), StSpec.pick(f), stb.walk(f)) : {FS.put_pick(_, "") == Stop.sp_w_reply(FS.AskWalk{f}) : String}
      stb.w_pick(StSpec.pick(f))
    case FS.AskNote{+a, +n}:
      Equal.cong(String, String, z => Wr.put_str(z, ""), S.note(a, n), StSpec.note(a, n), stb.note_text(a, n))
    case FS.AskRounds{+m, +d}:
      %Equal.sym(Maybe<&2, String>, S.rounds(m, d), StSpec.rounds(m, d), stb.rounds(m, d)) : {FS.put_text(_, "") == Stop.sp_w_reply(FS.AskRounds{m, d}) : String}
      stb.w_round(StSpec.rounds(m, d))

# The ladder
# ----------

# the model's test of a row under the cap is Nat's
def stb.below(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == RnRecovery.below(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      stb.below(p, q)

# a row at the cap is not under it
def stb.eq_not_below(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {RnRecovery.below(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      stb.absurd({RnRecovery.below(0n, 1n+q) == False{} : Bool}, h)
    case 1n+p 0n:
      stb.absurd({RnRecovery.below(1n+p, 0n) == False{} : Bool}, h)
    case 1n+p 1n+q:
      stb.eq_not_below(p, q, h)

# a row one past the cap is neither under it nor at it
def stb.succ_not_below(+m: Nat) -> {RnRecovery.below(1n+m, m) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      stb.succ_not_below(q)

def stb.succ_not_eq(+m: Nat) -> {Nat.is_eq(1n+m, m) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      stb.succ_not_eq(q)

# a rung that remains never fails the run
def stb.think_left(s: Bool, u: Bool, l: Bool, -x: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec, h: {Bool.or(s, Bool.or(u, l)) == True{} : Bool}) -> {Stop.quits(RnRecovery.Dec.act(RnRecovery.rec.think(s, u, l, x, same, last, r))) == False{} : Bool}:
  match s:
    case True{}:
      {==}
    case False{}:
      match u:
        case True{}:
          {==}
        case False{}:
          match l:
            case True{}:
              {==}
            case False{}:
              stb.absurd({Stop.quits(RnRecovery.Dec.act(RnRecovery.rec.think(False{}, False{}, False{}, x, same, last, r))) == False{} : Bool}, h)

# with every rung spent the run fails, the row as it was
def stb.think_spent(s: Bool, u: Bool, l: Bool, -x: Nat, -same: Nat, -last: Nat, +r: RnRecovery.Rec, h: {Bool.or(s, Bool.or(u, l)) == False{} : Bool}) -> {RnRecovery.rec.think(s, u, l, x, same, last, r) == RnRecovery.Dec{RnRecovery.Quit{}, r} : RnRecovery.Dec}:
  match s:
    case True{}:
      stb.absurd({RnRecovery.rec.think(True{}, u, l, x, same, last, r) == RnRecovery.Dec{RnRecovery.Quit{}, r} : RnRecovery.Dec}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      match u:
        case True{}:
          stb.absurd({RnRecovery.rec.think(False{}, True{}, l, x, same, last, r) == RnRecovery.Dec{RnRecovery.Quit{}, r} : RnRecovery.Dec}, Equal.sym(Bool, True{}, False{}, h))
        case False{}:
          match l:
            case True{}:
              stb.absurd({RnRecovery.rec.think(False{}, False{}, True{}, x, same, last, r) == RnRecovery.Dec{RnRecovery.Quit{}, r} : RnRecovery.Dec}, Equal.sym(Bool, True{}, False{}, h))
            case False{}:
              {==}
