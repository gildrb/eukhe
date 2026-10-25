# eukhe: lemmas the proofs of area wait share

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ../../laws/wire.bend as Wire
import ../../laws/base.bend as LawsBase

# ---- wait ----

# proof_wait: the wait laws of LAWS.bend (H6): a wait ends exactly once,
# no later than its deadline or its cancel, and with the event when the
# event comes first. Each lemma speaks of an open wait whose deadline
# passes on the (m + 1)-th tick (`pw.up` names that deadline in ticks
# from now), by induction on the signals it sees.

# Logic
# -----

def pw.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pw.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pw.BD(_, Unit, A)
  Unit{}

def pw.or_true(a: Bool) -> {True{} == Bool.or(a, True{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pw.le0(t: Nat) -> {True{} == Nat.is_le(0n, t) : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

# a deadline of 0 ticks is reached, whatever came
def pw.reached0(+a: Bool, +c: Bool, t: Nat) -> {True{} == Bool.or(a, Bool.or(c, Nat.is_le(0n, t))) : Bool}:
  %pw.le0(t) : {True{} == Bool.or(a, Bool.or(c, _)) : Bool}
  %pw.or_true(c) : {True{} == Bool.or(a, _) : Bool}
  pw.or_true(a)

# the deadline, in ticks from now, of an open wait
def pw.up(l: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match l:
    case None{}:
      None{}
    case Some{m}:
      Some{1n+m}

# an ended wait reports nothing more
def pw.over(xs: List<&2, Wt.Sig>) -> {Nil{} == Wt.go(xs, Wt.Over{}) : List<&2, Wt.End>}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      pw.over(rest)

# The stepper (bend/ffi_wait_race.bend)
# -------------------------------------
# The stepper reads every input as the laws' readers do (`ww.read`,
# `ww.read_dl`); a spelled poll runs the model's poll (`ws.spelled`),
# whose signals, wait after and spelled ends are the laws' (`ws.sigs`,
# `ws.after`, `ws.ends`). Over any polls, the stepper's wait is the
# model's wait after their signals (`ws.feed`), and its replies are the
# model's run cut at each poll (`ws.model`).

def ww.late(w: Bool, c: Bool, r: Wr.Dec<Bool>) -> {WaitLaws.ww_read.late(w, c, r) == FWt.get_ready.late(w, c, r) : Wr.Dec<Wt.Polled>}:
  match r:
    case Wr.Got{l, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ww.cancel(w: Bool, r: Wr.Dec<Bool>) -> {WaitLaws.ww_read.cancel(w, r) == FWt.get_ready.cancel(w, r) : Wr.Dec<Wt.Polled>}:
  match r:
    case Wr.Got{c, s}:
      ww.late(w, c, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

# the entry reads every poll as the laws' reader does
def ww.read(r: Wr.Dec<Bool>) -> {WaitLaws.ww_read.go(r) == FWt.get_ready.go(r) : Wr.Dec<Wt.Polled>}:
  match r:
    case Wr.Got{w, s}:
      ww.cancel(w, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ww.some(r: Wr.Dec<Nat>) -> {WaitLaws.ww_read_dl.some(r) == FWt.get_dl.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{d, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ww.tag(t: Nat, s: String) -> {WaitLaws.ww_read_dl.tag(t, s) == FWt.get_dl.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      match q:
        case 0n:
          ww.some(Wr.get_nat(s))
        case 1n+p:
          {==}

# the entry reads every open as the laws' reader does
def ww.read_dl(r: Wr.Dec<Nat>) -> {WaitLaws.ww_read_dl.go(r) == FWt.get_dl.go(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      ww.tag(t, s)
    case Wr.Bad{}:
      {==}

def ww.MD(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def ww.none_some(-A: Data, -G: Type, -r: A, h: {None{} == Some{r} : Maybe<&2, A>}) -> G:
  %h : ww.MD(A, _, G)
  Unit{}

def ww.get(-A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def ww.some_inj(-A: Data, +a: A, +b: A, h: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => ww.get(A, m, a), Some{a}, Some{b}, h)

def ws.LD(xs: List<&2, Wt.End>, G: Type) -> Type:
  match xs:
    case Nil{}:
      Unit
    case e <> t:
      G

# Nil is not a cons
def ws.nil_cons(-G: Type, -e: Wt.End, -t: List<&2, Wt.End>, h: {Nil{} == e <> t : List<&2, Wt.End>}) -> G:
  %h : ws.LD(_, G)
  Unit{}

def ws.app_assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %ws.app_assoc(A, rest, ys, zs) : {x <> List.append(&2, A, List.append(&2, A, rest, ys), zs) == x <> _ : List<&2, A>}
      {==}

# The model's poll, as the laws spell it
# ---------------------------------------

def ws.when(b: Bool, x: Wt.Sig, rest: List<&2, Wt.Sig>) -> {WaitLaws.ww_sig(b, x, rest) == Wt.sig.when(b, x, rest) : List<&2, Wt.Sig>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a poll's signals are the laws'
def ws.sigs(r: Wt.Polled) -> {WaitLaws.ww_sigs(r) == Wt.sigs(r) : List<&2, Wt.Sig>}:
  match r:
    case Wt.Polled{w, c, l}:
      match w c l:
        case True{} True{} True{}:
          {==}
        case True{} True{} False{}:
          {==}
        case True{} False{} True{}:
          {==}
        case True{} False{} False{}:
          {==}
        case False{} True{} True{}:
          {==}
        case False{} True{} False{}:
          {==}
        case False{} False{} True{}:
          {==}
        case False{} False{} False{}:
          {==}

# the wait after signals is the laws'
def ws.after(xs: List<&2, Wt.Sig>, w: Wt.W) -> {WaitLaws.ww_after(xs, w) == Wt.after(xs, w) : Wt.W}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      ws.after(rest, Wt.next(w, s))

def ws.pair(+n: Nat, e: Wt.End, +x: String) -> {(1n+n, WaitLaws.ww_spell_end(e, x)) == (1n+n, FWt.put_end(e, x)) : Nat & String}:
  match e:
    case Wt.Arrived{}:
      {==}
    case Wt.Expired{}:
      {==}
    case Wt.Cancelled{}:
      {==}

def ws.items(es: List<&2, Wt.End>) -> {(List.length(&2, Wt.End, es), WaitLaws.ww_spell_ends.items(es)) == Wr.put_list.go(~Wt.End, ~FWt.put_end, es, "") : Nat & String}:
  match es:
    case Nil{}:
      {==}
    case e <> +t:
      %ws.items(t) : {(1n+List.length(&2, Wt.End, t), WaitLaws.ww_spell_end(e, WaitLaws.ww_spell_ends.items(t))) == Wr.put_list.step(~Wt.End, ~FWt.put_end, e, _) : Nat & String}
      ws.pair(List.length(&2, Wt.End, t), e, WaitLaws.ww_spell_ends.items(t))

# the stepper spells ends as the laws do
def ws.ends(es: List<&2, Wt.End>) -> {WaitLaws.ww_spell_ends(es) == FWt.put_ends(es) : String}:
  %ws.items(es) : {WaitLaws.ww_spell_ends(es) == Wr.put_list.fin(_) : String}
  {==}

# a spelled poll is read whole: the stepper runs the model's poll
def ws.spelled(w: Wt.W, r: Wt.Polled) -> {FWt.step.reply(Wt.race(w, r)) == FWt.step(FWt.Live{w}, WaitLaws.ww_spell(r)) : FWt.St & String}:
  match r:
    case Wt.Polled{a, c, l}:
      match a c l:
        case True{} True{} True{}:
          {==}
        case True{} True{} False{}:
          {==}
        case True{} False{} True{}:
          {==}
        case True{} False{} False{}:
          {==}
        case False{} True{} True{}:
          {==}
        case False{} True{} False{}:
          {==}
        case False{} False{} True{}:
          {==}
        case False{} False{} False{}:
          {==}

# one spelled poll moves the wait as the model does and answers the
# spelled ends of the model's walk
def ws.step(+w: Wt.W, +r: Wt.Polled) -> {(FWt.Live{WaitLaws.ww_after(WaitLaws.ww_sigs(r), w)}, WaitLaws.ww_spell_ends(Wt.go(WaitLaws.ww_sigs(r), w))) == FWt.step(FWt.Live{w}, WaitLaws.ww_spell(r)) : FWt.St & String}:
  %ws.spelled(w, r) : {(FWt.Live{WaitLaws.ww_after(WaitLaws.ww_sigs(r), w)}, WaitLaws.ww_spell_ends(Wt.go(WaitLaws.ww_sigs(r), w))) == _ : FWt.St & String}
  %ws.sigs(r) : {(FWt.Live{WaitLaws.ww_after(WaitLaws.ww_sigs(r), w)}, WaitLaws.ww_spell_ends(Wt.go(WaitLaws.ww_sigs(r), w))) == (FWt.Live{Wt.after(_, w)}, FWt.put_ends(Wt.go(_, w))) : FWt.St & String}
  %ws.after(WaitLaws.ww_sigs(r), w) : {(FWt.Live{WaitLaws.ww_after(WaitLaws.ww_sigs(r), w)}, WaitLaws.ww_spell_ends(Wt.go(WaitLaws.ww_sigs(r), w))) == (FWt.Live{_}, FWt.put_ends(Wt.go(WaitLaws.ww_sigs(r), w))) : FWt.St & String}
  %ws.ends(Wt.go(WaitLaws.ww_sigs(r), w)) : {(FWt.Live{WaitLaws.ww_after(WaitLaws.ww_sigs(r), w)}, WaitLaws.ww_spell_ends(Wt.go(WaitLaws.ww_sigs(r), w))) == (FWt.Live{WaitLaws.ww_after(WaitLaws.ww_sigs(r), w)}, _) : FWt.St & String}
  {==}

# a spelled deadline that fits is read whole
def ws.open_spelled(+dl: Maybe<&2, Nat>, fits: {LawsBase.wire_mfits(dl) == True{} : Bool}) -> {FWt.open.end(True{}, dl) == FWt.open(WaitLaws.ww_spell_dl(dl)) : FWt.St & String}:
  match dl:
    case None{}:
      {==}
    case Some{d}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(d, "")), Wr.Got{d, ""}, Wire.wire_nat_round_trip(d, "", fits)) : {FWt.open.end(True{}, Some{d}) == FWt.open.dl(FWt.get_dl.some(_)) : FWt.St & String}
      {==}

# the stepper opened with a spelled deadline that fits is the model's wait
# at its start
def ws.opened(+dl: Maybe<&2, Nat>, fits: {LawsBase.wire_mfits(dl) == True{} : Bool}) -> {FWt.Live{Wt.start(dl)} == WaitLaws.ww_opened(dl) : FWt.St}:
  %ws.open_spelled(dl, fits) : {FWt.Live{Wt.start(dl)} == WaitLaws.ww_state(_) : FWt.St}
  {==}

# The model's run, cut at a poll
# -------------------------------

# an ended wait stays ended
def ws.over(xs: List<&2, Wt.Sig>) -> {Wt.Over{} == WaitLaws.ww_after(xs, Wt.Over{}) : Wt.W}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      ws.over(rest)

# a walk that reported an end leaves the wait ended
def ws.ended(xs: List<&2, Wt.Sig>, w: Wt.W, -e: Wt.End, -t: List<&2, Wt.End>, h: {Wt.go(xs, w) == e <> t : List<&2, Wt.End>}) -> {Wt.Over{} == WaitLaws.ww_after(xs, w) : Wt.W}:
  match xs:
    case Nil{}:
      ws.nil_cons({Wt.Over{} == w : Wt.W}, e, t, h)
    case s <> rest:
      match s:
        case Wt.Arrive{}:
          match w:
            case Wt.Over{}:
              ws.over(rest)
            case Wt.Open{l}:
              ws.over(rest)
        case Wt.Cancel{}:
          match w:
            case Wt.Over{}:
              ws.over(rest)
            case Wt.Open{l}:
              ws.over(rest)
        case Wt.Tick{}:
          match w:
            case Wt.Over{}:
              ws.over(rest)
            case Wt.Open{l}:
              match l:
                case None{}:
                  ws.ended(rest, Wt.Open{None{}}, e, t, h)
                case Some{m}:
                  match m:
                    case 0n:
                      ws.over(rest)
                    case 1n+q:
                      ws.ended(rest, Wt.Open{Some{q}}, e, t, h)

# a run that reported an end leaves the wait ended
def ws.run_ended(dl: Maybe<&2, Nat>, xs: List<&2, Wt.Sig>, -e: Wt.End, -t: List<&2, Wt.End>, h: {Wt.run(dl, xs) == e <> t : List<&2, Wt.End>}) -> {Wt.Over{} == WaitLaws.ww_after(xs, Wt.start(dl)) : Wt.W}:
  match dl:
    case None{}:
      ws.ended(xs, Wt.Open{None{}}, e, t, h)
    case Some{d}:
      match d:
        case 0n:
          ws.over(xs)
        case 1n+m:
          ws.ended(xs, Wt.Open{Some{m}}, e, t, h)

# the walk over xs then ys: the ends over xs, then over ys from the wait
# after xs
def ws.go_app(xs: List<&2, Wt.Sig>, +ys: List<&2, Wt.Sig>, +w: Wt.W) -> {List.append(&2, Wt.End, Wt.go(xs, w), Wt.go(ys, WaitLaws.ww_after(xs, w))) == Wt.go(List.append(&2, Wt.Sig, xs, ys), w) : List<&2, Wt.End>}:
  match xs:
    case Nil{}:
      {==}
    case +s <> +rest:
      %ws.go_app(rest, ys, Wt.next(w, s)) : {List.append(&2, Wt.End, List.append(&2, Wt.End, Wt.out(w, s), Wt.go(rest, Wt.next(w, s))), Wt.go(ys, WaitLaws.ww_after(rest, Wt.next(w, s)))) == List.append(&2, Wt.End, Wt.out(w, s), _) : List<&2, Wt.End>}
      ws.app_assoc(Wt.End, Wt.out(w, s), Wt.go(rest, Wt.next(w, s)), Wt.go(ys, WaitLaws.ww_after(rest, Wt.next(w, s))))

# the run over xs then ys: the run over xs, then the walk over ys from the
# wait after xs
def ws.run_app(+dl: Maybe<&2, Nat>, xs: List<&2, Wt.Sig>, +ys: List<&2, Wt.Sig>) -> {List.append(&2, Wt.End, Wt.run(dl, xs), Wt.go(ys, WaitLaws.ww_after(xs, Wt.start(dl)))) == Wt.run(dl, List.append(&2, Wt.Sig, xs, ys)) : List<&2, Wt.End>}:
  match dl:
    case None{}:
      ws.go_app(xs, ys, Wt.Open{None{}})
    case Some{d}:
      match d:
        case 0n:
          %ws.over(xs) : {List.append(&2, Wt.End, [Wt.Expired{}], Wt.go(ys, _)) == [Wt.Expired{}] : List<&2, Wt.End>}
          %pw.over(ys) : {List.append(&2, Wt.End, [Wt.Expired{}], _) == [Wt.Expired{}] : List<&2, Wt.End>}
          {==}
        case 1n+m:
          ws.go_app(xs, ys, Wt.Open{Some{m}})

# the signals of the polls xs then ys
def ws.flat_app(xs: List<&2, Wt.Polled>, +ys: List<&2, Wt.Polled>) -> {List.append(&2, Wt.Sig, WaitLaws.ww_flat(xs), WaitLaws.ww_flat(ys)) == WaitLaws.ww_flat(List.append(&2, Wt.Polled, xs, ys)) : List<&2, Wt.Sig>}:
  match xs:
    case Nil{}:
      {==}
    case +p <> +rest:
      %ws.flat_app(rest, ys) : {List.append(&2, Wt.Sig, List.append(&2, Wt.Sig, WaitLaws.ww_sigs(p), WaitLaws.ww_flat(rest)), WaitLaws.ww_flat(ys)) == List.append(&2, Wt.Sig, WaitLaws.ww_sigs(p), _) : List<&2, Wt.Sig>}
      ws.app_assoc(Wt.Sig, WaitLaws.ww_sigs(p), WaitLaws.ww_flat(rest), WaitLaws.ww_flat(ys))

# the wait after xs then ys
def ws.after_app(xs: List<&2, Wt.Sig>, -ys: List<&2, Wt.Sig>, w: Wt.W) -> {WaitLaws.ww_after(ys, WaitLaws.ww_after(xs, w)) == WaitLaws.ww_after(List.append(&2, Wt.Sig, xs, ys), w) : Wt.W}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      ws.after_app(rest, ys, Wt.next(w, s))

# the stepper sent spelled polls holds the model's wait after their
# signals
def ws.feed(ps: List<&2, Wt.Polled>, +w: Wt.W) -> {FWt.Live{WaitLaws.ww_after(WaitLaws.ww_flat(ps), w)} == WaitLaws.ww_feed(ps, FWt.Live{w}) : FWt.St}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      %ws.step(w, p) : {FWt.Live{WaitLaws.ww_after(WaitLaws.ww_flat(p <> rest), w)} == WaitLaws.ww_feed(rest, WaitLaws.ww_state(_)) : FWt.St}
      %ws.after_app(WaitLaws.ww_sigs(p), WaitLaws.ww_flat(rest), w) : {FWt.Live{_} == WaitLaws.ww_feed(rest, FWt.Live{WaitLaws.ww_after(WaitLaws.ww_sigs(p), w)}) : FWt.St}
      ws.feed(rest, WaitLaws.ww_after(WaitLaws.ww_sigs(p), w))

# the walk over ys after the run over xs, as ww_new cuts it
def ws.pick(+dl: Maybe<&2, Nat>, +xs: List<&2, Wt.Sig>, r: List<&2, Wt.End>, +ys: List<&2, Wt.Sig>, h: {Wt.run(dl, xs) == r : List<&2, Wt.End>}) -> {Wt.go(ys, WaitLaws.ww_after(xs, Wt.start(dl))) == WaitLaws.ww_new.go(r, List.append(&2, Wt.End, r, Wt.go(ys, WaitLaws.ww_after(xs, Wt.start(dl))))) : List<&2, Wt.End>}:
  match r:
    case Nil{}:
      {==}
    case +e <> +t:
      %ws.run_ended(dl, xs, e, t, h) : {Wt.go(ys, _) == Nil{} : List<&2, Wt.End>}
      Equal.sym(List<&2, Wt.End>, Nil{}, Wt.go(ys, Wt.Over{}), pw.over(ys))

# The stepper opened with any deadline that fits and sent any polls
# answers each poll with the model's run cut at it
def ws.model(+dl: Maybe<&2, Nat>, +pre: List<&2, Wt.Polled>, +p: Wt.Polled, fits: {LawsBase.wire_mfits(dl) == True{} : Bool}) -> {WaitLaws.ww_reply(FWt.step(WaitLaws.ww_feed(pre, WaitLaws.ww_opened(dl)), WaitLaws.ww_spell(p))) == WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, pre, p)) : String}:
  %ws.opened(dl, fits) : {WaitLaws.ww_reply(FWt.step(WaitLaws.ww_feed(pre, _), WaitLaws.ww_spell(p))) == WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, pre, p)) : String}
  %ws.feed(pre, Wt.start(dl)) : {WaitLaws.ww_reply(FWt.step(_, WaitLaws.ww_spell(p))) == WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, pre, p)) : String}
  %ws.step(WaitLaws.ww_after(WaitLaws.ww_flat(pre), Wt.start(dl)), p) : {WaitLaws.ww_reply(_) == WaitLaws.ww_spell_ends(WaitLaws.ww_new(dl, pre, p)) : String}
  %ws.run_app(dl, WaitLaws.ww_flat(pre), WaitLaws.ww_sigs(p)) : {WaitLaws.ww_spell_ends(Wt.go(WaitLaws.ww_sigs(p), WaitLaws.ww_after(WaitLaws.ww_flat(pre), Wt.start(dl)))) == WaitLaws.ww_spell_ends(WaitLaws.ww_new.go(Wt.run(dl, WaitLaws.ww_flat(pre)), _)) : String}
  Equal.cong(List<&2, Wt.End>, String, es => WaitLaws.ww_spell_ends(es), Wt.go(WaitLaws.ww_sigs(p), WaitLaws.ww_after(WaitLaws.ww_flat(pre), Wt.start(dl))), WaitLaws.ww_new.go(Wt.run(dl, WaitLaws.ww_flat(pre)), List.append(&2, Wt.End, Wt.run(dl, WaitLaws.ww_flat(pre)), Wt.go(WaitLaws.ww_sigs(p), WaitLaws.ww_after(WaitLaws.ww_flat(pre), Wt.start(dl))))), ws.pick(dl, WaitLaws.ww_flat(pre), Wt.run(dl, WaitLaws.ww_flat(pre)), WaitLaws.ww_sigs(p), {==}))
