# eukhe: lemmas the proofs of area once share: the entry
#
# A spelled event is read whole: the stepper runs the event on the life
# (oe.spelled; a keyed policy's cap reads back by the wire's round trip).
# The replies are spelled as Rust reads them (oe.put_life,
# oe.put_verdict). From the life a journal tells, every reply is the
# spec's for the records read so far (oe.model). The entry reads every
# input as the laws' reader does (oe.read), and every cap that reader
# answers fits the wire (oe.fit_go). Two spelled strings that are equal
# spell the same string before the same rest (oe.str_inj).

import Base
import ../../../bend/once.bend as O
import ../../../bend/ffi_once.bend as FO
import ../../../bend/wire.bend as Wr
import ../../../laws/once.bend as Once
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../spec/once/life.bend as S
import ../base.bend as LA
import ../../base/wire.bend as PBaseWire
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../once_life_is_spec.bend as POnceLifeIsSpec
import ../once_recover_is_spec.bend as POnceRecoverIsSpec

# A spelled event
# ---------------

# a question with a keyed policy: its cap reads back
def oe.keyed(-l: O.Life, m: O.Mode, s: O.Seen, +cap: Nat, fit: {LawsBase.wire_fits(cap) == True{} : Bool}) -> {FO.step(FO.Eff{l}, Once.on_spell(FO.Ask{m, O.Keyed{cap}, s})) == FO.step.ev(FO.Ask{m, O.Keyed{cap}, s}, l) : FO.St & String}:
  match m:
    case O.Resume{}:
      match s:
        case O.Dark{}:
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(cap, "0,")), Wr.Got{cap, "0,"}, Wire.wire_nat_round_trip(cap, "0,", fit)) : {FO.step.got(FO.get_ev.policy(O.Resume{}, FO.get_policy.cap(_)), l) == FO.step.ev(FO.Ask{O.Resume{}, O.Keyed{cap}, O.Dark{}}, l) : FO.St & String}
          {==}
        case O.Landed{}:
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(cap, "1,")), Wr.Got{cap, "1,"}, Wire.wire_nat_round_trip(cap, "1,", fit)) : {FO.step.got(FO.get_ev.policy(O.Resume{}, FO.get_policy.cap(_)), l) == FO.step.ev(FO.Ask{O.Resume{}, O.Keyed{cap}, O.Landed{}}, l) : FO.St & String}
          {==}
        case O.Clean{}:
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(cap, "2,")), Wr.Got{cap, "2,"}, Wire.wire_nat_round_trip(cap, "2,", fit)) : {FO.step.got(FO.get_ev.policy(O.Resume{}, FO.get_policy.cap(_)), l) == FO.step.ev(FO.Ask{O.Resume{}, O.Keyed{cap}, O.Clean{}}, l) : FO.St & String}
          {==}
    case O.Stop{}:
      match s:
        case O.Dark{}:
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(cap, "0,")), Wr.Got{cap, "0,"}, Wire.wire_nat_round_trip(cap, "0,", fit)) : {FO.step.got(FO.get_ev.policy(O.Stop{}, FO.get_policy.cap(_)), l) == FO.step.ev(FO.Ask{O.Stop{}, O.Keyed{cap}, O.Dark{}}, l) : FO.St & String}
          {==}
        case O.Landed{}:
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(cap, "1,")), Wr.Got{cap, "1,"}, Wire.wire_nat_round_trip(cap, "1,", fit)) : {FO.step.got(FO.get_ev.policy(O.Stop{}, FO.get_policy.cap(_)), l) == FO.step.ev(FO.Ask{O.Stop{}, O.Keyed{cap}, O.Landed{}}, l) : FO.St & String}
          {==}
        case O.Clean{}:
          %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(cap, "2,")), Wr.Got{cap, "2,"}, Wire.wire_nat_round_trip(cap, "2,", fit)) : {FO.step.got(FO.get_ev.policy(O.Stop{}, FO.get_policy.cap(_)), l) == FO.step.ev(FO.Ask{O.Stop{}, O.Keyed{cap}, O.Clean{}}, l) : FO.St & String}
          {==}

# a question with the policy never: no number to read
def oe.never(-l: O.Life, m: O.Mode, s: O.Seen) -> {FO.step(FO.Eff{l}, Once.on_spell(FO.Ask{m, O.Never{}, s})) == FO.step.ev(FO.Ask{m, O.Never{}, s}, l) : FO.St & String}:
  match m:
    case O.Resume{}:
      match s:
        case O.Dark{}:
          {==}
        case O.Landed{}:
          {==}
        case O.Clean{}:
          {==}
    case O.Stop{}:
      match s:
        case O.Dark{}:
          {==}
        case O.Landed{}:
          {==}
        case O.Clean{}:
          {==}

# a question with the policy safe: no number to read
def oe.safe(-l: O.Life, m: O.Mode, s: O.Seen) -> {FO.step(FO.Eff{l}, Once.on_spell(FO.Ask{m, O.Safe{}, s})) == FO.step.ev(FO.Ask{m, O.Safe{}, s}, l) : FO.St & String}:
  match m:
    case O.Resume{}:
      match s:
        case O.Dark{}:
          {==}
        case O.Landed{}:
          {==}
        case O.Clean{}:
          {==}
    case O.Stop{}:
      match s:
        case O.Dark{}:
          {==}
        case O.Landed{}:
          {==}
        case O.Clean{}:
          {==}

# a spelled event is read whole: the stepper runs the event on the life
def oe.spelled(-l: O.Life, e: FO.Ev, fit: {Once.on_fit.ev(e) == True{} : Bool}) -> {FO.step(FO.Eff{l}, Once.on_spell(e)) == FO.step.ev(e, l) : FO.St & String}:
  match e:
    case FO.Note{r}:
      match r:
        case O.Intended{}:
          {==}
        case O.Started{}:
          {==}
        case O.Finished{}:
          {==}
        case O.Unknown{}:
          {==}
        case O.Unstarted{}:
          {==}
    case FO.Ask{m, p, s}:
      match p:
        case O.Never{}:
          oe.never(l, m, s)
        case O.Safe{}:
          oe.safe(l, m, s)
        case O.Keyed{cap}:
          oe.keyed(l, m, s, cap, fit)

# The replies
# -----------

# a life is answered as Rust reads it
def oe.put_life(l: O.Life) -> {FO.put_life(l) == Once.on_spell_life(l) : String}:
  match l:
    case O.Absent{}:
      {==}
    case O.Pending{}:
      {==}
    case O.Running{again}:
      {==}
    case O.Ran{}:
      {==}
    case O.Lost{}:
      {==}
    case O.Void{}:
      {==}

# a verdict is answered as Rust reads it
def oe.put_verdict(v: O.Verdict) -> {FO.put_verdict(v) == Once.on_spell_verdict(v) : String}:
  match v:
    case O.Skip{}:
      {==}
    case O.Launch{}:
      {==}
    case O.Adopt{}:
      {==}
    case O.Interrupt{}:
      {==}
    case O.Abandon{}:
      {==}
    case O.Settled{}:
      {==}

# the reply to a record: the spec's life of the records read
def oe.life_reply(+j: List<&2, O.Rec>) -> {FO.put_life(O.life(j)) == Once.on_spell_life(S.life_spec(j)) : String}:
  %Once.once_life_is_spec(j) : {FO.put_life(O.life(j)) == Once.on_spell_life(_) : String}
  oe.put_life(O.life(j))

# the reply to a question: the spec's verdict for the records read
def oe.verdict_reply(+j: List<&2, O.Rec>, +s: O.Seen, +m: O.Mode, +p: O.Policy) -> {FO.put_verdict(O.recover(O.life(j), s, m, p)) == Once.on_spell_verdict(S.verdict_spec(S.life_spec(j), s, m, p)) : String}:
  %Once.once_life_is_spec(j) : {FO.put_verdict(O.recover(O.life(j), s, m, p)) == Once.on_spell_verdict(S.verdict_spec(_, s, m, p)) : String}
  %Once.once_recover_is_spec(O.life(j), s, m, p) : {FO.put_verdict(O.recover(O.life(j), s, m, p)) == Once.on_spell_verdict(_) : String}
  oe.put_verdict(O.recover(O.life(j), s, m, p))

# two equal heads before two equal tails
def oe.cons(-a: String, -b: String, -x: List<&2, String>, -y: List<&2, String>, e1: {a == b : String}, e2: {x == y : List<&2, String>}) -> {a <> x == b <> y : List<&2, String>}:
  %e2 : {a <> x == b <> _ : List<&2, String>}
  %e1 : {a <> x == _ <> x : List<&2, String>}
  {==}

# from the life the records j tell, every reply of the stepper is the
# spec's for the records read so far
def oe.model(es: List<&2, FO.Ev>, +j: List<&2, O.Rec>, +fits: {Once.on_fit(es) == True{} : Bool}) -> {Once.on_replies(es, FO.Eff{O.life(j)}) == Once.on_spec(es, j) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case FO.Note{+r}:
          %Equal.sym(FO.St & String, FO.step(FO.Eff{O.life(j)}, Once.on_spell(FO.Note{r})), FO.step.ev(FO.Note{r}, O.life(j)), oe.spelled(O.life(j), FO.Note{r}, {==})) : {Once.on_reply(_) <> Once.on_replies(rest, Once.on_state(_)) == Once.on_spell_life(S.life_spec(List.append(&2, O.Rec, j, [r]))) <> Once.on_spec(rest, List.append(&2, O.Rec, j, [r])) : List<&2, String>}
          %LA.ob.go_snoc(j, r) : {FO.put_life(_) <> Once.on_replies(rest, FO.Eff{_}) == Once.on_spell_life(S.life_spec(List.append(&2, O.Rec, j, [r]))) <> Once.on_spec(rest, List.append(&2, O.Rec, j, [r])) : List<&2, String>}
          oe.cons(FO.put_life(O.life(List.append(&2, O.Rec, j, [r]))), Once.on_spell_life(S.life_spec(List.append(&2, O.Rec, j, [r]))), Once.on_replies(rest, FO.Eff{O.life(List.append(&2, O.Rec, j, [r]))}), Once.on_spec(rest, List.append(&2, O.Rec, j, [r])), oe.life_reply(List.append(&2, O.Rec, j, [r])), oe.model(rest, List.append(&2, O.Rec, j, [r]), fits))
        case FO.Ask{+m, +p, +s}:
          %Equal.sym(FO.St & String, FO.step(FO.Eff{O.life(j)}, Once.on_spell(FO.Ask{m, p, s})), FO.step.ev(FO.Ask{m, p, s}, O.life(j)), oe.spelled(O.life(j), FO.Ask{m, p, s}, LA.ob.and_l(Once.on_fit.policy(p), Once.on_fit(rest), fits))) : {Once.on_reply(_) <> Once.on_replies(rest, Once.on_state(_)) == Once.on_spell_verdict(S.verdict_spec(S.life_spec(j), s, m, p)) <> Once.on_spec(rest, j) : List<&2, String>}
          oe.cons(FO.put_verdict(O.recover(O.life(j), s, m, p)), Once.on_spell_verdict(S.verdict_spec(S.life_spec(j), s, m, p)), Once.on_replies(rest, FO.Eff{O.life(j)}), Once.on_spec(rest, j), oe.verdict_reply(j, s, m, p), oe.model(rest, j, LA.ob.and_r(Once.on_fit.policy(p), Once.on_fit(rest), fits)))

# The laws' reader
# ----------------

def oe.rd_rec_tag(n: Nat, s: String) -> {Once.on_read_rec.tag(n, s) == FO.get_rec.tag(n, s) : Wr.Dec<O.Rec>}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n+p:
      {==}

def oe.rd_rec(r: Wr.Dec<Nat>) -> {Once.on_read_rec(r) == FO.get_rec.go(r) : Wr.Dec<O.Rec>}:
  match r:
    case Wr.Got{n, s}:
      oe.rd_rec_tag(n, s)
    case Wr.Bad{}:
      {==}

def oe.rd_mode_tag(n: Nat, s: String) -> {Once.on_read_mode.tag(n, s) == FO.get_mode.tag(n, s) : Wr.Dec<O.Mode>}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def oe.rd_mode(r: Wr.Dec<Nat>) -> {Once.on_read_mode(r) == FO.get_mode.go(r) : Wr.Dec<O.Mode>}:
  match r:
    case Wr.Got{n, s}:
      oe.rd_mode_tag(n, s)
    case Wr.Bad{}:
      {==}

def oe.rd_policy_cap(r: Wr.Dec<Nat>) -> {Once.on_read_policy.cap(r) == FO.get_policy.cap(r) : Wr.Dec<O.Policy>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def oe.rd_policy_tag(n: Nat, s: String) -> {Once.on_read_policy.tag(n, s) == FO.get_policy.tag(n, s) : Wr.Dec<O.Policy>}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      oe.rd_policy_cap(Wr.get_nat(s))
    case 3n+p:
      {==}

def oe.rd_policy(r: Wr.Dec<Nat>) -> {Once.on_read_policy(r) == FO.get_policy.go(r) : Wr.Dec<O.Policy>}:
  match r:
    case Wr.Got{n, s}:
      oe.rd_policy_tag(n, s)
    case Wr.Bad{}:
      {==}

def oe.rd_seen_tag(n: Nat, s: String) -> {Once.on_read_seen.tag(n, s) == FO.get_seen.tag(n, s) : Wr.Dec<O.Seen>}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+p:
      {==}

def oe.rd_seen(r: Wr.Dec<Nat>) -> {Once.on_read_seen(r) == FO.get_seen.go(r) : Wr.Dec<O.Seen>}:
  match r:
    case Wr.Got{n, s}:
      oe.rd_seen_tag(n, s)
    case Wr.Bad{}:
      {==}

def oe.rd_note(r: Wr.Dec<O.Rec>) -> {Once.on_read.note(r) == FO.get_ev.note(r) : Wr.Dec<FO.Ev>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def oe.rd_ask_seen(-m: O.Mode, -p: O.Policy, r: Wr.Dec<O.Seen>) -> {Once.on_read.seen(m, p, r) == FO.get_ev.seen(m, p, r) : Wr.Dec<FO.Ev>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def oe.rd_ask_policy(-m: O.Mode, r: Wr.Dec<O.Policy>) -> {Once.on_read.policy(m, r) == FO.get_ev.policy(m, r) : Wr.Dec<FO.Ev>}:
  match r:
    case Wr.Got{p, +s}:
      %oe.rd_seen(Wr.get_nat(s)) : {Once.on_read.seen(m, p, Once.on_read_seen(Wr.get_nat(s))) == FO.get_ev.seen(m, p, _) : Wr.Dec<FO.Ev>}
      oe.rd_ask_seen(m, p, Once.on_read_seen(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def oe.rd_ask_mode(r: Wr.Dec<O.Mode>) -> {Once.on_read.mode(r) == FO.get_ev.mode(r) : Wr.Dec<FO.Ev>}:
  match r:
    case Wr.Got{m, +s}:
      %oe.rd_policy(Wr.get_nat(s)) : {Once.on_read.policy(m, Once.on_read_policy(Wr.get_nat(s))) == FO.get_ev.policy(m, _) : Wr.Dec<FO.Ev>}
      oe.rd_ask_policy(m, Once.on_read_policy(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def oe.rd_tag(n: Nat, +s: String) -> {Once.on_read.tag(n, s) == FO.get_ev.tag(n, s) : Wr.Dec<FO.Ev>}:
  match n:
    case 0n:
      %oe.rd_rec(Wr.get_nat(s)) : {Once.on_read.note(Once.on_read_rec(Wr.get_nat(s))) == FO.get_ev.note(_) : Wr.Dec<FO.Ev>}
      oe.rd_note(Once.on_read_rec(Wr.get_nat(s)))
    case 1n:
      %oe.rd_mode(Wr.get_nat(s)) : {Once.on_read.mode(Once.on_read_mode(Wr.get_nat(s))) == FO.get_ev.mode(_) : Wr.Dec<FO.Ev>}
      oe.rd_ask_mode(Once.on_read_mode(Wr.get_nat(s)))
    case 2n+p:
      {==}

# the entry reads every event as the laws' reader does
def oe.read(r: Wr.Dec<Nat>) -> {Once.on_read.go(r) == FO.get_ev.go(r) : Wr.Dec<FO.Ev>}:
  match r:
    case Wr.Got{n, s}:
      oe.rd_tag(n, s)
    case Wr.Bad{}:
      {==}

# Every cap the laws' reader answers fits the wire
# ------------------------------------------------

def oe.FitP(d: Wr.Dec<O.Policy>) -> Type:
  match d:
    case Wr.Got{p, s}:
      {Once.on_fit.policy(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def oe.FitD(d: Wr.Dec<FO.Ev>) -> Type:
  match d:
    case Wr.Got{e, s}:
      {Once.on_fit.ev(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def oe.fit_cap(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> oe.FitP(Once.on_read_policy.cap(d)):
  match d:
    case Wr.Got{+cap, +r}:
      Wire.wire_nat_decoded_fits(s, cap, r, ed)
    case Wr.Bad{}:
      Unit{}

def oe.fit_policy_tag(n: Nat, +s: String) -> oe.FitP(Once.on_read_policy.tag(n, s)):
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      oe.fit_cap(s, Wr.get_nat(s), {==})
    case 3n+p:
      Unit{}

def oe.fit_policy(r: Wr.Dec<Nat>) -> oe.FitP(Once.on_read_policy(r)):
  match r:
    case Wr.Got{n, s}:
      oe.fit_policy_tag(n, s)
    case Wr.Bad{}:
      Unit{}

def oe.fit_seen(-m: O.Mode, -p: O.Policy, r: Wr.Dec<O.Seen>, fp: {Once.on_fit.policy(p) == True{} : Bool}) -> oe.FitD(Once.on_read.seen(m, p, r)):
  match r:
    case Wr.Got{x, s}:
      fp
    case Wr.Bad{}:
      Unit{}

def oe.fit_ask(-m: O.Mode, d: Wr.Dec<O.Policy>, fp: oe.FitP(d)) -> oe.FitD(Once.on_read.policy(m, d)):
  match d:
    case Wr.Got{p, s}:
      oe.fit_seen(m, p, Once.on_read_seen(Wr.get_nat(s)), fp)
    case Wr.Bad{}:
      Unit{}

def oe.fit_mode(d: Wr.Dec<O.Mode>) -> oe.FitD(Once.on_read.mode(d)):
  match d:
    case Wr.Got{m, +s}:
      oe.fit_ask(m, Once.on_read_policy(Wr.get_nat(s)), oe.fit_policy(Wr.get_nat(s)))
    case Wr.Bad{}:
      Unit{}

def oe.fit_note(d: Wr.Dec<O.Rec>) -> oe.FitD(Once.on_read.note(d)):
  match d:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      Unit{}

def oe.fit_tag(n: Nat, s: String) -> oe.FitD(Once.on_read.tag(n, s)):
  match n:
    case 0n:
      oe.fit_note(Once.on_read_rec(Wr.get_nat(s)))
    case 1n:
      oe.fit_mode(Once.on_read_mode(Wr.get_nat(s)))
    case 2n+p:
      Unit{}

# every cap of an event the laws' reader answers fits the wire
def oe.fit_go(r: Wr.Dec<Nat>) -> oe.FitD(Once.on_read.go(r)):
  match r:
    case Wr.Got{n, s}:
      oe.fit_tag(n, s)
    case Wr.Bad{}:
      Unit{}

# Strings
# -------

def oe.GotM(a: String, r: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{x, s}:
      {a == x : String} & {r == s : String}
    case Wr.Bad{}:
      Unit

# two equal answers of a decoder hold the same string and the same rest
def oe.got_inj(-a: String, -r: String, -c: String, -s: String, g: {Wr.Got{a, r} == Wr.Got{c, s} : Wr.Dec<String>}) -> ({a == c : String} & {r == s : String}):
  %g : oe.GotM(a, r, _)
  ({==}, {==})

# two spelled strings that are equal spell the same string before the
# same rest
def oe.str_inj(+a: String, +c: String, +r: String, +s: String, fa: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, fc: {LawsBase.wire_fits(String.length(c)) == True{} : Bool}, same: {Wr.put_str(a, r) == Wr.put_str(c, s) : String}) -> ({a == c : String} & {r == s : String}):
  oe.got_inj(a, r, c, s, Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_str(a, r)), Wr.Got{c, s}, Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, r)), Wr.Got{a, r}, Wire.wire_str_round_trip(a, r, fa)), Equal.trans(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, r)), Wr.get_str(Wr.put_str(c, s)), Wr.Got{c, s}, Equal.cong(String, Wr.Dec<String>, x => Wr.get_str(x), Wr.put_str(a, r), Wr.put_str(c, s), same), Wire.wire_str_round_trip(c, s, fc))))

# the entry answers a spelled key request with the key
def oe.key_answers(+a: String, +b: String, fa: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, fb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}) -> {FO.ffi(Once.on_spell_key(a, b)) == O.key(a, b) : String}:
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, Wr.put_str(b, ""))), Wr.Got{a, Wr.put_str(b, "")}, Wire.wire_str_round_trip(a, Wr.put_str(b, ""), fa)) : {FO.ffi.scope(_) == O.key(a, b) : String}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(b, "")), Wr.Got{b, ""}, Wire.wire_str_round_trip(b, "", fb)) : {FO.ffi.id(a, _) == O.key(a, b) : String}
  {==}
