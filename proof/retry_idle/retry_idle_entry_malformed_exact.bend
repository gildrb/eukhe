# eukhe: the proof of LAW retry_idle_entry_malformed_exact
# The entry reads every event and every open as the laws' readers do,
# one field at a time; where they find none, the entry answers its error
# form and keeps the state (an open: shut).
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ./base.bend as LA

def rn.fin(b: Bool, e0: R.IdleEv, +s: R.IdleSt, no: {RetryIdle.read_ev.fin(b, e0) == None{} : Maybe<&2, R.IdleEv>}) -> {Fi.step.end(b, s, e0) == (Fi.Live{s}, SCon{'E', SCon{' ', "retry_idle: malformed event"}}) : Fi.St & String}:
  match b:
    case True{}:
      LA.ri.none_some(R.IdleEv, {Fi.step.end(True{}, s, e0) == (Fi.Live{s}, SCon{'E', SCon{' ', "retry_idle: malformed event"}}) : Fi.St & String}, e0, Equal.sym(Maybe<&2, R.IdleEv>, Some{e0}, None{}, no))
    case False{}:
      {==}

def rn.life(r: Wr.Dec<Nat>, +s: R.IdleSt, no: {RetryIdle.read_ev.life(r) == None{} : Maybe<&2, R.IdleEv>}) -> {Fi.step.ev(s, Fi.get_ev.life(r)) == (Fi.Live{s}, SCon{'E', SCon{' ', "retry_idle: malformed event"}}) : Fi.St & String}:
  match r:
    case Wr.Got{now, rest}:
      rn.fin(Wr.end(rest), R.IdleLife{now}, s, no)
    case Wr.Bad{}:
      {==}

def rn.free(r: Wr.Dec<Nat>, +s: R.IdleSt, no: {RetryIdle.read_ev.free(r) == None{} : Maybe<&2, R.IdleEv>}) -> {Fi.step.ev(s, Fi.get_ev.free(r)) == (Fi.Live{s}, SCon{'E', SCon{' ', "retry_idle: malformed event"}}) : Fi.St & String}:
  match r:
    case Wr.Got{now, rest}:
      rn.fin(Wr.end(rest), R.IdleFree{now}, s, no)
    case Wr.Bad{}:
      {==}

def rn.fire(r: Wr.Dec<Nat>, +s: R.IdleSt, no: {RetryIdle.read_ev.fire(r) == None{} : Maybe<&2, R.IdleEv>}) -> {Fi.step.ev(s, Fi.get_ev.fire(r)) == (Fi.Live{s}, SCon{'E', SCon{' ', "retry_idle: malformed event"}}) : Fi.St & String}:
  match r:
    case Wr.Got{now, rest}:
      rn.fin(Wr.end(rest), R.IdleFire{now}, s, no)
    case Wr.Bad{}:
      {==}

def rn.tag(t: Nat, rest: String, +s: R.IdleSt, no: {RetryIdle.read_ev.tag(t, rest) == None{} : Maybe<&2, R.IdleEv>}) -> {Fi.step.ev(s, Fi.get_ev.tag(t, rest)) == (Fi.Live{s}, SCon{'E', SCon{' ', "retry_idle: malformed event"}}) : Fi.St & String}:
  match t:
    case 0n:
      rn.life(Wr.get_nat(rest), s, no)
    case 1n:
      rn.fin(Wr.end(rest), R.IdleHold{}, s, no)
    case 2n:
      rn.free(Wr.get_nat(rest), s, no)
    case 3n:
      rn.fire(Wr.get_nat(rest), s, no)
    case 4n+p:
      {==}

def rn.go(r: Wr.Dec<Nat>, +s: R.IdleSt, no: {RetryIdle.read_ev.go(r) == None{} : Maybe<&2, R.IdleEv>}) -> {Fi.step.ev(s, Fi.get_ev.go(r)) == (Fi.Live{s}, SCon{'E', SCon{' ', "retry_idle: malformed event"}}) : Fi.St & String}:
  match r:
    case Wr.Got{t, rest}:
      rn.tag(t, rest, s, no)
    case Wr.Bad{}:
      {==}

def rno.end(b: Bool, o: Fi.Open, no: {RetryIdle.read_open.end(b, o) == None{} : Maybe<&2, Fi.Open>}) -> {Fi.open.end(b, o) == (Fi.Shut{}, SCon{'E', SCon{' ', "retry_idle: malformed open"}}) : Fi.St & String}:
  match b:
    case True{}:
      LA.ri.none_some(Fi.Open, {Fi.open.end(True{}, o) == (Fi.Shut{}, SCon{'E', SCon{' ', "retry_idle: malformed open"}}) : Fi.St & String}, o, Equal.sym(Maybe<&2, Fi.Open>, Some{o}, None{}, no))
    case False{}:
      {==}

def rno.d(nan: Bool, neg: Bool, whole: Nat, frac: Bool, r: Wr.Dec<Nat>, no: {RetryIdle.read_open.d(nan, neg, whole, frac, r) == None{} : Maybe<&2, Fi.Open>}) -> {Fi.open.go(Fi.get_open.d(nan, neg, whole, frac, r)) == (Fi.Shut{}, SCon{'E', SCon{' ', "retry_idle: malformed open"}}) : Fi.St & String}:
  match r:
    case Wr.Got{d, s}:
      rno.end(Wr.end(s), Fi.Open{nan, neg, whole, frac, d}, no)
    case Wr.Bad{}:
      {==}

def rno.frac(nan: Bool, neg: Bool, whole: Nat, r: Wr.Dec<Bool>, no: {RetryIdle.read_open.frac(nan, neg, whole, r) == None{} : Maybe<&2, Fi.Open>}) -> {Fi.open.go(Fi.get_open.frac(nan, neg, whole, r)) == (Fi.Shut{}, SCon{'E', SCon{' ', "retry_idle: malformed open"}}) : Fi.St & String}:
  match r:
    case Wr.Got{frac, s}:
      rno.d(nan, neg, whole, frac, Wr.get_nat(s), no)
    case Wr.Bad{}:
      {==}

def rno.whole(nan: Bool, neg: Bool, r: Wr.Dec<Nat>, no: {RetryIdle.read_open.whole(nan, neg, r) == None{} : Maybe<&2, Fi.Open>}) -> {Fi.open.go(Fi.get_open.whole(nan, neg, r)) == (Fi.Shut{}, SCon{'E', SCon{' ', "retry_idle: malformed open"}}) : Fi.St & String}:
  match r:
    case Wr.Got{whole, s}:
      rno.frac(nan, neg, whole, Wr.get_bool(s), no)
    case Wr.Bad{}:
      {==}

def rno.neg(nan: Bool, r: Wr.Dec<Bool>, no: {RetryIdle.read_open.neg(nan, r) == None{} : Maybe<&2, Fi.Open>}) -> {Fi.open.go(Fi.get_open.neg(nan, r)) == (Fi.Shut{}, SCon{'E', SCon{' ', "retry_idle: malformed open"}}) : Fi.St & String}:
  match r:
    case Wr.Got{neg, s}:
      rno.whole(nan, neg, Wr.get_nat(s), no)
    case Wr.Bad{}:
      {==}

def rno.go(r: Wr.Dec<Bool>, no: {RetryIdle.read_open.go(r) == None{} : Maybe<&2, Fi.Open>}) -> {Fi.open.go(Fi.get_open.go(r)) == (Fi.Shut{}, SCon{'E', SCon{' ', "retry_idle: malformed open"}}) : Fi.St & String}:
  match r:
    case Wr.Got{nan, s}:
      rno.neg(nan, Wr.get_bool(s), no)
    case Wr.Bad{}:
      {==}

def RetryIdle.retry_idle_entry_malformed_exact(s, i, no, o, no_open, x):
  (rn.go(Wr.get_nat(i), s, no), rno.go(Wr.get_bool(o), no_open), {==})
