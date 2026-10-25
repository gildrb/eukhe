# eukhe: the proof of LAW retry_idle_open_reads
# The entry reads every open as the laws' reader does, one field at a
# time; a whole open opens as the same open spelled (LA.ri.open_spelled).
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

def ro.fin(b: Bool, o0: Fi.Open, +o: Fi.Open, got: {RetryIdle.read_open.end(b, o0) == Some{o} : Maybe<&2, Fi.Open>}) -> {Fi.open.end(b, o0) == Fi.open.end(True{}, o) : Fi.St & String}:
  match b:
    case True{}:
      %LA.ri.some_inj(Fi.Open, o0, o, got) : {Fi.open.end(True{}, o0) == Fi.open.end(True{}, _) : Fi.St & String}
      {==}
    case False{}:
      LA.ri.none_some(Fi.Open, {Fi.open.end(False{}, o0) == Fi.open.end(True{}, o) : Fi.St & String}, o, got)

def ro.d(nan: Bool, neg: Bool, whole: Nat, frac: Bool, r: Wr.Dec<Nat>, +o: Fi.Open, got: {RetryIdle.read_open.d(nan, neg, whole, frac, r) == Some{o} : Maybe<&2, Fi.Open>}) -> {Fi.open.go(Fi.get_open.d(nan, neg, whole, frac, r)) == Fi.open.end(True{}, o) : Fi.St & String}:
  match r:
    case Wr.Got{d, s}:
      ro.fin(Wr.end(s), Fi.Open{nan, neg, whole, frac, d}, o, got)
    case Wr.Bad{}:
      LA.ri.none_some(Fi.Open, {(Fi.Shut{}, Wr.err("retry_idle: malformed open")) == Fi.open.end(True{}, o) : Fi.St & String}, o, got)

def ro.frac(nan: Bool, neg: Bool, whole: Nat, r: Wr.Dec<Bool>, +o: Fi.Open, got: {RetryIdle.read_open.frac(nan, neg, whole, r) == Some{o} : Maybe<&2, Fi.Open>}) -> {Fi.open.go(Fi.get_open.frac(nan, neg, whole, r)) == Fi.open.end(True{}, o) : Fi.St & String}:
  match r:
    case Wr.Got{frac, s}:
      ro.d(nan, neg, whole, frac, Wr.get_nat(s), o, got)
    case Wr.Bad{}:
      LA.ri.none_some(Fi.Open, {(Fi.Shut{}, Wr.err("retry_idle: malformed open")) == Fi.open.end(True{}, o) : Fi.St & String}, o, got)

def ro.whole(nan: Bool, neg: Bool, r: Wr.Dec<Nat>, +o: Fi.Open, got: {RetryIdle.read_open.whole(nan, neg, r) == Some{o} : Maybe<&2, Fi.Open>}) -> {Fi.open.go(Fi.get_open.whole(nan, neg, r)) == Fi.open.end(True{}, o) : Fi.St & String}:
  match r:
    case Wr.Got{whole, s}:
      ro.frac(nan, neg, whole, Wr.get_bool(s), o, got)
    case Wr.Bad{}:
      LA.ri.none_some(Fi.Open, {(Fi.Shut{}, Wr.err("retry_idle: malformed open")) == Fi.open.end(True{}, o) : Fi.St & String}, o, got)

def ro.neg(nan: Bool, r: Wr.Dec<Bool>, +o: Fi.Open, got: {RetryIdle.read_open.neg(nan, r) == Some{o} : Maybe<&2, Fi.Open>}) -> {Fi.open.go(Fi.get_open.neg(nan, r)) == Fi.open.end(True{}, o) : Fi.St & String}:
  match r:
    case Wr.Got{neg, s}:
      ro.whole(nan, neg, Wr.get_nat(s), o, got)
    case Wr.Bad{}:
      LA.ri.none_some(Fi.Open, {(Fi.Shut{}, Wr.err("retry_idle: malformed open")) == Fi.open.end(True{}, o) : Fi.St & String}, o, got)

def ro.go(r: Wr.Dec<Bool>, +o: Fi.Open, got: {RetryIdle.read_open.go(r) == Some{o} : Maybe<&2, Fi.Open>}) -> {Fi.open.go(Fi.get_open.go(r)) == Fi.open.end(True{}, o) : Fi.St & String}:
  match r:
    case Wr.Got{nan, s}:
      ro.neg(nan, Wr.get_bool(s), o, got)
    case Wr.Bad{}:
      LA.ri.none_some(Fi.Open, {(Fi.Shut{}, Wr.err("retry_idle: malformed open")) == Fi.open.end(True{}, o) : Fi.St & String}, o, got)

def RetryIdle.retry_idle_open_reads(i, nan, neg, whole, frac, d, got, fits):
  Equal.trans(Fi.St & String, Fi.open(i), Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, d}), Fi.open(RetryIdle.spell_open(nan, neg, whole, frac, d)), ro.go(Wr.get_bool(i), Fi.Open{nan, neg, whole, frac, d}, got), Equal.sym(Fi.St & String, Fi.open(RetryIdle.spell_open(nan, neg, whole, frac, d)), Fi.open.end(True{}, Fi.Open{nan, neg, whole, frac, d}), LA.ri.open_spelled(nan, neg, whole, frac, d, fits)))
