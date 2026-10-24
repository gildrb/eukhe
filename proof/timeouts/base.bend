# eukhe: lemmas the proofs of area timeouts share

import Base
import ../../bend/ffi_timeouts.bend as FT
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/timeouts.bend as Timeouts

# a Some that is None proves anything
def tmo.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def tmo.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : tmo.if_none(A, _, G)
  Unit{}

def tmo.none_some(-A: Data, -x: A, -G: Type, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %Equal.sym(Maybe<&2, A>, None{}, Some{x}, e) : tmo.if_none(A, _, G)
  Unit{}

# The reply
# ---------

# the entry counts digits as the wire does
def tmo.digits(f: Nat, q: Nat) -> {LawsBase.wire_digits.go(f, q) == FT.digits.go(f, q) : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      match q:
        case 0n:
          {==}
        case 1n+p:
          %tmo.digits(g, Nat.div(1n+p, 10n)) : {1n+LawsBase.wire_digits.go(g, Nat.div(1n+p, 10n)) == 1n+_ : Nat}
          {==}

# the entry's bound is the laws'
def tmo.below(+x: Nat) -> {Timeouts.tw_below(x) == FT.fits(x) : Bool}:
  %tmo.digits(x, Nat.div(x, 10n)) : {Timeouts.tw_below(x) == Nat.is_le(1n+_, 14n) : Bool}
  {==}

# every value: the entry's bound is the laws'
def tmo.fit(xs: List<&2, Nat>) -> {Timeouts.tw_all_below(xs) == FT.all_fit(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      %tmo.fit(r) : {Bool.and(Timeouts.tw_below(x), Timeouts.tw_all_below(r)) == Bool.and(FT.fits(x), _) : Bool}
      %tmo.below(x) : {Bool.and(Timeouts.tw_below(x), Timeouts.tw_all_below(r)) == Bool.and(_, Timeouts.tw_all_below(r)) : Bool}
      {==}

# the entry spells the values as the laws do
def tmo.spell(xs: List<&2, Nat>) -> {Timeouts.tw_spell_values(xs) == FT.put_nats(xs, "") : String}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      %tmo.spell(r) : {Wr.put_nat(x, Timeouts.tw_spell_values(r)) == Wr.put_nat(x, _) : String}
      {==}

def tmo.put(b: Bool, xs: List<&2, Nat>) -> {FT.answer.put(b, xs) == Timeouts.tw_reply.put(b, xs) : String}:
  match b:
    case True{}:
      Equal.sym(String, Timeouts.tw_spell_values(xs), FT.put_nats(xs, ""), tmo.spell(xs))
    case False{}:
      {==}

# the entry derives the laws' values
def tmo.values(t: Su.Tm) -> {FT.derived(t) == Timeouts.tw_values(t) : List<&2, Nat>}:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, qanswer}:
      {==}

# the entry answers the laws' reply on every base values
def tmo.answer(+t: Su.Tm) -> {FT.answer(t) == Timeouts.tw_reply(t) : String}:
  %tmo.values(t) : {FT.answer(t) == Timeouts.tw_reply.put(Timeouts.tw_all_below(_), _) : String}
  %tmo.fit(FT.derived(t)) : {FT.answer.put(_, FT.derived(t)) == Timeouts.tw_reply.put(Timeouts.tw_all_below(FT.derived(t)), FT.derived(t)) : String}
  tmo.put(Timeouts.tw_all_below(FT.derived(t)), FT.derived(t))

# The reader, stage by stage
# --------------------------

def tmo.read.qanswer(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, k: Nat, bmax: Nat, loop: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.qanswer(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, r) == FT.get_tm.qanswer(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{qanswer, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tmo.read.loop(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, k: Nat, bmax: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.loop(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, r) == FT.get_tm.loop(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{loop, s}:
      tmo.read.qanswer(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, loop, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.bmax(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, k: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.bmax(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, r) == FT.get_tm.bmax(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{bmax, s}:
      tmo.read.loop(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, bmax, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.k(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, slack: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.k(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, r) == FT.get_tm.k(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{k, s}:
      tmo.read.bmax(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.slack(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, check: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.slack(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, r) == FT.get_tm.slack(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{slack, s}:
      tmo.read.k(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, slack, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.check(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, startup: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.check(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, r) == FT.get_tm.check(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{check, s}:
      tmo.read.slack(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, check, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.startup(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, relaunch: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.startup(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, r) == FT.get_tm.startup(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{startup, s}:
      tmo.read.check(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, startup, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.relaunch(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, boot: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.relaunch(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, r) == FT.get_tm.relaunch(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{relaunch, s}:
      tmo.read.startup(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, relaunch, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.boot(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, refresh: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.boot(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, r) == FT.get_tm.boot(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{boot, s}:
      tmo.read.relaunch(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, boot, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.refresh(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, margin: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.refresh(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, r) == FT.get_tm.refresh(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{refresh, s}:
      tmo.read.boot(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, refresh, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.margin(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, wverify: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.margin(snap, host, kstep, kterm, kverify, harness, wterm, wverify, r) == FT.get_tm.margin(snap, host, kstep, kterm, kverify, harness, wterm, wverify, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{margin, s}:
      tmo.read.refresh(snap, host, kstep, kterm, kverify, harness, wterm, wverify, margin, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.wverify(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, wterm: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.wverify(snap, host, kstep, kterm, kverify, harness, wterm, r) == FT.get_tm.wverify(snap, host, kstep, kterm, kverify, harness, wterm, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{wverify, s}:
      tmo.read.margin(snap, host, kstep, kterm, kverify, harness, wterm, wverify, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.wterm(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, harness: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.wterm(snap, host, kstep, kterm, kverify, harness, r) == FT.get_tm.wterm(snap, host, kstep, kterm, kverify, harness, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{wterm, s}:
      tmo.read.wverify(snap, host, kstep, kterm, kverify, harness, wterm, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.harness(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, kverify: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.harness(snap, host, kstep, kterm, kverify, r) == FT.get_tm.harness(snap, host, kstep, kterm, kverify, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{harness, s}:
      tmo.read.wterm(snap, host, kstep, kterm, kverify, harness, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.kverify(snap: Nat, host: Nat, kstep: Nat, kterm: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.kverify(snap, host, kstep, kterm, r) == FT.get_tm.kverify(snap, host, kstep, kterm, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{kverify, s}:
      tmo.read.harness(snap, host, kstep, kterm, kverify, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.kterm(snap: Nat, host: Nat, kstep: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.kterm(snap, host, kstep, r) == FT.get_tm.kterm(snap, host, kstep, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{kterm, s}:
      tmo.read.kverify(snap, host, kstep, kterm, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.kstep(snap: Nat, host: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.kstep(snap, host, r) == FT.get_tm.kstep(snap, host, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{kstep, s}:
      tmo.read.kterm(snap, host, kstep, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def tmo.read.host(snap: Nat, r: Wr.Dec<Nat>) -> {Timeouts.tw_read.host(snap, r) == FT.get_tm.host(snap, r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{host, s}:
      tmo.read.kstep(snap, host, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# the entry reads every input as the laws' reader does
def tmo.read.snap(r: Wr.Dec<Nat>) -> {Timeouts.tw_read.snap(r) == FT.get_tm.snap(r) : Wr.Dec<Su.Tm>}:
  match r:
    case Wr.Got{snap, s}:
      tmo.read.host(snap, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}
