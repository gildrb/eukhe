# eukhe: the proof of LAW cron_fire_claims
# By cases on the event. A claim pass adds a start only to a due active
# job with no claim, whose claim it then puts on record (the start is the
# head: fc.head). Every other event keeps the starts, or (a recovery that
# fires a one-shot again) empties them; neither is x <> the starts
# (fc.noloop, fc.nil_cons), so the premise is impossible.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_job.bend as CronJob

# Lists
# -----

def fc.void(-A: Type, e: Empty) -> A:
  match e:

# Unit on the empty list, Empty on a cons
def fc.ConsE(l: List<&2, Nat>) -> Type:
  match l:
    case Nil{}:
      Unit
    case y <> t:
      Empty

def fc.tail(l: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Nil{}:
      Nil{}
    case y <> t:
      t

def fc.head(l: List<&2, Nat>) -> Nat:
  match l:
    case Nil{}:
      0n
    case y <> t:
      y

def fc.nil_cons(+x: Nat, -ss: List<&2, Nat>, e: {Nil{} == x <> ss : List<&2, Nat>}) -> Empty:
  %e : fc.ConsE(_)
  Unit{}

# no list is itself with one more element in front
def fc.noloop(ss: List<&2, Nat>, +x: Nat, e: {ss == x <> ss : List<&2, Nat>}) -> Empty:
  match ss:
    case Nil{}:
      fc.nil_cons(x, Nil{}, e)
    case +y <> +t:
      fc.noloop(t, y, Equal.cong(List<&2, Nat>, List<&2, Nat>, l => fc.tail(l), y <> t, x <> (y <> t), e))

# starts kept: the premise is impossible
def fc.same(-A: Type, +after: List<&2, Nat>, +ss: List<&2, Nat>, +x: Nat, keep: {after == ss : List<&2, Nat>}, st: {after == x <> ss : List<&2, Nat>}) -> A:
  fc.void(A, fc.noloop(ss, x, Equal.trans(List<&2, Nat>, ss, after, x <> ss, Equal.sym(List<&2, Nat>, after, ss, keep), st)))

# The steps that keep the starts
# ------------------------------

def fc.pick(b: Bool, -a: Cr.Job, -j: Cr.Job, ea: {CronJob.starts_spec(a) == CronJob.starts_spec(j) : List<&2, Nat>}) -> {CronJob.starts_spec(Cr.job.pick(b, a, j)) == CronJob.starts_spec(j) : List<&2, Nat>}:
  match b:
    case True{}:
      ea
    case False{}:
      {==}

def fc.unrun(+p: Nat, j: Cr.Job) -> {CronJob.starts_spec(Cr.unrun(p, j)) == CronJob.starts_spec(j) : List<&2, Nat>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      {==}

def fc.cancel(j: Cr.Job) -> {CronJob.starts_spec(Cr.cancel(j)) == CronJob.starts_spec(j) : List<&2, Nat>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def fc.resume(+c: Nat, j: Cr.Job) -> {CronJob.starts_spec(Cr.resume(c, j)) == CronJob.starts_spec(j) : List<&2, Nat>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Cr.Once{d}:
          {==}
        case Cr.Every{n}:
          match st:
            case Cr.Active{}:
              {==}
            case Cr.Paused{}:
              {==}
            case Cr.Finished{}:
              {==}
            case Cr.Cancelled{}:
              {==}

def fc.pause(j: Cr.Job) -> {CronJob.starts_spec(Cr.pause(j)) == CronJob.starts_spec(j) : List<&2, Nat>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def fc.stop(j: Cr.Job) -> {CronJob.starts_spec(Cr.stop(j)) == CronJob.starts_spec(j) : List<&2, Nat>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def fc.delete(j: Cr.Job) -> {CronJob.starts_spec(Cr.delete(j)) == CronJob.starts_spec(j) : List<&2, Nat>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      {==}

def fc.edit(+c: Nat, +n: Nat, j: Cr.Job) -> {CronJob.starts_spec(Cr.edit(c, n, j)) == CronJob.starts_spec(j) : List<&2, Nat>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def fc.fail(b: Bool, +c: Nat, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.starts_spec(Cr.finish.fail(b, c, i, s, nx, k, rs, ss, h)) == ss : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fc.count(once: Bool, +c: Nat, o: Cr.Out, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.starts_spec(Cr.finish.count(once, c, o, i, s, nx, k, rs, ss, h)) == ss : List<&2, Nat>}:
  match once:
    case True{}:
      {==}
    case False{}:
      match o:
        case Cr.Win{}:
          {==}
        case Cr.Skip{}:
          {==}
        case Cr.Loss{}:
          fc.fail(Nat.is_lt(1n+k, Cr.CAP()), c, i, s, nx, 1n+k, rs, ss, Cr.MLoss{} <> h)

def fc.own(b: Bool, +x: Cr.Claim, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.starts_spec(Cr.finish.own(b, x, c, o, i, s, st, nx, k, rs, ss, h)) == ss : List<&2, Nat>}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case Cr.Active{}:
          fc.count(Cr.is_once(s), c, o, i, s, nx, k, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def fc.claim(cl: Maybe<&2, Cr.Claim>, +p: Nat, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.starts_spec(Cr.finish.claim(cl, p, c, o, i, s, st, nx, k, rs, ss, h)) == ss : List<&2, Nat>}:
  match cl:
    case None{}:
      {==}
    case Some{y}:
      match y:
        case Cr.Claim{+xo, +w}:
          fc.own(Nat.is_eq(w, p), Cr.Claim{xo, w}, c, o, i, s, st, nx, k, rs, ss, h)

def fc.run(b: Bool, +p: Nat, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.starts_spec(Cr.finish.run(b, p, c, o, i, s, st, nx, k, cl, rs, ss, h)) == ss : List<&2, Nat>}:
  match b:
    case False{}:
      {==}
    case True{}:
      fc.claim(cl, p, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h)

def fc.finish(+p: Nat, +c: Nat, +o: Cr.Out, j: Cr.Job) -> {CronJob.starts_spec(Cr.finish(p, c, o, j)) == CronJob.starts_spec(j) : List<&2, Nat>}:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      fc.run(Cr.has(p, rs), p, c, o, i, s, st, nx, k, cl, rs, ss, h)

# A recovery keeps the starts, or empties them
# --------------------------------------------

def fc.rec_end(once: Bool, +x: Nat, +i: Nat, +s: Cr.Sched, +nx: Maybe<&2, Nat>, +k: Nat, y: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, e: {CronJob.starts_spec(Cr.recover.end(once, i, s, nx, k, y, rs, ss, h)) == x <> ss : List<&2, Nat>}) -> Empty:
  match once:
    case True{}:
      match y:
        case Cr.Claim{oc, o}:
          fc.nil_cons(x, ss, e)
    case False{}:
      fc.noloop(ss, x, e)

def fc.rec_go(b: Bool, +x: Nat, +i: Nat, +s: Cr.Sched, st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +y: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, e: {CronJob.starts_spec(Cr.recover.go(b, i, s, st, nx, k, y, rs, ss, h)) == x <> ss : List<&2, Nat>}) -> Empty:
  match b:
    case False{}:
      fc.noloop(ss, x, e)
    case True{}:
      match st:
        case Cr.Active{}:
          fc.rec_end(Cr.is_once(s), x, i, s, nx, k, y, rs, ss, h, e)
        case Cr.Paused{}:
          fc.noloop(ss, x, e)
        case Cr.Finished{}:
          fc.noloop(ss, x, e)
        case Cr.Cancelled{}:
          fc.noloop(ss, x, e)

def fc.recover(+p: Nat, +dead: List<&2, Nat>, +x: Nat, j: Cr.Job, e: {CronJob.starts_spec(Cr.recover(p, dead, j)) == x <> CronJob.starts_spec(j) : List<&2, Nat>}) -> Empty:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          fc.noloop(ss, x, e)
        case Some{y}:
          match y:
            case Cr.Claim{+xo, +o}:
              fc.rec_go(Cr.clears(p, o, rs, dead), x, i, s, st, nx, k, Cr.Claim{xo, o}, rs, ss, h, e)

# A claim pass
# ------------

def fc.take_due(due: Bool, +p: Nat, +c: Nat, +x: Nat, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, e: {CronJob.starts_spec(Cr.take.due(due, p, c, i, s, n, k, cl, rs, ss, h)) == x <> ss : List<&2, Nat>}) -> ({cl == None{} : Maybe<&2, Cr.Claim>} & {Cr.Job.claim(Cr.take.due(due, p, c, i, s, n, k, cl, rs, ss, h)) == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}):
  match due:
    case False{}:
      fc.void(({cl == None{} : Maybe<&2, Cr.Claim>} & {Cr.Job.claim(Cr.Job{i, s, Cr.Active{}, Some{n}, k, cl, rs, ss, h}) == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}), fc.noloop(ss, x, e))
    case True{}:
      match cl:
        case None{}:
          +hx = Equal.cong(List<&2, Nat>, Nat, l => fc.head(l), n <> ss, x <> ss, e)
          %hx : ({None{} == None{} : Maybe<&2, Cr.Claim>} & {Some{Cr.Claim{n, p}} == Some{Cr.Claim{_, p}} : Maybe<&2, Cr.Claim>})
          ({==}, {==})
        case Some{y}:
          fc.void(({Some{y} == None{} : Maybe<&2, Cr.Claim>} & {Some{y} == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}), fc.noloop(ss, x, e))

def fc.take(+p: Nat, +c: Nat, +x: Nat, j: Cr.Job, e: {CronJob.starts_spec(Cr.take(p, c, j)) == x <> CronJob.starts_spec(j) : List<&2, Nat>}) -> ({Cr.Job.claim(j) == None{} : Maybe<&2, Cr.Claim>} & {Cr.Job.claim(Cr.take(p, c, j)) == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}):
  match j:
    case Cr.Job{+i, +s, st, nx, +k, +cl, +rs, +ss, +h}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              fc.void(({cl == None{} : Maybe<&2, Cr.Claim>} & {cl == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}), fc.noloop(ss, x, e))
            case Some{+n}:
              fc.take_due(Nat.is_le(n, c), p, c, x, i, s, n, k, cl, rs, ss, h, e)
        case Cr.Paused{}:
          fc.void(({cl == None{} : Maybe<&2, Cr.Claim>} & {cl == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}), fc.noloop(ss, x, e))
        case Cr.Finished{}:
          fc.void(({cl == None{} : Maybe<&2, Cr.Claim>} & {cl == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}), fc.noloop(ss, x, e))
        case Cr.Cancelled{}:
          fc.void(({cl == None{} : Maybe<&2, Cr.Claim>} & {cl == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}), fc.noloop(ss, x, e))

# CronJob
# -------

# what the law concludes of event e
def fc.G(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +x: Nat) -> Type:
  ({CronJob.take_spec(e) == True{} : Bool} & ({Cr.Job.claim(j) == None{} : Maybe<&2, Cr.Claim>} & {Cr.Job.claim(Cr.job(e, c, dead, j)) == CronJob.fired_by_spec(e, x) : Maybe<&2, Cr.Claim>}))

def CronJob.cron_fire_claims(e, c, dead, j, x, st):
  match e:
    case Cr.Take{p}:
      ({==}, fc.take(p, c, x, j, st))
    case Cr.Recover{p}:
      fc.void(fc.G(Cr.Recover{p}, c, dead, j, x), fc.recover(p, dead, x, j, st))
    case Cr.Finish{p, i, o}:
      fc.same(fc.G(Cr.Finish{p, i, o}, c, dead, j, x), CronJob.starts_spec(Cr.job(Cr.Finish{p, i, o}, c, dead, j)), CronJob.starts_spec(j), x, fc.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.finish(p, c, o, j), j, fc.finish(p, c, o, j)), st)
    case Cr.Abort{p}:
      fc.same(fc.G(Cr.Abort{p}, c, dead, j, x), CronJob.starts_spec(Cr.job(Cr.Abort{p}, c, dead, j)), CronJob.starts_spec(j), x, fc.unrun(p, j), st)
    case Cr.Die{p}:
      fc.same(fc.G(Cr.Die{p}, c, dead, j, x), CronJob.starts_spec(Cr.job(Cr.Die{p}, c, dead, j)), CronJob.starts_spec(j), x, fc.unrun(p, j), st)
    case Cr.Cancel{p, i}:
      fc.same(fc.G(Cr.Cancel{p, i}, c, dead, j, x), CronJob.starts_spec(Cr.job(Cr.Cancel{p, i}, c, dead, j)), CronJob.starts_spec(j), x, fc.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.cancel(j), j, fc.cancel(j)), st)
    case Cr.Resume{p, i}:
      fc.same(fc.G(Cr.Resume{p, i}, c, dead, j, x), CronJob.starts_spec(Cr.job(Cr.Resume{p, i}, c, dead, j)), CronJob.starts_spec(j), x, fc.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.resume(c, j), j, fc.resume(c, j)), st)
    case Cr.Pause{p, i}:
      fc.same(fc.G(Cr.Pause{p, i}, c, dead, j, x), CronJob.starts_spec(Cr.job(Cr.Pause{p, i}, c, dead, j)), CronJob.starts_spec(j), x, fc.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.pause(j), j, fc.pause(j)), st)
    case Cr.Stop{p, i}:
      fc.same(fc.G(Cr.Stop{p, i}, c, dead, j, x), CronJob.starts_spec(Cr.job(Cr.Stop{p, i}, c, dead, j)), CronJob.starts_spec(j), x, fc.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.stop(j), j, fc.stop(j)), st)
    case Cr.Delete{p, i}:
      fc.same(fc.G(Cr.Delete{p, i}, c, dead, j, x), CronJob.starts_spec(Cr.job(Cr.Delete{p, i}, c, dead, j)), CronJob.starts_spec(j), x, fc.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.delete(j), j, fc.delete(j)), st)
    case Cr.Edit{p, i, k}:
      fc.same(fc.G(Cr.Edit{p, i, k}, c, dead, j, x), CronJob.starts_spec(Cr.job(Cr.Edit{p, i, k}, c, dead, j)), CronJob.starts_spec(j), x, fc.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.edit(c, k, j), j, fc.edit(c, k, j)), st)
    case Cr.Create{p, s}:
      fc.same(fc.G(Cr.Create{p, s}, c, dead, j, x), CronJob.starts_spec(j), CronJob.starts_spec(j), x, {==}, st)
    case Cr.Tick{d}:
      fc.same(fc.G(Cr.Tick{d}, c, dead, j, x), CronJob.starts_spec(j), CronJob.starts_spec(j), x, {==}, st)
    case Cr.RawJob{t}:
      fc.same(fc.G(Cr.RawJob{t}, c, dead, j, x), CronJob.starts_spec(j), CronJob.starts_spec(j), x, {==}, st)
    case Cr.RawClaim{t}:
      fc.same(fc.G(Cr.RawClaim{t}, c, dead, j, x), CronJob.starts_spec(j), CronJob.starts_spec(j), x, {==}, st)
    case Cr.Corrupt{t}:
      fc.same(fc.G(Cr.Corrupt{t}, c, dead, j, x), CronJob.starts_spec(j), CronJob.starts_spec(j), x, {==}, st)
