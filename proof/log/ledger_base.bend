# eukhe: lemmas of the ledger's laws (ledger_ack_durable,
# ledger_only_records, ledger_stamped_after_ack)
#
# An operation's plan is one of three runs of the model: no step (a crash
# before the open's flush), the stamped first commit then what Lg.more
# does (a file no stamp names: lb.fst after the parent's flush), or what
# Lg.more does (a kept file). Each run keeps the log before, then what it
# acknowledged, then maybe more (lb.fa), and a prefix of its commits
# (lb.f1); when its entries end up not both durable, it acknowledged
# nothing and its file had none durable either (lb.Z); a run that
# acknowledged a record linked the stamp with both entries durable. The
# file at rest is then joined: what the next operations read starts with
# the log before or (a file with entries not durable, lost later) with
# nothing (lb.pick).

import Base
import ../../spec/durable/log.bend as Lg
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log
import ./base.bend as LA
import ./log_ack_durable.bend as PAck
import ./log_only_commits.bend as POnly
import ../base/logic/logic.bend as LLogicLogic

# The runs of an operation
# ------------------------

# a kept file's commits do what Lg.more does
def lb.more(cs: List<&2, List<&2, Nat>>, +p: Nat, s: Lg.St) -> {Log.log_exec(Log.log_plan(cs, Lr.Store{True{}, True{}, True{}}), p, s) == Lg.more(cs, p, s) : Lg.St}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match p:
        case 0n:
          {==}
        case 1n+p1:
          match p1:
            case 0n:
              {==}
            case 1n+p2:
              lb.more(rest, p2, Lg.ack(c, Lg.flush(Lg.append(c, s))))

# the first commit of a file no stamp names, after q steps: append, flush,
# the directory's flush, the stamp, then the ack and what Lg.more does
def lb.fst(cs: List<&2, List<&2, Nat>>, q: Nat, s: Lg.St) -> Lg.St:
  match cs:
    case Nil{}:
      s
    case +c <> rest:
      match q:
        case 0n:
          s
        case 1n+q1:
          match q1:
            case 0n:
              Lg.append(c, s)
            case 1n+q2:
              match q2:
                case 0n:
                  Lg.flush(Lg.append(c, s))
                case 1n+q3:
                  match q3:
                    case 0n:
                      Lg.dir(Lg.flush(Lg.append(c, s)))
                    case 1n+q4:
                      Lg.more(rest, q4, Lg.ack(c, Lg.dir(Lg.flush(Lg.append(c, s)))))

def lb.first(cs: List<&2, List<&2, Nat>>, +q: Nat, s: Lg.St) -> {Log.log_exec(Log.log_plan(cs, Lr.Store{True{}, False{}, True{}}), q, s) == lb.fst(cs, q, s) : Lg.St}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match q:
        case 0n:
          {==}
        case 1n+q1:
          match q1:
            case 0n:
              {==}
            case 1n+q2:
              match q2:
                case 0n:
                  {==}
                case 1n+q3:
                  match q3:
                    case 0n:
                      {==}
                    case 1n+q4:
                      lb.more(rest, q4, Lg.ack(c, Lg.dir(Lg.flush(Lg.append(c, s)))))

# an operation's run: kept, the commits from the open; else nothing, or
# the parent's flush and the stamped first commit
def lb.run(cs: List<&2, List<&2, Nat>>, kept: Bool, p: Nat, s: Lg.St) -> Lg.St:
  match kept:
    case True{}:
      Lg.more(cs, p, s)
    case False{}:
      match p:
        case 0n:
          s
        case 1n+q:
          lb.fst(cs, q, Lg.parent(s))

def lb.op(cs: List<&2, List<&2, Nat>>, kept: Bool, +p: Nat, s: Lg.St) -> {Log.log_exec(Log.log_ledger_plan(cs, kept), p, s) == lb.run(cs, kept, p, s) : Lg.St}:
  match kept:
    case True{}:
      lb.more(cs, p, s)
    case False{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          lb.first(cs, q, Lg.parent(s))

# whether the stamp was linked: the first commit's fourth step done
def lb.sp(cs: List<&2, List<&2, Nat>>, q: Nat) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> rest:
      match q:
        case 0n:
          False{}
        case 1n+q1:
          match q1:
            case 0n:
              False{}
            case 1n+q2:
              match q2:
                case 0n:
                  False{}
                case 1n+q3:
                  match q3:
                    case 0n:
                      False{}
                    case 1n+q4:
                      True{}

def lb.stamped(cs: List<&2, List<&2, Nat>>, kept: Bool, p: Nat) -> Bool:
  match kept:
    case True{}:
      False{}
    case False{}:
      match p:
        case 0n:
          False{}
        case 1n+q:
          lb.sp(cs, q)

def lb.st_more(cs: List<&2, List<&2, Nat>>, +p: Nat) -> {Log.log_stamped(Log.log_plan(cs, Lr.Store{True{}, True{}, True{}}), p) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match p:
        case 0n:
          {==}
        case 1n+p1:
          match p1:
            case 0n:
              {==}
            case 1n+p2:
              lb.st_more(rest, p2)

def lb.st_first(cs: List<&2, List<&2, Nat>>, +q: Nat) -> {Log.log_stamped(Log.log_plan(cs, Lr.Store{True{}, False{}, True{}}), q) == lb.sp(cs, q) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match q:
        case 0n:
          {==}
        case 1n+q1:
          match q1:
            case 0n:
              {==}
            case 1n+q2:
              match q2:
                case 0n:
                  {==}
                case 1n+q3:
                  match q3:
                    case 0n:
                      {==}
                    case 1n+q4:
                      {==}

def lb.op_stamped(cs: List<&2, List<&2, Nat>>, kept: Bool, +p: Nat) -> {Log.log_stamped(Log.log_ledger_plan(cs, kept), p) == lb.stamped(cs, kept, p) : Bool}:
  match kept:
    case True{}:
      lb.st_more(cs, p)
    case False{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          lb.st_first(cs, q)

# What the stamped first commit keeps
# -----------------------------------

# the log before, then what it acknowledged, then maybe more
def lb.fa(cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat, +fe: Bool, +l: List<&2, List<&2, Nat>>) -> &r: List<&2, List<&2, Nat>> -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, Lg.St.acked(lb.fst(cs, q, Lg.St{True{}, fe, l, None{}, Nil{}}))), r) == LA.pl.fin(k, lb.fst(cs, q, Lg.St{True{}, fe, l, None{}, Nil{}})) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      PAck.pl.ml2(Nil{}, 0n, k, True{}, fe, l, l, Nil{}, LA.pl.app_nil(List<&2, Nat>, l))
    case +c <> +rest:
      match q:
        case 0n:
          PAck.pl.ml2(Nil{}, 0n, k, True{}, fe, l, l, Nil{}, LA.pl.app_nil(List<&2, Nat>, l))
        case 1n+q1:
          match q1:
            case 0n:
              PAck.pl.ml2([c], 1n, k, True{}, fe, l, l, Nil{}, LA.pl.app_nil(List<&2, Nat>, l))
            case 1n+q2:
              match q2:
                case 0n:
                  +l2 = List.append(&2, List<&2, Nat>, l, [c])
                  ([c], (%LA.pl.app_nil(List<&2, Nat>, l) : {List.append(&2, List<&2, Nat>, _, [c]) == Lg.recover(List.append(&2, Nat, Lg.render(l2), Nil{})) : List<&2, List<&2, Nat>>}; LA.pl.rl(l2)))
                case 1n+q3:
                  match q3:
                    case 0n:
                      +l2 = List.append(&2, List<&2, Nat>, l, [c])
                      ([c], (%LA.pl.app_nil(List<&2, Nat>, l) : {List.append(&2, List<&2, Nat>, _, [c]) == Lg.recover(List.append(&2, Nat, Lg.render(l2), Nil{})) : List<&2, List<&2, Nat>>}; LA.pl.rl(l2)))
                    case 1n+q4:
                      +l2 = List.append(&2, List<&2, Nat>, l, [c])
                      PAck.pl.ml2(rest, q4, k, True{}, True{}, l, l2, [c], {==})

# the log before, then a prefix of the commits
def lb.f1(cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat, +fe: Bool, +l: List<&2, List<&2, Nat>>) -> &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, cs, n)) == LA.pl.fin(k, lb.fst(cs, q, Lg.St{True{}, fe, l, None{}, Nil{}})) : List<&2, List<&2, Nat>>}:
  match cs:
    case Nil{}:
      (0n, LA.pl.recover_render(l, Nil{}))
    case +c <> +rest:
      match q:
        case 0n:
          (0n, LA.pl.recover_render(l, Nil{}))
        case 1n+q1:
          match q1:
            case 0n:
              POnly.pl.ml1_torn(l, c, rest, k, POnly.pl.keep_take(k, c, rest))
            case 1n+q2:
              match q2:
                case 0n:
                  +l2 = List.append(&2, List<&2, Nat>, l, [c])
                  (1n, (%POnly.pl.take0(List<&2, Nat>, rest) : {List.append(&2, List<&2, Nat>, l, c <> _) == Lg.recover(List.append(&2, Nat, Lg.render(l2), Nil{})) : List<&2, List<&2, Nat>>}; LA.pl.rl(l2)))
                case 1n+q3:
                  match q3:
                    case 0n:
                      +l2 = List.append(&2, List<&2, Nat>, l, [c])
                      (1n, (%POnly.pl.take0(List<&2, Nat>, rest) : {List.append(&2, List<&2, Nat>, l, c <> _) == Lg.recover(List.append(&2, Nat, Lg.render(l2), Nil{})) : List<&2, List<&2, Nat>>}; LA.pl.rl(l2)))
                    case 1n+q4:
                      +l2 = List.append(&2, List<&2, Nat>, l, [c])
                      POnly.pl.ml1_step(l, c, rest, LA.pl.fin(k, Lg.more(rest, q4, Lg.St{True{}, True{}, l2, None{}, [c]})), POnly.pl.ml1(rest, q4, k, True{}, True{}, l2, [c]))

# The file at rest after an operation
# -----------------------------------

# what the next operations may read first: the log of the file (w), or its
# durable part dl
def lb.pv(w: Bool, l: List<&2, List<&2, Nat>>, dl: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match w:
    case True{}:
      l
    case False{}:
      dl

# the log of a file whose entries are durable, else nothing
def lb.dl(dur: Bool, d: Lg.Disk) -> List<&2, List<&2, Nat>>:
  match dur:
    case True{}:
      Lg.Disk.log(d)
    case False{}:
      Nil{}

def lb.dlog(r: Lg.Rest) -> List<&2, List<&2, Nat>>:
  match r:
    case Lg.Rest{d, dur, sp}:
      lb.dl(dur, d)

def lb.pick(w: Bool, +r: Lg.Rest) -> List<&2, List<&2, Nat>>:
  lb.pv(w, Lg.Disk.log(Lg.Rest.d(r)), lb.dlog(r))

def lb.dur(r: Lg.Rest) -> Bool:
  match r:
    case Lg.Rest{d, dur, sp}:
      dur

# a file its stamp names has durable entries
def lb.ok(+r: Lg.Rest) -> Bool:
  Bool.or(Bool.not(Lg.Rest.kept(r)), lb.dur(r))

# entries D not both durable: nothing acknowledged (a), no durable log
# before (dl)
def lb.Z(D: Bool, a: List<&2, List<&2, Nat>>, dl: List<&2, List<&2, Nat>>) -> Type:
  match D:
    case True{}:
      Unit
    case False{}:
      {a == Nil{} : List<&2, List<&2, Nat>>} & {dl == Nil{} : List<&2, List<&2, Nat>>}

# a file entry fe0 not durable: no durable log before
def lb.Z0(fe0: Bool, dl: List<&2, List<&2, Nat>>) -> Type:
  match fe0:
    case True{}:
      Unit
    case False{}:
      {dl == Nil{} : List<&2, List<&2, Nat>>}

# entries D not both durable: the stamp is not linked (spv)
def lb.Y(D: Bool, spv: Bool) -> Type:
  match D:
    case True{}:
      Unit
    case False{}:
      {spv == False{} : Bool}

# the file kept: the log before, then what was acknowledged, then more
def lb.keep_leaf(+l: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>, -dl: List<&2, List<&2, Nat>>, -f: List<&2, List<&2, Nat>>, fa: &y: List<&2, List<&2, Nat>> -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, a), y) == f : List<&2, List<&2, Nat>>}) -> &w: Bool -> &x: List<&2, List<&2, Nat>> -> {f == List.append(&2, List<&2, Nat>, lb.pv(w, l, dl), List.append(&2, List<&2, Nat>, a, x)) : List<&2, List<&2, Nat>>}:
  match fa:
    case (+y, e):
      (True{}, (y, Equal.trans(List<&2, List<&2, Nat>>, f, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, a), y), List.append(&2, List<&2, Nat>, l, List.append(&2, List<&2, Nat>, a, y)), Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, a), y), f, e), Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, l, List.append(&2, List<&2, Nat>, a, y)), List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, a), y), LA.pl.assoc(List<&2, Nat>, l, a, y)))))

# nothing read: nothing was acknowledged and nothing before was durable
def lb.nil_leaf(-l: List<&2, List<&2, Nat>>, -a: List<&2, List<&2, Nat>>, -dl: List<&2, List<&2, Nat>>, z: {a == Nil{} : List<&2, List<&2, Nat>>} & {dl == Nil{} : List<&2, List<&2, Nat>>}) -> &w: Bool -> &x: List<&2, List<&2, Nat>> -> {Nil{} == List.append(&2, List<&2, Nat>, lb.pv(w, l, dl), List.append(&2, List<&2, Nat>, a, x)) : List<&2, List<&2, Nat>>}:
  (za, zd) = z
  (False{}, (Nil{}, (%Equal.sym(List<&2, List<&2, Nat>>, a, Nil{}, za) : {Nil{} == List.append(&2, List<&2, Nat>, dl, List.append(&2, List<&2, Nat>, _, Nil{})) : List<&2, List<&2, Nat>>}; %Equal.sym(List<&2, List<&2, Nat>>, dl, Nil{}, zd) : {Nil{} == List.append(&2, List<&2, Nat>, _, List.append(&2, List<&2, Nat>, Nil{}, Nil{})) : List<&2, List<&2, Nat>>}; {==})))

def lb.join(m: Lg.St, +k: Nat, +drop: Bool, spv: Bool, +l: List<&2, List<&2, Nat>>, +dl: List<&2, List<&2, Nat>>, fa: &y: List<&2, List<&2, Nat>> -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, Lg.St.acked(m)), y) == LA.pl.fin(k, m) : List<&2, List<&2, Nat>>}, dz: lb.Z(Bool.and(LA.pl.de(m), LA.pl.fe(m)), Lg.St.acked(m), dl), +w2: Bool) -> &w: Bool -> &x: List<&2, List<&2, Nat>> -> {lb.pick(w2, Lg.rest(k, drop, m, spv)) == List.append(&2, List<&2, Nat>, lb.pv(w, l, dl), List.append(&2, List<&2, Nat>, Lg.St.acked(m), x)) : List<&2, List<&2, Nat>>}:
  match m:
    case Lg.St{+de, +fe, +log, +pend, +acked}:
      match de fe:
        case True{} True{}:
          match drop w2:
            case True{} True{}:
              lb.keep_leaf(l, acked, dl, LA.pl.fin(k, Lg.St{True{}, True{}, log, pend, acked}), fa)
            case True{} False{}:
              lb.keep_leaf(l, acked, dl, LA.pl.fin(k, Lg.St{True{}, True{}, log, pend, acked}), fa)
            case False{} True{}:
              lb.keep_leaf(l, acked, dl, LA.pl.fin(k, Lg.St{True{}, True{}, log, pend, acked}), fa)
            case False{} False{}:
              lb.keep_leaf(l, acked, dl, LA.pl.fin(k, Lg.St{True{}, True{}, log, pend, acked}), fa)
        case True{} False{}:
          match drop w2:
            case True{} True{}:
              lb.nil_leaf(l, acked, dl, dz)
            case True{} False{}:
              lb.nil_leaf(l, acked, dl, dz)
            case False{} True{}:
              lb.keep_leaf(l, acked, dl, LA.pl.fin(k, Lg.St{True{}, False{}, log, pend, acked}), fa)
            case False{} False{}:
              lb.nil_leaf(l, acked, dl, dz)
        case False{} True{}:
          match drop w2:
            case True{} True{}:
              lb.nil_leaf(l, acked, dl, dz)
            case True{} False{}:
              lb.nil_leaf(l, acked, dl, dz)
            case False{} True{}:
              lb.keep_leaf(l, acked, dl, LA.pl.fin(k, Lg.St{False{}, True{}, log, pend, acked}), fa)
            case False{} False{}:
              lb.nil_leaf(l, acked, dl, dz)
        case False{} False{}:
          match drop w2:
            case True{} True{}:
              lb.nil_leaf(l, acked, dl, dz)
            case True{} False{}:
              lb.nil_leaf(l, acked, dl, dz)
            case False{} True{}:
              lb.keep_leaf(l, acked, dl, LA.pl.fin(k, Lg.St{False{}, False{}, log, pend, acked}), fa)
            case False{} False{}:
              lb.nil_leaf(l, acked, dl, dz)

# a stamp is linked only with both entries durable (X the entries and the
# stamp), and a record acknowledged (E: none) only then
def lb.SA(E: Bool, X: Bool) -> Type:
  match X:
    case True{}:
      Unit
    case False{}:
      {E == True{} : Bool}

def lb.FA(+l: List<&2, List<&2, Nat>>, +k: Nat, +m: Lg.St) -> Type:
  &y: List<&2, List<&2, Nat>> -> {List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, Lg.St.acked(m)), y) == LA.pl.fin(k, m) : List<&2, List<&2, Nat>>}

def lb.F1(+l: List<&2, List<&2, Nat>>, cs: List<&2, List<&2, Nat>>, +k: Nat, m: Lg.St) -> Type:
  &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, cs, n)) == LA.pl.fin(k, m) : List<&2, List<&2, Nat>>}

# What the runs leave
# -------------------

def lb.zfe(+fe0: Bool, -dl: List<&2, List<&2, Nat>>, zd: lb.Z0(fe0, dl)) -> lb.Z(fe0, Nil{}, dl):
  match fe0:
    case True{}:
      Unit{}
    case False{}:
      ({==}, zd)

def lb.yfe(+fe0: Bool) -> lb.Y(fe0, False{}):
  match fe0:
    case True{}:
      Unit{}
    case False{}:
      {==}

def lb.safe(+fe0: Bool) -> lb.SA(True{}, Bool.and(fe0, False{})):
  match fe0:
    case True{}:
      {==}
    case False{}:
      {==}

# the commits of a kept file keep both entries durable
def lb.zmore(+cs: List<&2, List<&2, Nat>>, +p: Nat, +l: List<&2, List<&2, Nat>>, -dl: List<&2, List<&2, Nat>>) -> lb.Z(Bool.and(LA.pl.de(Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}})), LA.pl.fe(Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}}))), Lg.St.acked(Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}})), dl):
  +m = Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}})
  %LA.pl.md(cs, p, True{}, True{}, l, Nil{}) : lb.Z(Bool.and(_, LA.pl.fe(m)), Lg.St.acked(m), dl)
  %LA.pl.me(cs, p, True{}, True{}, l, Nil{}) : lb.Z(Bool.and(True{}, _), Lg.St.acked(m), dl)
  Unit{}

def lb.ymore(+cs: List<&2, List<&2, Nat>>, +p: Nat, +l: List<&2, List<&2, Nat>>) -> lb.Y(Bool.and(LA.pl.de(Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}})), LA.pl.fe(Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}}))), True{}):
  +m = Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}})
  %LA.pl.md(cs, p, True{}, True{}, l, Nil{}) : lb.Y(Bool.and(_, LA.pl.fe(m)), True{})
  %LA.pl.me(cs, p, True{}, True{}, l, Nil{}) : lb.Y(Bool.and(True{}, _), True{})
  Unit{}

def lb.samore(+cs: List<&2, List<&2, Nat>>, +p: Nat, +l: List<&2, List<&2, Nat>>) -> lb.SA(List.is_empty(&2, List<&2, Nat>, Lg.St.acked(Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}}))), Bool.and(Bool.and(LA.pl.de(Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}})), LA.pl.fe(Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}}))), True{})):
  +m = Lg.more(cs, p, Lg.St{True{}, True{}, l, None{}, Nil{}})
  %LA.pl.md(cs, p, True{}, True{}, l, Nil{}) : lb.SA(List.is_empty(&2, List<&2, Nat>, Lg.St.acked(m)), Bool.and(Bool.and(_, LA.pl.fe(m)), True{}))
  %LA.pl.me(cs, p, True{}, True{}, l, Nil{}) : lb.SA(List.is_empty(&2, List<&2, Nat>, Lg.St.acked(m)), Bool.and(Bool.and(True{}, _), True{}))
  Unit{}

# the stamped first commit: not both entries durable only before the
# directory's flush, with nothing acknowledged; the stamp linked before the
# ack, with both durable
def lb.fz(cs: List<&2, List<&2, Nat>>, +q: Nat, +fe0: Bool, +l: List<&2, List<&2, Nat>>, -dl: List<&2, List<&2, Nat>>, zd: lb.Z0(fe0, dl)) -> lb.Z(Bool.and(LA.pl.de(lb.fst(cs, q, Lg.St{True{}, fe0, l, None{}, Nil{}})), LA.pl.fe(lb.fst(cs, q, Lg.St{True{}, fe0, l, None{}, Nil{}}))), Lg.St.acked(lb.fst(cs, q, Lg.St{True{}, fe0, l, None{}, Nil{}})), dl):
  match cs:
    case Nil{}:
      lb.zfe(fe0, dl, zd)
    case +c <> +rest:
      match q:
        case 0n:
          lb.zfe(fe0, dl, zd)
        case 1n+q1:
          match q1:
            case 0n:
              lb.zfe(fe0, dl, zd)
            case 1n+q2:
              match q2:
                case 0n:
                  lb.zfe(fe0, dl, zd)
                case 1n+q3:
                  match q3:
                    case 0n:
                      Unit{}
                    case 1n+q4:
                      +l2 = List.append(&2, List<&2, Nat>, l, [c])
                      +m = Lg.more(rest, q4, Lg.St{True{}, True{}, l2, None{}, [c]})
                      %LA.pl.md(rest, q4, True{}, True{}, l2, [c]) : lb.Z(Bool.and(_, LA.pl.fe(m)), Lg.St.acked(m), dl)
                      %LA.pl.me(rest, q4, True{}, True{}, l2, [c]) : lb.Z(Bool.and(True{}, _), Lg.St.acked(m), dl)
                      Unit{}

def lb.fy(cs: List<&2, List<&2, Nat>>, +q: Nat, +fe0: Bool, +l: List<&2, List<&2, Nat>>) -> lb.Y(Bool.and(LA.pl.de(lb.fst(cs, q, Lg.St{True{}, fe0, l, None{}, Nil{}})), LA.pl.fe(lb.fst(cs, q, Lg.St{True{}, fe0, l, None{}, Nil{}}))), lb.sp(cs, q)):
  match cs:
    case Nil{}:
      lb.yfe(fe0)
    case +c <> +rest:
      match q:
        case 0n:
          lb.yfe(fe0)
        case 1n+q1:
          match q1:
            case 0n:
              lb.yfe(fe0)
            case 1n+q2:
              match q2:
                case 0n:
                  lb.yfe(fe0)
                case 1n+q3:
                  match q3:
                    case 0n:
                      Unit{}
                    case 1n+q4:
                      +l2 = List.append(&2, List<&2, Nat>, l, [c])
                      +m = Lg.more(rest, q4, Lg.St{True{}, True{}, l2, None{}, [c]})
                      %LA.pl.md(rest, q4, True{}, True{}, l2, [c]) : lb.Y(Bool.and(_, LA.pl.fe(m)), True{})
                      %LA.pl.me(rest, q4, True{}, True{}, l2, [c]) : lb.Y(Bool.and(True{}, _), True{})
                      Unit{}

def lb.fsa(cs: List<&2, List<&2, Nat>>, +q: Nat, +fe0: Bool, +l: List<&2, List<&2, Nat>>) -> lb.SA(List.is_empty(&2, List<&2, Nat>, Lg.St.acked(lb.fst(cs, q, Lg.St{True{}, fe0, l, None{}, Nil{}}))), Bool.and(Bool.and(LA.pl.de(lb.fst(cs, q, Lg.St{True{}, fe0, l, None{}, Nil{}})), LA.pl.fe(lb.fst(cs, q, Lg.St{True{}, fe0, l, None{}, Nil{}}))), lb.sp(cs, q))):
  match cs:
    case Nil{}:
      lb.safe(fe0)
    case +c <> +rest:
      match q:
        case 0n:
          lb.safe(fe0)
        case 1n+q1:
          match q1:
            case 0n:
              lb.safe(fe0)
            case 1n+q2:
              match q2:
                case 0n:
                  lb.safe(fe0)
                case 1n+q3:
                  match q3:
                    case 0n:
                      {==}
                    case 1n+q4:
                      +l2 = List.append(&2, List<&2, Nat>, l, [c])
                      +m = Lg.more(rest, q4, Lg.St{True{}, True{}, l2, None{}, [c]})
                      %LA.pl.md(rest, q4, True{}, True{}, l2, [c]) : lb.SA(List.is_empty(&2, List<&2, Nat>, Lg.St.acked(m)), Bool.and(Bool.and(_, LA.pl.fe(m)), True{}))
                      %LA.pl.me(rest, q4, True{}, True{}, l2, [c]) : lb.SA(List.is_empty(&2, List<&2, Nat>, Lg.St.acked(m)), Bool.and(Bool.and(True{}, _), True{}))
                      Unit{}

# An operation, viewed
# --------------------

# the run of the operation e from the file r, and what it leaves: m is
# the storage at the crash, with its facts
def lb.VM(ex: Lg.St, +l: List<&2, List<&2, Nat>>, cs: List<&2, List<&2, Nat>>, +k: Nat, -dl: List<&2, List<&2, Nat>>, +spv: Bool) -> Type:
  &m: Lg.St -> ({ex == m : Lg.St} & (lb.FA(l, k, m) & (lb.F1(l, cs, k, m) & (lb.Z(Bool.and(LA.pl.de(m), LA.pl.fe(m)), Lg.St.acked(m), dl) & (lb.Y(Bool.and(LA.pl.de(m), LA.pl.fe(m)), spv) & lb.SA(List.is_empty(&2, List<&2, Nat>, Lg.St.acked(m)), Bool.and(Bool.and(LA.pl.de(m), LA.pl.fe(m)), spv)))))))

def lb.V(+r: Lg.Rest, e: Lg.Epoch) -> Type:
  match e:
    case Lg.Epoch{+cs, +p, +k, drop}:
      lb.VM(Log.log_exec(Log.log_ledger_plan(cs, Lg.Rest.kept(r)), p, Lg.Rest.open(r)), Lg.Disk.log(Lg.Rest.d(r)), cs, k, lb.dlog(r), Bool.or(Lg.Rest.kept(r), Log.log_stamped(Log.log_ledger_plan(cs, Lg.Rest.kept(r)), p)))

def lb.zabs(+dur: Bool) -> {lb.dl(dur, Lg.Absent{}) == Nil{} : List<&2, List<&2, Nat>>}:
  match dur:
    case True{}:
      {==}
    case False{}:
      {==}

def lb.zabs2(+dur: Bool) -> lb.Z(False{}, Nil{}, lb.dl(dur, Lg.Absent{})):
  ({==}, lb.zabs(dur))

def lb.zp(+dur: Bool, -b: List<&2, Nat>) -> lb.Z0(dur, lb.dl(dur, Lg.Present{b})):
  match dur:
    case True{}:
      Unit{}
    case False{}:
      {==}

def lb.zp0(+dur: Bool, -b: List<&2, Nat>) -> lb.Z(Bool.and(dur, dur), Nil{}, lb.dl(dur, Lg.Present{b})):
  match dur:
    case True{}:
      Unit{}
    case False{}:
      ({==}, {==})

def lb.yp0(+dur: Bool) -> lb.Y(Bool.and(dur, dur), False{}):
  match dur:
    case True{}:
      Unit{}
    case False{}:
      {==}

def lb.sap0(+dur: Bool) -> lb.SA(True{}, Bool.and(Bool.and(dur, dur), False{})):
  match dur:
    case True{}:
      {==}
    case False{}:
      {==}

# a file no stamp names, after the parent's flush: the stamped first commit
def lb.view_first(+cs: List<&2, List<&2, Nat>>, +q: Nat, +k: Nat, +fe0: Bool, +l: List<&2, List<&2, Nat>>, +s0: Lg.St, -dl: List<&2, List<&2, Nat>>, zd: lb.Z0(fe0, dl), eq: {Log.log_exec(Log.log_ledger_plan(cs, False{}), 1n+q, s0) == lb.fst(cs, q, Lg.St{True{}, fe0, l, None{}, Nil{}}) : Lg.St}) -> lb.VM(Log.log_exec(Log.log_ledger_plan(cs, False{}), 1n+q, s0), l, cs, k, dl, Log.log_stamped(Log.log_plan(cs, Lr.Store{True{}, False{}, True{}}), q)):
  +m = lb.fst(cs, q, Lg.St{True{}, fe0, l, None{}, Nil{}})
  +st = Log.log_stamped(Log.log_plan(cs, Lr.Store{True{}, False{}, True{}}), q)
  +sym = Equal.sym(Bool, st, lb.sp(cs, q), lb.st_first(cs, q))
  (m, (eq, (lb.fa(cs, q, k, fe0, l), (lb.f1(cs, q, k, fe0, l), (lb.fz(cs, q, fe0, l, dl, zd), ((%sym : lb.Y(Bool.and(LA.pl.de(m), LA.pl.fe(m)), _); lb.fy(cs, q, fe0, l)), (%sym : lb.SA(List.is_empty(&2, List<&2, Nat>, Lg.St.acked(m)), Bool.and(Bool.and(LA.pl.de(m), LA.pl.fe(m)), _)); lb.fsa(cs, q, fe0, l))))))))

def lb.view_fresh(+b: List<&2, Nat>, +dur: Bool, +e: Lg.Epoch) -> lb.V(Lg.Rest{Lg.Present{b}, dur, False{}}, e):
  match e:
    case Lg.Epoch{+cs, +p, +k, drop}:
      match p:
        case 0n:
          +l = Lg.recover(b)
          +s0 = {Lg.St{dur, dur, l, None{}, Nil{}} : Lg.St}
          (s0, ({==}, (PAck.pl.ml2(Nil{}, 0n, k, dur, dur, l, l, Nil{}, LA.pl.app_nil(List<&2, Nat>, l)), ((0n, (%POnly.pl.take0(List<&2, Nat>, cs) : {List.append(&2, List<&2, Nat>, l, _) == LA.pl.fin(k, s0) : List<&2, List<&2, Nat>>}; LA.pl.recover_render(l, Nil{}))), (lb.zp0(dur, b), (lb.yp0(dur), lb.sap0(dur)))))))
        case 1n+q:
          +l = Lg.recover(b)
          +s0 = {Lg.St{dur, dur, l, None{}, Nil{}} : Lg.St}
          lb.view_first(cs, q, k, dur, l, s0, lb.dl(dur, Lg.Present{b}), lb.zp(dur, b), lb.op(cs, False{}, 1n+q, s0))

def lb.view_kept(+b: List<&2, Nat>, +e: Lg.Epoch) -> lb.V(Lg.Rest{Lg.Present{b}, True{}, True{}}, e):
  match e:
    case Lg.Epoch{+cs, +p, +k, drop}:
      +l = Lg.recover(b)
      +s = {Lg.St{True{}, True{}, l, None{}, Nil{}} : Lg.St}
      (Lg.more(cs, p, s), (lb.op(cs, True{}, p, s), (PAck.pl.ml2(cs, p, k, True{}, True{}, l, l, Nil{}, LA.pl.app_nil(List<&2, Nat>, l)), (POnly.pl.ml1(cs, p, k, True{}, True{}, l, Nil{}), (lb.zmore(cs, p, l, lb.dl(True{}, Lg.Present{b})), (lb.ymore(cs, p, l), lb.samore(cs, p, l)))))))

def lb.view_absent(+dur: Bool, +sp: Bool, +e: Lg.Epoch) -> lb.V(Lg.Rest{Lg.Absent{}, dur, sp}, e):
  match e:
    case Lg.Epoch{+cs, +p, +k, drop}:
      match p:
        case 0n:
          +s0 = {Lg.St{False{}, False{}, Nil{}, None{}, Nil{}} : Lg.St}
          (s0, ({==}, (PAck.pl.ml2(Nil{}, 0n, k, False{}, False{}, Nil{}, Nil{}, Nil{}, {==}), ((0n, (%POnly.pl.take0(List<&2, Nat>, cs) : {List.append(&2, List<&2, Nat>, Nil{}, _) == LA.pl.fin(k, s0) : List<&2, List<&2, Nat>>}; LA.pl.recover_render(Nil{}, Nil{}))), (lb.zabs2(dur), ({==}, {==}))))))
        case 1n+q:
          +s0 = {Lg.St{False{}, False{}, Nil{}, None{}, Nil{}} : Lg.St}
          lb.view_first(cs, q, k, False{}, Nil{}, s0, lb.dl(dur, Lg.Absent{}), lb.zabs(dur), lb.op(cs, False{}, 1n+q, s0))

def lb.view(+r: Lg.Rest, +e: Lg.Epoch, inv: {lb.ok(r) == True{} : Bool}) -> lb.V(r, e):
  match r:
    case Lg.Rest{d, +dur, +sp}:
      match d:
        case Lg.Absent{}:
          lb.view_absent(dur, sp, e)
        case Lg.Present{+b}:
          match dur sp:
            case True{} True{}:
              lb.view_kept(b, e)
            case True{} False{}:
              lb.view_fresh(b, True{}, e)
            case False{} True{}:
              LLogicLogic.absurd(lb.V(Lg.Rest{Lg.Present{b}, False{}, True{}}, e), inv)
            case False{} False{}:
              lb.view_fresh(b, False{}, e)

# The file at rest, joined
# ------------------------

def lb.keep_leaf_o(+l: List<&2, List<&2, Nat>>, -cs: List<&2, List<&2, Nat>>, -dl: List<&2, List<&2, Nat>>, -f: List<&2, List<&2, Nat>>, f1: &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, cs, n)) == f : List<&2, List<&2, Nat>>}) -> &w: Bool -> &n: Nat -> {f == List.append(&2, List<&2, Nat>, lb.pv(w, l, dl), List.take(&2, List<&2, Nat>, cs, n)) : List<&2, List<&2, Nat>>}:
  match f1:
    case (+n, e):
      (True{}, (n, Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, cs, n)), f, e)))

def lb.nil_leaf_o(-l: List<&2, List<&2, Nat>>, +cs: List<&2, List<&2, Nat>>, -a: List<&2, List<&2, Nat>>, -dl: List<&2, List<&2, Nat>>, z: {a == Nil{} : List<&2, List<&2, Nat>>} & {dl == Nil{} : List<&2, List<&2, Nat>>}) -> &w: Bool -> &n: Nat -> {Nil{} == List.append(&2, List<&2, Nat>, lb.pv(w, l, dl), List.take(&2, List<&2, Nat>, cs, n)) : List<&2, List<&2, Nat>>}:
  (za, zd) = z
  (False{}, (0n, (%Equal.sym(List<&2, List<&2, Nat>>, dl, Nil{}, zd) : {Nil{} == List.append(&2, List<&2, Nat>, _, List.take(&2, List<&2, Nat>, cs, 0n)) : List<&2, List<&2, Nat>>}; POnly.pl.take0(List<&2, Nat>, cs))))

def lb.joino(m: Lg.St, +k: Nat, +drop: Bool, spv: Bool, +l: List<&2, List<&2, Nat>>, +dl: List<&2, List<&2, Nat>>, +cs: List<&2, List<&2, Nat>>, f1: &n: Nat -> {List.append(&2, List<&2, Nat>, l, List.take(&2, List<&2, Nat>, cs, n)) == LA.pl.fin(k, m) : List<&2, List<&2, Nat>>}, dz: lb.Z(Bool.and(LA.pl.de(m), LA.pl.fe(m)), Lg.St.acked(m), dl), +w2: Bool) -> &w: Bool -> &n: Nat -> {lb.pick(w2, Lg.rest(k, drop, m, spv)) == List.append(&2, List<&2, Nat>, lb.pv(w, l, dl), List.take(&2, List<&2, Nat>, cs, n)) : List<&2, List<&2, Nat>>}:
  match m:
    case Lg.St{+de, +fe, +log, +pend, +acked}:
      match de fe:
        case True{} True{}:
          match drop w2:
            case True{} True{}:
              lb.keep_leaf_o(l, cs, dl, LA.pl.fin(k, Lg.St{True{}, True{}, log, pend, acked}), f1)
            case True{} False{}:
              lb.keep_leaf_o(l, cs, dl, LA.pl.fin(k, Lg.St{True{}, True{}, log, pend, acked}), f1)
            case False{} True{}:
              lb.keep_leaf_o(l, cs, dl, LA.pl.fin(k, Lg.St{True{}, True{}, log, pend, acked}), f1)
            case False{} False{}:
              lb.keep_leaf_o(l, cs, dl, LA.pl.fin(k, Lg.St{True{}, True{}, log, pend, acked}), f1)
        case True{} False{}:
          match drop w2:
            case True{} True{}:
              lb.nil_leaf_o(l, cs, acked, dl, dz)
            case True{} False{}:
              lb.nil_leaf_o(l, cs, acked, dl, dz)
            case False{} True{}:
              lb.keep_leaf_o(l, cs, dl, LA.pl.fin(k, Lg.St{True{}, False{}, log, pend, acked}), f1)
            case False{} False{}:
              lb.nil_leaf_o(l, cs, acked, dl, dz)
        case False{} True{}:
          match drop w2:
            case True{} True{}:
              lb.nil_leaf_o(l, cs, acked, dl, dz)
            case True{} False{}:
              lb.nil_leaf_o(l, cs, acked, dl, dz)
            case False{} True{}:
              lb.keep_leaf_o(l, cs, dl, LA.pl.fin(k, Lg.St{False{}, True{}, log, pend, acked}), f1)
            case False{} False{}:
              lb.nil_leaf_o(l, cs, acked, dl, dz)
        case False{} False{}:
          match drop w2:
            case True{} True{}:
              lb.nil_leaf_o(l, cs, acked, dl, dz)
            case True{} False{}:
              lb.nil_leaf_o(l, cs, acked, dl, dz)
            case False{} True{}:
              lb.keep_leaf_o(l, cs, dl, LA.pl.fin(k, Lg.St{False{}, False{}, log, pend, acked}), f1)
            case False{} False{}:
              lb.nil_leaf_o(l, cs, acked, dl, dz)

# a file its stamp names after the crash has durable entries
def lb.okj(m: Lg.St, +k: Nat, +drop: Bool, +spv: Bool, y: lb.Y(Bool.and(LA.pl.de(m), LA.pl.fe(m)), spv)) -> {lb.ok(Lg.rest(k, drop, m, spv)) == True{} : Bool}:
  match m:
    case Lg.St{+de, +fe, +log, +pend, +acked}:
      match de fe:
        case True{} True{}:
          match drop spv:
            case True{} True{}:
              {==}
            case True{} False{}:
              {==}
            case False{} True{}:
              {==}
            case False{} False{}:
              {==}
        case True{} False{}:
          match drop spv:
            case True{} True{}:
              LLogicLogic.pt.absurd({lb.ok(Lg.rest(k, True{}, Lg.St{True{}, False{}, log, pend, acked}, True{})) == True{} : Bool}, y)
            case True{} False{}:
              {==}
            case False{} True{}:
              LLogicLogic.pt.absurd({lb.ok(Lg.rest(k, False{}, Lg.St{True{}, False{}, log, pend, acked}, True{})) == True{} : Bool}, y)
            case False{} False{}:
              {==}
        case False{} True{}:
          match drop spv:
            case True{} True{}:
              LLogicLogic.pt.absurd({lb.ok(Lg.rest(k, True{}, Lg.St{False{}, True{}, log, pend, acked}, True{})) == True{} : Bool}, y)
            case True{} False{}:
              {==}
            case False{} True{}:
              LLogicLogic.pt.absurd({lb.ok(Lg.rest(k, False{}, Lg.St{False{}, True{}, log, pend, acked}, True{})) == True{} : Bool}, y)
            case False{} False{}:
              {==}
        case False{} False{}:
          match drop spv:
            case True{} True{}:
              LLogicLogic.pt.absurd({lb.ok(Lg.rest(k, True{}, Lg.St{False{}, False{}, log, pend, acked}, True{})) == True{} : Bool}, y)
            case True{} False{}:
              {==}
            case False{} True{}:
              LLogicLogic.pt.absurd({lb.ok(Lg.rest(k, False{}, Lg.St{False{}, False{}, log, pend, acked}, True{})) == True{} : Bool}, y)
            case False{} False{}:
              {==}

# a run that acknowledged a record leaves a file its stamp names
def lb.saj(m: Lg.St, +k: Nat, +drop: Bool, +spv: Bool, sa: lb.SA(List.is_empty(&2, List<&2, Nat>, Lg.St.acked(m)), Bool.and(Bool.and(LA.pl.de(m), LA.pl.fe(m)), spv)), h: {List.is_empty(&2, List<&2, Nat>, Lg.St.acked(m)) == False{} : Bool}) -> {Lg.Rest.kept(Lg.rest(k, drop, m, spv)) == True{} : Bool}:
  match m:
    case Lg.St{+de, +fe, +log, +pend, +acked}:
      match de fe:
        case True{} True{}:
          match drop spv:
            case True{} True{}:
              {==}
            case True{} False{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, True{}, Lg.St{True{}, True{}, log, pend, acked}, False{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
            case False{} True{}:
              {==}
            case False{} False{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, False{}, Lg.St{True{}, True{}, log, pend, acked}, False{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
        case True{} False{}:
          match drop spv:
            case True{} True{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, True{}, Lg.St{True{}, False{}, log, pend, acked}, True{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
            case True{} False{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, True{}, Lg.St{True{}, False{}, log, pend, acked}, False{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
            case False{} True{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, False{}, Lg.St{True{}, False{}, log, pend, acked}, True{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
            case False{} False{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, False{}, Lg.St{True{}, False{}, log, pend, acked}, False{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
        case False{} True{}:
          match drop spv:
            case True{} True{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, True{}, Lg.St{False{}, True{}, log, pend, acked}, True{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
            case True{} False{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, True{}, Lg.St{False{}, True{}, log, pend, acked}, False{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
            case False{} True{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, False{}, Lg.St{False{}, True{}, log, pend, acked}, True{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
            case False{} False{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, False{}, Lg.St{False{}, True{}, log, pend, acked}, False{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
        case False{} False{}:
          match drop spv:
            case True{} True{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, True{}, Lg.St{False{}, False{}, log, pend, acked}, True{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
            case True{} False{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, True{}, Lg.St{False{}, False{}, log, pend, acked}, False{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
            case False{} True{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, False{}, Lg.St{False{}, False{}, log, pend, acked}, True{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))
            case False{} False{}:
              LLogicLogic.pt.absurd({Lg.Rest.kept(Lg.rest(k, False{}, Lg.St{False{}, False{}, log, pend, acked}, False{})) == True{} : Bool}, Equal.trans(Bool, True{}, List.is_empty(&2, List<&2, Nat>, acked), False{}, Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, acked), True{}, sa), h))

# An operation's claims
# ---------------------

def lb.AckG(+r: Lg.Rest, e: Lg.Epoch, +w2: Bool) -> Type:
  &w: Bool -> &x: List<&2, List<&2, Nat>> -> {lb.pick(w2, Log.log_ledger_step(r, e)) == List.append(&2, List<&2, Nat>, lb.pick(w, r), List.append(&2, List<&2, Nat>, Log.log_ledger_acked(r, e), x)) : List<&2, List<&2, Nat>>}

def lb.ack_v(+r: Lg.Rest, e: Lg.Epoch, +w2: Bool, v: lb.V(r, e)) -> lb.AckG(r, e, w2):
  match e:
    case Lg.Epoch{+cs, +p, +k, +drop}:
      match v:
        case (+m, vs):
          (eq, (fa, (f1, (dz, (y, sa))))) = vs
          +kept = Lg.Rest.kept(r)
          +ex = Log.log_exec(Log.log_ledger_plan(cs, kept), p, Lg.Rest.open(r))
          +spv = Bool.or(kept, Log.log_stamped(Log.log_ledger_plan(cs, kept), p))
          %Equal.sym(Lg.St, ex, m, eq) : &w: Bool -> &x: List<&2, List<&2, Nat>> -> {lb.pick(w2, Lg.rest(k, drop, _, spv)) == List.append(&2, List<&2, Nat>, lb.pick(w, r), List.append(&2, List<&2, Nat>, Lg.St.acked(_), x)) : List<&2, List<&2, Nat>>}
          lb.join(m, k, drop, spv, Lg.Disk.log(Lg.Rest.d(r)), lb.dlog(r), fa, dz, w2)

def lb.OnlyG(+r: Lg.Rest, e: Lg.Epoch, +w2: Bool) -> Type:
  &w: Bool -> &n: Nat -> {lb.pick(w2, Log.log_ledger_step(r, e)) == List.append(&2, List<&2, Nat>, lb.pick(w, r), List.take(&2, List<&2, Nat>, Lg.Epoch.cs(e), n)) : List<&2, List<&2, Nat>>}

def lb.only_v(+r: Lg.Rest, e: Lg.Epoch, +w2: Bool, v: lb.V(r, e)) -> lb.OnlyG(r, e, w2):
  match e:
    case Lg.Epoch{+cs, +p, +k, +drop}:
      match v:
        case (+m, vs):
          (eq, (fa, (f1, (dz, (y, sa))))) = vs
          +kept = Lg.Rest.kept(r)
          +ex = Log.log_exec(Log.log_ledger_plan(cs, kept), p, Lg.Rest.open(r))
          +spv = Bool.or(kept, Log.log_stamped(Log.log_ledger_plan(cs, kept), p))
          %Equal.sym(Lg.St, ex, m, eq) : &w: Bool -> &n: Nat -> {lb.pick(w2, Lg.rest(k, drop, _, spv)) == List.append(&2, List<&2, Nat>, lb.pick(w, r), List.take(&2, List<&2, Nat>, cs, n)) : List<&2, List<&2, Nat>>}
          lb.joino(m, k, drop, spv, Lg.Disk.log(Lg.Rest.d(r)), lb.dlog(r), cs, f1, dz, w2)

def lb.ok_v(+r: Lg.Rest, e: Lg.Epoch, v: lb.V(r, e)) -> {lb.ok(Log.log_ledger_step(r, e)) == True{} : Bool}:
  match e:
    case Lg.Epoch{+cs, +p, +k, +drop}:
      match v:
        case (+m, vs):
          (eq, (fa, (f1, (dz, (y, sa))))) = vs
          +kept = Lg.Rest.kept(r)
          +ex = Log.log_exec(Log.log_ledger_plan(cs, kept), p, Lg.Rest.open(r))
          +spv = Bool.or(kept, Log.log_stamped(Log.log_ledger_plan(cs, kept), p))
          %Equal.sym(Lg.St, ex, m, eq) : {lb.ok(Lg.rest(k, drop, _, spv)) == True{} : Bool}
          lb.okj(m, k, drop, spv, y)

def lb.sa_v(+r: Lg.Rest, e: Lg.Epoch, v: lb.V(r, e), h: {List.is_empty(&2, List<&2, Nat>, Log.log_ledger_acked(r, e)) == False{} : Bool}) -> {Lg.Rest.kept(Log.log_ledger_step(r, e)) == True{} : Bool}:
  match e:
    case Lg.Epoch{+cs, +p, +k, +drop}:
      match v:
        case (+m, vs):
          (+eq, (fa, (f1, (dz, (y, sa))))) = vs
          +kept = Lg.Rest.kept(r)
          +ex = Log.log_exec(Log.log_ledger_plan(cs, kept), p, Lg.Rest.open(r))
          +spv = Bool.or(kept, Log.log_stamped(Log.log_ledger_plan(cs, kept), p))
          %Equal.sym(Lg.St, ex, m, eq) : {Lg.Rest.kept(Lg.rest(k, drop, _, spv)) == True{} : Bool}
          lb.saj(m, k, drop, spv, sa, (%eq : {List.is_empty(&2, List<&2, Nat>, Lg.St.acked(_)) == False{} : Bool}; h))

# Histories
# ---------

# every file a history leaves has durable entries when its stamp names it
def lb.ok_hist(es: List<&2, Lg.Epoch>, +r: Lg.Rest, inv: {lb.ok(r) == True{} : Bool}) -> {lb.ok(Log.log_ledger_rest(es, r)) == True{} : Bool}:
  match es:
    case Nil{}:
      inv
    case +e <> rest:
      lb.ok_hist(rest, Log.log_ledger_step(r, e), lb.ok_v(r, e, lb.view(r, e, inv)))

# F == M ++ K and M == P ++ A: F == P ++ (A ++ K)
def lb.hj(+P: List<&2, List<&2, Nat>>, +A: List<&2, List<&2, Nat>>, +K: List<&2, List<&2, Nat>>, -M: List<&2, List<&2, Nat>>, -F: List<&2, List<&2, Nat>>, h2: {F == List.append(&2, List<&2, Nat>, M, K) : List<&2, List<&2, Nat>>}, h1: {M == List.append(&2, List<&2, Nat>, P, A) : List<&2, List<&2, Nat>>}) -> {F == List.append(&2, List<&2, Nat>, P, List.append(&2, List<&2, Nat>, A, K)) : List<&2, List<&2, Nat>>}:
  +rhs = List.append(&2, List<&2, Nat>, P, List.append(&2, List<&2, Nat>, A, K))
  %Equal.sym(List<&2, List<&2, Nat>>, F, List.append(&2, List<&2, Nat>, M, K), h2) : {_ == rhs : List<&2, List<&2, Nat>>}
  %Equal.sym(List<&2, List<&2, Nat>>, M, List.append(&2, List<&2, Nat>, P, A), h1) : {List.append(&2, List<&2, Nat>, _, K) == rhs : List<&2, List<&2, Nat>>}
  %LA.pl.assoc(List<&2, Nat>, P, A, K) : {_ == rhs : List<&2, List<&2, Nat>>}
  {==}

def lb.ack_join(+r: Lg.Rest, +e: Lg.Epoch, +rest: List<&2, Lg.Epoch>, +w2: Bool, +xs2: List<&2, List<&2, List<&2, Nat>>>, h2: {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(rest, Log.log_ledger_step(r, e)))) == List.append(&2, List<&2, Nat>, lb.pick(w2, Log.log_ledger_step(r, e)), Log.log_ledger_kept.r(rest, Log.log_ledger_step(r, e), xs2)) : List<&2, List<&2, Nat>>}, st: lb.AckG(r, e, w2)) -> &w: Bool -> &xs: List<&2, List<&2, List<&2, Nat>>> -> {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(e <> rest, r))) == List.append(&2, List<&2, Nat>, lb.pick(w, r), Log.log_ledger_kept.r(e <> rest, r, xs)) : List<&2, List<&2, Nat>>}:
  match st:
    case (+w, st2):
      match st2:
        case (+x, h1):
          +r1 = Log.log_ledger_step(r, e)
          (w, (x <> xs2, lb.hj(lb.pick(w, r), List.append(&2, List<&2, Nat>, Log.log_ledger_acked(r, e), x), Log.log_ledger_kept.r(rest, r1, xs2), lb.pick(w2, r1), Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(rest, r1))), h2, h1)))

def lb.ack_cons(+r: Lg.Rest, +e: Lg.Epoch, +rest: List<&2, Lg.Epoch>, inv: {lb.ok(r) == True{} : Bool}, ih: &w2: Bool -> &xs2: List<&2, List<&2, List<&2, Nat>>> -> {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(rest, Log.log_ledger_step(r, e)))) == List.append(&2, List<&2, Nat>, lb.pick(w2, Log.log_ledger_step(r, e)), Log.log_ledger_kept.r(rest, Log.log_ledger_step(r, e), xs2)) : List<&2, List<&2, Nat>>}) -> &w: Bool -> &xs: List<&2, List<&2, List<&2, Nat>>> -> {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(e <> rest, r))) == List.append(&2, List<&2, Nat>, lb.pick(w, r), Log.log_ledger_kept.r(e <> rest, r, xs)) : List<&2, List<&2, Nat>>}:
  match ih:
    case (+w2, ih2):
      match ih2:
        case (+xs2, h2):
          lb.ack_join(r, e, rest, w2, xs2, h2, lb.ack_v(r, e, w2, lb.view(r, e, inv)))

# what a history leaves: the log before or its durable part, then each
# operation's acknowledged records, each followed by maybe more
def lb.ack_hist(es: List<&2, Lg.Epoch>, +r: Lg.Rest, +inv: {lb.ok(r) == True{} : Bool}) -> &w: Bool -> &xs: List<&2, List<&2, List<&2, Nat>>> -> {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(es, r))) == List.append(&2, List<&2, Nat>, lb.pick(w, r), Log.log_ledger_kept.r(es, r, xs)) : List<&2, List<&2, Nat>>}:
  match es:
    case Nil{}:
      (True{}, (Nil{}, LA.pl.app_nil(List<&2, Nat>, Lg.Disk.log(Lg.Rest.d(r)))))
    case +e <> +rest:
      lb.ack_cons(r, e, rest, inv, lb.ack_hist(rest, Log.log_ledger_step(r, e), lb.ok_v(r, e, lb.view(r, e, inv))))

def lb.only_join(+r: Lg.Rest, +e: Lg.Epoch, +rest: List<&2, Lg.Epoch>, +w2: Bool, +ns2: List<&2, Nat>, h2: {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(rest, Log.log_ledger_step(r, e)))) == List.append(&2, List<&2, Nat>, lb.pick(w2, Log.log_ledger_step(r, e)), Log.log_ledger_taken(rest, ns2)) : List<&2, List<&2, Nat>>}, st: lb.OnlyG(r, e, w2)) -> &w: Bool -> &ns: List<&2, Nat> -> {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(e <> rest, r))) == List.append(&2, List<&2, Nat>, lb.pick(w, r), Log.log_ledger_taken(e <> rest, ns)) : List<&2, List<&2, Nat>>}:
  match st:
    case (+w, st2):
      match st2:
        case (+n, h1):
          +r1 = Log.log_ledger_step(r, e)
          (w, (n <> ns2, lb.hj(lb.pick(w, r), List.take(&2, List<&2, Nat>, Lg.Epoch.cs(e), n), Log.log_ledger_taken(rest, ns2), lb.pick(w2, r1), Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(rest, r1))), h2, h1)))

def lb.only_cons(+r: Lg.Rest, +e: Lg.Epoch, +rest: List<&2, Lg.Epoch>, inv: {lb.ok(r) == True{} : Bool}, ih: &w2: Bool -> &ns2: List<&2, Nat> -> {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(rest, Log.log_ledger_step(r, e)))) == List.append(&2, List<&2, Nat>, lb.pick(w2, Log.log_ledger_step(r, e)), Log.log_ledger_taken(rest, ns2)) : List<&2, List<&2, Nat>>}) -> &w: Bool -> &ns: List<&2, Nat> -> {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(e <> rest, r))) == List.append(&2, List<&2, Nat>, lb.pick(w, r), Log.log_ledger_taken(e <> rest, ns)) : List<&2, List<&2, Nat>>}:
  match ih:
    case (+w2, ih2):
      match ih2:
        case (+ns2, h2):
          lb.only_join(r, e, rest, w2, ns2, h2, lb.only_v(r, e, w2, lb.view(r, e, inv)))

# what a history leaves: the log before or its durable part, then a
# prefix of each operation's records
def lb.only_hist(es: List<&2, Lg.Epoch>, +r: Lg.Rest, +inv: {lb.ok(r) == True{} : Bool}) -> &w: Bool -> &ns: List<&2, Nat> -> {Lg.Disk.log(Lg.Rest.d(Log.log_ledger_rest(es, r))) == List.append(&2, List<&2, Nat>, lb.pick(w, r), Log.log_ledger_taken(es, ns)) : List<&2, List<&2, Nat>>}:
  match es:
    case Nil{}:
      (True{}, (Nil{}, LA.pl.app_nil(List<&2, Nat>, Lg.Disk.log(Lg.Rest.d(r)))))
    case +e <> +rest:
      lb.only_cons(r, e, rest, inv, lb.only_hist(rest, Log.log_ledger_step(r, e), lb.ok_v(r, e, lb.view(r, e, inv))))

# From a file with durable entries
# --------------------------------

def lb.ok0(+d: Lg.Disk) -> {lb.ok(Log.log_ledger_start(d)) == True{} : Bool}:
  match d:
    case Lg.Absent{}:
      {==}
    case Lg.Present{b}:
      {==}

def lb.pk(+w: Bool, -d: Lg.Disk, -F: List<&2, List<&2, Nat>>, -K: List<&2, List<&2, Nat>>, h: {F == List.append(&2, List<&2, Nat>, lb.pick(w, Log.log_ledger_start(d)), K) : List<&2, List<&2, Nat>>}) -> {F == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), K) : List<&2, List<&2, Nat>>}:
  match w:
    case True{}:
      h
    case False{}:
      h
