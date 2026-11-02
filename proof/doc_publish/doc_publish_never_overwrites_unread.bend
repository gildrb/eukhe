# eukhe: the proof of LAW doc_publish_never_overwrites_unread
#
# PROOF: by induction on the re-reads, for every place a run stands
# (dpo.Ok: an ended run is safe). Each step keeps it: a target gone is
# refused; one whose version equals the base (the equation Nat.is_eq(v, b)
# == True) is placed, and that equation is the safety of the write; other
# bytes are rebased onto (the run goes on) or refused.

import Base
import ../../bend/doc_publish.bend as Dp
import ../../laws/doc_publish.bend as DocPublish
import ../../spec/harness/doc_publish.bend as S

# where a run stands is safe: an ended run replaced only bytes it read
def dpo.Ok(a: DocPublish.At) -> Type:
  match a:
    case DocPublish.Going{b, c}:
      Unit
    case DocPublish.Ended{r}:
      {S.safe(r) == True{} : Bool}

# other bytes after the step's choice: rebased onto, or refused
def dpo.left(+b: Nat, +c: Nat, +v: Nat, lt: Bool, r: Maybe<&2, Nat>) -> dpo.Ok(DocPublish.sp_next(Dp.step.moved(lt), b, c, Some{v}, r)):
  match lt:
    case True{}:
      match r:
        case None{}:
          {==}
        case Some{x}:
          Unit{}
    case False{}:
      {==}

# a version v met at base b: placed exactly when it is b
def dpo.eq(+n: Nat, +b: Nat, +c: Nat, +v: Nat, r: Maybe<&2, Nat>, e: Bool, h: {Nat.is_eq(v, b) == e : Bool}) -> dpo.Ok(DocPublish.sp_next(Dp.step(n, S.seen.of(e)), b, c, Some{v}, r)):
  match e:
    case True{}:
      h
    case False{}:
      dpo.left(b, c, v, Nat.is_lt(n, Dp.bound()), r)

# one step keeps a run safe
def dpo.next(+n: Nat, +b: Nat, +c: Nat, d: Maybe<&2, Nat>, r: Maybe<&2, Nat>) -> dpo.Ok(DocPublish.sp_next(Dp.step(n, S.seen(b, d)), b, c, d, r)):
  match d:
    case None{}:
      {==}
    case Some{+v}:
      dpo.eq(n, b, c, v, r, Nat.is_eq(v, b), {==})

def dpo.run(ls: List<&2, S.Reread>, +n: Nat, a: DocPublish.At, ok: dpo.Ok(a)) -> {S.safe(DocPublish.sp_run(ls, n, a)) == True{} : Bool}:
  match ls:
    case Nil{}:
      match a:
        case DocPublish.Going{b, c}:
          {==}
        case DocPublish.Ended{r}:
          ok
    case l <> rest:
      match l:
        case S.Reread{+d, +r}:
          match a:
            case DocPublish.Going{+b, +c}:
              dpo.run(rest, 1n+n, DocPublish.sp_next(Dp.step(n, S.seen(b, d)), b, c, d, r), dpo.next(n, b, c, d, r))
            case DocPublish.Ended{e}:
              ok

def DocPublish.doc_publish_never_overwrites_unread(ls, n, b, c):
  dpo.run(ls, n, DocPublish.Going{b, c}, Unit{})
