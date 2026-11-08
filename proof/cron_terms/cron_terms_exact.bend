# eukhe: the proof of LAW cron_terms_exact
# Each term by induction or by cases.

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_terms.bend as CronTerms

def ct.has(+p: Nat, xs: List<&2, Nat>) -> {CronTerms.has_spec(p, xs) == Cr.has(p, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %ct.has(p, t) : {Bool.or(Nat.is_eq(x, p), CronTerms.has_spec(p, t)) == Bool.or(Nat.is_eq(x, p), _) : Bool}
      {==}

def ct.ev_by(e: Cr.Ev) -> {Cr.Ev.by(e) == CronTerms.by_spec(e) : Maybe<&2, Nat>}:
  match e:
    case Cr.Create{p, s}:
      {==}
    case Cr.Take{p}:
      {==}
    case Cr.Recover{p}:
      {==}
    case Cr.Finish{p, i, o}:
      {==}
    case Cr.Abort{p}:
      {==}
    case Cr.Die{p}:
      {==}
    case Cr.Cancel{p, i}:
      {==}
    case Cr.Resume{p, i}:
      {==}
    case Cr.Tick{d}:
      {==}
    case Cr.RawJob{t}:
      {==}
    case Cr.RawClaim{t}:
      {==}
    case Cr.Corrupt{t}:
      {==}
    case Cr.Pause{p, i}:
      {==}
    case Cr.Stop{p, i}:
      {==}
    case Cr.Delete{p, i}:
      {==}
    case Cr.Edit{p, i, k}:
      {==}

def ct.ev_corrupt(e: Cr.Ev) -> {Cr.Ev.is_corrupt(e) == CronTerms.corrupt_spec(e) : Bool}:
  match e:
    case Cr.Create{p, s}:
      {==}
    case Cr.Take{p}:
      {==}
    case Cr.Recover{p}:
      {==}
    case Cr.Finish{p, i, o}:
      {==}
    case Cr.Abort{p}:
      {==}
    case Cr.Die{p}:
      {==}
    case Cr.Cancel{p, i}:
      {==}
    case Cr.Resume{p, i}:
      {==}
    case Cr.Tick{d}:
      {==}
    case Cr.RawJob{t}:
      {==}
    case Cr.RawClaim{t}:
      {==}
    case Cr.Corrupt{t}:
      {==}
    case Cr.Pause{p, i}:
      {==}
    case Cr.Stop{p, i}:
      {==}
    case Cr.Delete{p, i}:
      {==}
    case Cr.Edit{p, i, k}:
      {==}

def ct.ev_user(e: Cr.Ev) -> {Cr.Ev.is_user(e) == CronTerms.user_spec(e) : Bool}:
  match e:
    case Cr.Create{p, s}:
      {==}
    case Cr.Take{p}:
      {==}
    case Cr.Recover{p}:
      {==}
    case Cr.Finish{p, i, o}:
      {==}
    case Cr.Abort{p}:
      {==}
    case Cr.Die{p}:
      {==}
    case Cr.Cancel{p, i}:
      {==}
    case Cr.Resume{p, i}:
      {==}
    case Cr.Tick{d}:
      {==}
    case Cr.RawJob{t}:
      {==}
    case Cr.RawClaim{t}:
      {==}
    case Cr.Corrupt{t}:
      {==}
    case Cr.Pause{p, i}:
      {==}
    case Cr.Stop{p, i}:
      {==}
    case Cr.Delete{p, i}:
      {==}
    case Cr.Edit{p, i, k}:
      {==}

def ct.pick(b: Bool, cl: Maybe<&2, Cr.Claim>, rest: Maybe<&2, Cr.Claim>) -> {CronTerms.claim_spec.pick(b, cl, rest) == Cr.claim_of.pick(b, cl, rest) : Maybe<&2, Cr.Claim>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ct.claim(+i: Nat, rs: List<&2, Cr.Rec>) -> {CronTerms.claim_spec(i, rs) == Cr.claim_of(i, rs) : Maybe<&2, Cr.Claim>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Raw{x}:
          ct.claim(i, t)
        case Cr.Known{j}:
          match j:
            case Cr.Job{+id, s, st, nx, k, +cl, ru, ss, h}:
              %ct.claim(i, t) : {CronTerms.claim_spec.pick(Nat.is_eq(id, i), cl, CronTerms.claim_spec(i, t)) == Cr.claim_of.pick(Nat.is_eq(id, i), cl, _) : Maybe<&2, Cr.Claim>}
              ct.pick(Nat.is_eq(id, i), cl, CronTerms.claim_spec(i, t))

def ct.delay(k: Nat) -> {Cr.delay(k) == CronTerms.delay_spec(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      match e:
                        case 0n:
                          {==}
                        case 1n+f:
                          {==}

def ct.pick_succ(b: Bool, +p: Nat, +q: Nat) -> {Cr.later.pick(b, 1n+p, 1n+q) == 1n+Cr.later.pick(b, p, q) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ct.max(n: Nat, u: Nat) -> {Cr.later.pick(Nat.is_lt(n, u), n, u) == Nat.max(n, u) : Nat}:
  match n u:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+(+p) 1n+(+q):
      %Equal.sym(Nat, Cr.later.pick(Nat.is_lt(p, q), 1n+p, 1n+q), 1n+Cr.later.pick(Nat.is_lt(p, q), p, q), ct.pick_succ(Nat.is_lt(p, q), p, q)) : {_ == 1n+Nat.max(p, q) : Nat}
      %ct.max(p, q) : {1n+Cr.later.pick(Nat.is_lt(p, q), p, q) == 1n+_ : Nat}
      {==}

def ct.later(nx: Maybe<&2, Nat>, +u: Nat) -> {Cr.later(nx, u) == CronTerms.later_spec(nx, u) : Nat}:
  match nx:
    case None{}:
      {==}
    case Some{n}:
      ct.max(n, u)

def CronTerms.cron_terms_exact(p, xs, j, s, e, i, rs, k, nx, u):
  match j s e:
    case Cr.Job{ji, js, jst, jnx, jk, jcl, jrs, jss, jh} Cr.S{sb, srs, srd, sdead, sc, sn, sa} _:
      (Equal.sym(Bool, CronTerms.has_spec(p, xs), Cr.has(p, xs), ct.has(p, xs)), ({==}, ({==}, ({==}, ({==}, ({==}, (ct.ev_by(e), (ct.ev_corrupt(e), (ct.ev_user(e), (Equal.sym(Maybe<&2, Cr.Claim>, CronTerms.claim_spec(i, rs), Cr.claim_of(i, rs), ct.claim(i, rs)), (ct.delay(k), ct.later(nx, u))))))))))))
