# ffi_effort: the entry of the compiled Bend core for the thinking ladder
# of a model (bend/infer.bend section 6 and bend/effort.bend: the offer,
# the S10 clamp and cycle; crates/eukhe-ai `models/ladder.rs`). One
# request, one reply, in the wire format of bend/wire.bend:
#
#   request (a constructor)                  reply
#   0 Offered{f: Facts}                      List<Lv>    Ef.offered(m)
#   1 Clamp{f: Facts, l: Lv}                 Lv          Ef.clamp(m, l)
#   2 Cycle{f: Facts, l: Lv, d: Dir}         Maybe<Lv>   Ef.cycle(m, l, d)
#
# where m is If.lad.model(If.lad.reasons(flag, by_map, explicit),
# explicit, rule, Defaults{reasoning, plain}) and Facts is the record
# (flag: Bool, by_map: Bool, explicit: Maybe<LvMap>, rule: Maybe<LvMap>,
# reasoning: List<Lv>, plain: List<Lv>). A level is its tag (off 0 .. max
# 6), an entry its tag (missing 0, null 1, wire 2), a map its 7 entries in
# ladder order, a direction its tag (forward 0, backward 1). A malformed
# request, or one with input left over, answers the error form. Pure: no
# IO, no @unsafe, no foreign effect.

import Base
import ./wire.bend as W
import ./effort.bend as Ef
import ./infer.bend as If

# Decoding
# --------

# two decoded values, in order
type P2<-A: Data, -B: Data> is Data:
  P2{fst: A, snd: B}

# the value of d paired with the next value, read by get from d's rest
def seq.fin(~A: Data, ~B: Data, a: A, d: W.Dec<B>) -> W.Dec<P2<A, B>>:
  match d:
    case W.Got{b, r}:
      W.Got{P2{a, b}, r}
    case W.Bad{}:
      W.Bad{}

def seq(~A: Data, ~B: Data, ~get: String -> W.Dec<B>, d: W.Dec<A>) -> W.Dec<P2<A, B>>:
  match d:
    case W.Got{a, r}:
      seq.fin(~A, ~B, a, get(r))
    case W.Bad{}:
      W.Bad{}

# a level, by tag
def get_lv.tag(t: Nat, s: String) -> W.Dec<Ef.Lv>:
  match t:
    case 0n:
      W.Got{Ef.Off{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{Ef.Minimal{}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{Ef.Low{}, s}
            case 1n+c:
              match c:
                case 0n:
                  W.Got{Ef.Medium{}, s}
                case 1n+e:
                  match e:
                    case 0n:
                      W.Got{Ef.High{}, s}
                    case 1n+f:
                      match f:
                        case 0n:
                          W.Got{Ef.Xhigh{}, s}
                        case 1n+g:
                          match g:
                            case 0n:
                              W.Got{Ef.Max{}, s}
                            case 1n+h:
                              W.Bad{}

def get_lv.go(d: W.Dec<Nat>) -> W.Dec<Ef.Lv>:
  match d:
    case W.Got{t, r}:
      get_lv.tag(t, r)
    case W.Bad{}:
      W.Bad{}

def get_lv(s: String) -> W.Dec<Ef.Lv>:
  get_lv.go(W.get_nat(s))

# an entry of a map, by tag
def get_ent.tag(t: Nat, s: String) -> W.Dec<Ef.Ent>:
  match t:
    case 0n:
      W.Got{Ef.Missing{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{Ef.Null{}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{Ef.Wire{}, s}
            case 1n+c:
              W.Bad{}

def get_ent.go(d: W.Dec<Nat>) -> W.Dec<Ef.Ent>:
  match d:
    case W.Got{t, r}:
      get_ent.tag(t, r)
    case W.Bad{}:
      W.Bad{}

def get_ent(s: String) -> W.Dec<Ef.Ent>:
  get_ent.go(W.get_nat(s))

# a map: the entries of off .. max
def get_map.of(d: W.Dec<P2<P2<P2<P2<P2<P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>>) -> W.Dec<Ef.LvMap>:
  match d:
    case W.Got{q, r}:
      P2{q6, mx} = q
      P2{q5, xh} = q6
      P2{q4, hi} = q5
      P2{q3, me} = q4
      P2{q2, lo} = q3
      P2{o, mi} = q2
      W.Got{Ef.LvMap{o, mi, lo, me, hi, xh, mx}, r}
    case W.Bad{}:
      W.Bad{}

def get_map(s: String) -> W.Dec<Ef.LvMap>:
  get_map.of(seq(~P2<P2<P2<P2<P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~get_ent, seq(~P2<P2<P2<P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~get_ent, seq(~P2<P2<P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~get_ent, seq(~P2<P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~get_ent, seq(~P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, ~get_ent, seq(~Ef.Ent, ~Ef.Ent, ~get_ent, get_ent(s))))))))

# a Maybe<LvMap>: 0 None, 1 then the map
def get_mmap.some(d: W.Dec<Ef.LvMap>) -> W.Dec<Maybe<&2, Ef.LvMap>>:
  match d:
    case W.Got{m, r}:
      W.Got{Some{m}, r}
    case W.Bad{}:
      W.Bad{}

def get_mmap.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Ef.LvMap>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n+p:
      match p:
        case 0n:
          get_mmap.some(get_map(s))
        case 1n+q:
          W.Bad{}

def get_mmap.go(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, Ef.LvMap>>:
  match d:
    case W.Got{t, r}:
      get_mmap.tag(t, r)
    case W.Bad{}:
      W.Bad{}

def get_mmap(s: String) -> W.Dec<Maybe<&2, Ef.LvMap>>:
  get_mmap.go(W.get_nat(s))

# a cycle direction, by tag
def get_dir.tag(t: Nat, s: String) -> W.Dec<Ef.Dir>:
  match t:
    case 0n:
      W.Got{Ef.Forward{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{Ef.Backward{}, s}
        case 1n+b:
          W.Bad{}

def get_dir.go(d: W.Dec<Nat>) -> W.Dec<Ef.Dir>:
  match d:
    case W.Got{t, r}:
      get_dir.tag(t, r)
    case W.Bad{}:
      W.Bad{}

def get_dir(s: String) -> W.Dec<Ef.Dir>:
  get_dir.go(W.get_nat(s))

def get_lvs(s: String) -> W.Dec<List<&2, Ef.Lv>>:
  W.get_list(~Ef.Lv, ~get_lv, s)

# The facts of a model
# --------------------

type Facts is Data:
  Facts{flag: Bool, by_map: Bool, explicit: Maybe<&2, Ef.LvMap>, rule: Maybe<&2, Ef.LvMap>, reasoning: List<&2, Ef.Lv>, plain: List<&2, Ef.Lv>}

def get_facts.of(d: W.Dec<P2<P2<P2<P2<P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, List<&2, Ef.Lv>>>) -> W.Dec<Facts>:
  match d:
    case W.Got{q, r}:
      P2{q5, pl} = q
      P2{q4, re} = q5
      P2{q3, ru} = q4
      P2{q2, ex} = q3
      P2{f, bm} = q2
      W.Got{Facts{f, bm, ex, ru, re, pl}, r}
    case W.Bad{}:
      W.Bad{}

def get_facts(s: String) -> W.Dec<Facts>:
  get_facts.of(seq(~P2<P2<P2<P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~get_lvs, seq(~P2<P2<P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~get_lvs, seq(~P2<P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, ~get_mmap, seq(~P2<Bool, Bool>, ~Maybe<&2, Ef.LvMap>, ~get_mmap, seq(~Bool, ~Bool, ~W.get_bool, W.get_bool(s)))))))

# the S10 model whose ladder the facts give
def model(f: Facts) -> Ef.Mdl:
  match f:
    case Facts{flag, by_map, +explicit, rule, reasoning, plain}:
      If.lad.model(If.lad.reasons(flag, by_map, explicit), explicit, rule, If.Defaults{reasoning, plain})

# Requests
# --------

type Req is Data:
  Offered{f: Facts}
  Clamp{f: Facts, l: Ef.Lv}
  Cycle{f: Facts, l: Ef.Lv, d: Ef.Dir}

def get_offered.of(d: W.Dec<Facts>) -> W.Dec<Req>:
  match d:
    case W.Got{f, r}:
      W.Got{Offered{f}, r}
    case W.Bad{}:
      W.Bad{}

def get_clamp.of(d: W.Dec<P2<Facts, Ef.Lv>>) -> W.Dec<Req>:
  match d:
    case W.Got{q, r}:
      P2{f, l} = q
      W.Got{Clamp{f, l}, r}
    case W.Bad{}:
      W.Bad{}

def get_cycle.of(d: W.Dec<P2<P2<Facts, Ef.Lv>, Ef.Dir>>) -> W.Dec<Req>:
  match d:
    case W.Got{q, r}:
      P2{q2, dir} = q
      P2{f, l} = q2
      W.Got{Cycle{f, l, dir}, r}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_offered.of(get_facts(s))
    case 1n+a:
      match a:
        case 0n:
          get_clamp.of(seq(~Facts, ~Ef.Lv, ~get_lv, get_facts(s)))
        case 1n+b:
          match b:
            case 0n:
              get_cycle.of(seq(~P2<Facts, Ef.Lv>, ~Ef.Dir, ~get_dir, seq(~Facts, ~Ef.Lv, ~get_lv, get_facts(s))))
            case 1n+c:
              W.Bad{}

def get_req.go(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{t, r}:
      get_req.tag(t, r)
    case W.Bad{}:
      W.Bad{}

# a request
def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Replies
# -------

def put_lv(l: Ef.Lv, rest: String) -> String:
  W.put_nat(Ef.Lv.idx(l), rest)

def put_mlv(m: Maybe<&2, Ef.Lv>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{l}:
      W.put_nat(1n, put_lv(l, rest))

# the reply to a request
def answer(q: Req) -> String:
  match q:
    case Offered{f}:
      W.put_list(~Ef.Lv, ~put_lv, Ef.offered(model(f)), "")
    case Clamp{f, l}:
      put_lv(Ef.clamp(model(f), l), "")
    case Cycle{f, l, d}:
      put_mlv(Ef.cycle(model(f), l, d), "")

# whole is W.end(rest): nothing is left after the request
def ffi.done(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      W.err("ladder request: input left over")

def ffi.go(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{q, r}:
      ffi.done(W.end(r), q)
    case W.Bad{}:
      W.err("ladder request: malformed")

# the entry: decode the request, answer it
def ffi(input: String) -> String:
  ffi.go(get_req(input))
