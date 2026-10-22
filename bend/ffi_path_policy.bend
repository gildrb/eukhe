# ffi_path_policy: the entry of the compiled Bend core for the judgment of
# a resolved path (bend/path_policy.bend `judge`; crates/eukhe-shell/src/
# paths.rs `judge`). The request is the policy and the resolved path with
# every component interned by Rust (paths deepest first); the reply is
# the class and whether the path holds a secret. Lists of paths cross as
# one list (bend/wire_flat.bend); a rule is a path: 0 then the path for
# Tree, 1 then the path for Dir, [2, n] for Named{n}. The wire format is
# bend/wire.bend; malformed input answers the error form.
#
#   request  List<Nat> List<Nat> List<Nat> List<Nat> Bool
#            (the roots, the rules, the secret entries, the path, looped)
#   reply    Nat Bool (the class: 0 Inside, 1 Outside, 2 Protected,
#            3 Secret; holds a secret)

import Base
import ./wire.bend as W
import ./wire_flat.bend as Fl
import ./path_policy.bend as Pp

def rule(r: Pp.Rule) -> List<&2, Nat>:
  match r:
    case Pp.Tree{p}:
      0n <> p
    case Pp.Dir{p}:
      1n <> p
    case Pp.Named{n}:
      [2n, n]

def rules(rs: List<&2, Pp.Rule>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      rule(r) <> rules(rest)

# the rule a path spells: n is the name of a Named rule, rest what follows
def rule.named(n: Nat, rest: List<&2, Nat>) -> Maybe<&2, Pp.Rule>:
  match rest:
    case Nil{}:
      Some{Pp.Named{n}}
    case x <> more:
      None{}

def rule.of(xs: List<&2, Nat>) -> Maybe<&2, Pp.Rule>:
  match xs:
    case Nil{}:
      None{}
    case t <> p:
      match t:
        case 0n:
          Some{Pp.Tree{p}}
        case 1n+a:
          match a:
            case 0n:
              Some{Pp.Dir{p}}
            case 1n+b:
              match b:
                case 0n:
                  match p:
                    case Nil{}:
                      None{}
                    case n <> rest:
                      rule.named(n, rest)
                case 1n+c:
                  None{}

def rules.cons(m: Maybe<&2, Pp.Rule>, ms: Maybe<&2, List<&2, Pp.Rule>>) -> Maybe<&2, List<&2, Pp.Rule>>:
  match m ms:
    case Some{r} Some{rs}:
      Some{r <> rs}
    case Some{r} None{}:
      None{}
    case None{} Some{rs}:
      None{}
    case None{} None{}:
      None{}

def rules.of(xss: List<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Pp.Rule>>:
  match xss:
    case Nil{}:
      Some{Nil{}}
    case xs <> rest:
      rules.cons(rule.of(xs), rules.of(rest))

def put_ns(xs: List<&2, Nat>, rest: String) -> String:
  W.put_list(~Nat, ~W.put_nat, xs, rest)

def get_ns(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

type Req is Data:
  Req{pol: Pp.Pol, res: Pp.Res}

def put_req(q: Req, rest: String) -> String:
  match q:
    case Req{p, r}:
      match p r:
        case Pp.Pol{ro, ru, se} Pp.Res{at, l}:
          put_ns(Fl.flat(ro), put_ns(Fl.flat(rules(ru)), put_ns(Fl.flat(se), put_ns(at, W.put_bool(l, rest)))))

def get_req.build(mro: Maybe<&2, List<&2, List<&2, Nat>>>, mru: Maybe<&2, List<&2, Pp.Rule>>, mse: Maybe<&2, List<&2, List<&2, Nat>>>, at: List<&2, Nat>, l: Bool, s: String) -> W.Dec<Req>:
  match mro:
    case None{}:
      W.Bad{}
    case Some{ro}:
      match mru:
        case None{}:
          W.Bad{}
        case Some{ru}:
          match mse:
            case None{}:
              W.Bad{}
            case Some{se}:
              W.Got{Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, s}

def get_req.rules(m: Maybe<&2, List<&2, List<&2, Nat>>>) -> Maybe<&2, List<&2, Pp.Rule>>:
  match m:
    case None{}:
      None{}
    case Some{xss}:
      rules.of(xss)

def get_req.looped(ro: List<&2, Nat>, ru: List<&2, Nat>, se: List<&2, Nat>, at: List<&2, Nat>, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      get_req.build(Fl.unflat(ro), get_req.rules(Fl.unflat(ru)), Fl.unflat(se), at, l, s)
    case W.Bad{}:
      W.Bad{}

def get_req.at(ro: List<&2, Nat>, ru: List<&2, Nat>, se: List<&2, Nat>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{at, s}:
      get_req.looped(ro, ru, se, at, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_req.secret(ro: List<&2, Nat>, ru: List<&2, Nat>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{se, s}:
      get_req.at(ro, ru, se, get_ns(s))
    case W.Bad{}:
      W.Bad{}

def get_req.rule_list(ro: List<&2, Nat>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ru, s}:
      get_req.secret(ro, ru, get_ns(s))
    case W.Bad{}:
      W.Bad{}

def get_req.roots(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ro, s}:
      get_req.rule_list(ro, get_ns(s))
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.roots(get_ns(s))

def cls(c: Pp.Cls) -> Nat:
  match c:
    case Pp.Inside{}:
      0n
    case Pp.Outside{}:
      1n
    case Pp.Protected{}:
      2n
    case Pp.Secret{}:
      3n

def put_judged(j: Pp.Judged, rest: String) -> String:
  match j:
    case Pp.Judged{c, h}:
      W.put_nat(cls(c), W.put_bool(h, rest))

# the reply to a request read whole (done: nothing is left)
def reply(done: Bool, q: Req) -> String:
  match done:
    case True{}:
      match q:
        case Req{p, r}:
          put_judged(Pp.judge(p, r), "")
    case False{}:
      W.err("path_policy: input left over")

def answer(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      reply(W.end(s), q)
    case W.Bad{}:
      W.err("path_policy: malformed request")

def ffi(input: String) -> String:
  answer(get_req(input))
