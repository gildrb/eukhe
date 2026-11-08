# eukhe: lemmas of area path_policy: the entry reads and writes the
# spec's spelling (laws/path_policy/spec.bend, section the entry, whole)

import Base
import ../../../bend/ffi_path_policy.bend as FPp
import ../../../bend/path_policy.bend as Pp
import ../../../bend/wire.bend as Wr
import ../../../bend/wire_flat.bend as Fl
import ../../../laws/base.bend as LawsBase
import ../../../laws/path_policy/spec.bend as PathPolicySpec
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../../wire/wire_list_exact.bend as PWireListExact
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../glob/base/entry.bend as LGlobEntry
import ../path_class_spec.bend as PPathClassSpec
import ../path_holds_spec.bend as PPathHoldsSpec

# Maybe and Bool kit
# ------------------

def pe.get(-A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def pe.inj(-A: Data, +a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => pe.get(A, m, a), Some{a}, Some{b}, e)

def pe.if_some(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case Some{x}:
      G
    case None{}:
      Unit

# no value is a value
def pe.none_some(-A: Data, -G: Type, -b: A, e: {None{} == Some{b} : Maybe<&2, A>}) -> G:
  %e : pe.if_some(A, _, G)
  Unit{}

def pe.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# The spelling
# ------------

# a path's items before rest are its names, each plus one, then 0
def pe.one(xs: List<&2, Nat>, +rest: List<&2, Nat>) -> {Fl.one(xs, rest) == List.append(&2, Nat, PathPolicySpec.pp_succ(xs), 0n <> rest) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => (1n+x) <> z, Fl.one(t, rest), List.append(&2, Nat, PathPolicySpec.pp_succ(t), 0n <> rest), pe.one(t, rest))

# the flat list is the spec's
def pe.flat(xss: List<&2, List<&2, Nat>>) -> {Fl.flat(xss) == PathPolicySpec.pp_flat(xss) : List<&2, Nat>}:
  match xss:
    case Nil{}:
      {==}
    case +xs <> +t:
      Equal.trans(List<&2, Nat>, Fl.one(xs, Fl.flat(t)), List.append(&2, Nat, PathPolicySpec.pp_succ(xs), 0n <> Fl.flat(t)), List.append(&2, Nat, PathPolicySpec.pp_succ(xs), 0n <> PathPolicySpec.pp_flat(t)), pe.one(xs, Fl.flat(t)), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => List.append(&2, Nat, PathPolicySpec.pp_succ(xs), 0n <> z), Fl.flat(t), PathPolicySpec.pp_flat(t), pe.flat(t)))

def pe.rule(r: Pp.Rule) -> {FPp.rule(r) == PathPolicySpec.pp_rule(r) : List<&2, Nat>}:
  match r:
    case Pp.Tree{p}:
      {==}
    case Pp.Dir{p}:
      {==}
    case Pp.Named{n}:
      {==}

def pe.rules(rs: List<&2, Pp.Rule>) -> {FPp.rules(rs) == PathPolicySpec.pp_rules(rs) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      %Equal.sym(List<&2, Nat>, FPp.rule(r), PathPolicySpec.pp_rule(r), pe.rule(r)) : {_ <> FPp.rules(t) == PathPolicySpec.pp_rule(r) <> PathPolicySpec.pp_rules(t) : List<&2, List<&2, Nat>>}
      Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => PathPolicySpec.pp_rule(r) <> z, FPp.rules(t), PathPolicySpec.pp_rules(t), pe.rules(t))

# the flat rules are the spec's
def pe.flat_rules(+rs: List<&2, Pp.Rule>) -> {Fl.flat(FPp.rules(rs)) == PathPolicySpec.pp_flat(PathPolicySpec.pp_rules(rs)) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, Fl.flat(FPp.rules(rs)), Fl.flat(PathPolicySpec.pp_rules(rs)), PathPolicySpec.pp_flat(PathPolicySpec.pp_rules(rs)), Equal.cong(List<&2, List<&2, Nat>>, List<&2, Nat>, z => Fl.flat(z), FPp.rules(rs), PathPolicySpec.pp_rules(rs), pe.rules(rs)), pe.flat(PathPolicySpec.pp_rules(rs)))

# a list of Nats the entry writes is the spec's
def pe.ns(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +r1: String, +r2: String, e1: {xs == ys : List<&2, Nat>}, e2: {r1 == r2 : String}) -> {FPp.put_ns(xs, r1) == LawsBase.wire_spell_nats(ys, r2) : String}:
  %Equal.sym(List<&2, Nat>, xs, ys, e1) : {FPp.put_ns(_, r1) == LawsBase.wire_spell_nats(ys, r2) : String}
  %Equal.sym(String, r1, r2, e2) : {FPp.put_ns(ys, _) == LawsBase.wire_spell_nats(ys, r2) : String}
  Wire.wire_nats_spells(ys, r2)

# the entry's encoding of four lists and a flag
def pe.enc(ns1: List<&2, Nat>, ns2: List<&2, Nat>, ns3: List<&2, Nat>, at: List<&2, Nat>, l: Bool, rest: String) -> String:
  FPp.put_ns(ns1, FPp.put_ns(ns2, FPp.put_ns(ns3, FPp.put_ns(at, Wr.put_bool(l, rest)))))

# lists equal to the request's flat lists spell the spec's request
def pe.enc_eq(+ns1: List<&2, Nat>, +ns2: List<&2, Nat>, +ns3: List<&2, Nat>, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool, +rest: String, e1: {ns1 == Fl.flat(ro) : List<&2, Nat>}, e2: {ns2 == Fl.flat(FPp.rules(ru)) : List<&2, Nat>}, e3: {ns3 == Fl.flat(se) : List<&2, Nat>}) -> {pe.enc(ns1, ns2, ns3, at, l, rest) == PathPolicySpec.pp_spell_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) : String}:
  +b = Wr.put_bool(l, rest)
  +f1 = PathPolicySpec.pp_flat(ro)
  +f2 = PathPolicySpec.pp_flat(PathPolicySpec.pp_rules(ru))
  +f3 = PathPolicySpec.pp_flat(se)
  +i4 = pe.ns(at, at, b, b, {==}, {==})
  +i3 = pe.ns(ns3, f3, FPp.put_ns(at, b), LawsBase.wire_spell_nats(at, b), Equal.trans(List<&2, Nat>, ns3, Fl.flat(se), f3, e3, pe.flat(se)), i4)
  +i2 = pe.ns(ns2, f2, FPp.put_ns(ns3, FPp.put_ns(at, b)), LawsBase.wire_spell_nats(f3, LawsBase.wire_spell_nats(at, b)), Equal.trans(List<&2, Nat>, ns2, Fl.flat(FPp.rules(ru)), f2, e2, pe.flat_rules(ru)), i3)
  pe.ns(ns1, f1, FPp.put_ns(ns2, FPp.put_ns(ns3, FPp.put_ns(at, b))), LawsBase.wire_spell_nats(f2, LawsBase.wire_spell_nats(f3, LawsBase.wire_spell_nats(at, b))), Equal.trans(List<&2, Nat>, ns1, Fl.flat(ro), f1, e1, pe.flat(ro)), i2)

# the entry's encoding of a request is the spec's spelling
def pe.put(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool, +rest: String) -> {FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) == PathPolicySpec.pp_spell_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) : String}:
  pe.enc_eq(Fl.flat(ro), Fl.flat(FPp.rules(ru)), Fl.flat(se), ro, ru, se, at, l, rest, {==}, {==}, {==})

# The fits
# --------

def pe.F(x1: List<&2, Nat>, x2: List<&2, Nat>, x3: List<&2, Nat>, x4: List<&2, Nat>) -> Bool:
  Bool.and(Bool.and(Bool.and(PathPolicySpec.pp_ns_fit(x1), PathPolicySpec.pp_ns_fit(x2)), PathPolicySpec.pp_ns_fit(x3)), PathPolicySpec.pp_ns_fit(x4))

def pe.F_eq(+x1: List<&2, Nat>, +y1: List<&2, Nat>, +x2: List<&2, Nat>, +y2: List<&2, Nat>, +x3: List<&2, Nat>, +y3: List<&2, Nat>, +x4: List<&2, Nat>, e1: {x1 == y1 : List<&2, Nat>}, e2: {x2 == y2 : List<&2, Nat>}, e3: {x3 == y3 : List<&2, Nat>}) -> {pe.F(x1, x2, x3, x4) == pe.F(y1, y2, y3, x4) : Bool}:
  %Equal.sym(List<&2, Nat>, x1, y1, e1) : {pe.F(_, x2, x3, x4) == pe.F(y1, y2, y3, x4) : Bool}
  %Equal.sym(List<&2, Nat>, x2, y2, e2) : {pe.F(y1, _, x3, x4) == pe.F(y1, y2, y3, x4) : Bool}
  %Equal.sym(List<&2, Nat>, x3, y3, e3) : {pe.F(y1, y2, _, x4) == pe.F(y1, y2, y3, x4) : Bool}
  {==}

# the entry's fits of a request is the spec's
def pe.fits(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {pe.F(Fl.flat(ro), Fl.flat(FPp.rules(ru)), Fl.flat(se), at) == pe.F(PathPolicySpec.pp_flat(ro), PathPolicySpec.pp_flat(PathPolicySpec.pp_rules(ru)), PathPolicySpec.pp_flat(se), at) : Bool}:
  pe.F_eq(Fl.flat(ro), PathPolicySpec.pp_flat(ro), Fl.flat(FPp.rules(ru)), PathPolicySpec.pp_flat(PathPolicySpec.pp_rules(ru)), Fl.flat(se), PathPolicySpec.pp_flat(se), at, pe.flat(ro), pe.flat_rules(ru), pe.flat(se))

# The reply
# ---------

def pe.code(c: Pp.Cls) -> {FPp.cls(c) == PathPolicySpec.pp_code(c) : Nat}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      {==}
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      {==}

# the entry's reply to a request is the spec's
def pe.reply(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool) -> {FPp.put_judged(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), "") == PathPolicySpec.pp_spell_reply(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) : String}:
  +pol = {Pp.Pol{ro, ru, se} : Pp.Pol}
  +res = {Pp.Res{at, l} : Pp.Res}
  %Equal.sym(Pp.Cls, Pp.class_res(pol, res), PathPolicySpec.pp_class(pol, res), PathPolicySpec.path_class_spec(pol, res)) : {Wr.put_nat(FPp.cls(_), Wr.put_bool(Pp.holds_at(pol, at), "")) == PathPolicySpec.pp_spell_reply(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) : String}
  %Equal.sym(Nat, FPp.cls(PathPolicySpec.pp_class(pol, res)), PathPolicySpec.pp_code(PathPolicySpec.pp_class(pol, res)), pe.code(PathPolicySpec.pp_class(pol, res))) : {Wr.put_nat(_, Wr.put_bool(Pp.holds_at(pol, at), "")) == PathPolicySpec.pp_spell_reply(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) : String}
  %Equal.sym(Bool, Pp.holds_at(pol, at), PathPolicySpec.pp_holds(pol, at), PathPolicySpec.path_holds_spec(pol, at)) : {Wr.put_nat(PathPolicySpec.pp_code(PathPolicySpec.pp_class(pol, res)), Wr.put_bool(_, "")) == PathPolicySpec.pp_spell_reply(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) : String}
  {==}

# Reading: a decoded request is exactly a spelled one
# ---------------------------------------------------

# the items a state of the flat decoder stands for
def pe.st_flat(st: Fl.St) -> List<&2, Nat>:
  match st:
    case Fl.Start{}:
      Nil{}
    case Fl.Mid{o, d}:
      Fl.one(o, Fl.flat(d))

def pe.st_lists(st: Fl.St) -> {pe.st_flat(st) == Fl.flat(Fl.St.lists(st)) : List<&2, Nat>}:
  match st:
    case Fl.Start{}:
      {==}
    case Fl.Mid{o, d}:
      {==}

def pe.FX(ns: List<&2, Nat>, m: Maybe<&2, Fl.St>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{st}:
      {ns == pe.st_flat(st) : List<&2, Nat>}

def pe.fold_step(n: Nat, +rest: List<&2, Nat>, m: Maybe<&2, Fl.St>, ih: pe.FX(rest, m)) -> pe.FX(n <> rest, Fl.step(n, m)):
  match n:
    case 0n:
      match m:
        case None{}:
          Unit{}
        case Some{+st}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => 0n <> z, rest, Fl.flat(Fl.St.lists(st)), Equal.trans(List<&2, Nat>, rest, pe.st_flat(st), Fl.flat(Fl.St.lists(st)), ih, pe.st_lists(st)))
    case 1n+x:
      match m:
        case None{}:
          Unit{}
        case Some{st}:
          match st:
            case Fl.Start{}:
              Unit{}
            case Fl.Mid{o, d}:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => (1n+x) <> z, rest, Fl.one(o, Fl.flat(d)), ih)

def pe.fold(ns: List<&2, Nat>) -> pe.FX(ns, Fl.fold(ns)):
  match ns:
    case Nil{}:
      {==}
    case +n <> +rest:
      pe.fold_step(n, rest, Fl.fold(rest), pe.fold(rest))

def pe.unflat.at(m: Maybe<&2, Fl.St>, +ns: List<&2, Nat>, +xss: List<&2, List<&2, Nat>>, fx: pe.FX(ns, m), e: {Fl.unflat.fin(m) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}) -> {ns == Fl.flat(xss) : List<&2, Nat>}:
  match m:
    case None{}:
      pe.none_some(List<&2, List<&2, Nat>>, {ns == Fl.flat(xss) : List<&2, Nat>}, xss, e)
    case Some{+st}:
      +el = pe.inj(List<&2, List<&2, Nat>>, Fl.St.lists(st), xss, e)
      Equal.trans(List<&2, Nat>, ns, Fl.flat(Fl.St.lists(st)), Fl.flat(xss), Equal.trans(List<&2, Nat>, ns, pe.st_flat(st), Fl.flat(Fl.St.lists(st)), fx, pe.st_lists(st)), Equal.cong(List<&2, List<&2, Nat>>, List<&2, Nat>, z => Fl.flat(z), Fl.St.lists(st), xss, el))

# a list the flat decoder reads is the flat list of what it reads
def pe.unflat(+ns: List<&2, Nat>, +xss: List<&2, List<&2, Nat>>, e: {Fl.unflat(ns) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}) -> {ns == Fl.flat(xss) : List<&2, Nat>}:
  pe.unflat.at(Fl.fold(ns), ns, xss, pe.fold(ns), e)

# a path the rule decoder reads is the path of the rule it reads
def pe.rule_of(xs: List<&2, Nat>, +r: Pp.Rule, e: {FPp.rule.of(xs) == Some{r} : Maybe<&2, Pp.Rule>}) -> {xs == FPp.rule(r) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      pe.none_some(Pp.Rule, {Nil{} == FPp.rule(r) : List<&2, Nat>}, r, e)
    case t <> p:
      match t:
        case 0n:
          %pe.inj(Pp.Rule, Pp.Tree{p}, r, e) : {0n <> p == FPp.rule(_) : List<&2, Nat>}
          {==}
        case 1n+a:
          match a:
            case 0n:
              %pe.inj(Pp.Rule, Pp.Dir{p}, r, e) : {1n <> p == FPp.rule(_) : List<&2, Nat>}
              {==}
            case 1n+b:
              match b:
                case 0n:
                  match p:
                    case Nil{}:
                      pe.none_some(Pp.Rule, {[2n] == FPp.rule(r) : List<&2, Nat>}, r, e)
                    case n <> rest:
                      match rest:
                        case Nil{}:
                          %pe.inj(Pp.Rule, Pp.Named{n}, r, e) : {[2n, n] == FPp.rule(_) : List<&2, Nat>}
                          {==}
                        case y <> more:
                          pe.none_some(Pp.Rule, {2n <> n <> y <> more == FPp.rule(r) : List<&2, Nat>}, r, e)
                case 1n+c:
                  pe.none_some(Pp.Rule, {(3n+c) <> p == FPp.rule(r) : List<&2, Nat>}, r, e)

def pe.rules_cons(m1: Maybe<&2, Pp.Rule>, +xs: List<&2, Nat>, em1: {FPp.rule.of(xs) == m1 : Maybe<&2, Pp.Rule>}, m2: Maybe<&2, List<&2, Pp.Rule>>, +rest: List<&2, List<&2, Nat>>, em2: {FPp.rules.of(rest) == m2 : Maybe<&2, List<&2, Pp.Rule>>}, +ru: List<&2, Pp.Rule>, e: {FPp.rules.cons(m1, m2) == Some{ru} : Maybe<&2, List<&2, Pp.Rule>>}, ih: @rs: List<&2, Pp.Rule> -> {FPp.rules.of(rest) == Some{rs} : Maybe<&2, List<&2, Pp.Rule>>} -> {rest == FPp.rules(rs) : List<&2, List<&2, Nat>>}) -> {xs <> rest == FPp.rules(ru) : List<&2, List<&2, Nat>>}:
  match m1 m2:
    case Some{+r} Some{+rs}:
      +ex = pe.rule_of(xs, r, em1)
      +er = ih(rs, em2)
      %pe.inj(List<&2, Pp.Rule>, r <> rs, ru, e) : {xs <> rest == FPp.rules(_) : List<&2, List<&2, Nat>>}
      %Equal.sym(List<&2, Nat>, xs, FPp.rule(r), ex) : {_ <> rest == FPp.rule(r) <> FPp.rules(rs) : List<&2, List<&2, Nat>>}
      %Equal.sym(List<&2, List<&2, Nat>>, rest, FPp.rules(rs), er) : {FPp.rule(r) <> _ == FPp.rule(r) <> FPp.rules(rs) : List<&2, List<&2, Nat>>}
      {==}
    case Some{r} None{}:
      pe.none_some(List<&2, Pp.Rule>, {xs <> rest == FPp.rules(ru) : List<&2, List<&2, Nat>>}, ru, e)
    case None{} Some{rs}:
      pe.none_some(List<&2, Pp.Rule>, {xs <> rest == FPp.rules(ru) : List<&2, List<&2, Nat>>}, ru, e)
    case None{} None{}:
      pe.none_some(List<&2, Pp.Rule>, {xs <> rest == FPp.rules(ru) : List<&2, List<&2, Nat>>}, ru, e)

# paths the rules decoder reads are the paths of the rules it reads
def pe.rules_of(xss: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, e: {FPp.rules.of(xss) == Some{ru} : Maybe<&2, List<&2, Pp.Rule>>}) -> {xss == FPp.rules(ru) : List<&2, List<&2, Nat>>}:
  match xss:
    case Nil{}:
      %pe.inj(List<&2, Pp.Rule>, Nil{}, ru, e) : {Nil{} == FPp.rules(_) : List<&2, List<&2, Nat>>}
      {==}
    case +xs <> +rest:
      pe.rules_cons(FPp.rule.of(xs), xs, {==}, FPp.rules.of(rest), rest, {==}, ru, e, rs => h => pe.rules_of(rest, rs, h))

def pe.rules_m(m: Maybe<&2, List<&2, List<&2, Nat>>>, +ns: List<&2, Nat>, em: {Fl.unflat(ns) == m : Maybe<&2, List<&2, List<&2, Nat>>>}, +ru: List<&2, Pp.Rule>, e: {FPp.get_req.rules(m) == Some{ru} : Maybe<&2, List<&2, Pp.Rule>>}) -> {ns == Fl.flat(FPp.rules(ru)) : List<&2, Nat>}:
  match m:
    case None{}:
      pe.none_some(List<&2, Pp.Rule>, {ns == Fl.flat(FPp.rules(ru)) : List<&2, Nat>}, ru, e)
    case Some{+xss}:
      Equal.trans(List<&2, Nat>, ns, Fl.flat(xss), Fl.flat(FPp.rules(ru)), pe.unflat(ns, xss, em), Equal.cong(List<&2, List<&2, Nat>>, List<&2, Nat>, z => Fl.flat(z), xss, FPp.rules(ru), pe.rules_of(xss, ru, e)))

# what a decoder answer says about its input s: s spells the request,
# and the request fits
def pe.RP(s: String, d: Wr.Dec<FPp.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == PathPolicySpec.pp_spell_req(q, r) : String} & {PathPolicySpec.pp_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def pe.got(-s: String, +ns1: List<&2, Nat>, +ns2: List<&2, Nat>, +ns3: List<&2, Nat>, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool, +s5: String, pre: {s == pe.enc(ns1, ns2, ns3, at, l, s5) : String}, f1: {PathPolicySpec.pp_ns_fit(ns1) == True{} : Bool}, f2: {PathPolicySpec.pp_ns_fit(ns2) == True{} : Bool}, f3: {PathPolicySpec.pp_ns_fit(ns3) == True{} : Bool}, f4: {PathPolicySpec.pp_ns_fit(at) == True{} : Bool}, +e1: {ns1 == Fl.flat(ro) : List<&2, Nat>}, +e2: {ns2 == Fl.flat(FPp.rules(ru)) : List<&2, Nat>}, +e3: {ns3 == Fl.flat(se) : List<&2, Nat>}) -> pe.RP(s, Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, s5}):
  +es = Equal.trans(String, s, pe.enc(ns1, ns2, ns3, at, l, s5), PathPolicySpec.pp_spell_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, s5), pre, pe.enc_eq(ns1, ns2, ns3, ro, ru, se, at, l, s5, e1, e2, e3))
  +ft = pe.and_tt(Bool.and(Bool.and(PathPolicySpec.pp_ns_fit(ns1), PathPolicySpec.pp_ns_fit(ns2)), PathPolicySpec.pp_ns_fit(ns3)), PathPolicySpec.pp_ns_fit(at), pe.and_tt(Bool.and(PathPolicySpec.pp_ns_fit(ns1), PathPolicySpec.pp_ns_fit(ns2)), PathPolicySpec.pp_ns_fit(ns3), pe.and_tt(PathPolicySpec.pp_ns_fit(ns1), PathPolicySpec.pp_ns_fit(ns2), f1, f2), f3), f4)
  +eF = pe.F_eq(ns1, PathPolicySpec.pp_flat(ro), ns2, PathPolicySpec.pp_flat(PathPolicySpec.pp_rules(ru)), ns3, PathPolicySpec.pp_flat(se), at, Equal.trans(List<&2, Nat>, ns1, Fl.flat(ro), PathPolicySpec.pp_flat(ro), e1, pe.flat(ro)), Equal.trans(List<&2, Nat>, ns2, Fl.flat(FPp.rules(ru)), PathPolicySpec.pp_flat(PathPolicySpec.pp_rules(ru)), e2, pe.flat_rules(ru)), Equal.trans(List<&2, Nat>, ns3, Fl.flat(se), PathPolicySpec.pp_flat(se), e3, pe.flat(se)))
  (es, Equal.trans(Bool, PathPolicySpec.pp_req_fits(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}), pe.F(ns1, ns2, ns3, at), True{}, Equal.sym(Bool, pe.F(ns1, ns2, ns3, at), pe.F(PathPolicySpec.pp_flat(ro), PathPolicySpec.pp_flat(PathPolicySpec.pp_rules(ru)), PathPolicySpec.pp_flat(se), at), eF), ft))

def pe.build(-s: String, +ns1: List<&2, Nat>, +ns2: List<&2, Nat>, +ns3: List<&2, Nat>, +at: List<&2, Nat>, +l: Bool, +s5: String, pre: {s == pe.enc(ns1, ns2, ns3, at, l, s5) : String}, f1: {PathPolicySpec.pp_ns_fit(ns1) == True{} : Bool}, f2: {PathPolicySpec.pp_ns_fit(ns2) == True{} : Bool}, f3: {PathPolicySpec.pp_ns_fit(ns3) == True{} : Bool}, f4: {PathPolicySpec.pp_ns_fit(at) == True{} : Bool},
  mro: Maybe<&2, List<&2, List<&2, Nat>>>, emro: {Fl.unflat(ns1) == mro : Maybe<&2, List<&2, List<&2, Nat>>>}, mru: Maybe<&2, List<&2, Pp.Rule>>, emru: {FPp.get_req.rules(Fl.unflat(ns2)) == mru : Maybe<&2, List<&2, Pp.Rule>>}, mse: Maybe<&2, List<&2, List<&2, Nat>>>, emse: {Fl.unflat(ns3) == mse : Maybe<&2, List<&2, List<&2, Nat>>>}) -> pe.RP(s, FPp.get_req.build(mro, mru, mse, at, l, s5)):
  match mro:
    case None{}:
      Unit{}
    case Some{+ro}:
      match mru:
        case None{}:
          Unit{}
        case Some{+ru}:
          match mse:
            case None{}:
              Unit{}
            case Some{+se}:
              pe.got(s, ns1, ns2, ns3, ro, ru, se, at, l, s5, pre, f1, f2, f3, f4, pe.unflat(ns1, ro, emro), pe.rules_m(Fl.unflat(ns2), ns2, {==}, ru, emru), pe.unflat(ns3, se, emse))

def pe.looped(-s: String, +ns1: List<&2, Nat>, +ns2: List<&2, Nat>, +ns3: List<&2, Nat>, +at: List<&2, Nat>, +s4: String, pre: {s == FPp.put_ns(ns1, FPp.put_ns(ns2, FPp.put_ns(ns3, FPp.put_ns(at, s4)))) : String}, f1: {PathPolicySpec.pp_ns_fit(ns1) == True{} : Bool}, f2: {PathPolicySpec.pp_ns_fit(ns2) == True{} : Bool}, f3: {PathPolicySpec.pp_ns_fit(ns3) == True{} : Bool}, f4: {PathPolicySpec.pp_ns_fit(at) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s4) == d : Wr.Dec<Bool>}) -> pe.RP(s, FPp.get_req.looped(ns1, ns2, ns3, at, d)):
  match d:
    case Wr.Got{+l, +s5}:
      +e = Wire.wire_bool_exact(s4, l, s5, ed)
      +pre2 = Equal.trans(String, s, FPp.put_ns(ns1, FPp.put_ns(ns2, FPp.put_ns(ns3, FPp.put_ns(at, s4)))), pe.enc(ns1, ns2, ns3, at, l, s5), pre, Equal.cong(String, String, z => FPp.put_ns(ns1, FPp.put_ns(ns2, FPp.put_ns(ns3, FPp.put_ns(at, z)))), s4, Wr.put_bool(l, s5), e))
      pe.build(s, ns1, ns2, ns3, at, l, s5, pre2, f1, f2, f3, f4, Fl.unflat(ns1), {==}, FPp.get_req.rules(Fl.unflat(ns2)), {==}, Fl.unflat(ns3), {==})
    case Wr.Bad{}:
      Unit{}

def pe.at(-s: String, +ns1: List<&2, Nat>, +ns2: List<&2, Nat>, +ns3: List<&2, Nat>, +s3: String, pre: {s == FPp.put_ns(ns1, FPp.put_ns(ns2, FPp.put_ns(ns3, s3))) : String}, f1: {PathPolicySpec.pp_ns_fit(ns1) == True{} : Bool}, f2: {PathPolicySpec.pp_ns_fit(ns2) == True{} : Bool}, f3: {PathPolicySpec.pp_ns_fit(ns3) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s3) == d : Wr.Dec<List<&2, Nat>>}) -> pe.RP(s, FPp.get_req.at(ns1, ns2, ns3, d)):
  match d:
    case Wr.Got{+at, +s4}:
      +ee = ed
      +e = Wire.wire_list_exact(s3, at, s4, ee)
      +pre2 = Equal.trans(String, s, FPp.put_ns(ns1, FPp.put_ns(ns2, FPp.put_ns(ns3, s3))), FPp.put_ns(ns1, FPp.put_ns(ns2, FPp.put_ns(ns3, FPp.put_ns(at, s4)))), pre, Equal.cong(String, String, z => FPp.put_ns(ns1, FPp.put_ns(ns2, FPp.put_ns(ns3, z))), s3, FPp.put_ns(at, s4), e))
      pe.looped(s, ns1, ns2, ns3, at, s4, pre2, f1, f2, f3, LGlobEntry.ge.nats_fit(s3, at, s4, ee), Wr.get_bool(s4), {==})
    case Wr.Bad{}:
      Unit{}

def pe.secret(-s: String, +ns1: List<&2, Nat>, +ns2: List<&2, Nat>, +s2: String, pre: {s == FPp.put_ns(ns1, FPp.put_ns(ns2, s2)) : String}, f1: {PathPolicySpec.pp_ns_fit(ns1) == True{} : Bool}, f2: {PathPolicySpec.pp_ns_fit(ns2) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s2) == d : Wr.Dec<List<&2, Nat>>}) -> pe.RP(s, FPp.get_req.secret(ns1, ns2, d)):
  match d:
    case Wr.Got{+ns3, +s3}:
      +ee = ed
      +e = Wire.wire_list_exact(s2, ns3, s3, ee)
      +pre2 = Equal.trans(String, s, FPp.put_ns(ns1, FPp.put_ns(ns2, s2)), FPp.put_ns(ns1, FPp.put_ns(ns2, FPp.put_ns(ns3, s3))), pre, Equal.cong(String, String, z => FPp.put_ns(ns1, FPp.put_ns(ns2, z)), s2, FPp.put_ns(ns3, s3), e))
      pe.at(s, ns1, ns2, ns3, s3, pre2, f1, f2, LGlobEntry.ge.nats_fit(s2, ns3, s3, ee), Wr.get_list(~Nat, ~Wr.get_nat, s3), {==})
    case Wr.Bad{}:
      Unit{}

def pe.rule_list(-s: String, +ns1: List<&2, Nat>, +s1: String, pre: {s == FPp.put_ns(ns1, s1) : String}, f1: {PathPolicySpec.pp_ns_fit(ns1) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> pe.RP(s, FPp.get_req.rule_list(ns1, d)):
  match d:
    case Wr.Got{+ns2, +s2}:
      +ee = ed
      +e = Wire.wire_list_exact(s1, ns2, s2, ee)
      +pre2 = Equal.trans(String, s, FPp.put_ns(ns1, s1), FPp.put_ns(ns1, FPp.put_ns(ns2, s2)), pre, Equal.cong(String, String, z => FPp.put_ns(ns1, z), s1, FPp.put_ns(ns2, s2), e))
      pe.secret(s, ns1, ns2, s2, pre2, f1, LGlobEntry.ge.nats_fit(s1, ns2, s2, ee), Wr.get_list(~Nat, ~Wr.get_nat, s2), {==})
    case Wr.Bad{}:
      Unit{}

def pe.roots(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == d : Wr.Dec<List<&2, Nat>>}) -> pe.RP(s, FPp.get_req.roots(d)):
  match d:
    case Wr.Got{+ns1, +s1}:
      +ee = ed
      pe.rule_list(s, ns1, s1, Wire.wire_list_exact(s, ns1, s1, ee), LGlobEntry.ge.nats_fit(s, ns1, s1, ee), Wr.get_list(~Nat, ~Wr.get_nat, s1), {==})
    case Wr.Bad{}:
      Unit{}

# the decoder reads only spelled requests that fit, the rest after them
# untouched
def pe.dec(+s: String) -> pe.RP(s, FPp.get_req(s)):
  pe.roots(s, Wr.get_list(~Nat, ~Wr.get_nat, s), {==})
