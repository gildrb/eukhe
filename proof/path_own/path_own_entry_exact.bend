# eukhe: the proof of LAW path_own_entry_exact
#
# PROOF: each decoder stage answers Got only for the spelling of what it
# read so far, every number within the wire (wire_list_exact,
# wire_nat_exact, wire_bool_exact with their fits); a flat list that reads
# as rules is the rules' spelling (pe.unflat, pox.rules_exact); a class
# code is the code of the class it reads (pox.cls_exact); a value is
# answered only for a request read whole, nothing left (pox.top).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/path_own.bend as Po
import ../../bend/ffi_path_own.bend as FPo
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/path_own.bend as PathOwn
import ../base/bool.bend as LBool
import ../base/staging.bend as LStg
import ../glob/base/entry.bend as LGlobEntry
import ../path_policy/base/entry.bend as LPpEntry
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_list_exact.bend as PWireListExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ./base.bend as LA

# what a request decoder answers is the spelling of a request that fits,
# then its rest
def pox.Q(s: String, d: Wr.Dec<FPo.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == PathOwn.sp_po_req(q, r) : String} & {PathOwn.po_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# The rules
# ---------

def pox.RuleX(xs: List<&2, Nat>, m: Maybe<&2, Po.Rule>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      {xs == PathOwn.sp_po_rule(r) : List<&2, Nat>}

def pox.RulesX(xss: List<&2, List<&2, Nat>>, m: Maybe<&2, List<&2, Po.Rule>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{rs}:
      {xss == PathOwn.sp_po_rules(rs) : List<&2, List<&2, Nat>>}

# a path that reads as a rule is the rule's spelling
def pox.rule_exact(xs: List<&2, Nat>) -> pox.RuleX(xs, FPo.rule.of(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case t <> p:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n+u:
          Unit{}

def pox.rules_cons(m1: Maybe<&2, Po.Rule>, +xs: List<&2, Nat>, h1: pox.RuleX(xs, m1), m2: Maybe<&2, List<&2, Po.Rule>>, +rest: List<&2, List<&2, Nat>>, h2: pox.RulesX(rest, m2)) -> pox.RulesX(xs <> rest, FPo.rules.cons(m1, m2)):
  match m1 m2:
    case Some{+r} Some{+rs}:
      +e1 = {h1 : {xs == PathOwn.sp_po_rule(r) : List<&2, Nat>}}
      +e2 = {h2 : {rest == PathOwn.sp_po_rules(rs) : List<&2, List<&2, Nat>>}}
      Equal.trans(List<&2, List<&2, Nat>>, xs <> rest, PathOwn.sp_po_rule(r) <> rest, PathOwn.sp_po_rule(r) <> PathOwn.sp_po_rules(rs), Equal.cong(List<&2, Nat>, List<&2, List<&2, Nat>>, z => z <> rest, xs, PathOwn.sp_po_rule(r), e1), Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => PathOwn.sp_po_rule(r) <> z, rest, PathOwn.sp_po_rules(rs), e2))
    case Some{r} None{}:
      Unit{}
    case None{} Some{rs}:
      Unit{}
    case None{} None{}:
      Unit{}

# paths that read as rules are the rules' spelling
def pox.rules_exact(xss: List<&2, List<&2, Nat>>) -> pox.RulesX(xss, FPo.rules.of(xss)):
  match xss:
    case Nil{}:
      {==}
    case +xs <> +rest:
      pox.rules_cons(FPo.rule.of(xs), xs, pox.rule_exact(xs), FPo.rules.of(rest), rest, pox.rules_exact(rest))

def pox.RulesOk(ns: List<&2, Nat>, m: Maybe<&2, List<&2, Po.Rule>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{rs}:
      {ns == LA.po.F(rs) : List<&2, Nat>}

def pox.rules_ok.xss(+ns: List<&2, Nat>, +xss: List<&2, List<&2, Nat>>, eu: {ns == Fl.flat(xss) : List<&2, Nat>}, m: Maybe<&2, List<&2, Po.Rule>>, hx: pox.RulesX(xss, m)) -> pox.RulesOk(ns, m):
  match m:
    case None{}:
      Unit{}
    case Some{+rs}:
      +ex = {hx : {xss == PathOwn.sp_po_rules(rs) : List<&2, List<&2, Nat>>}}
      Equal.trans(List<&2, Nat>, ns, Fl.flat(xss), LA.po.F(rs), eu, Equal.trans(List<&2, Nat>, Fl.flat(xss), PathOwn.po_flat(xss), PathOwn.po_flat(PathOwn.sp_po_rules(rs)), LA.po.flat(xss), Equal.cong(List<&2, List<&2, Nat>>, List<&2, Nat>, z => PathOwn.po_flat(z), xss, PathOwn.sp_po_rules(rs), ex)))

def pox.rules_ok.of(+ns: List<&2, Nat>, mx: Maybe<&2, List<&2, List<&2, Nat>>>, emx: {Fl.unflat(ns) == mx : Maybe<&2, List<&2, List<&2, Nat>>>}) -> pox.RulesOk(ns, FPo.rules.flat(mx)):
  match mx:
    case None{}:
      Unit{}
    case Some{+xss}:
      pox.rules_ok.xss(ns, xss, LPpEntry.pe.unflat(ns, xss, emx), FPo.rules.of(xss), pox.rules_exact(xss))

# a flat list that reads as rules is the rules' spelling
def pox.rules_ok(+ns: List<&2, Nat>) -> pox.RulesOk(ns, FPo.rules.flat(Fl.unflat(ns))):
  pox.rules_ok.of(ns, Fl.unflat(ns), {==})

# A class code
# ------------

# a code that reads as a class is the class's code
def pox.cls_exact(k: Nat, +c: Pp.Cls, em: {FPo.cls.of(k) == Some{c} : Maybe<&2, Pp.Cls>}) -> {k == PathOwn.sp_po_code(c) : Nat}:
  match k:
    case 0n:
      Equal.cong(Pp.Cls, Nat, z => PathOwn.sp_po_code(z), Pp.Inside{}, c, LPpEntry.pe.inj(Pp.Cls, Pp.Inside{}, c, em))
    case 1n:
      Equal.cong(Pp.Cls, Nat, z => PathOwn.sp_po_code(z), Pp.Outside{}, c, LPpEntry.pe.inj(Pp.Cls, Pp.Outside{}, c, em))
    case 2n:
      Equal.cong(Pp.Cls, Nat, z => PathOwn.sp_po_code(z), Pp.Protected{}, c, LPpEntry.pe.inj(Pp.Cls, Pp.Protected{}, c, em))
    case 3n:
      Equal.cong(Pp.Cls, Nat, z => PathOwn.sp_po_code(z), Pp.Secret{}, c, LPpEntry.pe.inj(Pp.Cls, Pp.Secret{}, c, em))
    case 4n+u:
      LPpEntry.pe.none_some(Pp.Cls, {4n+u == PathOwn.sp_po_code(c) : Nat}, c, em)

# The stages, last first
# ----------------------

# the spelling of the rules rs, the path at, then s3
def pox.S(rs: List<&2, Po.Rule>, at: List<&2, Nat>, s3: String) -> String:
  PathOwn.sp_po_ns(LA.po.F(rs), PathOwn.sp_po_ns(at, s3))

def pox.FT(rs: List<&2, Po.Rule>, at: List<&2, Nat>) -> Bool:
  Bool.and(PathOwn.po_ns_fit(LA.po.F(rs)), PathOwn.po_ns_fit(at))

def pox.w(+s: String, +rs: List<&2, Po.Rule>, +at: List<&2, Nat>, +c: Pp.Cls, +s4: String, pre: {s == pox.S(rs, at, Wr.put_nat(PathOwn.sp_po_code(c), s4)) : String}, fits: {pox.FT(rs, at) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s4) == d : Wr.Dec<Bool>}) -> pox.Q(s, FPo.get_req.w(rs, at, c, d)):
  match d:
    case Wr.Got{+w, +s5}:
      +e = Wire.wire_bool_exact(s4, w, s5, ed)
      +k = PathOwn.sp_po_code(c)
      (Equal.trans(String, s, pox.S(rs, at, Wr.put_nat(k, s4)), pox.S(rs, at, Wr.put_nat(k, Wr.put_bool(w, s5))), pre, Equal.cong(String, String, z => pox.S(rs, at, Wr.put_nat(k, z)), s4, Wr.put_bool(w, s5), e)), fits)
    case Wr.Bad{}:
      Unit{}

def pox.c(+s: String, +rs: List<&2, Po.Rule>, +at: List<&2, Nat>, +k: Nat, +s4: String, pre: {s == pox.S(rs, at, Wr.put_nat(k, s4)) : String}, fits: {pox.FT(rs, at) == True{} : Bool}, m: Maybe<&2, Pp.Cls>, em: {FPo.cls.of(k) == m : Maybe<&2, Pp.Cls>}) -> pox.Q(s, FPo.get_req.c(rs, at, m, s4)):
  match m:
    case None{}:
      Unit{}
    case Some{+c}:
      +ek = pox.cls_exact(k, c, em)
      +pre2 = Equal.trans(String, s, pox.S(rs, at, Wr.put_nat(k, s4)), pox.S(rs, at, Wr.put_nat(PathOwn.sp_po_code(c), s4)), pre, Equal.cong(Nat, String, z => pox.S(rs, at, Wr.put_nat(z, s4)), k, PathOwn.sp_po_code(c), ek))
      pox.w(s, rs, at, c, s4, pre2, fits, Wr.get_bool(s4), {==})

def pox.cls(+s: String, +rs: List<&2, Po.Rule>, +at: List<&2, Nat>, +s3: String, pre: {s == pox.S(rs, at, s3) : String}, fits: {pox.FT(rs, at) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> pox.Q(s, FPo.get_req.cls(rs, at, d)):
  match d:
    case Wr.Got{+k, +s4}:
      +e = Wire.wire_nat_exact(s3, k, s4, ed)
      +pre2 = Equal.trans(String, s, pox.S(rs, at, s3), pox.S(rs, at, Wr.put_nat(k, s4)), pre, Equal.cong(String, String, z => pox.S(rs, at, z), s3, Wr.put_nat(k, s4), e))
      pox.c(s, rs, at, k, s4, pre2, fits, FPo.cls.of(k), {==})
    case Wr.Bad{}:
      Unit{}

def pox.at(+s: String, +rs: List<&2, Po.Rule>, +s2: String, pre: {s == PathOwn.sp_po_ns(LA.po.F(rs), s2) : String}, fr: {PathOwn.po_ns_fit(LA.po.F(rs)) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s2) == d : Wr.Dec<List<&2, Nat>>}) -> pox.Q(s, FPo.get_req.at(rs, d)):
  match d:
    case Wr.Got{+at, +s3}:
      +ee = ed
      +e = Wire.wire_list_exact(s2, at, s3, ee)
      +f = LA.po.F(rs)
      +pre2 = Equal.trans(String, s, PathOwn.sp_po_ns(f, s2), PathOwn.sp_po_ns(f, PathOwn.sp_po_ns(at, s3)), pre, Equal.cong(String, String, z => PathOwn.sp_po_ns(f, z), s2, PathOwn.sp_po_ns(at, s3), e))
      pox.cls(s, rs, at, s3, pre2, LBool.cb_and_intro(PathOwn.po_ns_fit(f), PathOwn.po_ns_fit(at), fr, LGlobEntry.ge.nats_fit(s2, at, s3, ee)), Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def pox.rs(+s: String, +ns: List<&2, Nat>, +s2: String, pre: {s == PathOwn.sp_po_ns(ns, s2) : String}, fns: {PathOwn.po_ns_fit(ns) == True{} : Bool}, m: Maybe<&2, List<&2, Po.Rule>>, hm: pox.RulesOk(ns, m)) -> pox.Q(s, FPo.get_req.rs(m, s2)):
  match m:
    case None{}:
      Unit{}
    case Some{+rs}:
      +f = LA.po.F(rs)
      +hq = {hm : {ns == f : List<&2, Nat>}}
      +pre2 = Equal.trans(String, s, PathOwn.sp_po_ns(ns, s2), PathOwn.sp_po_ns(f, s2), pre, Equal.cong(List<&2, Nat>, String, z => PathOwn.sp_po_ns(z, s2), ns, f, hq))
      +f2 = Equal.trans(Bool, PathOwn.po_ns_fit(f), PathOwn.po_ns_fit(ns), True{}, Equal.cong(List<&2, Nat>, Bool, z => PathOwn.po_ns_fit(z), f, ns, Equal.sym(List<&2, Nat>, ns, f, hq)), fns)
      pox.at(s, rs, s2, pre2, f2, FPo.get_ns(s2), {==})

def pox.rules(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == d : Wr.Dec<List<&2, Nat>>}) -> pox.Q(s, FPo.get_req.rules(d)):
  match d:
    case Wr.Got{+ns, +s2}:
      +ee = ed
      +e = Wire.wire_list_exact(s, ns, s2, ee)
      pox.rs(s, ns, s2, e, LGlobEntry.ge.nats_fit(s, ns, s2, ee), FPo.rules.flat(Fl.unflat(ns)), pox.rules_ok(ns))
    case Wr.Bad{}:
      Unit{}

def pox.T(s: String) -> Type:
  Sigma<&1, &1, FPo.Req, q => {s == PathOwn.sp_po_req(q, "") : String} & {PathOwn.po_req_fits(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def pox.top(-s: String, d: Wr.Dec<FPo.Req>, hq: pox.Q(s, d), ok: {LawsBase.wire_opens_err(FPo.run(d)) == False{} : Bool}) -> pox.T(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, hq)
        case SCon{x, y}:
          LStg.stg.absurd(pox.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(pox.T(s), ok)

def PathOwn.path_own_entry_exact(s, ok):
  pox.top(s, FPo.get_req(s), pox.rules(s, FPo.get_ns(s), {==}), ok)
