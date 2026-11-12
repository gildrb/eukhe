# eukhe: lemmas of the R1 proofs of area arg_repair: the name a repaired
# step takes is the one S2 names its key read (aw.name_n); admitted
# arguments (each key read, sent alone, repaired; names fresh) each repair
# taking the seen Seen{name, key read} (aw.build, aw.OKS), so a walk over
# them refuses as what follows them refuses (aw.rej) or repairs (aw.rep);
# what the names taken say of a later name (aw.first_*).

import Base
import ../../../bend/arg_repair.bend as Ar
import ../../../spec/harness/arguments.bend as ArgSpec
import ../../../laws/arg_repair.bend as ArgRepair
import ../base.bend as AB
import ./step.bend as SV
import ./look.bend as PSpec

# Logic
# -----

def aw.or_fl(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      AB.ab.absurd_tf({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def aw.or_fr(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      AB.ab.absurd_tf({b == False{} : Bool}, h)
    case False{}:
      h

def aw.not_t(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      AB.ab.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def aw.head(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      x

def aw.pick_none(b: Bool, -k: String, -r: Maybe<&2, String>, hb: {b == False{} : Bool}, hr: {r == None{} : Maybe<&2, String>}) -> {Ar.pick.at(b, k, r) == None{} : Maybe<&2, String>}:
  match b:
    case True{}:
      AB.ab.absurd_tf({Ar.pick.at(True{}, k, r) == None{} : Maybe<&2, String>}, hb)
    case False{}:
      hr

def aw.pick_skip(b: Bool, -k: String, -r: Maybe<&2, String>, hb: {b == False{} : Bool}) -> {Ar.pick.at(b, k, r) == r : Maybe<&2, String>}:
  match b:
    case True{}:
      AB.ab.absurd_tf({Ar.pick.at(True{}, k, r) == r : Maybe<&2, String>}, hb)
    case False{}:
      {==}

# Names
# -----

def aw.name2(dec: Bool, ha: Maybe<&2, String>, +k: String, +c: String, hd: {ArgRepair.ar_implies(dec, String.eq(c, k)) == True{} : Bool}, hn: {SV.sv.nalias(ha, dec, k, c) == True{} : Bool}) -> {c == ArgSpec.name_of.at(dec, ha, k) : String}:
  match dec:
    case True{}:
      AB.ab.str_eq(c, k, hd)
    case False{}:
      match ha:
        case None{}:
          AB.ab.str_eq(c, k, hn)
        case Some{+a}:
          AB.ab.str_eq(c, a, hn)

def aw.name_of(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +k: String) -> {ArgSpec.name_of.at(Ar.found(Ar.prop(k, ps)), Ar.lookup(k, als), k) == ArgSpec.name_of(ps, als, k) : String}:
  %PSpec.rs.lookup(k, als) : {ArgSpec.name_of.at(Ar.found(Ar.prop(k, ps)), Ar.lookup(k, als), k) == ArgSpec.name_of.at(ArgSpec.is_some(ArgSpec.declared(k, ps)), _, k) : String}
  %PSpec.rs.prop(k, ps) : {ArgSpec.name_of.at(Ar.found(Ar.prop(k, ps)), Ar.lookup(k, als), k) == ArgSpec.name_of.at(ArgSpec.is_some(_), Ar.lookup(k, als), k) : String}
  %PSpec.rs.found(Ar.prop(k, ps)) : {ArgSpec.name_of.at(Ar.found(Ar.prop(k, ps)), Ar.lookup(k, als), k) == ArgSpec.name_of.at(_, Ar.lookup(k, als), k) : String}
  {==}

# a key read as the name c: c is the name S2 gives it
def aw.name_n(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String, +c: String, +hn: {SV.sv.nok2(Ar.lookup(k, rs), Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, c) == True{} : Bool}) -> {c == ArgSpec.name_of(ps, als, k) : String}:
  +hr = Ar.lookup(k, rs)
  +ha = Ar.lookup(k, als)
  +dec = Ar.found(Ar.prop(k, ps))
  +e1 = aw.name2(dec, ha, k, c, SV.sv.nok_dec(hr, ha, dec, cl, k, c, hn), SV.sv.nok_alias(hr, ha, dec, cl, k, c, hn))
  Equal.trans(String, c, ArgSpec.name_of.at(dec, ha, k), ArgSpec.name_of(ps, als, k), e1, aw.name_of(ps, als, k))

def aw.cur(dm: Maybe<&2, String>, -k: String) -> {ArgSpec.key_read.of(dm, k) == ArgRepair.ar_cur(dm, k) : String}:
  match dm:
    case None{}:
      {==}
    case Some{p}:
      {==}

# the key read is the code's
def aw.kr(+ks: List<&2, String>, +k: String, +m: Maybe<&2, String>, -v: Ar.Val) -> {ArgSpec.key_read(ks, Ar.Arg{k, m, v}) == ArgRepair.ar_cur(Ar.decoded(ks, k, m), k) : String}:
  %PSpec.rs.decoded(ks, k, m) : {ArgSpec.key_read.of(_, k) == ArgRepair.ar_cur(Ar.decoded(ks, k, m), k) : String}
  aw.cur(Ar.decoded(ks, k, m), k)

# The names taken
# ---------------

def aw.names(ss: List<&2, Ar.Seen>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> t:
      match s:
        case Ar.Seen{n, k}:
          n <> aw.names(t)

# no name taken is c: no key took c
def aw.first_none(+c: String, ss: List<&2, Ar.Seen>, +h: {ArgSpec.member(c, aw.names(ss)) == False{} : Bool}) -> {Ar.first_of(c, ss) == None{} : Maybe<&2, String>}:
  match ss:
    case Nil{}:
      {==}
    case s <> +t:
      match s:
        case Ar.Seen{+n, +k}:
          +ec = String.eq(c, n)
          +mt = ArgSpec.member(c, aw.names(t))
          aw.pick_none(ec, k, Ar.first_of(c, t), aw.or_fl(ec, mt, h), aw.first_none(c, t, aw.or_fr(ec, mt, h)))

# the seen an argument takes: the name S2 gives its key read, and that key
def aw.seen(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, +a: Ar.Arg) -> Ar.Seen:
  Ar.Seen{ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, a)), ArgSpec.key_read(ks, a)}

# the seens after the arguments xs, from ss
def aw.after(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, xs: List<&2, Ar.Arg>, ss: List<&2, Ar.Seen>) -> List<&2, Ar.Seen>:
  match xs:
    case Nil{}:
      ss
    case +a <> t:
      aw.after(ps, als, ks, t, aw.seen(ps, als, ks, a) <> ss)

def aw.after_app(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, xs: List<&2, Ar.Arg>, +ys: List<&2, Ar.Arg>, +ss: List<&2, Ar.Seen>) -> {aw.after(ps, als, ks, List.append(&2, Ar.Arg, xs, ys), ss) == aw.after(ps, als, ks, ys, aw.after(ps, als, ks, xs, ss)) : List<&2, Ar.Seen>}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +t:
      aw.after_app(ps, als, ks, t, ys, aw.seen(ps, als, ks, a) <> ss)

def aw.names_app(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, xs: List<&2, Ar.Arg>, +ys: List<&2, Ar.Arg>) -> {ArgSpec.names(ps, als, ks, List.append(&2, Ar.Arg, xs, ys)) == List.append(&2, String, ArgSpec.names(ps, als, ks, xs), ArgSpec.names(ps, als, ks, ys)) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +t:
      +n = ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, a))
      Equal.cong(List<&2, String>, List<&2, String>, z => n <> z, ArgSpec.names(ps, als, ks, List.append(&2, Ar.Arg, t, ys)), List.append(&2, String, ArgSpec.names(ps, als, ks, t), ArgSpec.names(ps, als, ks, ys)), aw.names_app(ps, als, ks, t, ys))

# a name no argument of xs is read as: the seens after xs find it as ss does
def aw.first_after(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, +c: String, xs: List<&2, Ar.Arg>, +ss: List<&2, Ar.Seen>, +h: {ArgSpec.member(c, ArgSpec.names(ps, als, ks, xs)) == False{} : Bool}) -> {Ar.first_of(c, aw.after(ps, als, ks, xs, ss)) == Ar.first_of(c, ss) : Maybe<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +t:
      +n = ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, a))
      +ec = String.eq(c, n)
      +mt = ArgSpec.member(c, ArgSpec.names(ps, als, ks, t))
      Equal.trans(Maybe<&2, String>, Ar.first_of(c, aw.after(ps, als, ks, t, aw.seen(ps, als, ks, a) <> ss)), Ar.first_of(c, aw.seen(ps, als, ks, a) <> ss), Ar.first_of(c, ss), aw.first_after(ps, als, ks, c, t, aw.seen(ps, als, ks, a) <> ss, aw.or_fr(ec, mt, h)), aw.pick_skip(ec, ArgSpec.key_read(ks, a), Ar.first_of(c, ss), aw.or_fl(ec, mt, h)))

# Freshness
# ---------

def aw.mem_self(+n: String, -prev: List<&2, String>) -> {ArgSpec.member(n, n <> prev) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(n, n), True{}, AB.ab.str_refl(n)) : {Bool.or(_, ArgSpec.member(n, prev)) == True{} : Bool}
  {==}

# n is among the names taken, m is not: they differ
def aw.ne_at(b: Bool, +n: String, +m: String, +taken: List<&2, String>, eb: {String.eq(n, m) == b : Bool}, hin: {ArgSpec.member(n, taken) == True{} : Bool}, f1: {Bool.not(ArgSpec.member(m, taken)) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      +enm = AB.ab.str_eq(n, m, eb)
      +f2 = Equal.trans(Bool, Bool.not(ArgSpec.member(n, taken)), Bool.not(ArgSpec.member(m, taken)), True{}, Equal.cong(String, Bool, z => Bool.not(ArgSpec.member(z, taken)), n, m, enm), f1)
      AB.ab.absurd({True{} == False{} : Bool}, Equal.trans(Bool, False{}, Bool.not(ArgSpec.member(n, taken)), True{}, Equal.cong(Bool, Bool, z => Bool.not(z), True{}, ArgSpec.member(n, taken), Equal.sym(Bool, ArgSpec.member(n, taken), True{}, hin)), f2))
    case False{}:
      {==}

# a name among those taken is none of the fresh names after them
def aw.fresh_not_in(ns: List<&2, String>, +n: String, +taken: List<&2, String>, +hin: {ArgSpec.member(n, taken) == True{} : Bool}, +hf: {ArgSpec.fresh(ns, taken) == True{} : Bool}) -> {ArgSpec.member(n, ns) == False{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +m <> +w:
      +fa = Bool.not(ArgSpec.member(m, taken))
      +f1 = AB.ab.and_l(fa, ArgSpec.fresh(w, m <> taken), hf)
      +f2 = AB.ab.and_r(fa, ArgSpec.fresh(w, m <> taken), hf)
      +hne = aw.ne_at(String.eq(n, m), n, m, taken, {==}, hin, f1)
      %Equal.sym(Bool, String.eq(n, m), False{}, hne) : {Bool.or(_, ArgSpec.member(n, w)) == False{} : Bool}
      aw.fresh_not_in(w, n, m <> taken, AB.ab.or_r(String.eq(n, m), ArgSpec.member(n, taken), hin), f2)

# fresh names: one is none of the names after it
def aw.fresh_mid(ns1: List<&2, String>, +prev: List<&2, String>, +n: String, +ns2: List<&2, String>, h: {ArgSpec.fresh(List.append(&2, String, ns1, n <> ns2), prev) == True{} : Bool}) -> {ArgSpec.member(n, ns2) == False{} : Bool}:
  match ns1:
    case Nil{}:
      +f2 = AB.ab.and_r(Bool.not(ArgSpec.member(n, prev)), ArgSpec.fresh(ns2, n <> prev), h)
      aw.fresh_not_in(ns2, n, n <> prev, aw.mem_self(n, prev), f2)
    case +x <> +t:
      +rest = List.append(&2, String, t, n <> ns2)
      aw.fresh_mid(t, x <> prev, n, ns2, AB.ab.and_r(Bool.not(ArgSpec.member(x, prev)), ArgSpec.fresh(rest, x <> prev), h))

# Steps
# -----

def aw.seen_of(st: Ar.Step) -> Maybe<&2, Ar.Seen>:
  match st:
    case Ar.StepOk{o, r, s}:
      Some{s}
    case Ar.StepNo{x}:
      None{}

def aw.unsome(m: Maybe<&2, Ar.Seen>, d: Ar.Seen) -> Ar.Seen:
  match m:
    case None{}:
      d
    case Some{s}:
      s

def aw.no_of(v: Ar.Verdict) -> Ar.Step:
  match v:
    case Ar.Rejected{z}:
      Ar.StepNo{z}
    case Ar.Repaired{os, rs}:
      Ar.StepNo{Ar.Refused{"", ""}}

# a repaired step: the seen it takes
def aw.next(st: Ar.Step, +ss: List<&2, Ar.Seen>, +s: Ar.Seen, e: {aw.seen_of(st) == Some{s} : Maybe<&2, Ar.Seen>}) -> {Ar.seen.next(st, ss) == s <> ss : List<&2, Ar.Seen>}:
  match st:
    case Ar.StepOk{o, r, +s2}:
      Equal.cong(Ar.Seen, List<&2, Ar.Seen>, z => z <> ss, s2, s, Equal.cong(Maybe<&2, Ar.Seen>, Ar.Seen, m => aw.unsome(m, s), Some{s2}, Some{s}, e))
    case Ar.StepNo{x}:
      AB.ab.absurd({Ar.seen.next(Ar.StepNo{x}, ss) == s <> ss : List<&2, Ar.Seen>}, Equal.cong(Maybe<&2, Ar.Seen>, Bool, m => Maybe.is_some(&2, Ar.Seen, m), None{}, Some{s}, e))

def aw.rej_cons(st: Ar.Step, -rest: Ar.Verdict, -s: Ar.Seen, -x: Ar.Refusal, e: {aw.seen_of(st) == Some{s} : Maybe<&2, Ar.Seen>}, hr: {rest == Ar.Rejected{x} : Ar.Verdict}) -> {Ar.go.cons(st, rest) == Ar.Rejected{x} : Ar.Verdict}:
  match st:
    case Ar.StepOk{o, r, s2}:
      %Equal.sym(Ar.Verdict, rest, Ar.Rejected{x}, hr) : {Ar.go.cons(Ar.StepOk{o, r, s2}, _) == Ar.Rejected{x} : Ar.Verdict}
      {==}
    case Ar.StepNo{y}:
      AB.ab.absurd({Ar.go.cons(Ar.StepNo{y}, rest) == Ar.Rejected{x} : Ar.Verdict}, Equal.cong(Maybe<&2, Ar.Seen>, Bool, m => Maybe.is_some(&2, Ar.Seen, m), None{}, Some{s}, e))

def aw.rep_rest(-o: Ar.Out, -r: List<&2, Ar.Record>, -s2: Ar.Seen, rest: Ar.Verdict, hr: {ArgRepair.ar_rejected(rest) == False{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go.cons(Ar.StepOk{o, r, s2}, rest)) == False{} : Bool}:
  match rest:
    case Ar.Repaired{os, xs}:
      {==}
    case Ar.Rejected{x}:
      AB.ab.absurd_tf({ArgRepair.ar_rejected(Ar.go.cons(Ar.StepOk{o, r, s2}, Ar.Rejected{x})) == False{} : Bool}, hr)

def aw.rep_cons(st: Ar.Step, rest: Ar.Verdict, -s: Ar.Seen, e: {aw.seen_of(st) == Some{s} : Maybe<&2, Ar.Seen>}, hr: {ArgRepair.ar_rejected(rest) == False{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go.cons(st, rest)) == False{} : Bool}:
  match st:
    case Ar.StepOk{o, r, s2}:
      aw.rep_rest(o, r, s2, rest, hr)
    case Ar.StepNo{y}:
      AB.ab.absurd({ArgRepair.ar_rejected(Ar.go.cons(Ar.StepNo{y}, rest)) == False{} : Bool}, Equal.cong(Maybe<&2, Ar.Seen>, Bool, m => Maybe.is_some(&2, Ar.Seen, m), None{}, Some{s}, e))

# each argument of xs, from ss on, repairs taking its seen
def aw.OKS(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, xs: List<&2, Ar.Arg>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +a <> t:
      {aw.seen_of(Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a)) == Some{aw.seen(ps, als, ks, a)} : Maybe<&2, Ar.Seen>} & aw.OKS(ps, cl, als, rs, ks, aw.seen(ps, als, ks, a) <> ss, t)

# what follows repaired arguments refuses: the call refuses just so
def aw.rej(xs: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, +rest: List<&2, Ar.Arg>, -x: Ar.Refusal, oks: aw.OKS(ps, cl, als, rs, ks, ss, xs), hr: {Ar.go(rest, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, aw.after(ps, als, ks, xs, ss)) == Ar.Rejected{x} : Ar.Verdict}) -> {Ar.go(List.append(&2, Ar.Arg, xs, rest), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss) == Ar.Rejected{x} : Ar.Verdict}:
  match xs:
    case Nil{}:
      hr
    case +a <> +t:
      (+e, ot) = oks
      +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a)
      +s = aw.seen(ps, als, ks, a)
      +ih = aw.rej(t, ps, cl, als, rs, ks, s <> ss, rest, x, ot, hr)
      %Equal.sym(List<&2, Ar.Seen>, Ar.seen.next(st, ss), s <> ss, aw.next(st, ss, s, e)) : {Ar.go.cons(st, Ar.go(List.append(&2, Ar.Arg, t, rest), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, _)) == Ar.Rejected{x} : Ar.Verdict}
      aw.rej_cons(st, Ar.go(List.append(&2, Ar.Arg, t, rest), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, s <> ss), s, x, e, ih)

# repaired arguments: the call is repaired
def aw.rep(xs: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, oks: aw.OKS(ps, cl, als, rs, ks, ss, xs)) -> {ArgRepair.ar_rejected(Ar.go(xs, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +t:
      (+e, ot) = oks
      +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a)
      +s = aw.seen(ps, als, ks, a)
      +ih = aw.rep(t, ps, cl, als, rs, ks, s <> ss, ot)
      %Equal.sym(List<&2, Ar.Seen>, Ar.seen.next(st, ss), s <> ss, aw.next(st, ss, s, e)) : {ArgRepair.ar_rejected(Ar.go.cons(st, Ar.go(t, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, _))) == False{} : Bool}
      aw.rep_cons(st, Ar.go(t, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, s <> ss), s, e, ih)

# One admitted argument
# ---------------------

# a key read K, repaired alone, named N no earlier argument took: its
# step takes Seen{N, K}
def aw.key_n(n: Ar.Named, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ss: List<&2, Ar.Seen>, +r0: List<&2, Ar.Record>, +k: String, +v: Ar.Val, hn: {SV.sv.nok(Ar.lookup(k, rs), Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, n) == True{} : Bool}, h1: {Bool.not(ArgRepair.ar_rejected(Ar.go.cons(Ar.step.named(n, ps, Nil{}, Nil{}, k, v), Ar.Repaired{Nil{}, Nil{}}))) == True{} : Bool}, h2: {ArgSpec.member(ArgSpec.name_of(ps, als, k), aw.names(ss)) == False{} : Bool}) -> {aw.seen_of(Ar.step.named(n, ps, ss, r0, k, v)) == Some{Ar.Seen{ArgSpec.name_of(ps, als, k), k}} : Maybe<&2, Ar.Seen>}:
  match n:
    case Ar.NRefused{j, x}:
      AB.ab.absurd({aw.seen_of(Ar.step.named(Ar.NRefused{j, x}, ps, ss, r0, k, v)) == Some{Ar.Seen{ArgSpec.name_of(ps, als, k), k}} : Maybe<&2, Ar.Seen>}, h1)
    case Ar.NUnknown{j, ns}:
      AB.ab.absurd({aw.seen_of(Ar.step.named(Ar.NUnknown{j, ns}, ps, ss, r0, k, v)) == Some{Ar.Seen{ArgSpec.name_of(ps, als, k), k}} : Maybe<&2, Ar.Seen>}, h1)
    case Ar.NAs{+c}:
      +nm = ArgSpec.name_of(ps, als, k)
      +ec = aw.name_n(ps, cl, als, rs, k, c, hn)
      +h2c = Equal.trans(Bool, ArgSpec.member(c, aw.names(ss)), ArgSpec.member(nm, aw.names(ss)), False{}, Equal.cong(String, Bool, z => ArgSpec.member(z, aw.names(ss)), c, nm, ec), h2)
      %Equal.sym(Maybe<&2, String>, Ar.first_of(c, ss), None{}, aw.first_none(c, ss, h2c)) : {aw.seen_of(Ar.step.first(_, c, ps, r0, k, v)) == Some{Ar.Seen{nm, k}} : Maybe<&2, Ar.Seen>}
      Equal.cong(String, Maybe<&2, Ar.Seen>, z => Some{Ar.Seen{z, k}}, c, nm, ec)

def aw.key(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ss: List<&2, Ar.Seen>, +r0: List<&2, Ar.Record>, +k: String, +v: Ar.Val, h1: {Bool.not(ArgRepair.ar_rejected(Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{k, None{}, v}]))) == True{} : Bool}, h2: {ArgSpec.member(ArgSpec.name_of(ps, als, k), aw.names(ss)) == False{} : Bool}) -> {aw.seen_of(Ar.step.key(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ss, r0, k, v)) == Some{Ar.Seen{ArgSpec.name_of(ps, als, k), k}} : Maybe<&2, Ar.Seen>}:
  aw.key_n(Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k), ps, cl, als, rs, ss, r0, k, v, SV.sv.named(ps, cl, als, rs, k), h1, h2)

def aw.one_dm(dm: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ss: List<&2, Ar.Seen>, +k: String, +v: Ar.Val, h1: {Bool.not(ArgRepair.ar_rejected(Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{ArgRepair.ar_cur(dm, k), None{}, v}]))) == True{} : Bool}, h2: {ArgSpec.member(ArgSpec.name_of(ps, als, ArgRepair.ar_cur(dm, k)), aw.names(ss)) == False{} : Bool}) -> {aw.seen_of(Ar.step.read(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ss, k, dm, v)) == Some{Ar.Seen{ArgSpec.name_of(ps, als, ArgRepair.ar_cur(dm, k)), ArgRepair.ar_cur(dm, k)}} : Maybe<&2, Ar.Seen>}:
  match dm:
    case None{}:
      aw.key(ps, cl, als, rs, ss, Nil{}, k, v, h1, h2)
    case Some{+p}:
      aw.key(ps, cl, als, rs, ss, [Ar.RAlias{k, p}], p, v, h1, h2)

# an argument repaired alone, named as no earlier one: it takes its seen
def aw.one(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, a: Ar.Arg, h1: {Bool.not(ArgRepair.ar_rejected(ArgRepair.ar_alone(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, a))) == True{} : Bool}, h2: {ArgSpec.member(ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, a)), aw.names(ss)) == False{} : Bool}) -> {aw.seen_of(Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a)) == Some{aw.seen(ps, als, ks, a)} : Maybe<&2, Ar.Seen>}:
  match a:
    case Ar.Arg{+k, +m, +v}:
      +dm = Ar.decoded(ks, k, m)
      +kr = ArgSpec.key_read(ks, Ar.Arg{k, m, v})
      +cu = ArgRepair.ar_cur(dm, k)
      +ek = Equal.sym(String, kr, cu, aw.kr(ks, k, m, v))
      +h1c = Equal.trans(Bool, Bool.not(ArgRepair.ar_rejected(Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{cu, None{}, v}]))), Bool.not(ArgRepair.ar_rejected(Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{kr, None{}, v}]))), True{}, Equal.cong(String, Bool, z => Bool.not(ArgRepair.ar_rejected(Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{z, None{}, v}]))), cu, kr, ek), h1)
      +h2c = Equal.trans(Bool, ArgSpec.member(ArgSpec.name_of(ps, als, cu), aw.names(ss)), ArgSpec.member(ArgSpec.name_of(ps, als, kr), aw.names(ss)), False{}, Equal.cong(String, Bool, z => ArgSpec.member(ArgSpec.name_of(ps, als, z), aw.names(ss)), cu, kr, ek), h2)
      %ek : {aw.seen_of(Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, m, v})) == Some{Ar.Seen{ArgSpec.name_of(ps, als, _), _}} : Maybe<&2, Ar.Seen>}
      aw.one_dm(dm, ps, cl, als, rs, ss, k, v, h1c, h2c)

# admitted arguments, from the seens ss of the names prev: each takes its
# seen
def aw.build(xs: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, +prev: List<&2, String>, +hs: {aw.names(ss) == prev : List<&2, String>}, +ha: {ArgRepair.ar_alone_ok(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, xs) == True{} : Bool}, +hf: {ArgSpec.fresh(ArgSpec.names(ps, als, ks, xs), prev) == True{} : Bool}) -> aw.OKS(ps, cl, als, rs, ks, ss, xs):
  match xs:
    case Nil{}:
      Unit{}
    case +a <> +t:
      +nm = ArgSpec.name_of(ps, als, ArgSpec.key_read(ks, a))
      +ra = Bool.not(ArgRepair.ar_rejected(ArgRepair.ar_alone(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, a)))
      +rt = ArgRepair.ar_alone_ok(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, t)
      +fa = Bool.not(ArgSpec.member(nm, prev))
      +ft = ArgSpec.fresh(ArgSpec.names(ps, als, ks, t), nm <> prev)
      +hm = aw.not_t(ArgSpec.member(nm, prev), AB.ab.and_l(fa, ft, hf))
      +hm2 = Equal.trans(Bool, ArgSpec.member(nm, aw.names(ss)), ArgSpec.member(nm, prev), False{}, Equal.cong(List<&2, String>, Bool, z => ArgSpec.member(nm, z), aw.names(ss), prev, hs), hm)
      +hs2 = Equal.cong(List<&2, String>, List<&2, String>, z => nm <> z, aw.names(ss), prev, hs)
      (aw.one(ps, cl, als, rs, ks, ss, a, AB.ab.and_l(ra, rt, ha), hm2), aw.build(t, ps, cl, als, rs, ks, aw.seen(ps, als, ks, a) <> ss, nm <> prev, hs2, AB.ab.and_r(ra, rt, ha), AB.ab.and_r(fa, ft, hf)))

# One refused argument
# --------------------

# a key read refused alone refuses so after any names taken
def aw.no_n(n: Ar.Named, +ps: List<&2, Ar.Prop>, -ss: List<&2, Ar.Seen>, -r0: List<&2, Ar.Record>, +k: String, +v: Ar.Val, -x: Ar.Refusal, h: {Ar.go.cons(Ar.step.named(n, ps, Nil{}, Nil{}, k, v), Ar.Repaired{Nil{}, Nil{}}) == Ar.Rejected{x} : Ar.Verdict}) -> {Ar.step.named(n, ps, ss, r0, k, v) == Ar.StepNo{x} : Ar.Step}:
  match n:
    case Ar.NRefused{+j, +y}:
      Equal.cong(Ar.Verdict, Ar.Step, w => aw.no_of(w), Ar.Rejected{Ar.Refused{j, y}}, Ar.Rejected{x}, h)
    case Ar.NUnknown{+j, +ns}:
      Equal.cong(Ar.Verdict, Ar.Step, w => aw.no_of(w), Ar.Rejected{Ar.Unknown{j, ns}}, Ar.Rejected{x}, h)
    case Ar.NAs{+c}:
      AB.ab.absurd({Ar.step.named(Ar.NAs{c}, ps, ss, r0, k, v) == Ar.StepNo{x} : Ar.Step}, Equal.cong(Ar.Verdict, Bool, w => ArgRepair.ar_rejected(w), Ar.go.cons(Ar.step.named(Ar.NAs{c}, ps, Nil{}, Nil{}, k, v), Ar.Repaired{Nil{}, Nil{}}), Ar.Rejected{x}, h))

def aw.no_dm(dm: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ss: List<&2, Ar.Seen>, +k: String, +v: Ar.Val, -x: Ar.Refusal, h: {Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{ArgRepair.ar_cur(dm, k), None{}, v}]) == Ar.Rejected{x} : Ar.Verdict}) -> {Ar.step.read(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ss, k, dm, v) == Ar.StepNo{x} : Ar.Step}:
  match dm:
    case None{}:
      aw.no_n(Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k), ps, ss, Nil{}, k, v, x, h)
    case Some{+p}:
      aw.no_n(Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, p), ps, ss, [Ar.RAlias{k, p}], p, v, x, h)

# an argument refused alone refuses so after any names taken
def aw.no_step(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, a: Ar.Arg, -x: Ar.Refusal, h: {ArgRepair.ar_alone(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, a) == Ar.Rejected{x} : Ar.Verdict}) -> {Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a) == Ar.StepNo{x} : Ar.Step}:
  match a:
    case Ar.Arg{+k, +m, +v}:
      +dm = Ar.decoded(ks, k, m)
      +kr = ArgSpec.key_read(ks, Ar.Arg{k, m, v})
      +cu = ArgRepair.ar_cur(dm, k)
      +ek = Equal.sym(String, kr, cu, aw.kr(ks, k, m, v))
      +hc = Equal.trans(Ar.Verdict, Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{cu, None{}, v}]), Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{kr, None{}, v}]), Ar.Rejected{x}, Equal.cong(String, Ar.Verdict, z => Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, [Ar.Arg{z, None{}, v}]), cu, kr, ek), h)
      aw.no_dm(dm, ps, cl, als, rs, ss, k, v, x, hc)

# a call: the step refuses, so does the walk from it
def aw.no_go(st: Ar.Step, -rest: Ar.Verdict, -x: Ar.Refusal, e: {st == Ar.StepNo{x} : Ar.Step}) -> {Ar.go.cons(st, rest) == Ar.Rejected{x} : Ar.Verdict}:
  %Equal.sym(Ar.Step, st, Ar.StepNo{x}, e) : {Ar.go.cons(_, rest) == Ar.Rejected{x} : Ar.Verdict}
  {==}
