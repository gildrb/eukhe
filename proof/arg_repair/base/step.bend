# eukhe: lemmas of the property proofs of area arg_repair: what one step
# of the repair establishes (sv.SVa): a refused or unknown argument, or a
# repaired one whose name c satisfies the naming facts (sv.nok2: the key
# read is not refused, a declared key keeps its name, an undeclared alias
# takes its first canonical name, any other key keeps its name, a closed
# schema reads only declared keys and aliases), was taken by no earlier
# argument, whose value is the declared reading, whose records are the
# decoding, the renaming and the reading, and whose name c is read as c
# again when sent (sv.fix).

import Base
import ../../../bend/arg_repair.bend as Ar
import ../../../laws/arg_repair.bend as ArgRepair
import ../base.bend as AB

# Logic
# -----

def sv.and2(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def sv.imp_t(x: Bool) -> {ArgRepair.ar_implies(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# Names
# -----

def sv.nalias(ha: Maybe<&2, String>, dec: Bool, +k: String, +c: String) -> Bool:
  match ha:
    case None{}:
      String.eq(c, k)
    case Some{a}:
      ArgRepair.ar_implies(Bool.not(dec), String.eq(c, a))

# the key k read as the name c, from its lookups (hr: its refusal, ha: its
# alias, dec: whether it is declared, cl: whether the schema is closed)
def sv.nok2(hr: Maybe<&2, String>, +ha: Maybe<&2, String>, +dec: Bool, cl: Bool, +k: String, +c: String) -> Bool:
  Bool.and(ArgRepair.ar_none(hr), Bool.and(ArgRepair.ar_implies(dec, String.eq(c, k)), Bool.and(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha))))))

def sv.nok(hr: Maybe<&2, String>, ha: Maybe<&2, String>, dec: Bool, cl: Bool, k: String, n: Ar.Named) -> Bool:
  match n:
    case Ar.NRefused{j, x}:
      True{}
    case Ar.NUnknown{j, ns}:
      True{}
    case Ar.NAs{c}:
      sv.nok2(hr, ha, dec, cl, k, c)

def sv.nok_as(-ha: Maybe<&2, String>, -dec: Bool, -cl: Bool, +k: String, +c: String, h1: {ArgRepair.ar_implies(dec, String.eq(c, k)) == True{} : Bool}, h2: {sv.nalias(ha, dec, k, c) == True{} : Bool}, h3: {ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha))) == True{} : Bool}) -> {sv.nok2(None{}, ha, dec, cl, k, c) == True{} : Bool}:
  sv.and2(ArgRepair.ar_implies(dec, String.eq(c, k)), Bool.and(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha)))), h1, sv.and2(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha))), h2, h3))

# the naming facts of an undeclared alias whose canonical name a is
# admitted (or refused, or unknown)
def sv.target(h: Maybe<&2, String>, dec: Bool, cl: Bool, al: Maybe<&2, String>, +a: String, ps: List<&2, Ar.Prop>, +k: String) -> {sv.nok(None{}, Some{a}, False{}, cl, k, Ar.named.target(h, dec, cl, al, a, ps)) == True{} : Bool}:
  match h:
    case Some{x}:
      {==}
    case None{}:
      match dec:
        case True{}:
          sv.nok_as(Some{a}, False{}, cl, k, a, {==}, AB.ab.str_refl(a), sv.imp_t(cl))
        case False{}:
          match cl:
            case True{}:
              {==}
            case False{}:
              match al:
                case None{}:
                  sv.nok_as(Some{a}, False{}, False{}, k, a, {==}, AB.ab.str_refl(a), {==})
                case Some{z}:
                  {==}

def sv.named_alias(ha: Maybe<&2, String>, dec: Bool, cl: Bool, +k: String, +ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>) -> {sv.nok(None{}, ha, dec, cl, k, Ar.named.alias(ha, dec, cl, k, ps, als, rs)) == True{} : Bool}:
  match ha:
    case Some{+a}:
      match dec:
        case True{}:
          sv.nok_as(Some{a}, True{}, cl, k, k, AB.ab.str_refl(k), {==}, sv.imp_t(cl))
        case False{}:
          sv.target(Ar.lookup(a, rs), Ar.found(Ar.prop(a, ps)), cl, Ar.lookup(a, als), a, ps, k)
    case None{}:
      match dec:
        case True{}:
          sv.nok_as(None{}, True{}, cl, k, k, AB.ab.str_refl(k), AB.ab.str_refl(k), sv.imp_t(cl))
        case False{}:
          match cl:
            case True{}:
              {==}
            case False{}:
              sv.nok_as(None{}, False{}, False{}, k, k, {==}, AB.ab.str_refl(k), {==})

def sv.named_hint(hr: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String) -> {sv.nok(hr, Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, Ar.named.hint(hr, Ar.Schema{ps, cl}, als, rs, k)) == True{} : Bool}:
  match hr:
    case Some{x}:
      {==}
    case None{}:
      sv.named_alias(Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, ps, als, rs)

# the name every key is read as satisfies the naming facts
def sv.named(+ps: List<&2, Ar.Prop>, cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String) -> {sv.nok(Ar.lookup(k, rs), Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k)) == True{} : Bool}:
  sv.named_hint(Ar.lookup(k, rs), ps, cl, als, rs, k)

# A name read is read as itself
# ------------------------------

def sv.is_as(n: Ar.Named) -> Bool:
  match n:
    case Ar.NRefused{j, x}:
      False{}
    case Ar.NUnknown{j, ns}:
      False{}
    case Ar.NAs{c}:
      True{}

def sv.as_name(n: Ar.Named) -> String:
  match n:
    case Ar.NRefused{j, x}:
      j
    case Ar.NUnknown{j, ns}:
      j
    case Ar.NAs{c}:
      c

# a refusal is no name
def sv.no_as(-G: Type, -n: Ar.Named, -c: String, e: {n == Ar.NAs{c} : Ar.Named}, hn: {sv.is_as(n) == False{} : Bool}) -> G:
  AB.ab.absurd(G, Equal.trans(Bool, False{}, sv.is_as(n), True{}, Equal.sym(Bool, sv.is_as(n), False{}, hn), Equal.cong(Ar.Named, Bool, w => sv.is_as(w), n, Ar.NAs{c}, e)))

def sv.as_eq(-a: String, -c: String, e: {Ar.NAs{a} == Ar.NAs{c} : Ar.Named}) -> {a == c : String}:
  Equal.cong(Ar.Named, String, w => sv.as_name(w), Ar.NAs{a}, Ar.NAs{c}, e)

# k read as c, and k is c
def sv.fix_same(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String, +c: String, e0: {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k) == Ar.NAs{c} : Ar.Named}, ekc: {k == c : String}) -> {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}:
  Equal.trans(Ar.Named, Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c), Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k), Ar.NAs{c}, Equal.cong(String, Ar.Named, x => Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, x), c, k, Equal.sym(String, k, c, ekc)), e0)

def sv.alias_dec(ha: Maybe<&2, String>, cl: Bool, +k: String, ps: List<&2, Ar.Prop>, als: List<&2, Ar.KV>, rs: List<&2, Ar.KV>) -> {Ar.named.alias(ha, True{}, cl, k, ps, als, rs) == Ar.NAs{k} : Ar.Named}:
  match ha:
    case Some{a}:
      {==}
    case None{}:
      {==}

# a declared, unrefused name is read as itself
def sv.fix_own(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +a: String, eh: {Ar.lookup(a, rs) == None{} : Maybe<&2, String>}, ed: {Ar.found(Ar.prop(a, ps)) == True{} : Bool}) -> {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, a) == Ar.NAs{a} : Ar.Named}:
  %Equal.sym(Maybe<&2, String>, Ar.lookup(a, rs), None{}, eh) : {Ar.named.hint(_, Ar.Schema{ps, cl}, als, rs, a) == Ar.NAs{a} : Ar.Named}
  %Equal.sym(Bool, Ar.found(Ar.prop(a, ps)), True{}, ed) : {Ar.named.alias(Ar.lookup(a, als), _, cl, a, ps, als, rs) == Ar.NAs{a} : Ar.Named}
  sv.alias_dec(Ar.lookup(a, als), cl, a, ps, als, rs)

# an undeclared, unrefused name that is no alias is read as itself by an
# open schema
def sv.fix_open(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +a: String, eh: {Ar.lookup(a, rs) == None{} : Maybe<&2, String>}, ed: {Ar.found(Ar.prop(a, ps)) == False{} : Bool}, ea: {Ar.lookup(a, als) == None{} : Maybe<&2, String>}) -> {Ar.named(Ar.Schema{ps, False{}}, Ar.Dialect{als, rs}, a) == Ar.NAs{a} : Ar.Named}:
  %Equal.sym(Maybe<&2, String>, Ar.lookup(a, rs), None{}, eh) : {Ar.named.hint(_, Ar.Schema{ps, False{}}, als, rs, a) == Ar.NAs{a} : Ar.Named}
  %Equal.sym(Maybe<&2, String>, Ar.lookup(a, als), None{}, ea) : {Ar.named.alias(_, Ar.found(Ar.prop(a, ps)), False{}, a, ps, als, rs) == Ar.NAs{a} : Ar.Named}
  %Equal.sym(Bool, Ar.found(Ar.prop(a, ps)), False{}, ed) : {Ar.named.alias(None{}, _, False{}, a, ps, als, rs) == Ar.NAs{a} : Ar.Named}
  {==}

# an alias's canonical name a admitted as c: c is a, read as itself
def sv.fix_target(h: Maybe<&2, String>, dec: Bool, cl: Bool, al: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +a: String, +c: String, eh: {Ar.lookup(a, rs) == h : Maybe<&2, String>}, ed: {Ar.found(Ar.prop(a, ps)) == dec : Bool}, ea: {Ar.lookup(a, als) == al : Maybe<&2, String>}, e: {Ar.named.target(h, dec, cl, al, a, ps) == Ar.NAs{c} : Ar.Named}) -> {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}:
  match h:
    case Some{x}:
      sv.no_as({Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}, Ar.NRefused{a, x}, c, e, {==})
    case None{}:
      match dec:
        case True{}:
          %sv.as_eq(a, c, e) : {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, _) == Ar.NAs{_} : Ar.Named}
          sv.fix_own(ps, cl, als, rs, a, eh, ed)
        case False{}:
          match cl:
            case True{}:
              sv.no_as({Ar.named(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}, Ar.NUnknown{a, Ar.names(ps)}, c, e, {==})
            case False{}:
              match al:
                case None{}:
                  %sv.as_eq(a, c, e) : {Ar.named(Ar.Schema{ps, False{}}, Ar.Dialect{als, rs}, _) == Ar.NAs{_} : Ar.Named}
                  sv.fix_open(ps, als, rs, a, eh, ed, ea)
                case Some{z}:
                  sv.no_as({Ar.named(Ar.Schema{ps, False{}}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}, Ar.NUnknown{a, Ar.names(ps)}, c, e, {==})

def sv.fix_alias(al: Maybe<&2, String>, dec: Bool, cl: Bool, +ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String, +c: String, e0: {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k) == Ar.NAs{c} : Ar.Named}, e: {Ar.named.alias(al, dec, cl, k, ps, als, rs) == Ar.NAs{c} : Ar.Named}) -> {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}:
  match al:
    case Some{+a}:
      match dec:
        case True{}:
          sv.fix_same(ps, cl, als, rs, k, c, e0, sv.as_eq(k, c, e))
        case False{}:
          sv.fix_target(Ar.lookup(a, rs), Ar.found(Ar.prop(a, ps)), cl, Ar.lookup(a, als), ps, als, rs, a, c, {==}, {==}, {==}, e)
    case None{}:
      match dec:
        case True{}:
          sv.fix_same(ps, cl, als, rs, k, c, e0, sv.as_eq(k, c, e))
        case False{}:
          match cl:
            case True{}:
              sv.no_as({Ar.named(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}, Ar.NUnknown{k, Ar.names(ps)}, c, e, {==})
            case False{}:
              sv.fix_same(ps, False{}, als, rs, k, c, e0, sv.as_eq(k, c, e))

def sv.fix_hint(hr: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String, +c: String, e0: {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k) == Ar.NAs{c} : Ar.Named}, e: {Ar.named.hint(hr, Ar.Schema{ps, cl}, als, rs, k) == Ar.NAs{c} : Ar.Named}) -> {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}:
  match hr:
    case Some{x}:
      sv.no_as({Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}, Ar.NRefused{k, x}, c, e, {==})
    case None{}:
      sv.fix_alias(Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, ps, als, rs, k, c, e0, e)

# a key read as the name c: c sent is read as c (for every dialect)
def sv.fix(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String, +c: String, +e0: {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k) == Ar.NAs{c} : Ar.Named}) -> {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}:
  sv.fix_hint(Ar.lookup(k, rs), ps, cl, als, rs, k, c, e0, e0)

# Steps
# -----

def sv.SVo(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, ss: List<&2, Ar.Seen>, +dm: Maybe<&2, String>, +k: String, +v: Ar.Val, o: Ar.Out, r: List<&2, Ar.Record>, s: Ar.Seen) -> Type:
  match o:
    case Ar.Out{+c, +to}:
      {sv.nok2(Ar.lookup(ArgRepair.ar_cur(dm, k), rs), Ar.lookup(ArgRepair.ar_cur(dm, k), als), Ar.found(Ar.prop(ArgRepair.ar_cur(dm, k), ps)), cl, ArgRepair.ar_cur(dm, k), c) == True{} : Bool} & ({Ar.first_of(c, ss) == None{} : Maybe<&2, String>} & ({to == Ar.coerce(Ar.prop(c, ps), v) : Maybe<&2, Ar.To>} & ({s == Ar.Seen{c, ArgRepair.ar_cur(dm, k)} : Ar.Seen} & ({r == List.append(&2, Ar.Record, ArgRepair.ar_dec_rec(dm, k), List.append(&2, Ar.Record, Ar.rename(String.eq(c, ArgRepair.ar_cur(dm, k)), ArgRepair.ar_cur(dm, k), c), Ar.coerced(c, v, to))) : List<&2, Ar.Record>} & {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}))))

# what one step of the argument k (decoded as dm) with value v establishes
def sv.SV(sc: Ar.Schema, d: Ar.Dialect, ss: List<&2, Ar.Seen>, dm: Maybe<&2, String>, k: String, v: Ar.Val, st: Ar.Step) -> Type:
  match sc:
    case Ar.Schema{ps, cl}:
      match d:
        case Ar.Dialect{als, rs}:
          match st:
            case Ar.StepNo{x}:
              Unit
            case Ar.StepOk{o, r, s}:
              sv.SVo(ps, cl, als, rs, ss, dm, k, v, o, r, s)

def sv.SVa(sc: Ar.Schema, d: Ar.Dialect, +ks: List<&2, String>, ss: List<&2, Ar.Seen>, a: Ar.Arg, st: Ar.Step) -> Type:
  match a:
    case Ar.Arg{+k, m, v}:
      sv.SV(sc, d, ss, Ar.decoded(ks, k, m), k, v, st)

def sv.first(f: Maybe<&2, String>, +c: String, +ps: List<&2, Ar.Prop>, -cl: Bool, -als: List<&2, Ar.KV>, -rs: List<&2, Ar.KV>, -ss: List<&2, Ar.Seen>, +dm: Maybe<&2, String>, +k: String, +v: Ar.Val, ef: {Ar.first_of(c, ss) == f : Maybe<&2, String>}, hn: {sv.nok2(Ar.lookup(ArgRepair.ar_cur(dm, k), rs), Ar.lookup(ArgRepair.ar_cur(dm, k), als), Ar.found(Ar.prop(ArgRepair.ar_cur(dm, k), ps)), cl, ArgRepair.ar_cur(dm, k), c) == True{} : Bool}, hx: {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}) -> sv.SV(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ss, dm, k, v, Ar.step.first(f, c, ps, ArgRepair.ar_dec_rec(dm, k), ArgRepair.ar_cur(dm, k), v)):
  match f:
    case Some{x}:
      Unit{}
    case None{}:
      (hn, (ef, ({==}, ({==}, ({==}, hx)))))

def sv.named_step(n: Ar.Named, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ss: List<&2, Ar.Seen>, +dm: Maybe<&2, String>, +k: String, +v: Ar.Val, hn: {sv.nok(Ar.lookup(ArgRepair.ar_cur(dm, k), rs), Ar.lookup(ArgRepair.ar_cur(dm, k), als), Ar.found(Ar.prop(ArgRepair.ar_cur(dm, k), ps)), cl, ArgRepair.ar_cur(dm, k), n) == True{} : Bool}, en: {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ArgRepair.ar_cur(dm, k)) == n : Ar.Named}) -> sv.SV(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ss, dm, k, v, Ar.step.named(n, ps, ss, ArgRepair.ar_dec_rec(dm, k), ArgRepair.ar_cur(dm, k), v)):
  match n:
    case Ar.NRefused{j, x}:
      Unit{}
    case Ar.NUnknown{j, ns}:
      Unit{}
    case Ar.NAs{+c}:
      sv.first(Ar.first_of(c, ss), c, ps, cl, als, rs, ss, dm, k, v, {==}, hn, sv.fix(ps, cl, als, rs, ArgRepair.ar_cur(dm, k), c, en))

def sv.key(sc: Ar.Schema, d: Ar.Dialect, +ss: List<&2, Ar.Seen>, +dm: Maybe<&2, String>, +k: String, +v: Ar.Val) -> sv.SV(sc, d, ss, dm, k, v, Ar.step.key(sc, d, ss, ArgRepair.ar_dec_rec(dm, k), ArgRepair.ar_cur(dm, k), v)):
  match sc:
    case Ar.Schema{+ps, +cl}:
      match d:
        case Ar.Dialect{+als, +rs}:
          sv.named_step(Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ArgRepair.ar_cur(dm, k)), ps, cl, als, rs, ss, dm, k, v, sv.named(ps, cl, als, rs, ArgRepair.ar_cur(dm, k)), {==})

def sv.read(+sc: Ar.Schema, +d: Ar.Dialect, +ss: List<&2, Ar.Seen>, +k: String, dm: Maybe<&2, String>, +v: Ar.Val) -> sv.SV(sc, d, ss, dm, k, v, Ar.step.read(sc, d, ss, k, dm, v)):
  match dm:
    case None{}:
      sv.key(sc, d, ss, None{}, k, v)
    case Some{+p}:
      sv.key(sc, d, ss, Some{p}, k, v)

# what every step establishes
def sv.step(+sc: Ar.Schema, +d: Ar.Dialect, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, a: Ar.Arg) -> sv.SVa(sc, d, ks, ss, a, Ar.step(sc, d, ks, ss, a)):
  match a:
    case Ar.Arg{+k, +m, +v}:
      sv.read(sc, d, ss, k, Ar.decoded(ks, k, m), v)

# The naming facts, one by one
# ----------------------------

def sv.nok_hr(+hr: Maybe<&2, String>, -ha: Maybe<&2, String>, -dec: Bool, -cl: Bool, -k: String, -c: String, h: {sv.nok2(hr, ha, dec, cl, k, c) == True{} : Bool}) -> {ArgRepair.ar_none(hr) == True{} : Bool}:
  AB.ab.and_l(ArgRepair.ar_none(hr), Bool.and(ArgRepair.ar_implies(dec, String.eq(c, k)), Bool.and(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha))))), h)

def sv.nok_rest(+hr: Maybe<&2, String>, +ha: Maybe<&2, String>, +dec: Bool, +cl: Bool, +k: String, +c: String, h: {sv.nok2(hr, ha, dec, cl, k, c) == True{} : Bool}) -> {Bool.and(ArgRepair.ar_implies(dec, String.eq(c, k)), Bool.and(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha))))) == True{} : Bool}:
  AB.ab.and_r(ArgRepair.ar_none(hr), Bool.and(ArgRepair.ar_implies(dec, String.eq(c, k)), Bool.and(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha))))), h)

def sv.nok_dec(+hr: Maybe<&2, String>, +ha: Maybe<&2, String>, +dec: Bool, +cl: Bool, +k: String, +c: String, h: {sv.nok2(hr, ha, dec, cl, k, c) == True{} : Bool}) -> {ArgRepair.ar_implies(dec, String.eq(c, k)) == True{} : Bool}:
  AB.ab.and_l(ArgRepair.ar_implies(dec, String.eq(c, k)), Bool.and(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha)))), sv.nok_rest(hr, ha, dec, cl, k, c, h))

def sv.nok_alias(+hr: Maybe<&2, String>, +ha: Maybe<&2, String>, +dec: Bool, +cl: Bool, +k: String, +c: String, h: {sv.nok2(hr, ha, dec, cl, k, c) == True{} : Bool}) -> {sv.nalias(ha, dec, k, c) == True{} : Bool}:
  +r = AB.ab.and_r(ArgRepair.ar_implies(dec, String.eq(c, k)), Bool.and(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha)))), sv.nok_rest(hr, ha, dec, cl, k, c, h))
  AB.ab.and_l(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha))), r)

def sv.nok_cl(+hr: Maybe<&2, String>, +ha: Maybe<&2, String>, +dec: Bool, +cl: Bool, +k: String, +c: String, h: {sv.nok2(hr, ha, dec, cl, k, c) == True{} : Bool}) -> {ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha))) == True{} : Bool}:
  +r = AB.ab.and_r(ArgRepair.ar_implies(dec, String.eq(c, k)), Bool.and(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha)))), sv.nok_rest(hr, ha, dec, cl, k, c, h))
  AB.ab.and_r(sv.nalias(ha, dec, k, c), ArgRepair.ar_implies(cl, Bool.or(dec, Maybe.is_some(&2, String, ha))), r)
