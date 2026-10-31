# eukhe: the proof of LAW arg_repair_idempotent
#
# PROOF: by induction over the arguments of the first repair, the sent
# keys of both repairs and the names taken generalized (equal names,
# id.go): each repaired argument comes back plain, under the name c the
# first repair read (sv.step); a well-formed dialect reads c as itself
# (id.idn), no earlier argument took c (id.fo_*: the same names are taken),
# and its value as read reads as nothing more (id.cp, from the readings'
# types, arg_repair_coerce_typed); so its step keeps it with no record
# (id.st2), and the rest repairs to itself (the hypothesis).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./base/step.bend as SV
import ./arg_repair_spec.bend as PSpec
import ./arg_repair_coerce_typed.bend as PCoerceTyped

# Terms
# -----

def id.names(ss: List<&2, Ar.Seen>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> t:
      match s:
        case Ar.Seen{n, k}:
          n <> id.names(t)

def id.outs(v: Ar.Verdict) -> List<&2, Ar.Out>:
  match v:
    case Ar.Repaired{os, rs}:
      os
    case Ar.Rejected{x}:
      Nil{}

def id.is_rep(v: Ar.Verdict) -> Bool:
  match v:
    case Ar.Repaired{os, rs}:
      True{}
    case Ar.Rejected{x}:
      False{}

# a refusal is no repair
def id.no(-G: Type, -x: Ar.Refusal, -os: List<&2, Ar.Out>, -xs: List<&2, Ar.Record>, e: {Ar.Rejected{x} == Ar.Repaired{os, xs} : Ar.Verdict}) -> G:
  AB.ab.absurd(G, Equal.cong(Ar.Verdict, Bool, w => id.is_rep(w), Ar.Rejected{x}, Ar.Repaired{os, xs}, e))

# Well-formed aliases
# -------------------

def id.wt(m: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +rs: List<&2, Ar.KV>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+a}:
      Bool.and(ArgSpec.is_some(ArgSpec.declared(a, ps)), Bool.not(Maybe.is_some(&2, String, ArgSpec.first_text(a, rs))))

def id.wf_at(b: Bool, +c: String, -r: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +rs: List<&2, Ar.KV>, hc: {Bool.and(ArgSpec.is_some(ArgSpec.declared(c, ps)), Bool.not(Maybe.is_some(&2, String, ArgSpec.first_text(c, rs)))) == True{} : Bool}, hr: {id.wt(r, ps, rs) == True{} : Bool}) -> {id.wt(Ar.pick.at(b, c, r), ps, rs) == True{} : Bool}:
  match b:
    case True{}:
      hc
    case False{}:
      hr

# in a well-formed dialect, the first alias of k names a declared,
# unrefused argument
def id.wf(+ps: List<&2, Ar.Prop>, +rs: List<&2, Ar.KV>, als: List<&2, Ar.KV>, +k: String, h: {ArgRepair.ar_wf.alias(ps, rs, als) == True{} : Bool}) -> {id.wt(Ar.lookup(k, als), ps, rs) == True{} : Bool}:
  match als:
    case Nil{}:
      {==}
    case +e <> +t:
      match e:
        case Ar.KV{+x, +c}:
          +hh = h
          +a1 = Bool.and(ArgSpec.is_some(ArgSpec.declared(c, ps)), Bool.not(Maybe.is_some(&2, String, ArgSpec.first_text(c, rs))))
          id.wf_at(String.eq(k, x), c, Ar.lookup(k, t), ps, rs, AB.ab.and_l(a1, ArgRepair.ar_wf.alias(ps, rs, t), hh), id.wf(ps, rs, t, k, AB.ab.and_r(a1, ArgRepair.ar_wf.alias(ps, rs, t), hh)))

# Names
# -----

def id.alias_dec(ha: Maybe<&2, String>, cl: Bool, +k: String, ps: List<&2, Ar.Prop>) -> {Ar.named.alias(ha, True{}, cl, k, ps) == Ar.NAs{k} : Ar.Named}:
  match ha:
    case Some{a}:
      {==}
    case None{}:
      {==}

def id.not_some(m: Maybe<&2, String>, h: {Bool.not(Maybe.is_some(&2, String, m)) == True{} : Bool}) -> {m == None{} : Maybe<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      AB.ab.absurd({Some{x} == None{} : Maybe<&2, String>}, h)

# a declared, unrefused name is read as itself
def id.own(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +a: String, h: {Bool.and(ArgSpec.is_some(ArgSpec.declared(a, ps)), Bool.not(Maybe.is_some(&2, String, ArgSpec.first_text(a, rs)))) == True{} : Bool}) -> {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, a) == Ar.NAs{a} : Ar.Named}:
  +hh = h
  +hd = AB.ab.and_l(ArgSpec.is_some(ArgSpec.declared(a, ps)), Bool.not(Maybe.is_some(&2, String, ArgSpec.first_text(a, rs))), hh)
  +hr = AB.ab.and_r(ArgSpec.is_some(ArgSpec.declared(a, ps)), Bool.not(Maybe.is_some(&2, String, ArgSpec.first_text(a, rs))), hh)
  +er = Equal.trans(Maybe<&2, String>, Ar.lookup(a, rs), ArgSpec.first_text(a, rs), None{}, PSpec.rs.lookup(a, rs), id.not_some(ArgSpec.first_text(a, rs), hr))
  %Equal.sym(Maybe<&2, String>, Ar.lookup(a, rs), None{}, er) : {Ar.named.hint(_, Ar.Schema{ps, cl}, als, a) == Ar.NAs{a} : Ar.Named}
  +ed = Equal.trans(Bool, Ar.found(Ar.prop(a, ps)), ArgSpec.is_some(ArgSpec.declared(a, ps)), True{}, Equal.trans(Bool, Ar.found(Ar.prop(a, ps)), ArgSpec.is_some(Ar.prop(a, ps)), ArgSpec.is_some(ArgSpec.declared(a, ps)), PSpec.rs.found(Ar.prop(a, ps)), Equal.cong(Maybe<&2, Ar.Prop>, Bool, q => ArgSpec.is_some(q), Ar.prop(a, ps), ArgSpec.declared(a, ps), PSpec.rs.prop(a, ps))), hd)
  %Equal.sym(Bool, Ar.found(Ar.prop(a, ps)), True{}, ed) : {Ar.named.alias(Ar.lookup(a, als), _, cl, a, ps) == Ar.NAs{a} : Ar.Named}
  id.alias_dec(Ar.lookup(a, als), cl, a, ps)

# the name c a key cur was read as, under the naming facts, is read as c
# again in a well-formed dialect
def id.idn(hr: Maybe<&2, String>, ha: Maybe<&2, String>, dec: Bool, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +cur: String, +c: String, h: {SV.sv.nok2(hr, ha, dec, cl, cur, c) == True{} : Bool}, er: {Ar.lookup(cur, rs) == hr : Maybe<&2, String>}, ea: {Ar.lookup(cur, als) == ha : Maybe<&2, String>}, ed: {Ar.found(Ar.prop(cur, ps)) == dec : Bool}, hw: {id.wt(ha, ps, rs) == True{} : Bool}) -> {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}:
  match hr:
    case Some{x}:
      AB.ab.absurd({Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}, h)
    case None{}:
      match ha:
        case Some{+a}:
          match dec:
            case True{}:
              +ec = AB.ab.str_eq(c, cur, SV.sv.nok_dec(None{}, Some{a}, True{}, cl, cur, c, h))
              %Equal.sym(String, c, cur, ec) : {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, _) == Ar.NAs{_} : Ar.Named}
              %Equal.sym(Maybe<&2, String>, Ar.lookup(cur, rs), None{}, er) : {Ar.named.hint(_, Ar.Schema{ps, cl}, als, cur) == Ar.NAs{cur} : Ar.Named}
              %Equal.sym(Bool, Ar.found(Ar.prop(cur, ps)), True{}, ed) : {Ar.named.alias(Ar.lookup(cur, als), _, cl, cur, ps) == Ar.NAs{cur} : Ar.Named}
              id.alias_dec(Ar.lookup(cur, als), cl, cur, ps)
            case False{}:
              +ec = AB.ab.str_eq(c, a, SV.sv.nok_alias(None{}, Some{a}, False{}, cl, cur, c, h))
              %Equal.sym(String, c, a, ec) : {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, _) == Ar.NAs{_} : Ar.Named}
              id.own(ps, cl, als, rs, a, hw)
        case None{}:
          match dec:
            case True{}:
              +ec = AB.ab.str_eq(c, cur, SV.sv.nok_dec(None{}, None{}, True{}, cl, cur, c, h))
              %Equal.sym(String, c, cur, ec) : {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, _) == Ar.NAs{_} : Ar.Named}
              %Equal.sym(Maybe<&2, String>, Ar.lookup(cur, rs), None{}, er) : {Ar.named.hint(_, Ar.Schema{ps, cl}, als, cur) == Ar.NAs{cur} : Ar.Named}
              %Equal.sym(Bool, Ar.found(Ar.prop(cur, ps)), True{}, ed) : {Ar.named.alias(Ar.lookup(cur, als), _, cl, cur, ps) == Ar.NAs{cur} : Ar.Named}
              id.alias_dec(Ar.lookup(cur, als), cl, cur, ps)
            case False{}:
              match cl:
                case True{}:
                  AB.ab.absurd({Ar.named(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}, SV.sv.nok_cl(None{}, None{}, False{}, True{}, cur, c, h))
                case False{}:
                  +ec = AB.ab.str_eq(c, cur, SV.sv.nok_alias(None{}, None{}, False{}, False{}, cur, c, h))
                  %Equal.sym(String, c, cur, ec) : {Ar.named(Ar.Schema{ps, False{}}, Ar.Dialect{als, rs}, _) == Ar.NAs{_} : Ar.Named}
                  %Equal.sym(Maybe<&2, String>, Ar.lookup(cur, rs), None{}, er) : {Ar.named.hint(_, Ar.Schema{ps, False{}}, als, cur) == Ar.NAs{cur} : Ar.Named}
                  %Equal.sym(Maybe<&2, String>, Ar.lookup(cur, als), None{}, ea) : {Ar.named.alias(_, Ar.found(Ar.prop(cur, ps)), False{}, cur, ps) == Ar.NAs{cur} : Ar.Named}
                  %Equal.sym(Bool, Ar.found(Ar.prop(cur, ps)), False{}, ed) : {Ar.named.alias(None{}, _, False{}, cur, ps) == Ar.NAs{cur} : Ar.Named}
                  {==}

# Names taken
# -----------

def id.fo_at(b: Bool, -k: String, -r: Maybe<&2, String>, -hh: Bool, h: {Ar.pick.at(b, k, r) == None{} : Maybe<&2, String>}, ih: {r == None{} : Maybe<&2, String>} -> {hh == False{} : Bool}) -> {Bool.or(b, hh) == False{} : Bool}:
  match b:
    case True{}:
      AB.ab.some_none({Bool.or(True{}, hh) == False{} : Bool}, k, h)
    case False{}:
      ih(h)

# no seen name is c: c is none of the names
def id.fo_has(+c: String, ss: List<&2, Ar.Seen>, h: {Ar.first_of(c, ss) == None{} : Maybe<&2, String>}) -> {Ar.has(c, id.names(ss)) == False{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +t:
      match s:
        case Ar.Seen{+n, +k}:
          id.fo_at(String.eq(c, n), k, Ar.first_of(c, t), Ar.has(c, id.names(t)), h, e => id.fo_has(c, t, e))

def id.has_at(b: Bool, -k: String, -r: Maybe<&2, String>, -hh: Bool, h: {Bool.or(b, hh) == False{} : Bool}, ih: {hh == False{} : Bool} -> {r == None{} : Maybe<&2, String>}) -> {Ar.pick.at(b, k, r) == None{} : Maybe<&2, String>}:
  match b:
    case True{}:
      AB.ab.absurd_tf({Ar.pick.at(True{}, k, r) == None{} : Maybe<&2, String>}, h)
    case False{}:
      ih(h)

# c is none of the names: no seen name is c
def id.has_fo(+c: String, ss: List<&2, Ar.Seen>, h: {Ar.has(c, id.names(ss)) == False{} : Bool}) -> {Ar.first_of(c, ss) == None{} : Maybe<&2, String>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +t:
      match s:
        case Ar.Seen{+n, +k}:
          id.has_at(String.eq(c, n), k, Ar.first_of(c, t), Ar.has(c, id.names(t)), h, e => id.has_fo(c, t, e))

def id.fo(+c: String, +ss1: List<&2, Ar.Seen>, +ss2: List<&2, Ar.Seen>, hss: {id.names(ss1) == id.names(ss2) : List<&2, String>}, h: {Ar.first_of(c, ss1) == None{} : Maybe<&2, String>}) -> {Ar.first_of(c, ss2) == None{} : Maybe<&2, String>}:
  id.has_fo(c, ss2, Equal.trans(Bool, Ar.has(c, id.names(ss2)), Ar.has(c, id.names(ss1)), False{}, Equal.cong(List<&2, String>, Bool, ns => Ar.has(c, ns), id.names(ss2), id.names(ss1), Equal.sym(List<&2, String>, id.names(ss1), id.names(ss2), hss)), id.fo_has(c, ss1, h)))

def id.hs(+c: String, -cur: String, s: Ar.Seen, +ss1: List<&2, Ar.Seen>, +ss2: List<&2, Ar.Seen>, hs: {s == Ar.Seen{c, cur} : Ar.Seen}, hss: {id.names(ss1) == id.names(ss2) : List<&2, String>}) -> {id.names(s <> ss1) == id.names(Ar.Seen{c, c} <> ss2) : List<&2, String>}:
  %Equal.sym(Ar.Seen, s, Ar.Seen{c, cur}, hs) : {id.names(_ <> ss1) == id.names(Ar.Seen{c, c} <> ss2) : List<&2, String>}
  %hss : {c <> id.names(ss1) == c <> _ : List<&2, String>}
  {==}

# Values read
# -----------

def id.ci(k: Ar.Ty, it: Maybe<&2, String>, v: Ar.Val, r: Maybe<&2, Ar.To>, er: {Ar.coerce.val(k, it, v) == r : Maybe<&2, Ar.To>}, hok: {PCoerceTyped.ct.ok(k, r) == True{} : Bool}) -> {Ar.coerce.val(k, it, ArgRepair.ar_value(v, r)) == None{} : Maybe<&2, Ar.To>}:
  match k:
    case Ar.KString{}:
      match r:
        case None{}:
          er
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({Ar.coerce.val(Ar.KString{}, it, ArgRepair.ar_value(v, Some{Ar.TBool{b}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TNum{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KString{}, it, ArgRepair.ar_value(v, Some{Ar.TNum{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TStr{y}:
              {==}
            case Ar.TOne{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KString{}, it, ArgRepair.ar_value(v, Some{Ar.TOne{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TObj{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KString{}, it, ArgRepair.ar_value(v, Some{Ar.TObj{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TArr{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KString{}, it, ArgRepair.ar_value(v, Some{Ar.TArr{}})) == None{} : Maybe<&2, Ar.To>}, hok)
    case Ar.KBoolean{}:
      match r:
        case None{}:
          er
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              {==}
            case Ar.TNum{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KBoolean{}, it, ArgRepair.ar_value(v, Some{Ar.TNum{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TStr{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KBoolean{}, it, ArgRepair.ar_value(v, Some{Ar.TStr{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TOne{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KBoolean{}, it, ArgRepair.ar_value(v, Some{Ar.TOne{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TObj{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KBoolean{}, it, ArgRepair.ar_value(v, Some{Ar.TObj{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TArr{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KBoolean{}, it, ArgRepair.ar_value(v, Some{Ar.TArr{}})) == None{} : Maybe<&2, Ar.To>}, hok)
    case Ar.KInteger{}:
      match r:
        case None{}:
          er
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({Ar.coerce.val(Ar.KInteger{}, it, ArgRepair.ar_value(v, Some{Ar.TBool{b}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TNum{y}:
              {==}
            case Ar.TStr{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KInteger{}, it, ArgRepair.ar_value(v, Some{Ar.TStr{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TOne{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KInteger{}, it, ArgRepair.ar_value(v, Some{Ar.TOne{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TObj{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KInteger{}, it, ArgRepair.ar_value(v, Some{Ar.TObj{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TArr{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KInteger{}, it, ArgRepair.ar_value(v, Some{Ar.TArr{}})) == None{} : Maybe<&2, Ar.To>}, hok)
    case Ar.KNumber{}:
      match r:
        case None{}:
          er
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({Ar.coerce.val(Ar.KNumber{}, it, ArgRepair.ar_value(v, Some{Ar.TBool{b}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TNum{y}:
              {==}
            case Ar.TStr{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KNumber{}, it, ArgRepair.ar_value(v, Some{Ar.TStr{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TOne{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KNumber{}, it, ArgRepair.ar_value(v, Some{Ar.TOne{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TObj{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KNumber{}, it, ArgRepair.ar_value(v, Some{Ar.TObj{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TArr{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KNumber{}, it, ArgRepair.ar_value(v, Some{Ar.TArr{}})) == None{} : Maybe<&2, Ar.To>}, hok)
    case Ar.KObject{}:
      match r:
        case None{}:
          er
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({Ar.coerce.val(Ar.KObject{}, it, ArgRepair.ar_value(v, Some{Ar.TBool{b}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TNum{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KObject{}, it, ArgRepair.ar_value(v, Some{Ar.TNum{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TStr{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KObject{}, it, ArgRepair.ar_value(v, Some{Ar.TStr{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TOne{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KObject{}, it, ArgRepair.ar_value(v, Some{Ar.TOne{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TObj{}:
              {==}
            case Ar.TArr{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KObject{}, it, ArgRepair.ar_value(v, Some{Ar.TArr{}})) == None{} : Maybe<&2, Ar.To>}, hok)
    case Ar.KArray{}:
      match r:
        case None{}:
          er
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({Ar.coerce.val(Ar.KArray{}, it, ArgRepair.ar_value(v, Some{Ar.TBool{b}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TNum{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KArray{}, it, ArgRepair.ar_value(v, Some{Ar.TNum{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TStr{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KArray{}, it, ArgRepair.ar_value(v, Some{Ar.TStr{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TOne{}:
              {==}
            case Ar.TObj{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KArray{}, it, ArgRepair.ar_value(v, Some{Ar.TObj{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TArr{}:
              {==}
    case Ar.KOther{}:
      match r:
        case None{}:
          er
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({Ar.coerce.val(Ar.KOther{}, it, ArgRepair.ar_value(v, Some{Ar.TBool{b}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TNum{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KOther{}, it, ArgRepair.ar_value(v, Some{Ar.TNum{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TStr{y}:
              AB.ab.absurd({Ar.coerce.val(Ar.KOther{}, it, ArgRepair.ar_value(v, Some{Ar.TStr{y}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TOne{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KOther{}, it, ArgRepair.ar_value(v, Some{Ar.TOne{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TObj{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KOther{}, it, ArgRepair.ar_value(v, Some{Ar.TObj{}})) == None{} : Maybe<&2, Ar.To>}, hok)
            case Ar.TArr{}:
              AB.ab.absurd({Ar.coerce.val(Ar.KOther{}, it, ArgRepair.ar_value(v, Some{Ar.TArr{}})) == None{} : Maybe<&2, Ar.To>}, hok)

# a value as read reads as nothing more
def id.cp(p: Maybe<&2, Ar.Prop>, +v: Ar.Val) -> {Ar.coerce(p, ArgRepair.ar_value(v, Ar.coerce(p, v))) == None{} : Maybe<&2, Ar.To>}:
  match p:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case Ar.Prop{n, k, +it}:
          match k:
            case None{}:
              {==}
            case Some{+t}:
              id.ci(Ar.kind(t), it, v, Ar.coerce.val(Ar.kind(t), it, v), {==}, PCoerceTyped.ct.val(Ar.kind(t), it, v))

# The second step
# ---------------

def id.st_ok(same: Bool, to: Maybe<&2, Ar.To>, +c: String, -v: Ar.Val, es: {same == True{} : Bool}, eto: {to == None{} : Maybe<&2, Ar.To>}) -> {Ar.step.ok(same, c, to, Nil{}, c, v) == Ar.StepOk{Ar.Out{c, None{}}, Nil{}, Ar.Seen{c, c}} : Ar.Step}:
  %Equal.sym(Bool, same, True{}, es) : {Ar.step.ok(_, c, to, Nil{}, c, v) == Ar.StepOk{Ar.Out{c, None{}}, Nil{}, Ar.Seen{c, c}} : Ar.Step}
  %Equal.sym(Maybe<&2, Ar.To>, to, None{}, eto) : {Ar.step.ok(True{}, c, _, Nil{}, c, v) == Ar.StepOk{Ar.Out{c, None{}}, Nil{}, Ar.Seen{c, c}} : Ar.Step}
  {==}

def id.st_first(f: Maybe<&2, String>, +c: String, +ps: List<&2, Ar.Prop>, +v: Ar.Val, ef: {f == None{} : Maybe<&2, String>}, eto: {Ar.coerce(Ar.prop(c, ps), v) == None{} : Maybe<&2, Ar.To>}) -> {Ar.step.first(f, c, ps, Nil{}, c, v) == Ar.StepOk{Ar.Out{c, None{}}, Nil{}, Ar.Seen{c, c}} : Ar.Step}:
  %Equal.sym(Maybe<&2, String>, f, None{}, ef) : {Ar.step.first(_, c, ps, Nil{}, c, v) == Ar.StepOk{Ar.Out{c, None{}}, Nil{}, Ar.Seen{c, c}} : Ar.Step}
  id.st_ok(String.eq(c, c), Ar.coerce(Ar.prop(c, ps), v), c, v, AB.ab.str_refl(c), eto)

# a plain argument whose name is its own, untaken, and whose value reads as
# nothing more, is kept with no record
def id.st2(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, -ks: List<&2, String>, +ss: List<&2, Ar.Seen>, +c: String, +v: Ar.Val, en: {Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c) == Ar.NAs{c} : Ar.Named}, ef: {Ar.first_of(c, ss) == None{} : Maybe<&2, String>}, eto: {Ar.coerce(Ar.prop(c, ps), v) == None{} : Maybe<&2, Ar.To>}) -> {Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{c, None{}, v}) == Ar.StepOk{Ar.Out{c, None{}}, Nil{}, Ar.Seen{c, c}} : Ar.Step}:
  %Equal.sym(Ar.Named, Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, c), Ar.NAs{c}, en) : {Ar.step.named(_, ps, ss, Nil{}, c, v) == Ar.StepOk{Ar.Out{c, None{}}, Nil{}, Ar.Seen{c, c}} : Ar.Step}
  id.st_first(Ar.first_of(c, ss), c, ps, v, ef, eto)

# The walk
# --------

def id.eto(+c: String, +ps: List<&2, Ar.Prop>, +v: Ar.Val, to: Maybe<&2, Ar.To>, hto: {to == Ar.coerce(Ar.prop(c, ps), v) : Maybe<&2, Ar.To>}) -> {Ar.coerce(Ar.prop(c, ps), ArgRepair.ar_value(v, to)) == None{} : Maybe<&2, Ar.To>}:
  %Equal.sym(Maybe<&2, Ar.To>, to, Ar.coerce(Ar.prop(c, ps), v), hto) : {Ar.coerce(Ar.prop(c, ps), ArgRepair.ar_value(v, _)) == None{} : Maybe<&2, Ar.To>}
  id.cp(Ar.prop(c, ps), v)


def id.ok(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks1: List<&2, String>, +ss1: List<&2, Ar.Seen>, +ks2: List<&2, String>, +ss2: List<&2, Ar.Seen>, +hss: {id.names(ss1) == id.names(ss2) : List<&2, String>}, +wf: {ArgRepair.ar_wf.alias(ps, rs, als) == True{} : Bool}, +k: String, +m: Maybe<&2, String>, +v: Ar.Val, +t: List<&2, Ar.Arg>, +c: String, +to: Maybe<&2, Ar.To>, -r: List<&2, Ar.Record>, +s: Ar.Seen, +os1: List<&2, Ar.Out>, -xs1: List<&2, Ar.Record>, +os: List<&2, Ar.Out>, -xs: List<&2, Ar.Record>, eos: {Ar.Out{c, to} <> os1 == os : List<&2, Ar.Out>}, hn: {SV.sv.nok2(Ar.lookup(ArgRepair.ar_cur(Ar.decoded(ks1, k, m), k), rs), Ar.lookup(ArgRepair.ar_cur(Ar.decoded(ks1, k, m), k), als), Ar.found(Ar.prop(ArgRepair.ar_cur(Ar.decoded(ks1, k, m), k), ps)), cl, ArgRepair.ar_cur(Ar.decoded(ks1, k, m), k), c) == True{} : Bool}, hf: {Ar.first_of(c, ss1) == None{} : Maybe<&2, String>}, hto: {to == Ar.coerce(Ar.prop(c, ps), v) : Maybe<&2, Ar.To>}, hs: {s == Ar.Seen{c, ArgRepair.ar_cur(Ar.decoded(ks1, k, m), k)} : Ar.Seen}, ih: {Ar.go(ArgRepair.ar_after(t, os1), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, Ar.Seen{c, c} <> ss2) == Ar.Repaired{ArgRepair.ar_kept(os1), Nil{}} : Ar.Verdict}) -> {Ar.go(ArgRepair.ar_after(Ar.Arg{k, m, v} <> t, os), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, ss2) == Ar.Repaired{ArgRepair.ar_kept(os), Nil{}} : Ar.Verdict}:
  +cur = ArgRepair.ar_cur(Ar.decoded(ks1, k, m), k)
  +val = ArgRepair.ar_value(v, to)
  %eos : {Ar.go(ArgRepair.ar_after(Ar.Arg{k, m, v} <> t, _), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, ss2) == Ar.Repaired{ArgRepair.ar_kept(_), Nil{}} : Ar.Verdict}
  +en = id.idn(Ar.lookup(cur, rs), Ar.lookup(cur, als), Ar.found(Ar.prop(cur, ps)), ps, cl, als, rs, cur, c, hn, {==}, {==}, {==}, id.wf(ps, rs, als, cur, wf))
  +eto = id.eto(c, ps, v, to, hto)
  +st2 = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, ss2, Ar.Arg{c, None{}, val})
  %Equal.sym(Ar.Step, st2, Ar.StepOk{Ar.Out{c, None{}}, Nil{}, Ar.Seen{c, c}}, id.st2(ps, cl, als, rs, ks2, ss2, c, val, en, id.fo(c, ss1, ss2, hss, hf), eto)) : {Ar.go.cons(_, Ar.go(ArgRepair.ar_after(t, os1), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, Ar.seen.next(_, ss2))) == Ar.Repaired{Ar.Out{c, None{}} <> ArgRepair.ar_kept(os1), Nil{}} : Ar.Verdict}
  %Equal.sym(Ar.Verdict, Ar.go(ArgRepair.ar_after(t, os1), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, Ar.Seen{c, c} <> ss2), Ar.Repaired{ArgRepair.ar_kept(os1), Nil{}}, ih) : {Ar.go.cons(Ar.StepOk{Ar.Out{c, None{}}, Nil{}, Ar.Seen{c, c}}, _) == Ar.Repaired{Ar.Out{c, None{}} <> ArgRepair.ar_kept(os1), Nil{}} : Ar.Verdict}
  {==}

def id.repaired(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks1: List<&2, String>, +ss1: List<&2, Ar.Seen>, +ks2: List<&2, String>, +ss2: List<&2, Ar.Seen>, +hss: {id.names(ss1) == id.names(ss2) : List<&2, String>}, +wf: {ArgRepair.ar_wf.alias(ps, rs, als) == True{} : Bool}, +k: String, +m: Maybe<&2, String>, +v: Ar.Val, +t: List<&2, Ar.Arg>, +c: String, +to: Maybe<&2, Ar.To>, +r: List<&2, Ar.Record>, +s: Ar.Seen, h: SV.sv.SVo(ps, cl, als, rs, ss1, Ar.decoded(ks1, k, m), k, v, Ar.Out{c, to}, r, s), +os1: List<&2, Ar.Out>, +xs1: List<&2, Ar.Record>, +os: List<&2, Ar.Out>, +xs: List<&2, Ar.Record>, ok: {Ar.Repaired{Ar.Out{c, to} <> os1, List.append(&2, Ar.Record, r, xs1)} == Ar.Repaired{os, xs} : Ar.Verdict}, ih: @s2: List<&2, Ar.Seen> -> {id.names(s <> ss1) == id.names(s2) : List<&2, String>} -> @o2: List<&2, Ar.Out> -> @x2: List<&2, Ar.Record> -> {Ar.Repaired{os1, xs1} == Ar.Repaired{o2, x2} : Ar.Verdict} -> {Ar.go(ArgRepair.ar_after(t, o2), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, s2) == Ar.Repaired{ArgRepair.ar_kept(o2), Nil{}} : Ar.Verdict}) -> {Ar.go(ArgRepair.ar_after(Ar.Arg{k, m, v} <> t, os), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, ss2) == Ar.Repaired{ArgRepair.ar_kept(os), Nil{}} : Ar.Verdict}:
  (hn, (hf, (hto, (hs, hr)))) = h
  +hs2 = hs
  id.ok(ps, cl, als, rs, ks1, ss1, ks2, ss2, hss, wf, k, m, v, t, c, to, r, s, os1, xs1, os, xs, Equal.cong(Ar.Verdict, List<&2, Ar.Out>, w => id.outs(w), Ar.Repaired{Ar.Out{c, to} <> os1, List.append(&2, Ar.Record, r, xs1)}, Ar.Repaired{os, xs}, ok), hn, hf, hto, hs2, ih(Ar.Seen{c, c} <> ss2, id.hs(c, ArgRepair.ar_cur(Ar.decoded(ks1, k, m), k), s, ss1, ss2, hs2, hss), os1, xs1, {==}))

def id.cons(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks1: List<&2, String>, +ss1: List<&2, Ar.Seen>, +ks2: List<&2, String>, +ss2: List<&2, Ar.Seen>, +hss: {id.names(ss1) == id.names(ss2) : List<&2, String>}, +wf: {ArgRepair.ar_wf.alias(ps, rs, als) == True{} : Bool}, a: Ar.Arg, +t: List<&2, Ar.Arg>, st: Ar.Step, h: SV.sv.SVa(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks1, ss1, a, st), rest: Ar.Verdict, +os: List<&2, Ar.Out>, +xs: List<&2, Ar.Record>, ok: {Ar.go.cons(st, rest) == Ar.Repaired{os, xs} : Ar.Verdict}, ih: @s2: List<&2, Ar.Seen> -> {id.names(Ar.seen.next(st, ss1)) == id.names(s2) : List<&2, String>} -> @o2: List<&2, Ar.Out> -> @x2: List<&2, Ar.Record> -> {rest == Ar.Repaired{o2, x2} : Ar.Verdict} -> {Ar.go(ArgRepair.ar_after(t, o2), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, s2) == Ar.Repaired{ArgRepair.ar_kept(o2), Nil{}} : Ar.Verdict}) -> {Ar.go(ArgRepair.ar_after(a <> t, os), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, ss2) == Ar.Repaired{ArgRepair.ar_kept(os), Nil{}} : Ar.Verdict}:
  match a:
    case Ar.Arg{+k, +m, +v}:
      match st:
        case Ar.StepNo{x}:
          id.no({Ar.go(ArgRepair.ar_after(Ar.Arg{k, m, v} <> t, os), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, ss2) == Ar.Repaired{ArgRepair.ar_kept(os), Nil{}} : Ar.Verdict}, x, os, xs, ok)
        case Ar.StepOk{o, +r, +s}:
          match o:
            case Ar.Out{+c, +to}:
              match rest:
                case Ar.Rejected{x}:
                  id.no({Ar.go(ArgRepair.ar_after(Ar.Arg{k, m, v} <> t, os), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, ss2) == Ar.Repaired{ArgRepair.ar_kept(os), Nil{}} : Ar.Verdict}, x, os, xs, ok)
                case Ar.Repaired{+os1, +xs1}:
                  id.repaired(ps, cl, als, rs, ks1, ss1, ks2, ss2, hss, wf, k, m, v, t, c, to, r, s, h, os1, xs1, os, xs, ok, ih)

def id.go(args: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks1: List<&2, String>, +ss1: List<&2, Ar.Seen>, +ks2: List<&2, String>, +ss2: List<&2, Ar.Seen>, +hss: {id.names(ss1) == id.names(ss2) : List<&2, String>}, +wf: {ArgRepair.ar_wf.alias(ps, rs, als) == True{} : Bool}, +os: List<&2, Ar.Out>, +xs: List<&2, Ar.Record>, ok: {Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks1, ss1) == Ar.Repaired{os, xs} : Ar.Verdict}) -> {Ar.go(ArgRepair.ar_after(args, os), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, ss2) == Ar.Repaired{ArgRepair.ar_kept(os), Nil{}} : Ar.Verdict}:
  match args:
    case Nil{}:
      %Equal.cong(Ar.Verdict, List<&2, Ar.Out>, w => id.outs(w), Ar.Repaired{Nil{}, Nil{}}, Ar.Repaired{os, xs}, ok) : {Ar.go(ArgRepair.ar_after(Nil{}, _), Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks2, ss2) == Ar.Repaired{ArgRepair.ar_kept(_), Nil{}} : Ar.Verdict}
      {==}
    case +a <> +t:
      +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks1, ss1, a)
      id.cons(ps, cl, als, rs, ks1, ss1, ks2, ss2, hss, wf, a, t, st, SV.sv.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks1, ss1, a), Ar.go(t, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks1, Ar.seen.next(st, ss1)), os, xs, ok, s2 => hs => o2 => x2 => e => id.go(t, ps, cl, als, rs, ks1, Ar.seen.next(st, ss1), ks2, s2, hs, wf, o2, x2, e))

def ArgRepair.arg_repair_idempotent(sc, d, args, os, rs, wf, ok):
  match sc:
    case Ar.Schema{+ps, +cl}:
      match d:
        case Ar.Dialect{+als, +xs}:
          id.go(args, ps, cl, als, xs, Ar.keys(args), Nil{}, Ar.keys(ArgRepair.ar_after(args, os)), Nil{}, {==}, wf, os, rs, ok)
