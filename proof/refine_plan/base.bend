# eukhe: lemmas of the refine_plan proofs: each model def is its spec helper (laws/refine_plan/model.bend), def by def

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/model.bend as RefinePlan

def rpb.verb_name(+v: Rp.Verb) -> {Rp.verb_name(v) == RefinePlan.rp_verb_name(v) : String}:
  match v:
    case Rp.ACreate{}:
      {==}
    case Rp.AUpdate{}:
      {==}
    case Rp.ADelete{}:
      {==}

def rpb.comp_name(+c: Rp.Comp) -> {Rp.comp_name(c) == RefinePlan.rp_comp_name(c) : String}:
  match c:
    case Rp.KPrompt{}:
      {==}
    case Rp.KMemory{}:
      {==}
    case Rp.KSkill{}:
      {==}
    case Rp.KSubagent{}:
      {==}
    case Rp.KFactory{}:
      {==}

def rpb.comp_eq(+a: Rp.Comp, +b: Rp.Comp) -> {Rp.comp_eq(a, b) == RefinePlan.rp_comp_eq(a, b) : Bool}:
  %Equal.sym(String, Rp.comp_name(a), RefinePlan.rp_comp_name(a), rpb.comp_name(a)) : {String.eq(_, Rp.comp_name(b)) == String.eq(RefinePlan.rp_comp_name(a), RefinePlan.rp_comp_name(b)) : Bool}
  %Equal.sym(String, Rp.comp_name(b), RefinePlan.rp_comp_name(b), rpb.comp_name(b)) : {String.eq(RefinePlan.rp_comp_name(a), _) == String.eq(RefinePlan.rp_comp_name(a), RefinePlan.rp_comp_name(b)) : Bool}
  {==}

def rpb.slug.put.at(+alnum: Bool, +upper: Bool, +dotted: Bool, +kelvin: Bool, +c: Char, +r: String) -> {Rp.slug.put.at(alnum, upper, dotted, kelvin, c, r) == RefinePlan.rp_slug.put.at(alnum, upper, dotted, kelvin, c, r) : String}:
  match alnum:
    case True{}:
      {==}
    case False{}:
      match upper:
        case True{}:
          {==}
        case False{}:
          match dotted:
            case True{}:
              {==}
            case False{}:
              match kelvin:
                case True{}:
                  {==}
                case False{}:
                  {==}

def rpb.slug.marks(+s: String) -> {Rp.slug.marks(s) == RefinePlan.rp_slug.marks(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Rp.slug.marks(t), RefinePlan.rp_slug.marks(t), rpb.slug.marks(t)) : {Rp.slug.put.at(Bool.or(Char.is_lower(c), Char.is_digit(c)), Char.is_upper(c), U32.is_eq(Char.to_u32(c), 304), U32.is_eq(Char.to_u32(c), 8490), c, _) == RefinePlan.rp_slug.put.at(Bool.or(Char.is_lower(c), Char.is_digit(c)), Char.is_upper(c), U32.is_eq(Char.to_u32(c), 304), U32.is_eq(Char.to_u32(c), 8490), c, RefinePlan.rp_slug.marks(t)) : String}
      rpb.slug.put.at(Bool.or(Char.is_lower(c), Char.is_digit(c)), Char.is_upper(c), U32.is_eq(Char.to_u32(c), 304), U32.is_eq(Char.to_u32(c), 8490), c, RefinePlan.rp_slug.marks(t))

def rpb.slug.squeeze.at(+dup: Bool, +c: Char, +r: String) -> {Rp.slug.squeeze.at(dup, c, r) == RefinePlan.rp_slug.squeeze.at(dup, c, r) : String}:
  match dup:
    case True{}:
      {==}
    case False{}:
      {==}

def rpb.slug.squeeze(+s: String) -> {Rp.slug.squeeze(s) == RefinePlan.rp_slug.squeeze(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Rp.slug.squeeze(t), RefinePlan.rp_slug.squeeze(t), rpb.slug.squeeze(t)) : {Rp.slug.squeeze.at(Bool.and(Char.is_eq(c, '_'), String.starts_with(t, "_")), c, _) == RefinePlan.rp_slug.squeeze.at(Bool.and(Char.is_eq(c, '_'), String.starts_with(t, "_")), c, RefinePlan.rp_slug.squeeze(t)) : String}
      rpb.slug.squeeze.at(Bool.and(Char.is_eq(c, '_'), String.starts_with(t, "_")), c, RefinePlan.rp_slug.squeeze(t))

def rpb.slug.lead.at(+b: Bool, +c: Char, +t: String, +r: String) -> {Rp.slug.lead.at(b, c, t, r) == RefinePlan.rp_slug.lead.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rpb.slug.lead(+s: String) -> {Rp.slug.lead(s) == RefinePlan.rp_slug.lead(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Rp.slug.lead(t), RefinePlan.rp_slug.lead(t), rpb.slug.lead(t)) : {Rp.slug.lead.at(Char.is_eq(c, '_'), c, t, _) == RefinePlan.rp_slug.lead.at(Char.is_eq(c, '_'), c, t, RefinePlan.rp_slug.lead(t)) : String}
      rpb.slug.lead.at(Char.is_eq(c, '_'), c, t, RefinePlan.rp_slug.lead(t))

def rpb.slug.pick(+e: Bool, +s: String, +fb: String) -> {Rp.slug.pick(e, s, fb) == RefinePlan.rp_slug.pick(e, s, fb) : String}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def rpb.slug(+raw: String, +fb: String) -> {Rp.slug(raw, fb) == RefinePlan.rp_slug(raw, fb) : String}:
  %Equal.sym(String, Rp.slug.marks(raw), RefinePlan.rp_slug.marks(raw), rpb.slug.marks(raw)) : {Rp.slug.pick(String.is_empty(String.take(String.reverse(Rp.slug.lead(String.reverse(Rp.slug.lead(Rp.slug.squeeze(_))))), 80n)), String.take(String.reverse(Rp.slug.lead(String.reverse(Rp.slug.lead(Rp.slug.squeeze(Rp.slug.marks(raw)))))), 80n), fb) == RefinePlan.rp_slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n), fb) : String}
  %Equal.sym(String, Rp.slug.squeeze(RefinePlan.rp_slug.marks(raw)), RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)), rpb.slug.squeeze(RefinePlan.rp_slug.marks(raw))) : {Rp.slug.pick(String.is_empty(String.take(String.reverse(Rp.slug.lead(String.reverse(Rp.slug.lead(_)))), 80n)), String.take(String.reverse(Rp.slug.lead(String.reverse(Rp.slug.lead(Rp.slug.squeeze(Rp.slug.marks(raw)))))), 80n), fb) == RefinePlan.rp_slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n), fb) : String}
  %Equal.sym(String, Rp.slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw))), RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw))), rpb.slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))) : {Rp.slug.pick(String.is_empty(String.take(String.reverse(Rp.slug.lead(String.reverse(_))), 80n)), String.take(String.reverse(Rp.slug.lead(String.reverse(Rp.slug.lead(Rp.slug.squeeze(Rp.slug.marks(raw)))))), 80n), fb) == RefinePlan.rp_slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n), fb) : String}
  %Equal.sym(String, Rp.slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw))))), RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw))))), rpb.slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))) : {Rp.slug.pick(String.is_empty(String.take(String.reverse(_), 80n)), String.take(String.reverse(Rp.slug.lead(String.reverse(Rp.slug.lead(Rp.slug.squeeze(Rp.slug.marks(raw)))))), 80n), fb) == RefinePlan.rp_slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n), fb) : String}
  %Equal.sym(String, Rp.slug.marks(raw), RefinePlan.rp_slug.marks(raw), rpb.slug.marks(raw)) : {Rp.slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(Rp.slug.lead(String.reverse(Rp.slug.lead(Rp.slug.squeeze(_))))), 80n), fb) == RefinePlan.rp_slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n), fb) : String}
  %Equal.sym(String, Rp.slug.squeeze(RefinePlan.rp_slug.marks(raw)), RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)), rpb.slug.squeeze(RefinePlan.rp_slug.marks(raw))) : {Rp.slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(Rp.slug.lead(String.reverse(Rp.slug.lead(_)))), 80n), fb) == RefinePlan.rp_slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n), fb) : String}
  %Equal.sym(String, Rp.slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw))), RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw))), rpb.slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))) : {Rp.slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(Rp.slug.lead(String.reverse(_))), 80n), fb) == RefinePlan.rp_slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n), fb) : String}
  %Equal.sym(String, Rp.slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw))))), RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw))))), rpb.slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))) : {Rp.slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(_), 80n), fb) == RefinePlan.rp_slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n), fb) : String}
  rpb.slug.pick(String.is_empty(String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n)), String.take(String.reverse(RefinePlan.rp_slug.lead(String.reverse(RefinePlan.rp_slug.lead(RefinePlan.rp_slug.squeeze(RefinePlan.rp_slug.marks(raw)))))), 80n), fb)

def rpb.is_create(+m: Maybe<&2, Rp.Verb>) -> {Rp.is_create(m) == RefinePlan.rp_is_create(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      match v:
        case Rp.ACreate{}:
          {==}
        case Rp.AUpdate{}:
          {==}
        case Rp.ADelete{}:
          {==}

def rpb.comp_or_memory(+m: Maybe<&2, Rp.Comp>) -> {Rp.comp_or_memory(m) == RefinePlan.rp_comp_or_memory(m) : Rp.Comp}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      {==}

def rpb.computed.at(+create: Bool, +title: Maybe<&2, String>, +name: String) -> {Rp.computed.at(create, title, name) == RefinePlan.rp_computed.at(create, title, name) : Maybe<&2, String>}:
  match create:
    case True{}:
      %Equal.sym(String, Rp.slug(Maybe.default(&2, String, title, name), name), RefinePlan.rp_slug(Maybe.default(&2, String, title, name), name), rpb.slug(Maybe.default(&2, String, title, name), name)) : {Some{_} == Some{RefinePlan.rp_slug(Maybe.default(&2, String, title, name), name)} : Maybe<&2, String>}
      {==}
    case False{}:
      {==}

def rpb.computed(+e: Rp.Ed) -> {Rp.computed(e) == RefinePlan.rp_computed(e) : Maybe<&2, String>}:
  match e:
    case Rp.Ed{+verb, +comp, +id, +title, +content, +pyref, +args, +exists, +differs, +held}:
      %Equal.sym(Bool, Rp.is_create(verb), RefinePlan.rp_is_create(verb), rpb.is_create(verb)) : {Maybe.or(&2, String, id, Rp.computed.at(_, title, Rp.comp_name(Rp.comp_or_memory(comp)))) == Maybe.or(&2, String, id, RefinePlan.rp_computed.at(RefinePlan.rp_is_create(verb), title, RefinePlan.rp_comp_name(RefinePlan.rp_comp_or_memory(comp)))) : Maybe<&2, String>}
      %Equal.sym(Rp.Comp, Rp.comp_or_memory(comp), RefinePlan.rp_comp_or_memory(comp), rpb.comp_or_memory(comp)) : {Maybe.or(&2, String, id, Rp.computed.at(RefinePlan.rp_is_create(verb), title, Rp.comp_name(_))) == Maybe.or(&2, String, id, RefinePlan.rp_computed.at(RefinePlan.rp_is_create(verb), title, RefinePlan.rp_comp_name(RefinePlan.rp_comp_or_memory(comp)))) : Maybe<&2, String>}
      %Equal.sym(String, Rp.comp_name(RefinePlan.rp_comp_or_memory(comp)), RefinePlan.rp_comp_name(RefinePlan.rp_comp_or_memory(comp)), rpb.comp_name(RefinePlan.rp_comp_or_memory(comp))) : {Maybe.or(&2, String, id, Rp.computed.at(RefinePlan.rp_is_create(verb), title, _)) == Maybe.or(&2, String, id, RefinePlan.rp_computed.at(RefinePlan.rp_is_create(verb), title, RefinePlan.rp_comp_name(RefinePlan.rp_comp_or_memory(comp)))) : Maybe<&2, String>}
      %Equal.sym(Maybe<&2, String>, Rp.computed.at(RefinePlan.rp_is_create(verb), title, RefinePlan.rp_comp_name(RefinePlan.rp_comp_or_memory(comp))), RefinePlan.rp_computed.at(RefinePlan.rp_is_create(verb), title, RefinePlan.rp_comp_name(RefinePlan.rp_comp_or_memory(comp))), rpb.computed.at(RefinePlan.rp_is_create(verb), title, RefinePlan.rp_comp_name(RefinePlan.rp_comp_or_memory(comp)))) : {Maybe.or(&2, String, id, _) == Maybe.or(&2, String, id, RefinePlan.rp_computed.at(RefinePlan.rp_is_create(verb), title, RefinePlan.rp_comp_name(RefinePlan.rp_comp_or_memory(comp)))) : Maybe<&2, String>}
      {==}

def rpb.ids(+eds: List<&2, Rp.Ed>) -> {Rp.ids(eds) == RefinePlan.rp_ids(eds) : List<&2, Maybe<&2, String>>}:
  match eds:
    case Nil{}:
      {==}
    case +e <> +t:
      %Equal.sym(Maybe<&2, String>, Rp.computed(e), RefinePlan.rp_computed(e), rpb.computed(e)) : {_ <> Rp.ids(t) == RefinePlan.rp_computed(e) <> RefinePlan.rp_ids(t) : List<&2, Maybe<&2, String>>}
      %Equal.sym(List<&2, Maybe<&2, String>>, Rp.ids(t), RefinePlan.rp_ids(t), rpb.ids(t)) : {RefinePlan.rp_computed(e) <> _ == RefinePlan.rp_computed(e) <> RefinePlan.rp_ids(t) : List<&2, Maybe<&2, String>>}
      {==}

def rpb.first(+b: Bool, +msg: String, +r: Maybe<&2, String>) -> {Rp.first(b, msg, r) == RefinePlan.rp_first(b, msg, r) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rpb.is_text(+m: Maybe<&2, String>, +x: String) -> {Rp.is_text(m, x) == RefinePlan.rp_is_text(m, x) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+y}:
      {==}

def rpb.filled(+m: Maybe<&2, String>) -> {Rp.filled(m) == RefinePlan.rp_filled(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+y}:
      {==}

def rpb.is_comp(+c: Rp.Comp, +d: Rp.Comp) -> {Rp.is_comp(c, d) == RefinePlan.rp_is_comp(c, d) : Bool}:
  rpb.comp_eq(c, d)

def rpb.is_verb(+v: Rp.Verb, +w: Rp.Verb) -> {Rp.is_verb(v, w) == RefinePlan.rp_is_verb(v, w) : Bool}:
  %Equal.sym(String, Rp.verb_name(v), RefinePlan.rp_verb_name(v), rpb.verb_name(v)) : {String.eq(_, Rp.verb_name(w)) == String.eq(RefinePlan.rp_verb_name(v), RefinePlan.rp_verb_name(w)) : Bool}
  %Equal.sym(String, Rp.verb_name(w), RefinePlan.rp_verb_name(w), rpb.verb_name(w)) : {String.eq(RefinePlan.rp_verb_name(v), _) == String.eq(RefinePlan.rp_verb_name(v), RefinePlan.rp_verb_name(w)) : Bool}
  {==}

def rpb.skill.fields(+vn: String, +r: Rp.Pyref) -> {Rp.skill.fields(vn, r) == RefinePlan.rp_skill.fields(vn, r) : Maybe<&2, String>}:
  match r:
    case Rp.Pyref{+ty, +imp, +pyimp, +call, +pat}:
      %Equal.sym(Bool, Rp.is_text(ty, "python"), RefinePlan.rp_is_text(ty, "python"), rpb.is_text(ty, "python")) : {Rp.first(Bool.not(_), String.concat([vn, " skill reference.type must be python"]), Rp.first(Bool.not(Bool.or(Rp.filled(imp), Rp.filled(pyimp))), String.concat([vn, " skill requires python import"]), Rp.first(Bool.not(Bool.or(Rp.filled(call), Rp.filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) == RefinePlan.rp_first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) : Maybe<&2, String>}
      %Equal.sym(Bool, Rp.filled(imp), RefinePlan.rp_filled(imp), rpb.filled(imp)) : {Rp.first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), Rp.first(Bool.not(Bool.or(_, Rp.filled(pyimp))), String.concat([vn, " skill requires python import"]), Rp.first(Bool.not(Bool.or(Rp.filled(call), Rp.filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) == RefinePlan.rp_first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) : Maybe<&2, String>}
      %Equal.sym(Bool, Rp.filled(pyimp), RefinePlan.rp_filled(pyimp), rpb.filled(pyimp)) : {Rp.first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), Rp.first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), _)), String.concat([vn, " skill requires python import"]), Rp.first(Bool.not(Bool.or(Rp.filled(call), Rp.filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) == RefinePlan.rp_first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) : Maybe<&2, String>}
      %Equal.sym(Bool, Rp.filled(call), RefinePlan.rp_filled(call), rpb.filled(call)) : {Rp.first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), Rp.first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), Rp.first(Bool.not(Bool.or(_, Rp.filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) == RefinePlan.rp_first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) : Maybe<&2, String>}
      %Equal.sym(Bool, Rp.filled(pat), RefinePlan.rp_filled(pat), rpb.filled(pat)) : {Rp.first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), Rp.first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), Rp.first(Bool.not(Bool.or(RefinePlan.rp_filled(call), _)), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) == RefinePlan.rp_first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) : Maybe<&2, String>}
      %Equal.sym(Maybe<&2, String>, Rp.first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}), rpb.first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{})) : {Rp.first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), Rp.first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), _)) == RefinePlan.rp_first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) : Maybe<&2, String>}
      %Equal.sym(Maybe<&2, String>, Rp.first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{})), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{})), rpb.first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) : {Rp.first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), _) == RefinePlan.rp_first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{}))) : Maybe<&2, String>}
      rpb.first(Bool.not(RefinePlan.rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(imp), RefinePlan.rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), RefinePlan.rp_first(Bool.not(Bool.or(RefinePlan.rp_filled(call), RefinePlan.rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{})))

def rpb.skill.ref(+vn: String, +m: Maybe<&2, Rp.Pyref>) -> {Rp.skill.ref(vn, m) == RefinePlan.rp_skill.ref(vn, m) : Maybe<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{+r}:
      rpb.skill.fields(vn, r)

def rpb.skill(+vn: String, +args: Maybe<&2, Rp.Args>, +m: Maybe<&2, Rp.Pyref>) -> {Rp.skill(vn, args, m) == RefinePlan.rp_skill(vn, args, m) : Maybe<&2, String>}:
  %Equal.sym(Maybe<&2, String>, Rp.skill.ref(vn, m), RefinePlan.rp_skill.ref(vn, m), rpb.skill.ref(vn, m)) : {Rp.first(Maybe.is_none(&2, Rp.Args, args), String.concat([vn, " skill requires arguments"]), _) == RefinePlan.rp_first(Maybe.is_none(&2, Rp.Args, args), String.concat([vn, " skill requires arguments"]), RefinePlan.rp_skill.ref(vn, m)) : Maybe<&2, String>}
  rpb.first(Maybe.is_none(&2, Rp.Args, args), String.concat([vn, " skill requires arguments"]), RefinePlan.rp_skill.ref(vn, m))

def rpb.present(+v: Rp.Val) -> {Rp.present(v) == RefinePlan.rp_present(v) : Bool}:
  match v:
    case Rp.VMissing{}:
      {==}
    case Rp.VNull{}:
      {==}
    case Rp.VObject{}:
      {==}
    case Rp.VOther{}:
      {==}

def rpb.is_object(+v: Rp.Val) -> {Rp.is_object(v) == RefinePlan.rp_is_object(v) : Bool}:
  match v:
    case Rp.VMissing{}:
      {==}
    case Rp.VNull{}:
      {==}
    case Rp.VObject{}:
      {==}
    case Rp.VOther{}:
      {==}

def rpb.spec_object(+m: Bool, +dag: Rp.Val, +machine: Rp.Val) -> {Rp.spec_object(m, dag, machine) == RefinePlan.rp_spec_object(m, dag, machine) : Bool}:
  match m:
    case True{}:
      rpb.is_object(machine)
    case False{}:
      rpb.is_object(dag)

def rpb.factory.keys(+dag: Rp.Val, +machine: Rp.Val) -> {Rp.factory.keys(dag, machine) == RefinePlan.rp_factory.keys(dag, machine) : Maybe<&2, String>}:
  %Equal.sym(Bool, Rp.present(dag), RefinePlan.rp_present(dag), rpb.present(dag)) : {Rp.first(Bool.and(_, Rp.present(machine)), "pass either dag or machine form, not both", Rp.first(Bool.not(Rp.spec_object(Rp.present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{})) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_present(dag), RefinePlan.rp_present(machine)), "pass either dag or machine form, not both", RefinePlan.rp_first(Bool.not(RefinePlan.rp_spec_object(RefinePlan.rp_present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{})) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.present(machine), RefinePlan.rp_present(machine), rpb.present(machine)) : {Rp.first(Bool.and(RefinePlan.rp_present(dag), _), "pass either dag or machine form, not both", Rp.first(Bool.not(Rp.spec_object(Rp.present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{})) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_present(dag), RefinePlan.rp_present(machine)), "pass either dag or machine form, not both", RefinePlan.rp_first(Bool.not(RefinePlan.rp_spec_object(RefinePlan.rp_present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{})) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.present(machine), RefinePlan.rp_present(machine), rpb.present(machine)) : {Rp.first(Bool.and(RefinePlan.rp_present(dag), RefinePlan.rp_present(machine)), "pass either dag or machine form, not both", Rp.first(Bool.not(Rp.spec_object(_, dag, machine)), "factory entry requires a dag or machine object in arguments", None{})) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_present(dag), RefinePlan.rp_present(machine)), "pass either dag or machine form, not both", RefinePlan.rp_first(Bool.not(RefinePlan.rp_spec_object(RefinePlan.rp_present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{})) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.spec_object(RefinePlan.rp_present(machine), dag, machine), RefinePlan.rp_spec_object(RefinePlan.rp_present(machine), dag, machine), rpb.spec_object(RefinePlan.rp_present(machine), dag, machine)) : {Rp.first(Bool.and(RefinePlan.rp_present(dag), RefinePlan.rp_present(machine)), "pass either dag or machine form, not both", Rp.first(Bool.not(_), "factory entry requires a dag or machine object in arguments", None{})) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_present(dag), RefinePlan.rp_present(machine)), "pass either dag or machine form, not both", RefinePlan.rp_first(Bool.not(RefinePlan.rp_spec_object(RefinePlan.rp_present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{})) : Maybe<&2, String>}
  %Equal.sym(Maybe<&2, String>, Rp.first(Bool.not(RefinePlan.rp_spec_object(RefinePlan.rp_present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{}), RefinePlan.rp_first(Bool.not(RefinePlan.rp_spec_object(RefinePlan.rp_present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{}), rpb.first(Bool.not(RefinePlan.rp_spec_object(RefinePlan.rp_present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{})) : {Rp.first(Bool.and(RefinePlan.rp_present(dag), RefinePlan.rp_present(machine)), "pass either dag or machine form, not both", _) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_present(dag), RefinePlan.rp_present(machine)), "pass either dag or machine form, not both", RefinePlan.rp_first(Bool.not(RefinePlan.rp_spec_object(RefinePlan.rp_present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{})) : Maybe<&2, String>}
  rpb.first(Bool.and(RefinePlan.rp_present(dag), RefinePlan.rp_present(machine)), "pass either dag or machine form, not both", RefinePlan.rp_first(Bool.not(RefinePlan.rp_spec_object(RefinePlan.rp_present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{}))

def rpb.factory(+args: Maybe<&2, Rp.Args>) -> {Rp.factory(args) == RefinePlan.rp_factory(args) : Maybe<&2, String>}:
  match args:
    case None{}:
      rpb.factory.keys(Rp.VMissing{}, Rp.VMissing{})
    case Some{+a}:
      match a:
        case Rp.Args{+dag, +machine}:
          rpb.factory.keys(dag, machine)

def rpb.when(+b: Bool, +m: Maybe<&2, String>, +r: Maybe<&2, String>) -> {Rp.when(b, m, r) == RefinePlan.rp_when(b, m, r) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rpb.rules(+v: Rp.Verb, +c: Rp.Comp, +id: Maybe<&2, String>, +cid: Maybe<&2, String>, +titled: Bool, +content: Bool, +m: Maybe<&2, Rp.Pyref>, +args: Maybe<&2, Rp.Args>) -> {Rp.rules(v, c, id, cid, titled, content, m, args) == RefinePlan.rp_rules(v, c, id, cid, titled, content, m, args) : Maybe<&2, String>}:
  %Equal.sym(Bool, Rp.is_comp(c, Rp.KPrompt{}), RefinePlan.rp_is_comp(c, Rp.KPrompt{}), rpb.is_comp(c, Rp.KPrompt{})) : {Rp.first(Bool.and(_, Bool.or(Rp.is_text(id, "base_system_prompt"), Rp.is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(Rp.is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([Rp.verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([Rp.verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Rp.is_comp(c, Rp.KSkill{})), Rp.skill(Rp.verb_name(v), args, m), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(id, "base_system_prompt"), rpb.is_text(id, "base_system_prompt")) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(_, Rp.is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(Rp.is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([Rp.verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([Rp.verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Rp.is_comp(c, Rp.KSkill{})), Rp.skill(Rp.verb_name(v), args, m), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.is_text(cid, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"), rpb.is_text(cid, "base_system_prompt")) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), _)), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(Rp.is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([Rp.verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([Rp.verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Rp.is_comp(c, Rp.KSkill{})), Rp.skill(Rp.verb_name(v), args, m), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.is_verb(v, Rp.ACreate{}), RefinePlan.rp_is_verb(v, Rp.ACreate{}), rpb.is_verb(v, Rp.ACreate{})) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(_), Maybe.is_none(&2, String, id)), String.concat([Rp.verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([Rp.verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Rp.is_comp(c, Rp.KSkill{})), Rp.skill(Rp.verb_name(v), args, m), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(String, Rp.verb_name(v), RefinePlan.rp_verb_name(v), rpb.verb_name(v)) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([_, " requires id"]), Rp.first(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([Rp.verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Rp.is_comp(c, Rp.KSkill{})), Rp.skill(Rp.verb_name(v), args, m), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.is_verb(v, Rp.ADelete{}), RefinePlan.rp_is_verb(v, Rp.ADelete{}), rpb.is_verb(v, Rp.ADelete{})) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(_), Bool.not(Bool.and(titled, content))), String.concat([Rp.verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Rp.is_comp(c, Rp.KSkill{})), Rp.skill(Rp.verb_name(v), args, m), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(String, Rp.verb_name(v), RefinePlan.rp_verb_name(v), rpb.verb_name(v)) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([_, " requires title and content"]), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Rp.is_comp(c, Rp.KSkill{})), Rp.skill(Rp.verb_name(v), args, m), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.is_verb(v, Rp.ADelete{}), RefinePlan.rp_is_verb(v, Rp.ADelete{}), rpb.is_verb(v, Rp.ADelete{})) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(_), Rp.is_comp(c, Rp.KSkill{})), Rp.skill(Rp.verb_name(v), args, m), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.is_comp(c, Rp.KSkill{}), RefinePlan.rp_is_comp(c, Rp.KSkill{}), rpb.is_comp(c, Rp.KSkill{})) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), _), Rp.skill(Rp.verb_name(v), args, m), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(String, Rp.verb_name(v), RefinePlan.rp_verb_name(v), rpb.verb_name(v)) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), Rp.skill(_, args, m), Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Maybe<&2, String>, Rp.skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), rpb.skill(RefinePlan.rp_verb_name(v), args, m)) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), _, Rp.when(Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.is_verb(v, Rp.ADelete{}), RefinePlan.rp_is_verb(v, Rp.ADelete{}), rpb.is_verb(v, Rp.ADelete{})) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), Rp.when(Bool.and(Bool.not(_), Bool.and(Rp.is_comp(c, Rp.KFactory{}), Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.is_comp(c, Rp.KFactory{}), RefinePlan.rp_is_comp(c, Rp.KFactory{}), rpb.is_comp(c, Rp.KFactory{})) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(_, Bool.or(Rp.is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Bool, Rp.is_verb(v, Rp.ACreate{}), RefinePlan.rp_is_verb(v, Rp.ACreate{}), rpb.is_verb(v, Rp.ACreate{})) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(_, Maybe.is_some(&2, Rp.Args, args)))), Rp.factory(args), None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Maybe<&2, String>, Rp.factory(args), RefinePlan.rp_factory(args), rpb.factory(args)) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), _, None{}))))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Maybe<&2, String>, Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}), rpb.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{})) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), _)))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Maybe<&2, String>, Rp.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{})), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{})), rpb.when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), _))) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Maybe<&2, String>, Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))), rpb.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{})))) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), _)) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  %Equal.sym(Maybe<&2, String>, Rp.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{})))), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{})))), rpb.first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : {Rp.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", _) == RefinePlan.rp_first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{}))))) : Maybe<&2, String>}
  rpb.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KPrompt{}), Bool.or(RefinePlan.rp_is_text(id, "base_system_prompt"), RefinePlan.rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([RefinePlan.rp_verb_name(v), " requires id"]), RefinePlan.rp_first(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(Bool.and(titled, content))), String.concat([RefinePlan.rp_verb_name(v), " requires title and content"]), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), RefinePlan.rp_is_comp(c, Rp.KSkill{})), RefinePlan.rp_skill(RefinePlan.rp_verb_name(v), args, m), RefinePlan.rp_when(Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.or(RefinePlan.rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), RefinePlan.rp_factory(args), None{})))))

def rpb.check.at(+v: Rp.Verb, +c: Rp.Comp, +r: Maybe<&2, String>) -> {Rp.check.at(v, c, r) == RefinePlan.rp_check.at(v, c, r) : Rp.Check}:
  match r:
    case None{}:
      {==}
    case Some{+msg}:
      {==}

def rpb.check.comp(+v: Rp.Verb, +m: Maybe<&2, Rp.Comp>, +id: Maybe<&2, String>, +cid: Maybe<&2, String>, +titled: Bool, +content: Bool, +p: Maybe<&2, Rp.Pyref>, +args: Maybe<&2, Rp.Args>) -> {Rp.check.comp(v, m, id, cid, titled, content, p, args) == RefinePlan.rp_check.comp(v, m, id, cid, titled, content, p, args) : Rp.Check}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      %Equal.sym(Maybe<&2, String>, Rp.rules(v, c, id, cid, titled, content, p, args), RefinePlan.rp_rules(v, c, id, cid, titled, content, p, args), rpb.rules(v, c, id, cid, titled, content, p, args)) : {Rp.check.at(v, c, _) == RefinePlan.rp_check.at(v, c, RefinePlan.rp_rules(v, c, id, cid, titled, content, p, args)) : Rp.Check}
      rpb.check.at(v, c, RefinePlan.rp_rules(v, c, id, cid, titled, content, p, args))

def rpb.check.verb(+m: Maybe<&2, Rp.Verb>, +k: Maybe<&2, Rp.Comp>, +id: Maybe<&2, String>, +cid: Maybe<&2, String>, +titled: Bool, +content: Bool, +p: Maybe<&2, Rp.Pyref>, +args: Maybe<&2, Rp.Args>) -> {Rp.check.verb(m, k, id, cid, titled, content, p, args) == RefinePlan.rp_check.verb(m, k, id, cid, titled, content, p, args) : Rp.Check}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      rpb.check.comp(v, k, id, cid, titled, content, p, args)

def rpb.check(+e: Rp.Ed, +cid: Maybe<&2, String>) -> {Rp.check(e, cid) == RefinePlan.rp_check(e, cid) : Rp.Check}:
  match e:
    case Rp.Ed{+verb, +comp, +id, +title, +content, +pyref, +args, +exists, +differs, +held}:
      rpb.check.verb(verb, comp, id, cid, Maybe.is_some(&2, String, title), content, pyref, args)

def rpb.lookup.at(+hit: Bool, +p: Bool, +r: Maybe<&2, Bool>) -> {Rp.lookup.at(hit, p, r) == RefinePlan.rp_lookup.at(hit, p, r) : Maybe<&2, Bool>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def rpb.lookup.touch(+t: Rp.Touch, +c: Rp.Comp, +id: String, +r: Maybe<&2, Bool>) -> {Rp.lookup.touch(t, c, id, r) == RefinePlan.rp_lookup.touch(t, c, id, r) : Maybe<&2, Bool>}:
  match t:
    case Rp.Touch{+tc, +tid, +p}:
      %Equal.sym(Bool, Rp.comp_eq(tc, c), RefinePlan.rp_comp_eq(tc, c), rpb.comp_eq(tc, c)) : {Rp.lookup.at(Bool.and(_, String.eq(tid, id)), p, r) == RefinePlan.rp_lookup.at(Bool.and(RefinePlan.rp_comp_eq(tc, c), String.eq(tid, id)), p, r) : Maybe<&2, Bool>}
      rpb.lookup.at(Bool.and(RefinePlan.rp_comp_eq(tc, c), String.eq(tid, id)), p, r)

def rpb.lookup(+ts: List<&2, Rp.Touch>, +c: Rp.Comp, +id: String) -> {Rp.lookup(ts, c, id) == RefinePlan.rp_lookup(ts, c, id) : Maybe<&2, Bool>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      %Equal.sym(Maybe<&2, Bool>, Rp.lookup(rest, c, id), RefinePlan.rp_lookup(rest, c, id), rpb.lookup(rest, c, id)) : {Rp.lookup.touch(t, c, id, _) == RefinePlan.rp_lookup.touch(t, c, id, RefinePlan.rp_lookup(rest, c, id)) : Maybe<&2, Bool>}
      rpb.lookup.touch(t, c, id, RefinePlan.rp_lookup(rest, c, id))

def rpb.out.first(+b: Bool, +msg: String, +r: Rp.Out) -> {Rp.out.first(b, msg, r) == RefinePlan.rp_out.first(b, msg, r) : Rp.Out}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rpb.out.final(+v: Rp.Verb, +p: Bool) -> {Rp.out.final(v, p) == RefinePlan.rp_out.final(v, p) : Rp.Out}:
  match v:
    case Rp.ACreate{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case Rp.AUpdate{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case Rp.ADelete{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}

def rpb.decide(+o: Rp.Opts, +e: Rp.Ed, +v: Rp.Verb, +c: Rp.Comp, +look: Maybe<&2, Bool>) -> {Rp.decide(o, e, v, c, look) == RefinePlan.rp_decide(o, e, v, c, look) : Rp.Out}:
  match o:
    case Rp.Opts{+factory, +baseline}:
      match e:
        case Rp.Ed{+verb, +comp, +id, +title, +content, +pyref, +args, +exists, +differs, +held}:
          %Equal.sym(Bool, Rp.is_comp(c, Rp.KFactory{}), RefinePlan.rp_is_comp(c, Rp.KFactory{}), rpb.is_comp(c, Rp.KFactory{})) : {Rp.out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", Rp.out.first(Bool.and(_, Bool.and(Bool.not(Rp.is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", Rp.out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", Rp.out.final(v, Maybe.default(&2, Bool, look, exists))))) == RefinePlan.rp_out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", RefinePlan.rp_out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", RefinePlan.rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists))))) : Rp.Out}
          %Equal.sym(Bool, Rp.is_verb(v, Rp.ADelete{}), RefinePlan.rp_is_verb(v, Rp.ADelete{}), rpb.is_verb(v, Rp.ADelete{})) : {Rp.out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", Rp.out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(_), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", Rp.out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", Rp.out.final(v, Maybe.default(&2, Bool, look, exists))))) == RefinePlan.rp_out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", RefinePlan.rp_out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", RefinePlan.rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists))))) : Rp.Out}
          %Equal.sym(Rp.Out, Rp.out.final(v, Maybe.default(&2, Bool, look, exists)), RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists)), rpb.out.final(v, Maybe.default(&2, Bool, look, exists))) : {Rp.out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", Rp.out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", Rp.out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", _))) == RefinePlan.rp_out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", RefinePlan.rp_out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", RefinePlan.rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists))))) : Rp.Out}
          %Equal.sym(Rp.Out, Rp.out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists))), RefinePlan.rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists))), rpb.out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists)))) : {Rp.out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", Rp.out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", _)) == RefinePlan.rp_out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", RefinePlan.rp_out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", RefinePlan.rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists))))) : Rp.Out}
          %Equal.sym(Rp.Out, Rp.out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", RefinePlan.rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists)))), RefinePlan.rp_out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", RefinePlan.rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists)))), rpb.out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", RefinePlan.rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists))))) : {Rp.out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", _) == RefinePlan.rp_out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", RefinePlan.rp_out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", RefinePlan.rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists))))) : Rp.Out}
          rpb.out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", RefinePlan.rp_out.first(Bool.and(RefinePlan.rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(RefinePlan.rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", RefinePlan.rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", RefinePlan.rp_out.final(v, Maybe.default(&2, Bool, look, exists)))))

def rpb.invalid_verb.at(+comp: Maybe<&2, Rp.Comp>, +verb: Maybe<&2, Rp.Verb>) -> {Rp.invalid_verb.at(comp, verb) == RefinePlan.rp_invalid_verb.at(comp, verb) : Rp.Verb}:
  match comp:
    case None{}:
      {==}
    case Some{+c}:
      match verb:
        case None{}:
          {==}
        case Some{+v}:
          {==}

def rpb.invalid_verb(+e: Rp.Ed) -> {Rp.invalid_verb(e) == RefinePlan.rp_invalid_verb(e) : Rp.Verb}:
  match e:
    case Rp.Ed{+verb, +comp, +id, +title, +content, +pyref, +args, +exists, +differs, +held}:
      rpb.invalid_verb.at(comp, verb)

def rpb.comp_of(+e: Rp.Ed) -> {Rp.comp_of(e) == RefinePlan.rp_comp_of(e) : Rp.Comp}:
  match e:
    case Rp.Ed{+verb, +comp, +id, +title, +content, +pyref, +args, +exists, +differs, +held}:
      rpb.comp_or_memory(comp)

def rpb.row.at(+o: Rp.Opts, +e: Rp.Ed, +ts: List<&2, Rp.Touch>, +id: String, +k: Rp.Check) -> {Rp.row.at(o, e, ts, id, k) == RefinePlan.rp_row.at(o, e, ts, id, k) : Rp.Row}:
  match k:
    case Rp.CBad{+msg}:
      %Equal.sym(Rp.Verb, Rp.invalid_verb(e), RefinePlan.rp_invalid_verb(e), rpb.invalid_verb(e)) : {Rp.Row{_, Rp.comp_of(e), id, Rp.OInvalid{msg}} == Rp.Row{RefinePlan.rp_invalid_verb(e), RefinePlan.rp_comp_of(e), id, Rp.OInvalid{msg}} : Rp.Row}
      %Equal.sym(Rp.Comp, Rp.comp_of(e), RefinePlan.rp_comp_of(e), rpb.comp_of(e)) : {Rp.Row{RefinePlan.rp_invalid_verb(e), _, id, Rp.OInvalid{msg}} == Rp.Row{RefinePlan.rp_invalid_verb(e), RefinePlan.rp_comp_of(e), id, Rp.OInvalid{msg}} : Rp.Row}
      {==}
    case Rp.COk{+v, +c}:
      %Equal.sym(Maybe<&2, Bool>, Rp.lookup(ts, c, id), RefinePlan.rp_lookup(ts, c, id), rpb.lookup(ts, c, id)) : {Rp.Row{v, c, id, Rp.decide(o, e, v, c, _)} == Rp.Row{v, c, id, RefinePlan.rp_decide(o, e, v, c, RefinePlan.rp_lookup(ts, c, id))} : Rp.Row}
      %Equal.sym(Rp.Out, Rp.decide(o, e, v, c, RefinePlan.rp_lookup(ts, c, id)), RefinePlan.rp_decide(o, e, v, c, RefinePlan.rp_lookup(ts, c, id)), rpb.decide(o, e, v, c, RefinePlan.rp_lookup(ts, c, id))) : {Rp.Row{v, c, id, _} == Rp.Row{v, c, id, RefinePlan.rp_decide(o, e, v, c, RefinePlan.rp_lookup(ts, c, id))} : Rp.Row}
      {==}

def rpb.row(+o: Rp.Opts, +e: Rp.Ed, +ts: List<&2, Rp.Touch>) -> {Rp.row(o, e, ts) == RefinePlan.rp_row(o, e, ts) : Rp.Row}:
  %Equal.sym(Maybe<&2, String>, Rp.computed(e), RefinePlan.rp_computed(e), rpb.computed(e)) : {Rp.row.at(o, e, ts, Maybe.default(&2, String, _, ""), Rp.check(e, Rp.computed(e))) == RefinePlan.rp_row.at(o, e, ts, Maybe.default(&2, String, RefinePlan.rp_computed(e), ""), RefinePlan.rp_check(e, RefinePlan.rp_computed(e))) : Rp.Row}
  %Equal.sym(Maybe<&2, String>, Rp.computed(e), RefinePlan.rp_computed(e), rpb.computed(e)) : {Rp.row.at(o, e, ts, Maybe.default(&2, String, RefinePlan.rp_computed(e), ""), Rp.check(e, _)) == RefinePlan.rp_row.at(o, e, ts, Maybe.default(&2, String, RefinePlan.rp_computed(e), ""), RefinePlan.rp_check(e, RefinePlan.rp_computed(e))) : Rp.Row}
  %Equal.sym(Rp.Check, Rp.check(e, RefinePlan.rp_computed(e)), RefinePlan.rp_check(e, RefinePlan.rp_computed(e)), rpb.check(e, RefinePlan.rp_computed(e))) : {Rp.row.at(o, e, ts, Maybe.default(&2, String, RefinePlan.rp_computed(e), ""), _) == RefinePlan.rp_row.at(o, e, ts, Maybe.default(&2, String, RefinePlan.rp_computed(e), ""), RefinePlan.rp_check(e, RefinePlan.rp_computed(e))) : Rp.Row}
  rpb.row.at(o, e, ts, Maybe.default(&2, String, RefinePlan.rp_computed(e), ""), RefinePlan.rp_check(e, RefinePlan.rp_computed(e)))

def rpb.touch.out(+x: Rp.Out, +c: Rp.Comp, +id: String, +ts: List<&2, Rp.Touch>) -> {Rp.touch.out(x, c, id, ts) == RefinePlan.rp_touch.out(x, c, id, ts) : List<&2, Rp.Touch>}:
  match x:
    case Rp.OInvalid{+m}:
      {==}
    case Rp.ORefused{+m}:
      {==}
    case Rp.ORemoved{}:
      {==}
    case Rp.OWritten{}:
      {==}

def rpb.touch(+r: Rp.Row, +ts: List<&2, Rp.Touch>) -> {Rp.touch(r, ts) == RefinePlan.rp_touch(r, ts) : List<&2, Rp.Touch>}:
  match r:
    case Rp.Row{+v, +c, +id, +x}:
      rpb.touch.out(x, c, id, ts)

def rpb.plan.rows(+o: Rp.Opts, +eds: List<&2, Rp.Ed>, +ts: List<&2, Rp.Touch>) -> {Rp.plan.rows(o, eds, ts) == RefinePlan.rp_plan.rows(o, eds, ts) : List<&2, Rp.Row>}:
  match eds:
    case Nil{}:
      {==}
    case +e <> +t:
      %Equal.sym(Rp.Row, Rp.row(o, e, ts), RefinePlan.rp_row(o, e, ts), rpb.row(o, e, ts)) : {_ <> Rp.plan.rows(o, t, Rp.touch(Rp.row(o, e, ts), ts)) == RefinePlan.rp_row(o, e, ts) <> RefinePlan.rp_plan.rows(o, t, RefinePlan.rp_touch(RefinePlan.rp_row(o, e, ts), ts)) : List<&2, Rp.Row>}
      %Equal.sym(Rp.Row, Rp.row(o, e, ts), RefinePlan.rp_row(o, e, ts), rpb.row(o, e, ts)) : {RefinePlan.rp_row(o, e, ts) <> Rp.plan.rows(o, t, Rp.touch(_, ts)) == RefinePlan.rp_row(o, e, ts) <> RefinePlan.rp_plan.rows(o, t, RefinePlan.rp_touch(RefinePlan.rp_row(o, e, ts), ts)) : List<&2, Rp.Row>}
      %Equal.sym(List<&2, Rp.Touch>, Rp.touch(RefinePlan.rp_row(o, e, ts), ts), RefinePlan.rp_touch(RefinePlan.rp_row(o, e, ts), ts), rpb.touch(RefinePlan.rp_row(o, e, ts), ts)) : {RefinePlan.rp_row(o, e, ts) <> Rp.plan.rows(o, t, _) == RefinePlan.rp_row(o, e, ts) <> RefinePlan.rp_plan.rows(o, t, RefinePlan.rp_touch(RefinePlan.rp_row(o, e, ts), ts)) : List<&2, Rp.Row>}
      %Equal.sym(List<&2, Rp.Row>, Rp.plan.rows(o, t, RefinePlan.rp_touch(RefinePlan.rp_row(o, e, ts), ts)), RefinePlan.rp_plan.rows(o, t, RefinePlan.rp_touch(RefinePlan.rp_row(o, e, ts), ts)), rpb.plan.rows(o, t, RefinePlan.rp_touch(RefinePlan.rp_row(o, e, ts), ts))) : {RefinePlan.rp_row(o, e, ts) <> _ == RefinePlan.rp_row(o, e, ts) <> RefinePlan.rp_plan.rows(o, t, RefinePlan.rp_touch(RefinePlan.rp_row(o, e, ts), ts)) : List<&2, Rp.Row>}
      {==}

def rpb.change.out(+x: Rp.Out, +v: Rp.Verb, +c: Rp.Comp, +id: String, +r: List<&2, String>) -> {Rp.change.out(x, v, c, id, r) == RefinePlan.rp_change.out(x, v, c, id, r) : List<&2, String>}:
  match x:
    case Rp.OInvalid{+m}:
      {==}
    case Rp.ORefused{+m}:
      {==}
    case Rp.ORemoved{}:
      %Equal.sym(String, Rp.verb_name(v), RefinePlan.rp_verb_name(v), rpb.verb_name(v)) : {String.concat([_, " ", Rp.comp_name(c), ":", id]) <> r == String.concat([RefinePlan.rp_verb_name(v), " ", RefinePlan.rp_comp_name(c), ":", id]) <> r : List<&2, String>}
      %Equal.sym(String, Rp.comp_name(c), RefinePlan.rp_comp_name(c), rpb.comp_name(c)) : {String.concat([RefinePlan.rp_verb_name(v), " ", _, ":", id]) <> r == String.concat([RefinePlan.rp_verb_name(v), " ", RefinePlan.rp_comp_name(c), ":", id]) <> r : List<&2, String>}
      {==}
    case Rp.OWritten{}:
      %Equal.sym(String, Rp.verb_name(v), RefinePlan.rp_verb_name(v), rpb.verb_name(v)) : {String.concat([_, " ", Rp.comp_name(c), ":", id]) <> r == String.concat([RefinePlan.rp_verb_name(v), " ", RefinePlan.rp_comp_name(c), ":", id]) <> r : List<&2, String>}
      %Equal.sym(String, Rp.comp_name(c), RefinePlan.rp_comp_name(c), rpb.comp_name(c)) : {String.concat([RefinePlan.rp_verb_name(v), " ", _, ":", id]) <> r == String.concat([RefinePlan.rp_verb_name(v), " ", RefinePlan.rp_comp_name(c), ":", id]) <> r : List<&2, String>}
      {==}

def rpb.change(+w: Rp.Row, +r: List<&2, String>) -> {Rp.change(w, r) == RefinePlan.rp_change(w, r) : List<&2, String>}:
  match w:
    case Rp.Row{+v, +c, +id, +x}:
      rpb.change.out(x, v, c, id, r)

def rpb.changes(+rows: List<&2, Rp.Row>) -> {Rp.changes(rows) == RefinePlan.rp_changes(rows) : List<&2, String>}:
  match rows:
    case Nil{}:
      {==}
    case +w <> +t:
      %Equal.sym(List<&2, String>, Rp.changes(t), RefinePlan.rp_changes(t), rpb.changes(t)) : {Rp.change(w, _) == RefinePlan.rp_change(w, RefinePlan.rp_changes(t)) : List<&2, String>}
      rpb.change(w, RefinePlan.rp_changes(t))

def rpb.plan(+o: Rp.Opts, +eds: List<&2, Rp.Ed>) -> {Rp.plan(o, eds) == RefinePlan.rp_plan(o, eds) : Rp.Plan}:
  %Equal.sym(List<&2, Rp.Row>, Rp.plan.rows(o, eds, []), RefinePlan.rp_plan.rows(o, eds, []), rpb.plan.rows(o, eds, [])) : {Rp.Plan{_, Rp.changes(Rp.plan.rows(o, eds, []))} == Rp.Plan{RefinePlan.rp_plan.rows(o, eds, []), RefinePlan.rp_changes(RefinePlan.rp_plan.rows(o, eds, []))} : Rp.Plan}
  %Equal.sym(List<&2, Rp.Row>, Rp.plan.rows(o, eds, []), RefinePlan.rp_plan.rows(o, eds, []), rpb.plan.rows(o, eds, [])) : {Rp.Plan{RefinePlan.rp_plan.rows(o, eds, []), Rp.changes(_)} == Rp.Plan{RefinePlan.rp_plan.rows(o, eds, []), RefinePlan.rp_changes(RefinePlan.rp_plan.rows(o, eds, []))} : Rp.Plan}
  %Equal.sym(List<&2, String>, Rp.changes(RefinePlan.rp_plan.rows(o, eds, [])), RefinePlan.rp_changes(RefinePlan.rp_plan.rows(o, eds, [])), rpb.changes(RefinePlan.rp_plan.rows(o, eds, []))) : {Rp.Plan{RefinePlan.rp_plan.rows(o, eds, []), _} == Rp.Plan{RefinePlan.rp_plan.rows(o, eds, []), RefinePlan.rp_changes(RefinePlan.rp_plan.rows(o, eds, []))} : Rp.Plan}
  {==}

def rpb.back.restore(+after: Bool) -> {Rp.back.restore(after) == RefinePlan.rp_back.restore(after) : Rp.Verb}:
  match after:
    case True{}:
      {==}
    case False{}:
      {==}

def rpb.back.pick.at(+applied: Bool, +before: Bool, +after: Bool, +at: Nat) -> {Rp.back.pick.at(applied, before, after, at) == RefinePlan.rp_back.pick.at(applied, before, after, at) : List<&2, Rp.Pick>}:
  match applied:
    case False{}:
      {==}
    case True{}:
      match before:
        case True{}:
          %Equal.sym(Rp.Verb, Rp.back.restore(after), RefinePlan.rp_back.restore(after), rpb.back.restore(after)) : {[Rp.Pick{at, _}] == [Rp.Pick{at, RefinePlan.rp_back.restore(after)}] : List<&2, Rp.Pick>}
          {==}
        case False{}:
          match after:
            case True{}:
              {==}
            case False{}:
              {==}

def rpb.back.pick(+w: Rp.Was, +at: Nat) -> {Rp.back.pick(w, at) == RefinePlan.rp_back.pick(w, at) : List<&2, Rp.Pick>}:
  match w:
    case Rp.Was{+applied, +before, +after}:
      rpb.back.pick.at(applied, before, after, at)

def rpb.back.fwd(+was: List<&2, Rp.Was>, +at: Nat) -> {Rp.back.fwd(was, at) == RefinePlan.rp_back.fwd(was, at) : List<&2, Rp.Pick>}:
  match was:
    case Nil{}:
      {==}
    case +w <> +t:
      %Equal.sym(List<&2, Rp.Pick>, Rp.back.pick(w, at), RefinePlan.rp_back.pick(w, at), rpb.back.pick(w, at)) : {List.append(&2, Rp.Pick, _, Rp.back.fwd(t, 1n+at)) == List.append(&2, Rp.Pick, RefinePlan.rp_back.pick(w, at), RefinePlan.rp_back.fwd(t, 1n+at)) : List<&2, Rp.Pick>}
      %Equal.sym(List<&2, Rp.Pick>, Rp.back.fwd(t, 1n+at), RefinePlan.rp_back.fwd(t, 1n+at), rpb.back.fwd(t, 1n+at)) : {List.append(&2, Rp.Pick, RefinePlan.rp_back.pick(w, at), _) == List.append(&2, Rp.Pick, RefinePlan.rp_back.pick(w, at), RefinePlan.rp_back.fwd(t, 1n+at)) : List<&2, Rp.Pick>}
      {==}

def rpb.back(+id: String, +was: List<&2, Rp.Was>) -> {Rp.back(id, was) == RefinePlan.rp_back(id, was) : Rp.Back}:
  %Equal.sym(List<&2, Rp.Pick>, Rp.back.fwd(was, 0n), RefinePlan.rp_back.fwd(was, 0n), rpb.back.fwd(was, 0n)) : {Rp.Back{String.concat(["Rollback refinement ", id]), String.concat(["Restores continual harness state snapshots from refinement ", id, "."]), "Faulty refinement edits are reverted.", String.concat(["Rollback ", id]), List.reverse(&2, Rp.Pick, _)} == Rp.Back{String.concat(["Rollback refinement ", id]), String.concat(["Restores continual harness state snapshots from refinement ", id, "."]), "Faulty refinement edits are reverted.", String.concat(["Rollback ", id]), List.reverse(&2, Rp.Pick, RefinePlan.rp_back.fwd(was, 0n))} : Rp.Back}
  {==}

def rpb.norm(+s: Maybe<&2, String>, +r: Maybe<&2, String>, +o: Maybe<&2, String>) -> {Rp.norm(s, r, o) == RefinePlan.rp_norm(s, r, o) : Rp.Texts}:
  {==}

def rpb.scan.code(+c: Char, +x: U32) -> {Rp.scan.code(c, x) == RefinePlan.rp_scan.code(c, x) : Bool}:
  {==}

def rpb.scan.out(+ins: Bool, +bs: Bool, +q: Bool, +op: Bool, +cl: Bool, +o: Nat, +k: Nat) -> {Rp.scan.out(ins, bs, q, op, cl, o, k) == RefinePlan.rp_scan.out(ins, bs, q, op, cl, o, k) : Rp.Scan}:
  match ins:
    case True{}:
      match bs:
        case True{}:
          {==}
        case False{}:
          match q:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match q:
        case True{}:
          {==}
        case False{}:
          match op:
            case True{}:
              {==}
            case False{}:
              match cl:
                case True{}:
                  {==}
                case False{}:
                  {==}

def rpb.scan.at(+esc: Bool, +ins: Bool, +c: Char, +o: Nat, +k: Nat) -> {Rp.scan.at(esc, ins, c, o, k) == RefinePlan.rp_scan.at(esc, ins, c, o, k) : Rp.Scan}:
  match esc:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Rp.scan.code(c, 92), RefinePlan.rp_scan.code(c, 92), rpb.scan.code(c, 92)) : {Rp.scan.out(ins, _, Rp.scan.code(c, 34), Bool.or(Rp.scan.code(c, 123), Rp.scan.code(c, 91)), Bool.or(Rp.scan.code(c, 125), Rp.scan.code(c, 93)), o, k) == RefinePlan.rp_scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(RefinePlan.rp_scan.code(c, 123), RefinePlan.rp_scan.code(c, 91)), Bool.or(RefinePlan.rp_scan.code(c, 125), RefinePlan.rp_scan.code(c, 93)), o, k) : Rp.Scan}
      %Equal.sym(Bool, Rp.scan.code(c, 34), RefinePlan.rp_scan.code(c, 34), rpb.scan.code(c, 34)) : {Rp.scan.out(ins, RefinePlan.rp_scan.code(c, 92), _, Bool.or(Rp.scan.code(c, 123), Rp.scan.code(c, 91)), Bool.or(Rp.scan.code(c, 125), Rp.scan.code(c, 93)), o, k) == RefinePlan.rp_scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(RefinePlan.rp_scan.code(c, 123), RefinePlan.rp_scan.code(c, 91)), Bool.or(RefinePlan.rp_scan.code(c, 125), RefinePlan.rp_scan.code(c, 93)), o, k) : Rp.Scan}
      %Equal.sym(Bool, Rp.scan.code(c, 123), RefinePlan.rp_scan.code(c, 123), rpb.scan.code(c, 123)) : {Rp.scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(_, Rp.scan.code(c, 91)), Bool.or(Rp.scan.code(c, 125), Rp.scan.code(c, 93)), o, k) == RefinePlan.rp_scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(RefinePlan.rp_scan.code(c, 123), RefinePlan.rp_scan.code(c, 91)), Bool.or(RefinePlan.rp_scan.code(c, 125), RefinePlan.rp_scan.code(c, 93)), o, k) : Rp.Scan}
      %Equal.sym(Bool, Rp.scan.code(c, 91), RefinePlan.rp_scan.code(c, 91), rpb.scan.code(c, 91)) : {Rp.scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(RefinePlan.rp_scan.code(c, 123), _), Bool.or(Rp.scan.code(c, 125), Rp.scan.code(c, 93)), o, k) == RefinePlan.rp_scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(RefinePlan.rp_scan.code(c, 123), RefinePlan.rp_scan.code(c, 91)), Bool.or(RefinePlan.rp_scan.code(c, 125), RefinePlan.rp_scan.code(c, 93)), o, k) : Rp.Scan}
      %Equal.sym(Bool, Rp.scan.code(c, 125), RefinePlan.rp_scan.code(c, 125), rpb.scan.code(c, 125)) : {Rp.scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(RefinePlan.rp_scan.code(c, 123), RefinePlan.rp_scan.code(c, 91)), Bool.or(_, Rp.scan.code(c, 93)), o, k) == RefinePlan.rp_scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(RefinePlan.rp_scan.code(c, 123), RefinePlan.rp_scan.code(c, 91)), Bool.or(RefinePlan.rp_scan.code(c, 125), RefinePlan.rp_scan.code(c, 93)), o, k) : Rp.Scan}
      %Equal.sym(Bool, Rp.scan.code(c, 93), RefinePlan.rp_scan.code(c, 93), rpb.scan.code(c, 93)) : {Rp.scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(RefinePlan.rp_scan.code(c, 123), RefinePlan.rp_scan.code(c, 91)), Bool.or(RefinePlan.rp_scan.code(c, 125), _), o, k) == RefinePlan.rp_scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(RefinePlan.rp_scan.code(c, 123), RefinePlan.rp_scan.code(c, 91)), Bool.or(RefinePlan.rp_scan.code(c, 125), RefinePlan.rp_scan.code(c, 93)), o, k) : Rp.Scan}
      rpb.scan.out(ins, RefinePlan.rp_scan.code(c, 92), RefinePlan.rp_scan.code(c, 34), Bool.or(RefinePlan.rp_scan.code(c, 123), RefinePlan.rp_scan.code(c, 91)), Bool.or(RefinePlan.rp_scan.code(c, 125), RefinePlan.rp_scan.code(c, 93)), o, k)

def rpb.scan.step(+st: Rp.Scan, +c: Char) -> {Rp.scan.step(st, c) == RefinePlan.rp_scan.step(st, c) : Rp.Scan}:
  match st:
    case Rp.Scan{+ins, +esc, +o, +k}:
      rpb.scan.at(esc, ins, c, o, k)

def rpb.scan(+s: String, +st: Rp.Scan) -> {Rp.scan(s, st) == RefinePlan.rp_scan(s, st) : Rp.Scan}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Rp.Scan, Rp.scan.step(st, c), RefinePlan.rp_scan.step(st, c), rpb.scan.step(st, c)) : {Rp.scan(t, _) == RefinePlan.rp_scan(t, RefinePlan.rp_scan.step(st, c)) : Rp.Scan}
      rpb.scan(t, RefinePlan.rp_scan.step(st, c))

def rpb.scan.done(+st: Rp.Scan) -> {Rp.scan.done(st) == RefinePlan.rp_scan.done(st) : Bool}:
  match st:
    case Rp.Scan{+ins, +esc, +o, +k}:
      {==}

def rpb.incomplete(+text: String) -> {Rp.incomplete(text) == RefinePlan.rp_incomplete(text) : Bool}:
  %Equal.sym(Rp.Scan, Rp.scan(text, Rp.Scan{False{}, False{}, 0n, 0n}), RefinePlan.rp_scan(text, Rp.Scan{False{}, False{}, 0n, 0n}), rpb.scan(text, Rp.Scan{False{}, False{}, 0n, 0n})) : {Rp.scan.done(_) == RefinePlan.rp_scan.done(RefinePlan.rp_scan(text, Rp.Scan{False{}, False{}, 0n, 0n})) : Bool}
  rpb.scan.done(RefinePlan.rp_scan(text, Rp.Scan{False{}, False{}, 0n, 0n}))

def rpb.fit.room.at(+z: Bool, +m: Nat) -> {Rp.fit.room.at(z, m) == RefinePlan.rp_fit.room.at(z, m) : Rp.Step}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def rpb.fit.room(+m: Nat) -> {Rp.fit.room(m) == RefinePlan.rp_fit.room(m) : Rp.Step}:
  rpb.fit.room.at(Nat.is_eq(m, 0n), m)

def rpb.fit.probe.at(+b: Bool, +low: Nat, +high: Nat) -> {Rp.fit.probe.at(b, low, high) == RefinePlan.rp_fit.probe.at(b, low, high) : Rp.Step}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rpb.fit.probe(+low: Nat, +high: Nat) -> {Rp.fit.probe(low, high) == RefinePlan.rp_fit.probe(low, high) : Rp.Step}:
  rpb.fit.probe.at(Nat.is_lt(low, high), low, high)

def rpb.fit.full(+trim: Bool, +conv: Nat, +r: Rp.Step) -> {Rp.fit.full(trim, conv, r) == RefinePlan.rp_fit.full(trim, conv, r) : Rp.Step}:
  match trim:
    case True{}:
      rpb.fit.probe(0n, conv)
    case False{}:
      {==}

def rpb.fit.narrow(+fits: Bool, +low: Nat, +high: Nat, +len: Nat) -> {Rp.fit.narrow(fits, low, high, len) == RefinePlan.rp_fit.narrow(fits, low, high, len) : Rp.Step}:
  match fits:
    case True{}:
      rpb.fit.probe(len, high)
    case False{}:
      rpb.fit.probe(low, Nat.sub(len, 1n))

def rpb.fit.at(+st: Rp.Search, +conv: Nat, +plen: Nat, +sysr: Nat, +budget: Nat, +mx: Nat, +cw: Nat) -> {Rp.fit.at(st, conv, plen, sysr, budget, mx, cw) == RefinePlan.rp_fit.at(st, conv, plen, sysr, budget, mx, cw) : Rp.Step}:
  match st:
    case Rp.SFull{}:
      %Equal.sym(Rp.Step, Rp.fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(sysr, plen)))), RefinePlan.rp_fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(sysr, plen)))), rpb.fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(sysr, plen))))) : {Rp.fit.full(Bool.and(Bool.not(Nat.is_le(Nat.add(sysr, plen), budget)), Bool.not(Nat.is_eq(conv, 0n))), conv, _) == RefinePlan.rp_fit.full(Bool.and(Bool.not(Nat.is_le(Nat.add(sysr, plen), budget)), Bool.not(Nat.is_eq(conv, 0n))), conv, RefinePlan.rp_fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(sysr, plen))))) : Rp.Step}
      rpb.fit.full(Bool.and(Bool.not(Nat.is_le(Nat.add(sysr, plen), budget)), Bool.not(Nat.is_eq(conv, 0n))), conv, RefinePlan.rp_fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(sysr, plen)))))
    case Rp.SProbe{+low, +high, +len}:
      rpb.fit.narrow(Nat.is_le(Nat.add(sysr, plen), budget), low, high, len)
    case Rp.SFinal{}:
      rpb.fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(sysr, plen))))

def rpb.fit(+w: Rp.Win, +conv: Nat, +st: Rp.Search, +plen: Nat) -> {Rp.fit(w, conv, st, plen) == RefinePlan.rp_fit(w, conv, st, plen) : Rp.Step}:
  match w:
    case Rp.Win{+cw, +mx, +res, +sys}:
      rpb.fit.at(st, conv, plen, Nat.add(sys, 1024n), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n))), mx, cw)
