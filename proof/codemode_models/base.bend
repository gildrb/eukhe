# eukhe: lemmas of the proofs of area codemode_models: each helper of the
# model equals its spec helper
#
# A value's text: the model's loop over an object's keys is the spec's
# first six keys joined, then `...` when a seventh is left (cm.more). The
# checks: the model's `first(unless(ok, p), rest)` chains are the spec's
# `or_else` chains (cm.fu, cm.ft), kind by kind (cm.obj, cm.str, ...), list
# by list (cm.bad_image, cm.bad_block, cm.questions).

import Base
import ../../bend/codemode_models.bend as Mod
import ../../laws/codemode_models/checks.bend as CodemodeModels

# ---- strings and Bools ----

def cm.app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), cm.app_assoc(t, b, c))

def cm.and2(-a: Bool, -b: Bool, -c: Bool, -d: Bool, e1: {a == b : Bool}, e2: {c == d : Bool}) -> {Bool.and(a, c) == Bool.and(b, d) : Bool}:
  %e1 : {Bool.and(a, c) == Bool.and(_, d) : Bool}
  %e2 : {Bool.and(a, c) == Bool.and(a, _) : Bool}
  {==}

def cm.or2(-a: Bool, -b: Bool, -c: Bool, -d: Bool, e1: {a == b : Bool}, e2: {c == d : Bool}) -> {Bool.or(a, c) == Bool.or(b, d) : Bool}:
  %e1 : {Bool.or(a, c) == Bool.or(_, d) : Bool}
  %e2 : {Bool.or(a, c) == Bool.or(a, _) : Bool}
  {==}

# ---- a value's text ----

# after the first key h, the keys r with n more allowed: the spec's joined
# first keys, then `...` when one is left over
def cm.more(r: List<&2, String>, n: Nat, +h: String) -> {String.append(h, Mod.obj_more(r, n)) == String.concat([String.join.go(List.take(&2, String, r, n), h, ", "), CodemodeModels.more_spec(Bool.not(List.is_empty(&2, String, List.drop(&2, String, r, n)))), " }"]) : String}:
  match r:
    case Nil{}:
      {==}
    case Con{+k, +t}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          +J = String.join.go(List.take(&2, String, t, m), k, ", ")
          +X = String.append(CodemodeModels.more_spec(Bool.not(List.is_empty(&2, String, List.drop(&2, String, t, m)))), String.append(" }", ""))
          %Equal.sym(String, String.append(k, Mod.obj_more(t, m)), String.concat([J, CodemodeModels.more_spec(Bool.not(List.is_empty(&2, String, List.drop(&2, String, t, m)))), " }"]), cm.more(t, m, k)) : {String.append(h, String.append(", ", _)) == String.append(String.append(h, String.append(", ", J)), X) : String}
          Equal.sym(String, String.append(String.append(h, String.append(", ", J)), X), String.append(h, String.append(String.append(", ", J), X)), cm.app_assoc(h, String.append(", ", J), X))

def cm.desc(d: Mod.Desc) -> {Mod.describe(d) == CodemodeModels.desc_spec(d) : String}:
  match d:
    case Mod.DUndef{}:
      {==}
    case Mod.DNull{}:
      {==}
    case Mod.DBool{}:
      {==}
    case Mod.DNum{}:
      {==}
    case Mod.DStr{}:
      {==}
    case Mod.DArr{e}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}
    case Mod.DObj{ks}:
      match ks:
        case Nil{}:
          {==}
        case Con{+k, +r}:
          Equal.cong(String, String, x => String.append("{ ", x), String.append(k, Mod.obj_more(r, 5n)), String.concat([String.join.go(List.take(&2, String, r, 5n), k, ", "), CodemodeModels.more_spec(Bool.not(List.is_empty(&2, String, List.drop(&2, String, r, 5n)))), " }"]), cm.more(r, 5n, k))

def cm.art_of(b: Bool) -> {Mod.article.of(b) == CodemodeModels.sel_str(b, "an ", "a ") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cm.article(+w: String) -> {Mod.article(w) == CodemodeModels.article_spec(w) : String}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      Equal.cong(String, String, x => String.append(x, SCon{c, r}), Mod.article.of(Mod.vowel(c)), CodemodeModels.sel_str(Mod.vowel(c), "an ", "a "), cm.art_of(Mod.vowel(c)))

def cm.got(w: String, d: Mod.Desc) -> {Mod.got(w, d) == CodemodeModels.got_spec(w, d) : String}:
  Equal.cong(String, String, x => String.concat([w, ", got ", x]), Mod.describe(d), CodemodeModels.desc_spec(d), cm.desc(d))

# ---- kinds ----

def cm.obj(d: Mod.Desc) -> {Mod.is_obj(d) == CodemodeModels.kind_obj(d) : Bool}:
  match d:
    case Mod.DUndef{}:
      {==}
    case Mod.DNull{}:
      {==}
    case Mod.DBool{}:
      {==}
    case Mod.DNum{}:
      {==}
    case Mod.DStr{}:
      {==}
    case Mod.DArr{e}:
      {==}
    case Mod.DObj{ks}:
      {==}

def cm.str(d: Mod.Desc) -> {Mod.is_str(d) == CodemodeModels.kind_str(d) : Bool}:
  match d:
    case Mod.DUndef{}:
      {==}
    case Mod.DNull{}:
      {==}
    case Mod.DBool{}:
      {==}
    case Mod.DNum{}:
      {==}
    case Mod.DStr{}:
      {==}
    case Mod.DArr{e}:
      {==}
    case Mod.DObj{ks}:
      {==}

def cm.arr(d: Mod.Desc) -> {Mod.is_arr(d) == CodemodeModels.kind_arr(d) : Bool}:
  match d:
    case Mod.DUndef{}:
      {==}
    case Mod.DNull{}:
      {==}
    case Mod.DBool{}:
      {==}
    case Mod.DNum{}:
      {==}
    case Mod.DStr{}:
      {==}
    case Mod.DArr{e}:
      {==}
    case Mod.DObj{ks}:
      {==}

def cm.none(d: Mod.Desc) -> {Mod.is_none(d) == CodemodeModels.kind_none(d) : Bool}:
  match d:
    case Mod.DUndef{}:
      {==}
    case Mod.DNull{}:
      {==}
    case Mod.DBool{}:
      {==}
    case Mod.DNum{}:
      {==}
    case Mod.DStr{}:
      {==}
    case Mod.DArr{e}:
      {==}
    case Mod.DObj{ks}:
      {==}

def cm.map(d: Mod.Desc) -> {Mod.is_map(d) == CodemodeModels.map_spec(d) : Bool}:
  match d:
    case Mod.DUndef{}:
      {==}
    case Mod.DNull{}:
      {==}
    case Mod.DBool{}:
      {==}
    case Mod.DNum{}:
      {==}
    case Mod.DStr{}:
      {==}
    case Mod.DArr{e}:
      {==}
    case Mod.DObj{ks}:
      {==}

def cm.full(d: Mod.Desc) -> {Mod.is_full(d) == CodemodeModels.full_spec(d) : Bool}:
  match d:
    case Mod.DUndef{}:
      {==}
    case Mod.DNull{}:
      {==}
    case Mod.DBool{}:
      {==}
    case Mod.DNum{}:
      {==}
    case Mod.DStr{}:
      {==}
    case Mod.DArr{e}:
      {==}
    case Mod.DObj{ks}:
      {==}

def cm.txt(t: Mod.Txt, +w: String) -> {Mod.txt_is(t, w) == CodemodeModels.txt_eq(t, w) : Bool}:
  match t:
    case Mod.NoTxt{}:
      {==}
    case Mod.Txt{s}:
      {==}

def cm.every(ds: List<&2, Mod.Desc>) -> {Mod.every_str(ds) == CodemodeModels.strs_spec(ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      cm.and2(Mod.is_str(d), CodemodeModels.kind_str(d), Mod.every_str(r), CodemodeModels.strs_spec(r), cm.str(d), cm.every(r))

def cm.all(ds: List<&2, Mod.Desc>) -> {Mod.all_strs(ds) == Bool.and(CodemodeModels.some_spec(ds), CodemodeModels.strs_spec(ds)) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      cm.and2(Mod.is_str(d), CodemodeModels.kind_str(d), Mod.every_str(r), CodemodeModels.strs_spec(r), cm.str(d), cm.every(r))

def cm.image(b: Mod.Blk) -> {Mod.is_image(b) == CodemodeModels.image_spec(b) : Bool}:
  match b:
    case Mod.Blk{+k, +t, x, +d, +m}:
      cm.and2(Mod.is_obj(k), CodemodeModels.kind_obj(k), Bool.and(Mod.txt_is(t, "image"), Bool.and(Mod.is_str(d), Mod.is_str(m))), Bool.and(CodemodeModels.txt_eq(t, "image"), Bool.and(CodemodeModels.kind_str(d), CodemodeModels.kind_str(m))), cm.obj(k), cm.and2(Mod.txt_is(t, "image"), CodemodeModels.txt_eq(t, "image"), Bool.and(Mod.is_str(d), Mod.is_str(m)), Bool.and(CodemodeModels.kind_str(d), CodemodeModels.kind_str(m)), cm.txt(t, "image"), cm.and2(Mod.is_str(d), CodemodeModels.kind_str(d), Mod.is_str(m), CodemodeModels.kind_str(m), cm.str(d), cm.str(m))))

def cm.text(b: Mod.Blk) -> {Mod.is_text(b) == CodemodeModels.text_spec(b) : Bool}:
  match b:
    case Mod.Blk{+k, +t, +x, d, m}:
      cm.and2(Mod.is_obj(k), CodemodeModels.kind_obj(k), Bool.and(Mod.txt_is(t, "text"), Mod.is_str(x)), Bool.and(CodemodeModels.txt_eq(t, "text"), CodemodeModels.kind_str(x)), cm.obj(k), cm.and2(Mod.txt_is(t, "text"), CodemodeModels.txt_eq(t, "text"), Mod.is_str(x), CodemodeModels.kind_str(x), cm.txt(t, "text"), cm.str(x)))

def cm.gotb(w: String, b: Mod.Blk) -> {Mod.got(w, Mod.blk_desc(b)) == CodemodeModels.got_spec(w, CodemodeModels.blk_of(b)) : String}:
  match b:
    case Mod.Blk{k, t, x, d, m}:
      cm.got(w, k)

# ---- problem chains ----

def cm.fu.go(ok: Bool, -p1: String, -p2: String, -r1: Maybe<&2, String>, -r2: Maybe<&2, String>, ep: {p1 == p2 : String}, er: {r1 == r2 : Maybe<&2, String>}) -> {Mod.first(Mod.unless(ok, p1), r1) == CodemodeModels.or_else(ok, p2, r2) : Maybe<&2, String>}:
  match ok:
    case True{}:
      er
    case False{}:
      Equal.cong(String, Maybe<&2, String>, x => Some{x}, p1, p2, ep)

# a model check is the spec's when its parts are
def cm.fu(ok1: Bool, -ok2: Bool, -p1: String, -p2: String, -r1: Maybe<&2, String>, -r2: Maybe<&2, String>, eo: {ok1 == ok2 : Bool}, ep: {p1 == p2 : String}, er: {r1 == r2 : Maybe<&2, String>}) -> {Mod.first(Mod.unless(ok1, p1), r1) == CodemodeModels.or_else(ok2, p2, r2) : Maybe<&2, String>}:
  %eo : {Mod.first(Mod.unless(ok1, p1), r1) == CodemodeModels.or_else(_, p2, r2) : Maybe<&2, String>}
  cm.fu.go(ok1, p1, p2, r1, r2, ep, er)

def cm.ft.go(a: Maybe<&2, String>, -r1: Maybe<&2, String>, -r2: Maybe<&2, String>, er: {r1 == r2 : Maybe<&2, String>}) -> {Mod.first(a, r1) == CodemodeModels.then_spec(a, r2) : Maybe<&2, String>}:
  match a:
    case None{}:
      er
    case Some{p}:
      {==}

# a problem, else the rest's, is the spec's when its parts are
def cm.ft(a1: Maybe<&2, String>, -a2: Maybe<&2, String>, -r1: Maybe<&2, String>, -r2: Maybe<&2, String>, ea: {a1 == a2 : Maybe<&2, String>}, er: {r1 == r2 : Maybe<&2, String>}) -> {Mod.first(a1, r1) == CodemodeModels.then_spec(a2, r2) : Maybe<&2, String>}:
  %ea : {Mod.first(a1, r1) == CodemodeModels.then_spec(_, r2) : Maybe<&2, String>}
  cm.ft.go(a1, r1, r2, er)

def cm.unless(ok: Bool, p: String) -> {Mod.unless(ok, p) == CodemodeModels.or_else(ok, p, None{}) : Maybe<&2, String>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def cm.unless_eq(a: Bool, -b: Bool, p: String, e: {a == b : Bool}) -> {Mod.unless(a, p) == CodemodeModels.or_else(b, p, None{}) : Maybe<&2, String>}:
  %e : {Mod.unless(a, p) == CodemodeModels.or_else(_, p, None{}) : Maybe<&2, String>}
  cm.unless(a, p)

def cm.wrap.go(+h: String, +t: String, p: Maybe<&2, String>) -> {Mod.wrap(h, t, p) == CodemodeModels.wrap_spec(h, t, p) : Maybe<&2, String>}:
  match p:
    case None{}:
      {==}
    case Some{x}:
      {==}

def cm.wrap(+h: String, +t: String, p1: Maybe<&2, String>, -p2: Maybe<&2, String>, e: {p1 == p2 : Maybe<&2, String>}) -> {Mod.wrap(h, t, p1) == CodemodeModels.wrap_spec(h, t, p2) : Maybe<&2, String>}:
  %e : {Mod.wrap(h, t, p1) == CodemodeModels.wrap_spec(h, t, _) : Maybe<&2, String>}
  cm.wrap.go(h, t, p1)

# ---- the lists ----

def cm.bad_image(bs: List<&2, Mod.Blk>, +i: Nat) -> {Mod.bad_image(bs, i) == CodemodeModels.images_spec(bs, i) : Maybe<&2, String>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      +w = String.concat(["context.images[", Nat.show(i), "] must be an image block"])
      cm.fu(Mod.is_image(b), CodemodeModels.image_spec(b), Mod.got(w, Mod.blk_desc(b)), CodemodeModels.got_spec(w, CodemodeModels.blk_of(b)), Mod.bad_image(r, 1n+i), CodemodeModels.images_spec(r, 1n+i), cm.image(b), cm.gotb(w, b), cm.bad_image(r, 1n+i))

def cm.bad_block(bs: List<&2, Mod.Blk>, +i: Nat) -> {Mod.bad_block(bs, i) == CodemodeModels.blocks_spec(bs, i) : Maybe<&2, String>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      +w = String.concat(["context.input[", Nat.show(i), "] must be a text or image block"])
      cm.fu(Bool.or(Mod.is_text(b), Mod.is_image(b)), Bool.or(CodemodeModels.text_spec(b), CodemodeModels.image_spec(b)), Mod.got(w, Mod.blk_desc(b)), CodemodeModels.got_spec(w, CodemodeModels.blk_of(b)), Mod.bad_block(r, 1n+i), CodemodeModels.blocks_spec(r, 1n+i), cm.or2(Mod.is_text(b), CodemodeModels.text_spec(b), Mod.is_image(b), CodemodeModels.image_spec(b), cm.text(b), cm.image(b)), cm.gotb(w, b), cm.bad_block(r, 1n+i))

def cm.images_check(d: Mod.Desc, bs: List<&2, Mod.Blk>) -> {Mod.images_check(d, bs) == CodemodeModels.images_part(d, bs) : Maybe<&2, String>}:
  match d:
    case Mod.DUndef{}:
      {==}
    case Mod.DNull{}:
      {==}
    case Mod.DBool{}:
      {==}
    case Mod.DNum{}:
      {==}
    case Mod.DStr{}:
      {==}
    case Mod.DObj{+ks}:
      Equal.cong(String, Maybe<&2, String>, x => Some{x}, Mod.got("context.images must be an array", Mod.DObj{ks}), CodemodeModels.got_spec("context.images must be an array", Mod.DObj{ks}), cm.got("context.images must be an array", Mod.DObj{ks}))
    case Mod.DArr{e}:
      cm.bad_image(bs, 0n)

def cm.crit_of(b1: Bool, b2: Bool, b3: Bool, +at: String, json: String, +c: Mod.Desc, +vs: List<&2, Mod.Desc>, +yes: Mod.Desc, +no: Mod.Desc) -> {Mod.criteria_of(b1, b2, b3, at, json, c, vs, yes, no) == CodemodeModels.criteria_spec(at, CodemodeModels.qt_of(b1, b2, b3), json, c, vs, yes, no) : Maybe<&2, String>}:
  match b1:
    case True{}:
      cm.unless_eq(Bool.and(Mod.is_obj(c), Mod.all_strs(vs)), Bool.and(CodemodeModels.kind_obj(c), Bool.and(CodemodeModels.some_spec(vs), CodemodeModels.strs_spec(vs))), String.append(at, " is a \"choice\" question, so criteria must map each label to its meaning"), cm.and2(Mod.is_obj(c), CodemodeModels.kind_obj(c), Mod.all_strs(vs), Bool.and(CodemodeModels.some_spec(vs), CodemodeModels.strs_spec(vs)), cm.obj(c), cm.all(vs)))
    case False{}:
      match b2:
        case True{}:
          cm.unless_eq(Bool.and(Mod.is_arr(c), Mod.all_strs(vs)), Bool.and(CodemodeModels.kind_arr(c), Bool.and(CodemodeModels.some_spec(vs), CodemodeModels.strs_spec(vs))), String.append(at, " is a \"score\" question, so criteria must list the levels as strings, lowest first"), cm.and2(Mod.is_arr(c), CodemodeModels.kind_arr(c), Mod.all_strs(vs), Bool.and(CodemodeModels.some_spec(vs), CodemodeModels.strs_spec(vs)), cm.arr(c), cm.all(vs)))
        case False{}:
          match b3:
            case True{}:
              cm.unless_eq(Bool.and(Mod.is_obj(c), Bool.and(Mod.is_str(yes), Mod.is_str(no))), Bool.and(CodemodeModels.kind_obj(c), Bool.and(CodemodeModels.kind_str(yes), CodemodeModels.kind_str(no))), String.append(at, " is a \"bool\" question, so criteria must be { true: string, false: string }"), cm.and2(Mod.is_obj(c), CodemodeModels.kind_obj(c), Bool.and(Mod.is_str(yes), Mod.is_str(no)), Bool.and(CodemodeModels.kind_str(yes), CodemodeModels.kind_str(no)), cm.obj(c), cm.and2(Mod.is_str(yes), CodemodeModels.kind_str(yes), Mod.is_str(no), CodemodeModels.kind_str(no), cm.str(yes), cm.str(no))))
            case False{}:
              {==}

def cm.criteria(+at: String, kind: Mod.Txt, json: String, c: Mod.Desc, vs: List<&2, Mod.Desc>, yes: Mod.Desc, no: Mod.Desc) -> {Mod.criteria_check(at, kind, json, c, vs, yes, no) == CodemodeModels.criteria_spec(at, CodemodeModels.qt_spec(kind), json, c, vs, yes, no) : Maybe<&2, String>}:
  match kind:
    case Mod.NoTxt{}:
      {==}
    case Mod.Txt{+s}:
      cm.crit_of(String.eq(s, "choice"), String.eq(s, "score"), String.eq(s, "bool"), at, json, c, vs, yes, no)

def cm.questions(qs: List<&2, Mod.Q>) -> {Mod.questions_check(qs) == CodemodeModels.questions_spec(qs) : Maybe<&2, String>}:
  match qs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      match x:
        case Mod.Q{+id, +q, +ins, +kind, +json, +c, +vs, +yes, +no}:
          +at = String.concat(["context.questions.", id])
          +w = String.concat([at, " must be a question object"])
          +v = String.concat([at, ".instructions must be a string"])
          cm.fu(Mod.is_obj(q), CodemodeModels.kind_obj(q), Mod.got(w, q), CodemodeModels.got_spec(w, q), Mod.first(Mod.unless(Mod.is_str(ins), v), Mod.first(Mod.criteria_check(at, kind, json, c, vs, yes, no), Mod.questions_check(r))), CodemodeModels.or_else(CodemodeModels.kind_str(ins), v, CodemodeModels.then_spec(CodemodeModels.criteria_spec(at, CodemodeModels.qt_spec(kind), json, c, vs, yes, no), CodemodeModels.questions_spec(r))), cm.obj(q), cm.got(w, q), cm.fu(Mod.is_str(ins), CodemodeModels.kind_str(ins), v, v, Mod.first(Mod.criteria_check(at, kind, json, c, vs, yes, no), Mod.questions_check(r)), CodemodeModels.then_spec(CodemodeModels.criteria_spec(at, CodemodeModels.qt_spec(kind), json, c, vs, yes, no), CodemodeModels.questions_spec(r)), cm.str(ins), {==}, cm.ft(Mod.criteria_check(at, kind, json, c, vs, yes, no), CodemodeModels.criteria_spec(at, CodemodeModels.qt_spec(kind), json, c, vs, yes, no), Mod.questions_check(r), CodemodeModels.questions_spec(r), cm.criteria(at, kind, json, c, vs, yes, no), cm.questions(r))))
