# eukhe: lemmas of the proofs of area codemode_models: the model a call
# names, the catalog calls, the tools and the results
#
# Each model helper equals its spec helper, by cases on the call, the
# types, the found models and the Bools the tests answer (cm.named,
# cm.catalog_go, cm.tool_of, cm.result).

import Base
import ../../../bend/codemode_models.bend as Mod
import ../../../laws/codemode_models/checks.bend as CodemodeModels
import ../base.bend as LACm

# ---- the model a call names ----

def cm.hint(d: Mod.Desc) -> {Mod.undefined_hint(Mod.is_none(d)) == CodemodeModels.sel_str(CodemodeModels.kind_none(d), " models.getModelOfType() returns undefined for an unknown provider or id.", "") : String}:
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

def cm.expects.call(c: Mod.Call, -x: String, -y: String) -> {Mod.RFail{String.concat([Mod.call_name(c), "() expects ", Mod.article(Mod.type_name(Mod.call_type(c))), " model as its first argument, got ", x, ".", y, " ", Mod.list_hint(Mod.call_type(c))])} == Mod.RFail{String.concat([CodemodeModels.call_spec(c), "() expects ", CodemodeModels.article_spec(CodemodeModels.tname(CodemodeModels.call_type_spec(c))), " model as its first argument, got ", x, ".", y, " ", CodemodeModels.hint_spec(CodemodeModels.call_type_spec(c))])} : Mod.RAns}:
  match c:
    case Mod.CClassify{}:
      {==}
    case Mod.CImages{}:
      {==}

def cm.expects.with(c: Mod.Call, -x1: String, -x2: String, ex: {x1 == x2 : String}, -y1: String, -y2: String, ey: {y1 == y2 : String}) -> {Mod.RFail{String.concat([Mod.call_name(c), "() expects ", Mod.article(Mod.type_name(Mod.call_type(c))), " model as its first argument, got ", x1, ".", y1, " ", Mod.list_hint(Mod.call_type(c))])} == Mod.RFail{String.concat([CodemodeModels.call_spec(c), "() expects ", CodemodeModels.article_spec(CodemodeModels.tname(CodemodeModels.call_type_spec(c))), " model as its first argument, got ", x2, ".", y2, " ", CodemodeModels.hint_spec(CodemodeModels.call_type_spec(c))])} : Mod.RAns}:
  %ex : {Mod.RFail{String.concat([Mod.call_name(c), "() expects ", Mod.article(Mod.type_name(Mod.call_type(c))), " model as its first argument, got ", x1, ".", y1, " ", Mod.list_hint(Mod.call_type(c))])} == Mod.RFail{String.concat([CodemodeModels.call_spec(c), "() expects ", CodemodeModels.article_spec(CodemodeModels.tname(CodemodeModels.call_type_spec(c))), " model as its first argument, got ", _, ".", y2, " ", CodemodeModels.hint_spec(CodemodeModels.call_type_spec(c))])} : Mod.RAns}
  %ey : {Mod.RFail{String.concat([Mod.call_name(c), "() expects ", Mod.article(Mod.type_name(Mod.call_type(c))), " model as its first argument, got ", x1, ".", y1, " ", Mod.list_hint(Mod.call_type(c))])} == Mod.RFail{String.concat([CodemodeModels.call_spec(c), "() expects ", CodemodeModels.article_spec(CodemodeModels.tname(CodemodeModels.call_type_spec(c))), " model as its first argument, got ", x1, ".", _, " ", CodemodeModels.hint_spec(CodemodeModels.call_type_spec(c))])} : Mod.RAns}
  cm.expects.call(c, x1, y1)

def cm.expects(+c: Mod.Call, +model: Mod.Desc) -> {Mod.expects(c, model) == CodemodeModels.expects_spec(c, model) : Mod.RAns}:
  cm.expects.with(c, Mod.describe(model), CodemodeModels.desc_spec(model), LACm.cm.desc(model), Mod.undefined_hint(Mod.is_none(model)), CodemodeModels.sel_str(CodemodeModels.kind_none(model), " models.getModelOfType() returns undefined for an unknown provider or id.", ""), cm.hint(model))

def cm.other(t: Mod.MType, chat: Maybe<&2, Mod.MType>, image: Maybe<&2, Mod.MType>, classifier: Maybe<&2, Mod.MType>) -> {Mod.other(t, chat, image, classifier) == CodemodeModels.first_other(t, [CodemodeModels.CmLook{Mod.TChat{}, chat}, CodemodeModels.CmLook{Mod.TImage{}, image}, CodemodeModels.CmLook{Mod.TClassifier{}, classifier}]) : Maybe<&2, Mod.MType>}:
  match t chat image classifier:
    case Mod.TChat{} None{} None{} None{}:
      {==}
    case Mod.TChat{} None{} None{} Some{z}:
      {==}
    case Mod.TChat{} None{} Some{y} None{}:
      {==}
    case Mod.TChat{} None{} Some{y} Some{z}:
      {==}
    case Mod.TChat{} Some{x} None{} None{}:
      {==}
    case Mod.TChat{} Some{x} None{} Some{z}:
      {==}
    case Mod.TChat{} Some{x} Some{y} None{}:
      {==}
    case Mod.TChat{} Some{x} Some{y} Some{z}:
      {==}
    case Mod.TImage{} None{} None{} None{}:
      {==}
    case Mod.TImage{} None{} None{} Some{z}:
      {==}
    case Mod.TImage{} None{} Some{y} None{}:
      {==}
    case Mod.TImage{} None{} Some{y} Some{z}:
      {==}
    case Mod.TImage{} Some{x} None{} None{}:
      {==}
    case Mod.TImage{} Some{x} None{} Some{z}:
      {==}
    case Mod.TImage{} Some{x} Some{y} None{}:
      {==}
    case Mod.TImage{} Some{x} Some{y} Some{z}:
      {==}
    case Mod.TClassifier{} None{} None{} None{}:
      {==}
    case Mod.TClassifier{} None{} None{} Some{z}:
      {==}
    case Mod.TClassifier{} None{} Some{y} None{}:
      {==}
    case Mod.TClassifier{} None{} Some{y} Some{z}:
      {==}
    case Mod.TClassifier{} Some{x} None{} None{}:
      {==}
    case Mod.TClassifier{} Some{x} None{} Some{z}:
      {==}
    case Mod.TClassifier{} Some{x} Some{y} None{}:
      {==}
    case Mod.TClassifier{} Some{x} Some{y} Some{z}:
      {==}

def cm.look(t: Mod.MType, chat: Maybe<&2, Mod.MType>, image: Maybe<&2, Mod.MType>, classifier: Maybe<&2, Mod.MType>) -> {Mod.look(t, chat, image, classifier) == CodemodeModels.found_at(t, chat, image, classifier) : Maybe<&2, Mod.MType>}:
  match t:
    case Mod.TChat{}:
      {==}
    case Mod.TImage{}:
      {==}
    case Mod.TClassifier{}:
      {==}

def cm.found_as(c: Mod.Call, a: Mod.MType, t: Mod.MType) -> {Mod.found.as(Mod.same_type(a, t), c, a) == CodemodeModels.resolved_as(CodemodeModels.type_eq(a, t), c, a) : Mod.RAns}:
  match c a t:
    case Mod.CClassify{} Mod.TChat{} Mod.TChat{}:
      {==}
    case Mod.CClassify{} Mod.TChat{} Mod.TImage{}:
      {==}
    case Mod.CClassify{} Mod.TChat{} Mod.TClassifier{}:
      {==}
    case Mod.CClassify{} Mod.TImage{} Mod.TChat{}:
      {==}
    case Mod.CClassify{} Mod.TImage{} Mod.TImage{}:
      {==}
    case Mod.CClassify{} Mod.TImage{} Mod.TClassifier{}:
      {==}
    case Mod.CClassify{} Mod.TClassifier{} Mod.TChat{}:
      {==}
    case Mod.CClassify{} Mod.TClassifier{} Mod.TImage{}:
      {==}
    case Mod.CClassify{} Mod.TClassifier{} Mod.TClassifier{}:
      {==}
    case Mod.CImages{} Mod.TChat{} Mod.TChat{}:
      {==}
    case Mod.CImages{} Mod.TChat{} Mod.TImage{}:
      {==}
    case Mod.CImages{} Mod.TChat{} Mod.TClassifier{}:
      {==}
    case Mod.CImages{} Mod.TImage{} Mod.TChat{}:
      {==}
    case Mod.CImages{} Mod.TImage{} Mod.TImage{}:
      {==}
    case Mod.CImages{} Mod.TImage{} Mod.TClassifier{}:
      {==}
    case Mod.CImages{} Mod.TClassifier{} Mod.TChat{}:
      {==}
    case Mod.CImages{} Mod.TClassifier{} Mod.TImage{}:
      {==}
    case Mod.CImages{} Mod.TClassifier{} Mod.TClassifier{}:
      {==}

def cm.missing(t: Mod.MType, +p: String, +i: String, o: Maybe<&2, Mod.MType>) -> {Mod.missing(t, p, i, o) == CodemodeModels.other_spec(t, p, i, o) : Mod.RAns}:
  match t o:
    case Mod.TChat{} None{}:
      {==}
    case Mod.TImage{} None{}:
      {==}
    case Mod.TClassifier{} None{}:
      {==}
    case Mod.TChat{} Some{a}:
      match a:
        case Mod.TChat{}:
          {==}
        case Mod.TImage{}:
          {==}
        case Mod.TClassifier{}:
          {==}
    case Mod.TImage{} Some{a}:
      match a:
        case Mod.TChat{}:
          {==}
        case Mod.TImage{}:
          {==}
        case Mod.TClassifier{}:
          {==}
    case Mod.TClassifier{} Some{a}:
      match a:
        case Mod.TChat{}:
          {==}
        case Mod.TImage{}:
          {==}
        case Mod.TClassifier{}:
          {==}

def cm.found.go(+c: Mod.Call, +t: Mod.MType, +p: String, +i: String, m: Maybe<&2, Mod.MType>, +o: Maybe<&2, Mod.MType>) -> {Mod.found(c, t, p, i, m, o) == CodemodeModels.lookup_spec(c, t, p, i, m, o) : Mod.RAns}:
  match m:
    case None{}:
      cm.missing(t, p, i, o)
    case Some{+a}:
      cm.found_as(c, a, t)

def cm.found(+c: Mod.Call, +t: Mod.MType, +p: String, +i: String, -m1: Maybe<&2, Mod.MType>, m2: Maybe<&2, Mod.MType>, em: {m1 == m2 : Maybe<&2, Mod.MType>}, -o1: Maybe<&2, Mod.MType>, o2: Maybe<&2, Mod.MType>, eo: {o1 == o2 : Maybe<&2, Mod.MType>}) -> {Mod.found(c, t, p, i, m1, o1) == CodemodeModels.lookup_spec(c, t, p, i, m2, o2) : Mod.RAns}:
  %Equal.sym(Maybe<&2, Mod.MType>, m1, m2, em) : {Mod.found(c, t, p, i, _, o1) == CodemodeModels.lookup_spec(c, t, p, i, m2, o2) : Mod.RAns}
  %Equal.sym(Maybe<&2, Mod.MType>, o1, o2, eo) : {Mod.found(c, t, p, i, m2, _) == CodemodeModels.lookup_spec(c, t, p, i, m2, o2) : Mod.RAns}
  cm.found.go(c, t, p, i, m2, o2)

def cm.named.ids(c: Mod.Call, +model: Mod.Desc, +p: String, id: Mod.Txt, +chat: Maybe<&2, Mod.MType>, +image: Maybe<&2, Mod.MType>, +classifier: Maybe<&2, Mod.MType>) -> {Mod.named.id(c, model, p, id, chat, image, classifier) == CodemodeModels.named_spec(c, model, Mod.Txt{p}, id, chat, image, classifier) : Mod.RAns}:
  match c id:
    case Mod.CClassify{} Mod.NoTxt{}:
      cm.expects(Mod.CClassify{}, model)
    case Mod.CImages{} Mod.NoTxt{}:
      cm.expects(Mod.CImages{}, model)
    case Mod.CClassify{} Mod.Txt{+i}:
      cm.found(Mod.CClassify{}, Mod.TClassifier{}, p, i, Mod.look(Mod.TClassifier{}, chat, image, classifier), CodemodeModels.found_at(Mod.TClassifier{}, chat, image, classifier), cm.look(Mod.TClassifier{}, chat, image, classifier), Mod.other(Mod.TClassifier{}, chat, image, classifier), CodemodeModels.first_other(Mod.TClassifier{}, [CodemodeModels.CmLook{Mod.TChat{}, chat}, CodemodeModels.CmLook{Mod.TImage{}, image}, CodemodeModels.CmLook{Mod.TClassifier{}, classifier}]), cm.other(Mod.TClassifier{}, chat, image, classifier))
    case Mod.CImages{} Mod.Txt{+i}:
      cm.found(Mod.CImages{}, Mod.TImage{}, p, i, Mod.look(Mod.TImage{}, chat, image, classifier), CodemodeModels.found_at(Mod.TImage{}, chat, image, classifier), cm.look(Mod.TImage{}, chat, image, classifier), Mod.other(Mod.TImage{}, chat, image, classifier), CodemodeModels.first_other(Mod.TImage{}, [CodemodeModels.CmLook{Mod.TChat{}, chat}, CodemodeModels.CmLook{Mod.TImage{}, image}, CodemodeModels.CmLook{Mod.TClassifier{}, classifier}]), cm.other(Mod.TImage{}, chat, image, classifier))

def cm.named(+c: Mod.Call, +model: Mod.Desc, provider: Mod.Txt, id: Mod.Txt, chat: Maybe<&2, Mod.MType>, image: Maybe<&2, Mod.MType>, classifier: Maybe<&2, Mod.MType>) -> {Mod.named(c, model, provider, id, chat, image, classifier) == CodemodeModels.named_spec(c, model, provider, id, chat, image, classifier) : Mod.RAns}:
  match provider:
    case Mod.NoTxt{}:
      cm.expects(c, model)
    case Mod.Txt{p}:
      cm.named.ids(c, model, p, id, chat, image, classifier)

def cm.resolve.go(dflt: Bool, +c: Mod.Call, +model: Mod.Desc, provider: Mod.Txt, id: Mod.Txt, chat: Maybe<&2, Mod.MType>, image: Maybe<&2, Mod.MType>, classifier: Maybe<&2, Mod.MType>) -> {Mod.resolve.go(dflt, c, model, provider, id, chat, image, classifier) == CodemodeModels.resolve_pick(dflt, c, model, provider, id, chat, image, classifier) : Mod.RAns}:
  match dflt:
    case True{}:
      {==}
    case False{}:
      cm.named(c, model, provider, id, chat, image, classifier)

def cm.resolve(c: Mod.Call, +d: Bool, +model: Mod.Desc, provider: Mod.Txt, id: Mod.Txt, chat: Maybe<&2, Mod.MType>, image: Maybe<&2, Mod.MType>, classifier: Maybe<&2, Mod.MType>) -> {Mod.resolve(Mod.Res{c, d, model, provider, id, chat, image, classifier}) == CodemodeModels.resolve_spec(Mod.Res{c, d, model, provider, id, chat, image, classifier}) : Mod.RAns}:
  match c:
    case Mod.CClassify{}:
      %Equal.sym(Bool, Mod.is_none(model), CodemodeModels.kind_none(model), LACm.cm.none(model)) : {Mod.resolve.go(Bool.and(d, _), Mod.CClassify{}, model, provider, id, chat, image, classifier) == CodemodeModels.resolve_pick(Bool.and(d, CodemodeModels.kind_none(model)), Mod.CClassify{}, model, provider, id, chat, image, classifier) : Mod.RAns}
      cm.resolve.go(Bool.and(d, CodemodeModels.kind_none(model)), Mod.CClassify{}, model, provider, id, chat, image, classifier)
    case Mod.CImages{}:
      cm.resolve.go(False{}, Mod.CImages{}, model, provider, id, chat, image, classifier)

# ---- the catalog calls ----

def cm.mt_of(b1: Bool, b2: Bool, b3: Bool) -> {Mod.model_type.of(b1, b2, b3) == CodemodeModels.pick_type(b1, Mod.TChat{}, CodemodeModels.pick_type(b2, Mod.TImage{}, CodemodeModels.pick_type(b3, Mod.TClassifier{}, None{}))) : Maybe<&2, Mod.MType>}:
  match b1 b2 b3:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def cm.mtype(kind: Mod.Txt) -> {Mod.model_type(kind) == CodemodeModels.mtype_spec(kind) : Maybe<&2, Mod.MType>}:
  match kind:
    case Mod.NoTxt{}:
      {==}
    case Mod.Txt{+s}:
      cm.mt_of(String.eq(s, "chat"), String.eq(s, "image"), String.eq(s, "classifier"))

def cm.nth(ds: List<&2, Mod.Desc>, n: Nat) -> {Mod.nth(ds, n) == CodemodeModels.arg_at(ds, n) : Mod.Desc}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, r}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          cm.nth(r, k)

def cm.listing(all: Bool, t: Mod.MType, d: Mod.Desc) -> {Mod.listing(all, t, Mod.provider(d)) == CodemodeModels.list_pick(CodemodeModels.kind_none(d), CodemodeModels.kind_str(d), all, t) : Mod.CAns}:
  match all d:
    case True{} Mod.DUndef{}:
      {==}
    case True{} Mod.DNull{}:
      {==}
    case True{} Mod.DBool{}:
      {==}
    case True{} Mod.DNum{}:
      {==}
    case True{} Mod.DStr{}:
      {==}
    case True{} Mod.DArr{e}:
      {==}
    case True{} Mod.DObj{ks}:
      {==}
    case False{} Mod.DUndef{}:
      {==}
    case False{} Mod.DNull{}:
      {==}
    case False{} Mod.DBool{}:
      {==}
    case False{} Mod.DNum{}:
      {==}
    case False{} Mod.DStr{}:
      {==}
    case False{} Mod.DArr{e}:
      {==}
    case False{} Mod.DObj{ks}:
      {==}

def cm.list.go(all: Bool, json: String, m: Maybe<&2, Mod.MType>, +d: Mod.Desc) -> {Mod.list_call(all, json, m, d) == CodemodeModels.list_spec(all, json, m, d) : Mod.CAns}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      cm.listing(all, t, d)

def cm.list(+all: Bool, +json: String, +kind: Mod.Txt, +args: List<&2, Mod.Desc>) -> {Mod.list_call(all, json, Mod.model_type(kind), Mod.nth(args, 1n)) == CodemodeModels.list_spec(all, json, CodemodeModels.mtype_spec(kind), CodemodeModels.arg_at(args, 1n)) : Mod.CAns}:
  %Equal.sym(Maybe<&2, Mod.MType>, Mod.model_type(kind), CodemodeModels.mtype_spec(kind), cm.mtype(kind)) : {Mod.list_call(all, json, _, Mod.nth(args, 1n)) == CodemodeModels.list_spec(all, json, CodemodeModels.mtype_spec(kind), CodemodeModels.arg_at(args, 1n)) : Mod.CAns}
  %Equal.sym(Mod.Desc, Mod.nth(args, 1n), CodemodeModels.arg_at(args, 1n), cm.nth(args, 1n)) : {Mod.list_call(all, json, CodemodeModels.mtype_spec(kind), _) == CodemodeModels.list_spec(all, json, CodemodeModels.mtype_spec(kind), CodemodeModels.arg_at(args, 1n)) : Mod.CAns}
  cm.list.go(all, json, CodemodeModels.mtype_spec(kind), CodemodeModels.arg_at(args, 1n))

def cm.descs(ds: List<&2, Mod.Desc>) -> {Mod.descs(ds) == CodemodeModels.descs_spec(ds) : List<&2, String>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +r}:
      %Equal.sym(String, Mod.describe(d), CodemodeModels.desc_spec(d), LACm.cm.desc(d)) : {_ <> Mod.descs(r) == CodemodeModels.desc_spec(d) <> CodemodeModels.descs_spec(r) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, x => CodemodeModels.desc_spec(d) <> x, Mod.descs(r), CodemodeModels.descs_spec(r), cm.descs(r))

def cm.one(json: String, m: Maybe<&2, Mod.MType>) -> {Mod.one_call(json, m) == CodemodeModels.one_spec(json, m) : Mod.CAns}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      {==}

def cm.get.go(strs: Bool, +args: List<&2, Mod.Desc>, +json: String, +kind: Mod.Txt) -> {Mod.get_call(strs, args, json, Mod.model_type(kind)) == CodemodeModels.get_spec(strs, args, kind, json) : Mod.CAns}:
  match strs:
    case False{}:
      Equal.cong(List<&2, String>, Mod.CAns, x => Mod.CFail{String.concat(["models.getModelOfType(type, provider, id) expects three strings, got (", String.join(x, ", "), "). The provider and the id are separate arguments, for example models.getModelOfType(\"classifier\", \"typesafe\", \"jev-latest\")."])}, Mod.descs(args), CodemodeModels.descs_spec(args), cm.descs(args))
    case True{}:
      %Equal.sym(Maybe<&2, Mod.MType>, Mod.model_type(kind), CodemodeModels.mtype_spec(kind), cm.mtype(kind)) : {Mod.one_call(json, _) == CodemodeModels.one_spec(json, CodemodeModels.mtype_spec(kind)) : Mod.CAns}
      cm.one(json, CodemodeModels.mtype_spec(kind))

def cm.strn(+args: List<&2, Mod.Desc>, +n: Nat) -> {Mod.is_str(Mod.nth(args, n)) == CodemodeModels.kind_str(CodemodeModels.arg_at(args, n)) : Bool}:
  %Equal.sym(Mod.Desc, Mod.nth(args, n), CodemodeModels.arg_at(args, n), cm.nth(args, n)) : {Mod.is_str(_) == CodemodeModels.kind_str(CodemodeModels.arg_at(args, n)) : Bool}
  LACm.cm.str(CodemodeModels.arg_at(args, n))

def cm.get(strs1: Bool, -strs2: Bool, e: {strs1 == strs2 : Bool}, +args: List<&2, Mod.Desc>, +json: String, +kind: Mod.Txt) -> {Mod.get_call(strs1, args, json, Mod.model_type(kind)) == CodemodeModels.get_spec(strs2, args, kind, json) : Mod.CAns}:
  %e : {Mod.get_call(strs1, args, json, Mod.model_type(kind)) == CodemodeModels.get_spec(_, args, kind, json) : Mod.CAns}
  cm.get.go(strs1, args, json, kind)

def cm.catalog_go(b1: Bool, b2: Bool, +args: List<&2, Mod.Desc>, +json: String, +kind: Mod.Txt) -> {Mod.catalog.go(b1, b2, args, json, Mod.model_type(kind)) == CodemodeModels.catalog_pick(b1, b2, args, kind, json) : Mod.CAns}:
  match b1:
    case True{}:
      cm.list(True{}, json, kind, args)
    case False{}:
      match b2:
        case True{}:
          cm.list(False{}, json, kind, args)
        case False{}:
          cm.get(Bool.and(Mod.is_str(Mod.nth(args, 1n)), Mod.is_str(Mod.nth(args, 2n))), Bool.and(CodemodeModels.kind_str(CodemodeModels.arg_at(args, 1n)), CodemodeModels.kind_str(CodemodeModels.arg_at(args, 2n))), LACm.cm.and2(Mod.is_str(Mod.nth(args, 1n)), CodemodeModels.kind_str(CodemodeModels.arg_at(args, 1n)), Mod.is_str(Mod.nth(args, 2n)), CodemodeModels.kind_str(CodemodeModels.arg_at(args, 2n)), cm.strn(args, 1n), cm.strn(args, 2n)), args, json, kind)

# ---- tools and results ----

def cm.tool_of(b1: Bool, b2: Bool) -> {Mod.tool.of(b1, b2) == CodemodeModels.pick_call(b1, Mod.CClassify{}, CodemodeModels.pick_call(b2, Mod.CImages{}, None{})) : Maybe<&2, Mod.Call>}:
  match b1 b2:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def cm.result(ok: Bool, c: Mod.Call, p: String, i: String, stop: String, e: Mod.Txt) -> {Mod.result.go(ok, c, p, i, stop, e) == CodemodeModels.result_pick(ok, c, p, i, stop, e) : Bool & String}:
  match ok c e:
    case True{} Mod.CClassify{} _:
      {==}
    case True{} Mod.CImages{} _:
      {==}
    case False{} Mod.CClassify{} Mod.NoTxt{}:
      {==}
    case False{} Mod.CClassify{} Mod.Txt{t}:
      {==}
    case False{} Mod.CImages{} Mod.NoTxt{}:
      {==}
    case False{} Mod.CImages{} Mod.Txt{t}:
      {==}
