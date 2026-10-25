# codemode_models: what code mode scripts get wrong when they call the
# `models.*` globals, and the texts the calls answer (port of pi-durable
# `codemode/models.ts`; the Rust host is crates/eukhe-durable/src/codemode/
# models.rs). The host reads a script's JSON values and gives only what the
# checks read of them (Desc: the kind of a value, an array's emptiness, an
# object's keys in order; a string's text where a check compares or prints
# it; serde's JSON text of a value an error prints); this model decides
# every check, which error wins and its exact text: a classifier context, an
# images context, the model a call names (by provider and id, with the
# host's catalog lookups), the catalog functions' arguments, which global
# runs which internal tool, how many model calls of one script run at once
# (the one place that number lives: the host's limit and the code mode
# tool's description both read it), and the texts of a call's result and
# of a context serde cannot read. Pure: no IO, no @unsafe.
# laws/codemode_models/ states its laws.

import Base

# Facts
# -----

# what a check reads of a JSON value: its kind (DUndef: absent), whether an
# array is empty, an object's keys in order
type Desc is Data:
  DUndef{}
  DNull{}
  DBool{}
  DNum{}
  DStr{}
  DArr{empty: Bool}
  DObj{keys: List<&2, String>}

# a string's text where a check compares it (NoTxt: the value is no string)
type Txt is Data:
  NoTxt{}
  Txt{text: String}

# an item of `images` or `input`: the item, and, when it is an object, its
# `type` (a string's text), `text`, `data` and `mimeType`
type Blk is Data:
  Blk{block: Desc, kind: Txt, text: Desc, data: Desc, mime: Desc}

# a question of `questions`: its id, the question, and, when it is an
# object, its `instructions`, its `type` (a string's text, and serde's JSON
# text of the value, `undefined` when absent), its `criteria`, the
# criteria's values (an object's values in order, an array's items, else
# none), and the criteria's `true` and `false`
type Q is Data:
  Q{id: String, q: Desc, instructions: Desc, kind: Txt, json: String, criteria: Desc, values: List<&2, Desc>, yes: Desc, no: Desc}

# `models.classify()`'s context: the context, and, when it is an object,
# its `state`, its `images` (with their items, when an array), and its
# `questions` (with each question, when an object)
type Ctx is Data:
  Ctx{ctx: Desc, state: Desc, images: Desc, blocks: List<&2, Blk>, questions: Desc, qs: List<&2, Q>}

# `models.generateImages()`'s context: the context, and, when it is an
# object, its `input` (with its items, when an array)
type ICtx is Data:
  ICtx{ctx: Desc, input: Desc, blocks: List<&2, Blk>}

# a model type, in the catalog's order
type MType is Data:
  TChat{}
  TImage{}
  TClassifier{}

# a model call of scripts
type Call is Data:
  CClassify{}
  CImages{}

# the model a call names: the call, whether the session resolves a default
# classifier, the model argument, its `provider` and `id` (strings' texts,
# when it is an object), and, when both are strings, the type of the model
# the catalog finds under them for each type asked (chat, image,
# classifier; none: not found)
type Res is Data:
  Res{call: Call, default: Bool, model: Desc, provider: Txt, id: Txt, chat: Maybe<&2, MType>, image: Maybe<&2, MType>, classifier: Maybe<&2, MType>}

# which model the call uses
type RAns is Data:
  RFail{text: String}
  RDefault{}
  RFound{}

# a catalog call: the global's name, the arguments, the first argument (a
# string's text, and serde's JSON text, `undefined` when absent)
type Cat is Data:
  Cat{name: String, args: List<&2, Desc>, kind: Txt, json: String}

# what a catalog call does: refuse, list the models of a type (of the
# second argument's provider when given), list those with configured auth,
# or get one by the second and third arguments
type CAns is Data:
  CFail{text: String}
  CModels{t: MType, given: Bool}
  CAvailable{t: MType, given: Bool}
  COne{t: MType}

# Values in texts
# ---------------

def obj_more(ks: List<&2, String>, left: Nat) -> String:
  match ks:
    case Nil{}:
      " }"
    case Con{k, r}:
      match left:
        case 0n:
          ", ... }"
        case 1n+l:
          String.append(", ", String.append(k, obj_more(r, l)))

def arr_text(empty: Bool) -> String:
  match empty:
    case True{}:
      "an empty array"
    case False{}:
      "an array"

def obj_text(ks: List<&2, String>) -> String:
  match ks:
    case Nil{}:
      "{}"
    case Con{k, r}:
      String.append("{ ", String.append(k, obj_more(r, 5n)))

# a script value in an error: `undefined`, `null`, `an array`, `{ a, b }`
# (the first six keys, then `...`), `a string`, ...
def describe(d: Desc) -> String:
  match d:
    case DUndef{}:
      "undefined"
    case DNull{}:
      "null"
    case DBool{}:
      "a boolean"
    case DNum{}:
      "a number"
    case DStr{}:
      "a string"
    case DArr{e}:
      arr_text(e)
    case DObj{ks}:
      obj_text(ks)

# a, e, i, o or u
def vowel(+c: Char) -> Bool:
  Bool.or(Char.is_eq('a', c), Bool.or(Char.is_eq('e', c), Bool.or(Char.is_eq('i', c), Bool.or(Char.is_eq('o', c), Bool.or(Char.is_eq('u', c), False{})))))

def article.of(on: Bool) -> String:
  match on:
    case True{}:
      "an "
    case False{}:
      "a "

# `an image`, `a classifier`: `an` before a, e, i, o, u
def article(+w: String) -> String:
  match w:
    case SNil{}:
      "a "
    case SCon{c, r}:
      String.append(article.of(vowel(c)), SCon{c, r})

def type_name(t: MType) -> String:
  match t:
    case TChat{}:
      "chat"
    case TImage{}:
      "image"
    case TClassifier{}:
      "classifier"

def call_name(c: Call) -> String:
  match c:
    case CClassify{}:
      "models.classify"
    case CImages{}:
      "models.generateImages"

def call_type(c: Call) -> MType:
  match c:
    case CClassify{}:
      TClassifier{}
    case CImages{}:
      TImage{}

# Kinds
# -----

def is_obj(d: Desc) -> Bool:
  match d:
    case DObj{ks}:
      True{}
    case DUndef{}:
      False{}
    case DNull{}:
      False{}
    case DBool{}:
      False{}
    case DNum{}:
      False{}
    case DStr{}:
      False{}
    case DArr{e}:
      False{}

def is_str(d: Desc) -> Bool:
  match d:
    case DStr{}:
      True{}
    case DUndef{}:
      False{}
    case DNull{}:
      False{}
    case DBool{}:
      False{}
    case DNum{}:
      False{}
    case DArr{e}:
      False{}
    case DObj{ks}:
      False{}

def is_arr(d: Desc) -> Bool:
  match d:
    case DArr{e}:
      True{}
    case DUndef{}:
      False{}
    case DNull{}:
      False{}
    case DBool{}:
      False{}
    case DNum{}:
      False{}
    case DStr{}:
      False{}
    case DObj{ks}:
      False{}

# an object with at least one key
def is_map(d: Desc) -> Bool:
  match d:
    case DObj{ks}:
      Bool.not(List.is_empty(&2, String, ks))
    case DUndef{}:
      False{}
    case DNull{}:
      False{}
    case DBool{}:
      False{}
    case DNum{}:
      False{}
    case DStr{}:
      False{}
    case DArr{e}:
      False{}

# an array with at least one item
def is_full(d: Desc) -> Bool:
  match d:
    case DArr{e}:
      Bool.not(e)
    case DUndef{}:
      False{}
    case DNull{}:
      False{}
    case DBool{}:
      False{}
    case DNum{}:
      False{}
    case DStr{}:
      False{}
    case DObj{ks}:
      False{}

# absent or null
def is_none(d: Desc) -> Bool:
  match d:
    case DUndef{}:
      True{}
    case DNull{}:
      True{}
    case DBool{}:
      False{}
    case DNum{}:
      False{}
    case DStr{}:
      False{}
    case DArr{e}:
      False{}
    case DObj{ks}:
      False{}

def txt_is(t: Txt, +w: String) -> Bool:
  match t:
    case NoTxt{}:
      False{}
    case Txt{s}:
      String.eq(s, w)

# every value a string
def every_str(ds: List<&2, Desc>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, r}:
      Bool.and(is_str(d), every_str(r))

# at least one value, each a string
def all_strs(ds: List<&2, Desc>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, r}:
      Bool.and(is_str(d), every_str(r))

def is_image(b: Blk) -> Bool:
  match b:
    case Blk{k, t, x, d, m}:
      Bool.and(is_obj(k), Bool.and(txt_is(t, "image"), Bool.and(is_str(d), is_str(m))))

def is_text(b: Blk) -> Bool:
  match b:
    case Blk{k, t, x, d, m}:
      Bool.and(is_obj(k), Bool.and(txt_is(t, "text"), is_str(x)))

def blk_desc(b: Blk) -> Desc:
  match b:
    case Blk{k, t, x, d, m}:
      k

# Checks
# ------

# the first problem: a, else b
def first(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Maybe<&2, String>:
  match a:
    case None{}:
      b
    case Some{p}:
      Some{p}

def unless(ok: Bool, problem: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      None{}
    case False{}:
      Some{problem}

def got(what: String, d: Desc) -> String:
  String.concat([what, ", got ", describe(d)])

# the first image at or after index i that is no image block
def bad_image(bs: List<&2, Blk>, +i: Nat) -> Maybe<&2, String>:
  match bs:
    case Nil{}:
      None{}
    case Con{+b, r}:
      first(unless(is_image(b), got(String.concat(["context.images[", Nat.show(i), "] must be an image block"]), blk_desc(b))), bad_image(r, 1n+i))

# the first input block at or after index i that is neither a text nor an
# image block
def bad_block(bs: List<&2, Blk>, +i: Nat) -> Maybe<&2, String>:
  match bs:
    case Nil{}:
      None{}
    case Con{+b, r}:
      first(unless(Bool.or(is_text(b), is_image(b)), got(String.concat(["context.input[", Nat.show(i), "] must be a text or image block"]), blk_desc(b))), bad_block(r, 1n+i))

def images_check(d: Desc, bs: List<&2, Blk>) -> Maybe<&2, String>:
  match d:
    case DUndef{}:
      None{}
    case DNull{}:
      Some{got("context.images must be an array", DNull{})}
    case DBool{}:
      Some{got("context.images must be an array", DBool{})}
    case DNum{}:
      Some{got("context.images must be an array", DNum{})}
    case DStr{}:
      Some{got("context.images must be an array", DStr{})}
    case DObj{ks}:
      Some{got("context.images must be an array", DObj{ks})}
    case DArr{e}:
      bad_image(bs, 0n)

def type_error(at: String, json: String) -> String:
  String.concat([at, ".type must be \"choice\", \"score\", or \"bool\", got ", json])

def criteria_of(choice: Bool, score: Bool, flags: Bool, +at: String, json: String, +c: Desc, vs: List<&2, Desc>, yes: Desc, no: Desc) -> Maybe<&2, String>:
  match choice:
    case True{}:
      unless(Bool.and(is_obj(c), all_strs(vs)), String.append(at, " is a \"choice\" question, so criteria must map each label to its meaning"))
    case False{}:
      match score:
        case True{}:
          unless(Bool.and(is_arr(c), all_strs(vs)), String.append(at, " is a \"score\" question, so criteria must list the levels as strings, lowest first"))
        case False{}:
          match flags:
            case True{}:
              unless(Bool.and(is_obj(c), Bool.and(is_str(yes), is_str(no))), String.append(at, " is a \"bool\" question, so criteria must be { true: string, false: string }"))
            case False{}:
              Some{type_error(at, json)}

def criteria_check(+at: String, kind: Txt, json: String, c: Desc, vs: List<&2, Desc>, yes: Desc, no: Desc) -> Maybe<&2, String>:
  match kind:
    case NoTxt{}:
      Some{type_error(at, json)}
    case Txt{+s}:
      criteria_of(String.eq(s, "choice"), String.eq(s, "score"), String.eq(s, "bool"), at, json, c, vs, yes, no)

# the first problem of the questions, in order
def questions_check(qs: List<&2, Q>) -> Maybe<&2, String>:
  match qs:
    case Nil{}:
      None{}
    case Con{x, r}:
      match x:
        case Q{id, +q, ins, kind, json, c, vs, yes, no}:
          +at = String.concat(["context.questions.", id])
          first(unless(is_obj(q), got(String.concat([at, " must be a question object"]), q)), first(unless(is_str(ins), String.concat([at, ".instructions must be a string"])), first(criteria_check(at, kind, json, c, vs, yes, no), questions_check(r))))

def classify_shape() -> String:
  "{ state: { ... }, images?: [{ type: \"image\", data: <base64>, mimeType }], questions: { <id>: { type: \"choice\", instructions, criteria: { <label>: <meaning> } } | { type: \"score\", instructions, criteria: [<lowest level>, ..., <highest level>] } | { type: \"bool\", instructions, criteria: { true: <meaning>, false: <meaning> } } } }"

# a problem as the call's error: its head, the problem, its tail
def wrap(head: String, tail: String, p: Maybe<&2, String>) -> Maybe<&2, String>:
  match p:
    case None{}:
      None{}
    case Some{t}:
      Some{String.concat([head, t, tail])}

# what is wrong with a classifier context, if anything
def classify(x: Ctx) -> Maybe<&2, String>:
  match x:
    case Ctx{+ctx, +state, images, bs, +questions, qs}:
      wrap("models.classify() ", String.concat([". Expected context: ", classify_shape(), "."]), first(unless(is_obj(ctx), got("expects a context object as its second argument", ctx)), first(unless(is_obj(state), got("context.state must be an object", state)), first(images_check(images, bs), first(unless(is_map(questions), got("context.questions must map question IDs to questions", questions)), questions_check(qs))))))

# what is wrong with an images context, if anything
def images(x: ICtx) -> Maybe<&2, String>:
  match x:
    case ICtx{+ctx, +input, bs}:
      wrap("models.generateImages() ", ". Expected context: { input: [{ type: \"text\", text: <prompt> }, ...optional { type: \"image\", data: <base64>, mimeType } references] }.", first(unless(is_obj(ctx), got("expects a context object as its second argument", ctx)), first(unless(is_full(input), got("context.input must be a non-empty array of blocks", input)), bad_block(bs, 0n))))

# The model a call names
# ----------------------

def list_hint(+t: MType) -> String:
  String.concat(["List the ", type_name(t), " models you can use with models.getAvailableOfType(\"", type_name(t), "\")."])

def undefined_hint(none: Bool) -> String:
  match none:
    case True{}:
      " models.getModelOfType() returns undefined for an unknown provider or id."
    case False{}:
      ""

def same_type(a: MType, b: MType) -> Bool:
  match a b:
    case TChat{} TChat{}:
      True{}
    case TImage{} TImage{}:
      True{}
    case TClassifier{} TClassifier{}:
      True{}
    case TChat{} TImage{}:
      False{}
    case TChat{} TClassifier{}:
      False{}
    case TImage{} TChat{}:
      False{}
    case TImage{} TClassifier{}:
      False{}
    case TClassifier{} TChat{}:
      False{}
    case TClassifier{} TImage{}:
      False{}

def look(t: MType, chat: Maybe<&2, MType>, image: Maybe<&2, MType>, classifier: Maybe<&2, MType>) -> Maybe<&2, MType>:
  match t:
    case TChat{}:
      chat
    case TImage{}:
      image
    case TClassifier{}:
      classifier

def other.at(same: Bool, o: MType, m: Maybe<&2, MType>, rest: Maybe<&2, MType>) -> Maybe<&2, MType>:
  match same:
    case True{}:
      rest
    case False{}:
      match m:
        case None{}:
          rest
        case Some{x}:
          Some{o}

# the first other type, in the catalog's order, under which the catalog
# finds a model
def other(+t: MType, chat: Maybe<&2, MType>, image: Maybe<&2, MType>, classifier: Maybe<&2, MType>) -> Maybe<&2, MType>:
  other.at(same_type(t, TChat{}), TChat{}, chat, other.at(same_type(t, TImage{}), TImage{}, image, other.at(same_type(t, TClassifier{}), TClassifier{}, classifier, None{})))

def pid(p: String, i: String) -> String:
  String.concat(["\"", p, "/", i, "\""])

def missing(+t: MType, +p: String, +i: String, o: Maybe<&2, MType>) -> RAns:
  match o:
    case None{}:
      RFail{String.concat(["Unknown ", type_name(t), " model ", pid(p, i), ". ", list_hint(t)])}
    case Some{a}:
      RFail{String.concat([pid(p, i), " is ", article(type_name(a)), " model, not ", article(type_name(t)), " model. ", list_hint(t)])}

def found.as(same: Bool, c: Call, a: MType) -> RAns:
  match same:
    case True{}:
      RFound{}
    case False{}:
      RFail{String.concat([call_name(c), "() resolved ", article(type_name(a)), ", not the requested model type"])}

def found(+c: Call, +t: MType, +p: String, +i: String, m: Maybe<&2, MType>, o: Maybe<&2, MType>) -> RAns:
  match m:
    case None{}:
      missing(t, p, i, o)
    case Some{+a}:
      found.as(same_type(a, t), c, a)

def expects(+c: Call, +model: Desc) -> RAns:
  +t = call_type(c)
  RFail{String.concat([call_name(c), "() expects ", article(type_name(t)), " model as its first argument, got ", describe(model), ".", undefined_hint(is_none(model)), " ", list_hint(t)])}

def named.id(+c: Call, +model: Desc, p: String, id: Txt, +chat: Maybe<&2, MType>, +image: Maybe<&2, MType>, +classifier: Maybe<&2, MType>) -> RAns:
  match id:
    case NoTxt{}:
      expects(c, model)
    case Txt{+i}:
      +t = call_type(c)
      found(c, t, p, i, look(t, chat, image, classifier), other(t, chat, image, classifier))

def named(+c: Call, +model: Desc, provider: Txt, id: Txt, chat: Maybe<&2, MType>, image: Maybe<&2, MType>, classifier: Maybe<&2, MType>) -> RAns:
  match provider:
    case NoTxt{}:
      expects(c, model)
    case Txt{p}:
      named.id(c, model, p, id, chat, image, classifier)

def by_default(c: Call, default: Bool, none: Bool) -> Bool:
  match c:
    case CClassify{}:
      Bool.and(default, none)
    case CImages{}:
      False{}

def resolve.go(dflt: Bool, +c: Call, +model: Desc, provider: Txt, id: Txt, chat: Maybe<&2, MType>, image: Maybe<&2, MType>, classifier: Maybe<&2, MType>) -> RAns:
  match dflt:
    case True{}:
      RDefault{}
    case False{}:
      named(c, model, provider, id, chat, image, classifier)

# which model the call uses: the session's default classifier
# (`models.classify` without a model, when the session resolves one), the
# one the catalog finds by provider and id, or an error
def resolve(x: Res) -> RAns:
  match x:
    case Res{+c, d, +model, provider, id, chat, image, classifier}:
      resolve.go(by_default(c, d, is_none(model)), c, model, provider, id, chat, image, classifier)

# The catalog calls
# -----------------

def model_type.of(chat: Bool, image: Bool, classifier: Bool) -> Maybe<&2, MType>:
  match chat:
    case True{}:
      Some{TChat{}}
    case False{}:
      match image:
        case True{}:
          Some{TImage{}}
        case False{}:
          match classifier:
            case True{}:
              Some{TClassifier{}}
            case False{}:
              None{}

# the model type a string names
def model_type(kind: Txt) -> Maybe<&2, MType>:
  match kind:
    case NoTxt{}:
      None{}
    case Txt{+s}:
      model_type.of(String.eq(s, "chat"), String.eq(s, "image"), String.eq(s, "classifier"))

def unknown_type(json: String) -> String:
  String.concat(["Unknown model type ", json, ". Use \"chat\", \"image\", or \"classifier\"."])

def nth(ds: List<&2, Desc>, n: Nat) -> Desc:
  match ds:
    case Nil{}:
      DUndef{}
    case Con{d, r}:
      match n:
        case 0n:
          d
        case 1n+k:
          nth(r, k)

# a provider filter: none, given, or an error
def provider(d: Desc) -> Maybe<&2, Bool>:
  match d:
    case DUndef{}:
      Some{False{}}
    case DNull{}:
      Some{False{}}
    case DStr{}:
      Some{True{}}
    case DBool{}:
      None{}
    case DNum{}:
      None{}
    case DArr{e}:
      None{}
    case DObj{ks}:
      None{}

def listing(all: Bool, t: MType, p: Maybe<&2, Bool>) -> CAns:
  match all:
    case True{}:
      match p:
        case None{}:
          CFail{"provider must be a string"}
        case Some{g}:
          CModels{t, g}
    case False{}:
      match p:
        case None{}:
          CFail{"provider must be a string"}
        case Some{g}:
          CAvailable{t, g}

def list_call(all: Bool, json: String, m: Maybe<&2, MType>, d: Desc) -> CAns:
  match m:
    case None{}:
      CFail{unknown_type(json)}
    case Some{t}:
      listing(all, t, provider(d))

def descs(ds: List<&2, Desc>) -> List<&2, String>:
  match ds:
    case Nil{}:
      []
    case Con{d, r}:
      describe(d) <> descs(r)

def one_call(json: String, m: Maybe<&2, MType>) -> CAns:
  match m:
    case None{}:
      CFail{unknown_type(json)}
    case Some{t}:
      COne{t}

def get_call(strs: Bool, args: List<&2, Desc>, json: String, m: Maybe<&2, MType>) -> CAns:
  match strs:
    case False{}:
      CFail{String.concat(["models.getModelOfType(type, provider, id) expects three strings, got (", String.join(descs(args), ", "), "). The provider and the id are separate arguments, for example models.getModelOfType(\"classifier\", \"typesafe\", \"jev-latest\")."])}
    case True{}:
      one_call(json, m)

def catalog.go(models: Bool, available: Bool, +args: List<&2, Desc>, json: String, m: Maybe<&2, MType>) -> CAns:
  match models:
    case True{}:
      list_call(True{}, json, m, nth(args, 1n))
    case False{}:
      match available:
        case True{}:
          list_call(False{}, json, m, nth(args, 1n))
        case False{}:
          get_call(Bool.and(is_str(nth(args, 1n)), is_str(nth(args, 2n))), args, json, m)

# what a catalog call does with its arguments
def catalog(x: Cat) -> CAns:
  match x:
    case Cat{+name, args, kind, json}:
      catalog.go(String.eq(name, "models.getModelsOfType"), String.eq(name, "models.getAvailableOfType"), args, json, model_type(kind))

# Calls and results
# -----------------

def tool.of(classify: Bool, images: Bool) -> Maybe<&2, Call>:
  match classify:
    case True{}:
      Some{CClassify{}}
    case False{}:
      match images:
        case True{}:
          Some{CImages{}}
        case False{}:
          None{}

# the model call a script global makes
def tool(+g: String) -> Maybe<&2, Call>:
  tool.of(String.eq(g, "models.classify"), String.eq(g, "models.generateImages"))

# how many `models.classify()` and `models.generateImages()` calls one
# script may have in flight; the rest wait
def max_calls() -> Nat:
  4n

def label(c: Call) -> String:
  match c:
    case CClassify{}:
      "classify"
    case CImages{}:
      "generateImages"

def error_text(error: Txt) -> String:
  match error:
    case NoTxt{}:
      ""
    case Txt{e}:
      e

def result.go(ok: Bool, c: Call, p: String, i: String, stop: String, error: Txt) -> Bool & String:
  match ok:
    case True{}:
      (True{}, String.concat([label(c), " ", p, "/", i, " done"]))
    case False{}:
      (False{}, String.concat([label(c), " ", p, "/", i, " ", stop, ": ", error_text(error)]))

# a model call's result: whether it ended with `stop`, and its text
def result(c: Call, p: String, i: String, +stop: String, error: Txt) -> Bool & String:
  result.go(String.eq(stop, "stop"), c, p, i, stop, error)

# a context serde cannot read: the call and serde's error
def unread(c: Call, error: String) -> String:
  String.concat([call_name(c), "() could not read its context: ", error])
