# eukhe: the laws of area codemode_models: the checks and texts

import Base
import ../../bend/codemode_models.bend as Mod
import ../../bend/ffi_codemode_models.bend as FMod
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# LAWS (R1-R10): what code mode scripts get wrong when they call the
# `models.*` globals, and the texts of those calls
# (bend/codemode_models.bend, the port of eukhe-durable codemode/models.rs
# `describe_value`, `with_article`, `check_classifier_context`,
# `check_images_context`, `resolve_model` with `classify`'s default
# classifier and `wrong_type`, `catalog_call`'s argument checks with
# `to_model_type` and `to_provider`, `model_call_tool`, `model_result`'s
# text, `read_context`'s error and `MAX_CONCURRENT_MODEL_CALLS`). Each law
# is an open claim about the model or its entry; PROOF.bend proves them (as
# CodemodeModels.<law>) with the lemmas of proof/codemode_models/.
#
# The host reads a script's JSON values and gives what the checks read: a
# value's kind (absent, null, a boolean, a number, a string, an array and
# whether it is empty, an object and its keys in order), a string's text
# where a check compares it, and serde's JSON text (`undefined` when
# absent) of a value an error prints.
#
# R1: a value in an error reads `undefined`, `null`, `a boolean`, `a
#     number`, `a string`, `an empty array`, `an array`, `{}` for an object
#     without keys, else `{ ` then its first six keys joined by `, `, then
#     `, ...` when it has more than six, then ` }`.
# R2: a word with its article: `an ` before a word starting with a, e, i,
#     o or u, else `a ` (the empty word too).
# R3: a classifier context fails, the first of these that holds, with
#     "models.classify() <problem>. Expected context: <shape>.": no object
#     ("expects a context object as its second argument, got <v>"); a
#     `state` that is no object ("context.state must be an object, got
#     <v>"); an `images` present that is no array ("context.images must be
#     an array, got <v>"), or its first item that is no image block (an
#     object whose `type` is "image" and whose `data` and `mimeType` are
#     strings: "context.images[<i>] must be an image block, got <v>"); a
#     `questions` that is no object with a key ("context.questions must map
#     question IDs to questions, got <v>"); then each question in order
#     (`at` = "context.questions.<id>"): no object ("<at> must be a question
#     object, got <v>"), `instructions` no string ("<at>.instructions must
#     be a string"), a `type` "choice" whose `criteria` is no object with
#     at least one value, all strings ("<at> is a \"choice\" question, so
#     criteria must map each label to its meaning"), "score" whose
#     `criteria` is no array with at least one item, all strings ("<at> is
#     a \"score\" question, so criteria must list the levels as strings,
#     lowest first"), "bool" whose `criteria` is no object with string
#     `true` and `false` ("<at> is a \"bool\" question, so criteria must be
#     { true: string, false: string }"), any other `type` ("<at>.type must
#     be \"choice\", \"score\", or \"bool\", got <its JSON text>").
# R4: an images context fails, the first that holds, with
#     "models.generateImages() <problem>. Expected context: { input: [{
#     type: \"text\", text: <prompt> }, ...optional { type: \"image\",
#     data: <base64>, mimeType } references] }.": no object; an `input`
#     that is no array with an item ("context.input must be a non-empty
#     array of blocks, got <v>"); its first item that is neither a text
#     block (an object whose `type` is "text" and whose `text` is a string)
#     nor an image block ("context.input[<i>] must be a text or image
#     block, got <v>").
# R5: a model call (`models.classify`: classifier; `models.generateImages`:
#     image) uses the session's default classifier when it is
#     `models.classify`, the session resolves one, and the model is absent
#     or null; else, unless the model is an object whose `provider` and
#     `id` are strings, it fails with "<call>() expects <a type> model as
#     its first argument, got <v>.<hint> List the <type> models you can use
#     with models.getAvailableOfType(\"<type>\")." (hint: " models.
#     getModelOfType() returns undefined for an unknown provider or id."
#     when the model is absent or null); else the model the catalog finds
#     under the call's type is used when it is of that type, and fails with
#     "<call>() resolved <a its type>, not the requested model type" when
#     not; else the first other type (chat, image, classifier) under which
#     the catalog finds one fails with "\"<provider>/<id>\" is <a other>
#     model, not <a type> model. <list hint>"; else "Unknown <type> model
#     \"<provider>/<id>\". <list hint>".
# R6: a catalog call `models.getModelsOfType` or
#     `models.getAvailableOfType` names its type in its first argument (a
#     string "chat", "image" or "classifier", else "Unknown model type
#     <JSON text>. Use \"chat\", \"image\", or \"classifier\"."), then its
#     provider in its second (absent or null: none; a string: given; else
#     "provider must be a string"); any other global
#     (`models.getModelOfType`) needs strings as second and third arguments
#     (else "models.getModelOfType(type, provider, id) expects three
#     strings, got (<each argument, joined by `, `>). The provider and the
#     id are separate arguments, for example
#     models.getModelOfType(\"classifier\", \"typesafe\", \"jev-latest\").")
#     and then the type as above.
# R7: the global `models.classify` runs the classify tool,
#     `models.generateImages` the images tool, any other none.
# R8: a call's result is ok when its stop reason is "stop"; its text is
#     "<classify|generateImages> <provider>/<id>" then " done" when ok, else
#     " <stop reason>: <error message, or nothing>".
# R9: a context serde cannot read fails with "<call>() could not read its
#     context: <serde's error>".
# R10: at most 4 `models.classify()` and `models.generateImages()` calls of
#     one script run at once; the rest wait. The host's limit and the code
#     mode tool's description (laws/codemode_describe.bend) read this one
#     number.

# Terms
# -----

def more_spec(more: Bool) -> String:
  match more:
    case True{}:
      ", ..."
    case False{}:
      ""

# R1: an object's keys
def keys_spec(ks: List<&2, String>) -> String:
  match ks:
    case Nil{}:
      "{}"
    case Con{+k, +r}:
      String.concat(["{ ", String.join(List.take(&2, String, Con{k, r}, 6n), ", "), more_spec(Bool.not(List.is_empty(&2, String, List.drop(&2, String, Con{k, r}, 6n)))), " }"])

# R1: a value in an error
def desc_spec(d: Mod.Desc) -> String:
  match d:
    case Mod.DUndef{}:
      "undefined"
    case Mod.DNull{}:
      "null"
    case Mod.DBool{}:
      "a boolean"
    case Mod.DNum{}:
      "a number"
    case Mod.DStr{}:
      "a string"
    case Mod.DArr{e}:
      match e:
        case True{}:
          "an empty array"
        case False{}:
          "an array"
    case Mod.DObj{ks}:
      keys_spec(ks)

def vowels() -> List<&2, Char>:
  ['a', 'e', 'i', 'o', 'u']

def has_char(cs: List<&2, Char>, +c: Char) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{x, r}:
      Bool.or(Char.is_eq(x, c), has_char(r, c))

def sel_str(b: Bool, x: String, y: String) -> String:
  match b:
    case True{}:
      x
    case False{}:
      y

# R2: a word with its article
def article_spec(+w: String) -> String:
  match w:
    case SNil{}:
      "a "
    case SCon{+c, +r}:
      String.append(sel_str(has_char(vowels(), c), "an ", "a "), SCon{c, r})

def kind_obj(d: Mod.Desc) -> Bool:
  match d:
    case Mod.DObj{ks}:
      True{}
    case Mod.DUndef{}:
      False{}
    case Mod.DNull{}:
      False{}
    case Mod.DBool{}:
      False{}
    case Mod.DNum{}:
      False{}
    case Mod.DStr{}:
      False{}
    case Mod.DArr{e}:
      False{}

def kind_str(d: Mod.Desc) -> Bool:
  match d:
    case Mod.DStr{}:
      True{}
    case Mod.DUndef{}:
      False{}
    case Mod.DNull{}:
      False{}
    case Mod.DBool{}:
      False{}
    case Mod.DNum{}:
      False{}
    case Mod.DArr{e}:
      False{}
    case Mod.DObj{ks}:
      False{}

def kind_arr(d: Mod.Desc) -> Bool:
  match d:
    case Mod.DArr{e}:
      True{}
    case Mod.DUndef{}:
      False{}
    case Mod.DNull{}:
      False{}
    case Mod.DBool{}:
      False{}
    case Mod.DNum{}:
      False{}
    case Mod.DStr{}:
      False{}
    case Mod.DObj{ks}:
      False{}

# absent or null
def kind_none(d: Mod.Desc) -> Bool:
  match d:
    case Mod.DUndef{}:
      True{}
    case Mod.DNull{}:
      True{}
    case Mod.DBool{}:
      False{}
    case Mod.DNum{}:
      False{}
    case Mod.DStr{}:
      False{}
    case Mod.DArr{e}:
      False{}
    case Mod.DObj{ks}:
      False{}

def txt_eq(t: Mod.Txt, +w: String) -> Bool:
  match t:
    case Mod.NoTxt{}:
      False{}
    case Mod.Txt{s}:
      String.eq(s, w)

# every value a string
def strs_spec(ds: List<&2, Mod.Desc>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, r}:
      Bool.and(kind_str(d), strs_spec(r))

# at least one value
def some_spec(ds: List<&2, Mod.Desc>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, r}:
      True{}

# R3: an image block
def image_spec(b: Mod.Blk) -> Bool:
  match b:
    case Mod.Blk{k, t, x, d, m}:
      Bool.and(kind_obj(k), Bool.and(txt_eq(t, "image"), Bool.and(kind_str(d), kind_str(m))))

# R4: a text block
def text_spec(b: Mod.Blk) -> Bool:
  match b:
    case Mod.Blk{k, t, x, d, m}:
      Bool.and(kind_obj(k), Bool.and(txt_eq(t, "text"), kind_str(x)))

def blk_of(b: Mod.Blk) -> Mod.Desc:
  match b:
    case Mod.Blk{k, t, x, d, m}:
      k

# the problem when ok does not hold, else the rest's
def or_else(ok: Bool, problem: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      rest
    case False{}:
      Some{problem}

def got_spec(what: String, d: Mod.Desc) -> String:
  String.concat([what, ", got ", desc_spec(d)])

# R3: the first image (from index i) that is no image block
def images_spec(bs: List<&2, Mod.Blk>, +i: Nat) -> Maybe<&2, String>:
  match bs:
    case Nil{}:
      None{}
    case Con{+b, r}:
      or_else(image_spec(b), got_spec(String.concat(["context.images[", Nat.show(i), "] must be an image block"]), blk_of(b)), images_spec(r, 1n+i))

# R3: the images part
def images_part(d: Mod.Desc, bs: List<&2, Mod.Blk>) -> Maybe<&2, String>:
  match d:
    case Mod.DUndef{}:
      None{}
    case Mod.DNull{}:
      Some{got_spec("context.images must be an array", Mod.DNull{})}
    case Mod.DBool{}:
      Some{got_spec("context.images must be an array", Mod.DBool{})}
    case Mod.DNum{}:
      Some{got_spec("context.images must be an array", Mod.DNum{})}
    case Mod.DStr{}:
      Some{got_spec("context.images must be an array", Mod.DStr{})}
    case Mod.DObj{ks}:
      Some{got_spec("context.images must be an array", Mod.DObj{ks})}
    case Mod.DArr{e}:
      images_spec(bs, 0n)

def type_err(at: String, json: String) -> String:
  String.concat([at, ".type must be \"choice\", \"score\", or \"bool\", got ", json])

# R3: a question's `type`
type QT is Data:
  CmChoice{}
  CmScore{}
  CmFlags{}
  CmOther{}

def qt_of(choice: Bool, score: Bool, flags: Bool) -> QT:
  match choice:
    case True{}:
      CmChoice{}
    case False{}:
      match score:
        case True{}:
          CmScore{}
        case False{}:
          match flags:
            case True{}:
              CmFlags{}
            case False{}:
              CmOther{}

def qt_spec(kind: Mod.Txt) -> QT:
  match kind:
    case Mod.NoTxt{}:
      CmOther{}
    case Mod.Txt{+t}:
      qt_of(String.eq(t, "choice"), String.eq(t, "score"), String.eq(t, "bool"))

# R3: a question's criteria for its type
def criteria_spec(+at: String, qt: QT, json: String, +c: Mod.Desc, +vs: List<&2, Mod.Desc>, yes: Mod.Desc, no: Mod.Desc) -> Maybe<&2, String>:
  match qt:
    case CmChoice{}:
      or_else(Bool.and(kind_obj(c), Bool.and(some_spec(vs), strs_spec(vs))), String.append(at, " is a \"choice\" question, so criteria must map each label to its meaning"), None{})
    case CmScore{}:
      or_else(Bool.and(kind_arr(c), Bool.and(some_spec(vs), strs_spec(vs))), String.append(at, " is a \"score\" question, so criteria must list the levels as strings, lowest first"), None{})
    case CmFlags{}:
      or_else(Bool.and(kind_obj(c), Bool.and(kind_str(yes), kind_str(no))), String.append(at, " is a \"bool\" question, so criteria must be { true: string, false: string }"), None{})
    case CmOther{}:
      Some{type_err(at, json)}

def then_spec(p: Maybe<&2, String>, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match p:
    case None{}:
      rest
    case Some{t}:
      Some{t}

# R3: each question in order
def questions_spec(qs: List<&2, Mod.Q>) -> Maybe<&2, String>:
  match qs:
    case Nil{}:
      None{}
    case Con{x, r}:
      match x:
        case Mod.Q{id, +q, ins, kind, json, c, vs, yes, no}:
          +at = String.concat(["context.questions.", id])
          or_else(kind_obj(q), got_spec(String.concat([at, " must be a question object"]), q), or_else(kind_str(ins), String.concat([at, ".instructions must be a string"]), then_spec(criteria_spec(at, qt_spec(kind), json, c, vs, yes, no), questions_spec(r))))

def wrap_spec(head: String, tail: String, p: Maybe<&2, String>) -> Maybe<&2, String>:
  match p:
    case None{}:
      None{}
    case Some{t}:
      Some{String.concat([head, t, tail])}

def shape_spec() -> String:
  "{ state: { ... }, images?: [{ type: \"image\", data: <base64>, mimeType }], questions: { <id>: { type: \"choice\", instructions, criteria: { <label>: <meaning> } } | { type: \"score\", instructions, criteria: [<lowest level>, ..., <highest level>] } | { type: \"bool\", instructions, criteria: { true: <meaning>, false: <meaning> } } } }"

def map_spec(d: Mod.Desc) -> Bool:
  match d:
    case Mod.DObj{ks}:
      Bool.not(List.is_empty(&2, String, ks))
    case Mod.DUndef{}:
      False{}
    case Mod.DNull{}:
      False{}
    case Mod.DBool{}:
      False{}
    case Mod.DNum{}:
      False{}
    case Mod.DStr{}:
      False{}
    case Mod.DArr{e}:
      False{}

# R3: what is wrong with a classifier context
def classify_spec(x: Mod.Ctx) -> Maybe<&2, String>:
  match x:
    case Mod.Ctx{+ctx, +state, images, bs, +questions, qs}:
      wrap_spec("models.classify() ", String.concat([". Expected context: ", shape_spec(), "."]), or_else(kind_obj(ctx), got_spec("expects a context object as its second argument", ctx), or_else(kind_obj(state), got_spec("context.state must be an object", state), then_spec(images_part(images, bs), or_else(map_spec(questions), got_spec("context.questions must map question IDs to questions", questions), questions_spec(qs))))))

# R4: the first input item (from index i) that is no text or image block
def blocks_spec(bs: List<&2, Mod.Blk>, +i: Nat) -> Maybe<&2, String>:
  match bs:
    case Nil{}:
      None{}
    case Con{+b, r}:
      or_else(Bool.or(text_spec(b), image_spec(b)), got_spec(String.concat(["context.input[", Nat.show(i), "] must be a text or image block"]), blk_of(b)), blocks_spec(r, 1n+i))

def full_spec(d: Mod.Desc) -> Bool:
  match d:
    case Mod.DArr{e}:
      Bool.not(e)
    case Mod.DUndef{}:
      False{}
    case Mod.DNull{}:
      False{}
    case Mod.DBool{}:
      False{}
    case Mod.DNum{}:
      False{}
    case Mod.DStr{}:
      False{}
    case Mod.DObj{ks}:
      False{}

# R4: what is wrong with an images context
def images_ctx_spec(x: Mod.ICtx) -> Maybe<&2, String>:
  match x:
    case Mod.ICtx{+ctx, +input, bs}:
      wrap_spec("models.generateImages() ", ". Expected context: { input: [{ type: \"text\", text: <prompt> }, ...optional { type: \"image\", data: <base64>, mimeType } references] }.", or_else(kind_obj(ctx), got_spec("expects a context object as its second argument", ctx), or_else(full_spec(input), got_spec("context.input must be a non-empty array of blocks", input), blocks_spec(bs, 0n))))

def tname(t: Mod.MType) -> String:
  match t:
    case Mod.TChat{}:
      "chat"
    case Mod.TImage{}:
      "image"
    case Mod.TClassifier{}:
      "classifier"

def call_type_spec(c: Mod.Call) -> Mod.MType:
  match c:
    case Mod.CClassify{}:
      Mod.TClassifier{}
    case Mod.CImages{}:
      Mod.TImage{}

def call_spec(c: Mod.Call) -> String:
  match c:
    case Mod.CClassify{}:
      "models.classify"
    case Mod.CImages{}:
      "models.generateImages"

def type_eq(a: Mod.MType, b: Mod.MType) -> Bool:
  match a:
    case Mod.TChat{}:
      match b:
        case Mod.TChat{}:
          True{}
        case Mod.TImage{}:
          False{}
        case Mod.TClassifier{}:
          False{}
    case Mod.TImage{}:
      match b:
        case Mod.TChat{}:
          False{}
        case Mod.TImage{}:
          True{}
        case Mod.TClassifier{}:
          False{}
    case Mod.TClassifier{}:
      match b:
        case Mod.TChat{}:
          False{}
        case Mod.TImage{}:
          False{}
        case Mod.TClassifier{}:
          True{}

def hint_spec(+t: Mod.MType) -> String:
  String.concat(["List the ", tname(t), " models you can use with models.getAvailableOfType(\"", tname(t), "\")."])

# a type and what the catalog finds under it
type CmLook is Data:
  CmLook{t: Mod.MType, found: Maybe<&2, Mod.MType>}

def other_pick(same: Bool, o: Mod.MType, rest: Maybe<&2, Mod.MType>) -> Maybe<&2, Mod.MType>:
  match same:
    case True{}:
      rest
    case False{}:
      Some{o}

# R5: the first type of ls, other than t, under which the catalog finds a
# model
def first_other(+t: Mod.MType, ls: List<&2, CmLook>) -> Maybe<&2, Mod.MType>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, r}:
      match l:
        case CmLook{+o, f}:
          match f:
            case None{}:
              first_other(t, r)
            case Some{x}:
              other_pick(type_eq(o, t), o, first_other(t, r))

def found_at(t: Mod.MType, chat: Maybe<&2, Mod.MType>, image: Maybe<&2, Mod.MType>, classifier: Maybe<&2, Mod.MType>) -> Maybe<&2, Mod.MType>:
  match t:
    case Mod.TChat{}:
      chat
    case Mod.TImage{}:
      image
    case Mod.TClassifier{}:
      classifier

def quoted(p: String, i: String) -> String:
  String.concat(["\"", p, "/", i, "\""])

def expects_spec(+c: Mod.Call, +model: Mod.Desc) -> Mod.RAns:
  +t = call_type_spec(c)
  Mod.RFail{String.concat([call_spec(c), "() expects ", article_spec(tname(t)), " model as its first argument, got ", desc_spec(model), ".", sel_str(kind_none(model), " models.getModelOfType() returns undefined for an unknown provider or id.", ""), " ", hint_spec(t)])}

def resolved_as(same: Bool, c: Mod.Call, a: Mod.MType) -> Mod.RAns:
  match same:
    case True{}:
      Mod.RFound{}
    case False{}:
      Mod.RFail{String.concat([call_spec(c), "() resolved ", article_spec(tname(a)), ", not the requested model type"])}

def other_spec(+t: Mod.MType, +p: String, +i: String, o: Maybe<&2, Mod.MType>) -> Mod.RAns:
  match o:
    case None{}:
      Mod.RFail{String.concat(["Unknown ", tname(t), " model ", quoted(p, i), ". ", hint_spec(t)])}
    case Some{a}:
      Mod.RFail{String.concat([quoted(p, i), " is ", article_spec(tname(a)), " model, not ", article_spec(tname(t)), " model. ", hint_spec(t)])}

def lookup_spec(+c: Mod.Call, +t: Mod.MType, p: String, i: String, m: Maybe<&2, Mod.MType>, o: Maybe<&2, Mod.MType>) -> Mod.RAns:
  match m:
    case Some{+a}:
      resolved_as(type_eq(a, t), c, a)
    case None{}:
      other_spec(t, p, i, o)

def named_spec(+c: Mod.Call, +model: Mod.Desc, provider: Mod.Txt, id: Mod.Txt, +chat: Maybe<&2, Mod.MType>, +image: Maybe<&2, Mod.MType>, +classifier: Maybe<&2, Mod.MType>) -> Mod.RAns:
  match provider:
    case Mod.NoTxt{}:
      expects_spec(c, model)
    case Mod.Txt{p}:
      match id:
        case Mod.NoTxt{}:
          expects_spec(c, model)
        case Mod.Txt{i}:
          +t = call_type_spec(c)
          lookup_spec(c, t, p, i, found_at(t, chat, image, classifier), first_other(t, [CmLook{Mod.TChat{}, chat}, CmLook{Mod.TImage{}, image}, CmLook{Mod.TClassifier{}, classifier}]))

def resolve_pick(dflt: Bool, +c: Mod.Call, +model: Mod.Desc, provider: Mod.Txt, id: Mod.Txt, chat: Maybe<&2, Mod.MType>, image: Maybe<&2, Mod.MType>, classifier: Maybe<&2, Mod.MType>) -> Mod.RAns:
  match dflt:
    case True{}:
      Mod.RDefault{}
    case False{}:
      named_spec(c, model, provider, id, chat, image, classifier)

# R5: which model a call uses
def resolve_spec(x: Mod.Res) -> Mod.RAns:
  match x:
    case Mod.Res{+c, d, +model, provider, id, chat, image, classifier}:
      resolve_pick(Bool.and(type_eq(call_type_spec(c), Mod.TClassifier{}), Bool.and(d, kind_none(model))), c, model, provider, id, chat, image, classifier)

# a name and what it names
type CmNamed is Data:
  CmNamed{name: String, t: Mod.MType}

def type_names() -> List<&2, CmNamed>:
  [CmNamed{"chat", Mod.TChat{}}, CmNamed{"image", Mod.TImage{}}, CmNamed{"classifier", Mod.TClassifier{}}]

def pick_type(b: Bool, t: Mod.MType, rest: Maybe<&2, Mod.MType>) -> Maybe<&2, Mod.MType>:
  match b:
    case True{}:
      Some{t}
    case False{}:
      rest

def find_type(ns: List<&2, CmNamed>, +s: String) -> Maybe<&2, Mod.MType>:
  match ns:
    case Nil{}:
      None{}
    case Con{n, r}:
      match n:
        case CmNamed{w, t}:
          pick_type(String.eq(s, w), t, find_type(r, s))

# R6: the model type a first argument names
def mtype_spec(kind: Mod.Txt) -> Maybe<&2, Mod.MType>:
  match kind:
    case Mod.NoTxt{}:
      None{}
    case Mod.Txt{s}:
      find_type(type_names(), s)

def arg_at(ds: List<&2, Mod.Desc>, n: Nat) -> Mod.Desc:
  match ds:
    case Nil{}:
      Mod.DUndef{}
    case Con{d, r}:
      match n:
        case 0n:
          d
        case 1n+k:
          arg_at(r, k)

def descs_spec(ds: List<&2, Mod.Desc>) -> List<&2, String>:
  match ds:
    case Nil{}:
      []
    case Con{d, r}:
      desc_spec(d) <> descs_spec(r)

def unknown_spec(json: String) -> String:
  String.concat(["Unknown model type ", json, ". Use \"chat\", \"image\", or \"classifier\"."])

def list_pick(none: Bool, str: Bool, models: Bool, t: Mod.MType) -> Mod.CAns:
  match none:
    case True{}:
      match models:
        case True{}:
          Mod.CModels{t, False{}}
        case False{}:
          Mod.CAvailable{t, False{}}
    case False{}:
      match str:
        case True{}:
          match models:
            case True{}:
              Mod.CModels{t, True{}}
            case False{}:
              Mod.CAvailable{t, True{}}
        case False{}:
          Mod.CFail{"provider must be a string"}

def list_spec(models: Bool, json: String, m: Maybe<&2, Mod.MType>, +d: Mod.Desc) -> Mod.CAns:
  match m:
    case None{}:
      Mod.CFail{unknown_spec(json)}
    case Some{t}:
      list_pick(kind_none(d), kind_str(d), models, t)

def one_spec(json: String, m: Maybe<&2, Mod.MType>) -> Mod.CAns:
  match m:
    case None{}:
      Mod.CFail{unknown_spec(json)}
    case Some{t}:
      Mod.COne{t}

def get_spec(strs: Bool, args: List<&2, Mod.Desc>, kind: Mod.Txt, json: String) -> Mod.CAns:
  match strs:
    case False{}:
      Mod.CFail{String.concat(["models.getModelOfType(type, provider, id) expects three strings, got (", String.join(descs_spec(args), ", "), "). The provider and the id are separate arguments, for example models.getModelOfType(\"classifier\", \"typesafe\", \"jev-latest\")."])}
    case True{}:
      one_spec(json, mtype_spec(kind))

def catalog_pick(models: Bool, available: Bool, +args: List<&2, Mod.Desc>, kind: Mod.Txt, json: String) -> Mod.CAns:
  match models:
    case True{}:
      list_spec(True{}, json, mtype_spec(kind), arg_at(args, 1n))
    case False{}:
      match available:
        case True{}:
          list_spec(False{}, json, mtype_spec(kind), arg_at(args, 1n))
        case False{}:
          get_spec(Bool.and(kind_str(arg_at(args, 1n)), kind_str(arg_at(args, 2n))), args, kind, json)

# R6: what a catalog call does
def catalog_spec(x: Mod.Cat) -> Mod.CAns:
  match x:
    case Mod.Cat{+name, args, kind, json}:
      catalog_pick(String.eq(name, "models.getModelsOfType"), String.eq(name, "models.getAvailableOfType"), args, kind, json)

# a global and the model call it makes
type CmRuns is Data:
  CmRuns{global: String, call: Mod.Call}

def pick_call(b: Bool, c: Mod.Call, rest: Maybe<&2, Mod.Call>) -> Maybe<&2, Mod.Call>:
  match b:
    case True{}:
      Some{c}
    case False{}:
      rest

def find_call(rs: List<&2, CmRuns>, +g: String) -> Maybe<&2, Mod.Call>:
  match rs:
    case Nil{}:
      None{}
    case Con{x, r}:
      match x:
        case CmRuns{w, c}:
          pick_call(String.eq(g, w), c, find_call(r, g))

# R7: the model call of a global
def tool_spec(g: String) -> Maybe<&2, Mod.Call>:
  find_call([CmRuns{"models.classify", Mod.CClassify{}}, CmRuns{"models.generateImages", Mod.CImages{}}], g)

def label_spec(c: Mod.Call) -> String:
  match c:
    case Mod.CClassify{}:
      "classify"
    case Mod.CImages{}:
      "generateImages"

def error_spec(e: Mod.Txt) -> String:
  match e:
    case Mod.NoTxt{}:
      ""
    case Mod.Txt{t}:
      t

def result_pick(ok: Bool, c: Mod.Call, p: String, i: String, stop: String, e: Mod.Txt) -> Bool & String:
  match ok:
    case True{}:
      (True{}, String.concat([label_spec(c), " ", p, "/", i, " done"]))
    case False{}:
      (False{}, String.concat([label_spec(c), " ", p, "/", i, " ", stop, ": ", error_spec(e)]))

# R8: a call's result
def result_spec(c: Mod.Call, p: String, i: String, +stop: String, e: Mod.Txt) -> Bool & String:
  result_pick(String.eq(stop, "stop"), c, p, i, stop, e)

# Laws
# ----

# LAW codemode_models_describe_exact: a value in an error is R1's: its kind, an array's emptiness, an object's first six keys then `...`
# EXCLUDES: a cut after five or seven keys, `...` without more keys, `{ }`
#   for an object without keys, an article that does not fit, `an array`
#   for an empty one
law codemode_models_describe_exact:
  for d: Mod.Desc
  {Mod.describe(d) == desc_spec(d) : String}

# LAW codemode_models_article_exact: a word's article is `an` before a, e, i, o, u, else `a`
# EXCLUDES: `an` before a consonant or y, a capital vowel taken for one, a
#   missing space, the empty word with `an`
law codemode_models_article_exact:
  for +w: String
  {Mod.article(w) == article_spec(w) : String}

# LAW codemode_models_classify_exact: a classifier context fails as R3 says: the first failing check in R3's order, with its exact text, wrapped in the expected shape
# EXCLUDES: checks in another order, an absent `images` refused, a null one
#   accepted, an image block without `mimeType`, an index off by one, a
#   choice question with no labels accepted, a score question with an
#   object, a bool question with one meaning, another question's id, a
#   type error without its JSON text, a later question's problem first
law codemode_models_classify_exact:
  for x: Mod.Ctx
  {Mod.classify(x) == classify_spec(x) : Maybe<&2, String>}

# LAW codemode_models_images_exact: an images context fails as R4 says: no object, an empty or missing input, its first item that is neither a text nor an image block
# EXCLUDES: an empty input accepted, a text block without text accepted, an
#   image block accepted as text, an index off by one, another shape text
law codemode_models_images_exact:
  for x: Mod.ICtx
  {Mod.images(x) == images_ctx_spec(x) : Maybe<&2, String>}

# LAW codemode_models_resolve_exact: a call's model is R5's: the default classifier only for classify without a model, else the one the catalog finds by provider and id under the call's type, else the exact error
# EXCLUDES: the default for generateImages or for a named model, a model of
#   another type used, the other type searched in another order or the
#   asked type named as the other, the undefined hint for a string, a
#   missing list hint, `a image`
law codemode_models_resolve_exact:
  for x: Mod.Res
  {Mod.resolve(x) == resolve_spec(x) : Mod.RAns}

# LAW codemode_models_catalog_exact: a catalog call's arguments are checked as R6 says: the type first, then the provider; getModelOfType's three strings before its type
# EXCLUDES: the provider checked first, a number accepted as a provider, a
#   null provider refused, getModelOfType's type checked before its
#   strings, the arguments listed without the first, a type parsed
#   case-insensitively
law codemode_models_catalog_exact:
  for x: Mod.Cat
  {Mod.catalog(x) == catalog_spec(x) : Mod.CAns}

# LAW codemode_models_tool_exact: only `models.classify` and `models.generateImages` run a model tool, each its own
# EXCLUDES: the tools swapped, a catalog global run as a model call, a
#   prefix match
law codemode_models_tool_exact:
  for +g: String
  {Mod.tool(g) == tool_spec(g) : Maybe<&2, Mod.Call>}

# LAW codemode_models_result_exact: a call's result is ok exactly when it stopped with "stop", with R8's text
# EXCLUDES: another stop reason taken as ok, the error message dropped or
#   shown on success, another label
law codemode_models_result_exact:
  for c: Mod.Call
  for p: String
  for i: String
  for +stop: String
  for e: Mod.Txt
  {Mod.result(c, p, i, stop, e) == result_spec(c, p, i, stop, e) : Bool & String}

# LAW codemode_models_unread_exact: a context serde cannot read fails with R9's text
# EXCLUDES: another call's name, serde's error dropped
law codemode_models_unread_exact:
  for c: Mod.Call
  for e: String
  {Mod.unread(c, e) == String.concat([call_spec(c), "() could not read its context: ", e]) : String}

# LAW codemode_models_cap_exact: at most 4 model calls of one script run at once
# EXCLUDES: another limit, a limit of 0 that never runs a call
law codemode_models_cap_exact:
  {Mod.max_calls() == 4n : Nat}

# LAW codemode_models_example: anchor: models.rs's tests: the values described, unknown model types, each classifier and images context error, the models resolved by provider and id, getModelOfType's three strings
# EXCLUDES: a spec that is wrong on the shipped cases
law codemode_models_example:
  {[Mod.describe(Mod.DUndef{}), Mod.describe(Mod.DNull{}), Mod.describe(Mod.DArr{True{}}), Mod.describe(Mod.DArr{False{}}), Mod.describe(Mod.DObj{[]}), Mod.describe(Mod.DObj{["prompt"]}), Mod.describe(Mod.DObj{["a", "b", "c", "d", "e", "f", "g"]}), Mod.describe(Mod.DStr{}), Mod.describe(Mod.DNum{}), Mod.describe(Mod.DBool{})] == ["undefined", "null", "an empty array", "an array", "{}", "{ prompt }", "{ a, b, c, d, e, f, ... }", "a string", "a number", "a boolean"] : List<&2, String>} &
  {[Mod.catalog(Mod.Cat{"models.getModelsOfType", [Mod.DStr{}], Mod.Txt{"text"}, "\"text\""}), Mod.catalog(Mod.Cat{"models.getModelsOfType", [], Mod.NoTxt{}, "undefined"}), Mod.catalog(Mod.Cat{"models.getModelsOfType", [Mod.DStr{}, Mod.DNum{}], Mod.Txt{"image"}, "\"image\""}), Mod.catalog(Mod.Cat{"models.getModelOfType", [Mod.DStr{}, Mod.DStr{}], Mod.Txt{"classifier"}, "\"classifier\""}), Mod.catalog(Mod.Cat{"models.getModelOfType", [Mod.DStr{}, Mod.DStr{}, Mod.DStr{}], Mod.Txt{"chat"}, "\"chat\""}), Mod.catalog(Mod.Cat{"models.getAvailableOfType", [Mod.DStr{}, Mod.DNull{}], Mod.Txt{"chat"}, "\"chat\""})] == [Mod.CFail{"Unknown model type \"text\". Use \"chat\", \"image\", or \"classifier\"."}, Mod.CFail{"Unknown model type undefined. Use \"chat\", \"image\", or \"classifier\"."}, Mod.CFail{"provider must be a string"}, Mod.CFail{"models.getModelOfType(type, provider, id) expects three strings, got (a string, a string). The provider and the id are separate arguments, for example models.getModelOfType(\"classifier\", \"typesafe\", \"jev-latest\")."}, Mod.COne{Mod.TChat{}}, Mod.CAvailable{Mod.TChat{}, False{}}] : List<&2, Mod.CAns>} &
  {[Mod.classify(Mod.Ctx{Mod.DUndef{}, Mod.DUndef{}, Mod.DUndef{}, [], Mod.DUndef{}, []}), Mod.classify(Mod.Ctx{Mod.DObj{["questions"]}, Mod.DUndef{}, Mod.DUndef{}, [], Mod.DObj{[]}, []}), Mod.classify(Mod.Ctx{Mod.DObj{["state", "images"]}, Mod.DObj{[]}, Mod.DObj{[]}, [], Mod.DUndef{}, []}), Mod.classify(Mod.Ctx{Mod.DObj{["state", "images"]}, Mod.DObj{[]}, Mod.DArr{False{}}, [Mod.Blk{Mod.DObj{["type", "data"]}, Mod.Txt{"image"}, Mod.DUndef{}, Mod.DStr{}, Mod.DUndef{}}], Mod.DUndef{}, []})] == [Some{String.concat(["models.classify() expects a context object as its second argument, got undefined. Expected context: ", shape_spec(), "."])}, Some{String.concat(["models.classify() context.state must be an object, got undefined. Expected context: ", shape_spec(), "."])}, Some{String.concat(["models.classify() context.images must be an array, got {}. Expected context: ", shape_spec(), "."])}, Some{String.concat(["models.classify() context.images[0] must be an image block, got { type, data }. Expected context: ", shape_spec(), "."])}] : List<&2, Maybe<&2, String>>} &
  {[Mod.classify(Mod.Ctx{Mod.DObj{["state", "questions"]}, Mod.DObj{[]}, Mod.DUndef{}, [], Mod.DObj{[]}, []}), Mod.classify(Mod.Ctx{Mod.DObj{["state", "questions"]}, Mod.DObj{[]}, Mod.DUndef{}, [], Mod.DObj{["q"]}, [Mod.Q{"q", Mod.DStr{}, Mod.DUndef{}, Mod.NoTxt{}, "undefined", Mod.DUndef{}, [], Mod.DUndef{}, Mod.DUndef{}}]}), Mod.classify(Mod.Ctx{Mod.DObj{["state", "questions"]}, Mod.DObj{[]}, Mod.DUndef{}, [], Mod.DObj{["q"]}, [Mod.Q{"q", Mod.DObj{["type"]}, Mod.DUndef{}, Mod.Txt{"bool"}, "\"bool\"", Mod.DUndef{}, [], Mod.DUndef{}, Mod.DUndef{}}]}), Mod.classify(Mod.Ctx{Mod.DObj{["state", "questions"]}, Mod.DObj{[]}, Mod.DUndef{}, [], Mod.DObj{["q"]}, [Mod.Q{"q", Mod.DObj{["type", "instructions", "criteria"]}, Mod.DStr{}, Mod.Txt{"choice"}, "\"choice\"", Mod.DObj{[]}, [], Mod.DUndef{}, Mod.DUndef{}}]})] == [Some{String.concat(["models.classify() context.questions must map question IDs to questions, got {}. Expected context: ", shape_spec(), "."])}, Some{String.concat(["models.classify() context.questions.q must be a question object, got a string. Expected context: ", shape_spec(), "."])}, Some{String.concat(["models.classify() context.questions.q.instructions must be a string. Expected context: ", shape_spec(), "."])}, Some{String.concat(["models.classify() context.questions.q is a \"choice\" question, so criteria must map each label to its meaning. Expected context: ", shape_spec(), "."])}] : List<&2, Maybe<&2, String>>} &
  {[Mod.classify(Mod.Ctx{Mod.DObj{["state", "questions"]}, Mod.DObj{[]}, Mod.DUndef{}, [], Mod.DObj{["q"]}, [Mod.Q{"q", Mod.DObj{["type", "instructions", "criteria"]}, Mod.DStr{}, Mod.Txt{"score"}, "\"score\"", Mod.DArr{False{}}, [Mod.DNum{}], Mod.DUndef{}, Mod.DUndef{}}]}), Mod.classify(Mod.Ctx{Mod.DObj{["state", "questions"]}, Mod.DObj{[]}, Mod.DUndef{}, [], Mod.DObj{["q"]}, [Mod.Q{"q", Mod.DObj{["type", "instructions", "criteria"]}, Mod.DStr{}, Mod.Txt{"bool"}, "\"bool\"", Mod.DObj{["true"]}, [Mod.DStr{}], Mod.DStr{}, Mod.DUndef{}}]}), Mod.classify(Mod.Ctx{Mod.DObj{["state", "questions"]}, Mod.DObj{[]}, Mod.DUndef{}, [], Mod.DObj{["q"]}, [Mod.Q{"q", Mod.DObj{["type", "instructions"]}, Mod.DStr{}, Mod.Txt{"rank"}, "\"rank\"", Mod.DUndef{}, [], Mod.DUndef{}, Mod.DUndef{}}]}), Mod.classify(Mod.Ctx{Mod.DObj{["state", "questions"]}, Mod.DObj{["x"]}, Mod.DUndef{}, [], Mod.DObj{["c", "s", "b"]}, [Mod.Q{"c", Mod.DObj{["type", "instructions", "criteria"]}, Mod.DStr{}, Mod.Txt{"choice"}, "\"choice\"", Mod.DObj{["a"]}, [Mod.DStr{}], Mod.DUndef{}, Mod.DUndef{}}, Mod.Q{"s", Mod.DObj{["type", "instructions", "criteria"]}, Mod.DStr{}, Mod.Txt{"score"}, "\"score\"", Mod.DArr{False{}}, [Mod.DStr{}, Mod.DStr{}], Mod.DUndef{}, Mod.DUndef{}}, Mod.Q{"b", Mod.DObj{["type", "instructions", "criteria"]}, Mod.DStr{}, Mod.Txt{"bool"}, "\"bool\"", Mod.DObj{["true", "false"]}, [Mod.DStr{}, Mod.DStr{}], Mod.DStr{}, Mod.DStr{}}]})] == [Some{String.concat(["models.classify() context.questions.q is a \"score\" question, so criteria must list the levels as strings, lowest first. Expected context: ", shape_spec(), "."])}, Some{String.concat(["models.classify() context.questions.q is a \"bool\" question, so criteria must be { true: string, false: string }. Expected context: ", shape_spec(), "."])}, Some{String.concat(["models.classify() context.questions.q.type must be \"choice\", \"score\", or \"bool\", got \"rank\". Expected context: ", shape_spec(), "."])}, None{}] : List<&2, Maybe<&2, String>>} &
  {[Mod.images(Mod.ICtx{Mod.DStr{}, Mod.DUndef{}, []}), Mod.images(Mod.ICtx{Mod.DObj{["prompt"]}, Mod.DUndef{}, []}), Mod.images(Mod.ICtx{Mod.DObj{["input"]}, Mod.DArr{True{}}, []}), Mod.images(Mod.ICtx{Mod.DObj{["input"]}, Mod.DArr{False{}}, [Mod.Blk{Mod.DObj{["type", "text"]}, Mod.Txt{"text"}, Mod.DStr{}, Mod.DUndef{}, Mod.DUndef{}}, Mod.Blk{Mod.DObj{["text"]}, Mod.NoTxt{}, Mod.DStr{}, Mod.DUndef{}, Mod.DUndef{}}]}), Mod.images(Mod.ICtx{Mod.DObj{["input"]}, Mod.DArr{False{}}, [Mod.Blk{Mod.DObj{["type", "text"]}, Mod.Txt{"text"}, Mod.DStr{}, Mod.DUndef{}, Mod.DUndef{}}, Mod.Blk{Mod.DObj{["type", "data", "mimeType"]}, Mod.Txt{"image"}, Mod.DUndef{}, Mod.DStr{}, Mod.DStr{}}]})] == [Some{"models.generateImages() expects a context object as its second argument, got a string. Expected context: { input: [{ type: \"text\", text: <prompt> }, ...optional { type: \"image\", data: <base64>, mimeType } references] }."}, Some{"models.generateImages() context.input must be a non-empty array of blocks, got undefined. Expected context: { input: [{ type: \"text\", text: <prompt> }, ...optional { type: \"image\", data: <base64>, mimeType } references] }."}, Some{"models.generateImages() context.input must be a non-empty array of blocks, got an empty array. Expected context: { input: [{ type: \"text\", text: <prompt> }, ...optional { type: \"image\", data: <base64>, mimeType } references] }."}, Some{"models.generateImages() context.input[1] must be a text or image block, got { text }. Expected context: { input: [{ type: \"text\", text: <prompt> }, ...optional { type: \"image\", data: <base64>, mimeType } references] }."}, None{}] : List<&2, Maybe<&2, String>>} &
  {[Mod.resolve(Mod.Res{Mod.CClassify{}, False{}, Mod.DObj{["provider", "id"]}, Mod.Txt{"faux"}, Mod.Txt{"faux-1"}, Some{Mod.TChat{}}, None{}, None{}}), Mod.resolve(Mod.Res{Mod.CClassify{}, False{}, Mod.DObj{["provider", "id"]}, Mod.Txt{"faux"}, Mod.Txt{"nope"}, None{}, None{}, None{}}), Mod.resolve(Mod.Res{Mod.CClassify{}, False{}, Mod.DUndef{}, Mod.NoTxt{}, Mod.NoTxt{}, None{}, None{}, None{}}), Mod.resolve(Mod.Res{Mod.CImages{}, False{}, Mod.DStr{}, Mod.NoTxt{}, Mod.NoTxt{}, None{}, None{}, None{}}), Mod.resolve(Mod.Res{Mod.CClassify{}, True{}, Mod.DNull{}, Mod.NoTxt{}, Mod.NoTxt{}, None{}, None{}, None{}})] == [Mod.RFail{"\"faux/faux-1\" is a chat model, not a classifier model. List the classifier models you can use with models.getAvailableOfType(\"classifier\")."}, Mod.RFail{"Unknown classifier model \"faux/nope\". List the classifier models you can use with models.getAvailableOfType(\"classifier\")."}, Mod.RFail{"models.classify() expects a classifier model as its first argument, got undefined. models.getModelOfType() returns undefined for an unknown provider or id. List the classifier models you can use with models.getAvailableOfType(\"classifier\")."}, Mod.RFail{"models.generateImages() expects an image model as its first argument, got a string. List the image models you can use with models.getAvailableOfType(\"image\")."}, Mod.RDefault{}] : List<&2, Mod.RAns>} &
  {[Mod.tool("models.classify"), Mod.tool("models.generateImages"), Mod.tool("models.getModelOfType")] == [Some{Mod.CClassify{}}, Some{Mod.CImages{}}, None{}] : List<&2, Maybe<&2, Mod.Call>>}
