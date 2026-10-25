# ffi_codemode_models: the entry of the compiled Bend core for what code
# mode scripts get wrong when they call the `models.*` globals, and the
# texts of those calls (bend/codemode_models.bend; Rust:
# crates/eukhe-durable/src/codemode/models.rs and call.rs through
# `eukhe_bend::rules::codemode_models`). The request is a question
# (crates/eukhe-bend/WIRE.md is the grammar):
#
#   Desc   0 (absent) | 1 (null) | 2 (a boolean) | 3 (a number) |
#          4 (a string) | 5 Bool (an array: empty) |
#          6 List<String> (an object: its keys in order)
#   Txt    0 (no string) | 1 String (a string's text)
#   Blk    Desc (the item), Txt (`type`), Desc (`text`), Desc (`data`),
#          Desc (`mimeType`)
#   Q      String (the id), Desc (the question), Desc (`instructions`),
#          Txt (`type`), String (`type`'s JSON text), Desc (`criteria`),
#          List<Desc> (the criteria's values or items), Desc (`true`),
#          Desc (`false`)
#   MType  0 chat | 1 image | 2 classifier;  Call  0 classify | 1 images
#   Found  0 (none) | 1 MType (the type of the model found)
#
#   tag 0 classify: Desc (context), Desc (`state`), Desc (`images`),
#         List<Blk> (its items), Desc (`questions`), List<Q> (its
#         questions) -> 0 (fine) | 1 String (the error)
#   tag 1 images: Desc (context), Desc (`input`), List<Blk> (its items)
#         -> 0 | 1 String
#   tag 2 resolve: Call, Bool (a default classifier), Desc (the model),
#         Txt (`provider`), Txt (`id`), Found (chat), Found (image),
#         Found (classifier) -> 0 String (the error) | 1 (the default) |
#         2 (the model found)
#   tag 3 catalog: String (the global), List<Desc> (the arguments), Txt
#         (the first argument), String (its JSON text) -> 0 String (the
#         error) | 1 MType Bool (list, provider given) | 2 MType Bool
#         (list with auth, provider given) | 3 MType (get one)
#   tag 4 tool: String (a global) -> 0 (none) | 1 Call
#   tag 5 result: Call, String (provider), String (id), String (the stop
#         reason), Txt (the error message) -> Bool (ok), String (the text)
#   tag 6 unread: Call, String (serde's error) -> String
#   tag 7 cap: (nothing) -> Nat (the model calls of one script that run at
#         once)
#
# Malformed input, or input left after the request, answers
# `E codemode_models: malformed request`, never a default. Pure: no IO, no
# @unsafe.

import Base
import ./wire.bend as W
import ./codemode_models.bend as Mod

# A request of the entry
type Req is Data:
  QClassify{x: Mod.Ctx}
  QImages{x: Mod.ICtx}
  QResolve{x: Mod.Res}
  QCatalog{x: Mod.Cat}
  QTool{g: String}
  QResult{c: Mod.Call, p: String, i: String, stop: String, error: Mod.Txt}
  QUnread{c: Mod.Call, error: String}
  QCap{}

# Facts
# -----

def get_desc.empty(r: W.Dec<Bool>) -> W.Dec<Mod.Desc>:
  match r:
    case W.Got{e, s}:
      W.Got{Mod.DArr{e}, s}
    case W.Bad{}:
      W.Bad{}

def get_desc.keys(r: W.Dec<List<&2, String>>) -> W.Dec<Mod.Desc>:
  match r:
    case W.Got{ks, s}:
      W.Got{Mod.DObj{ks}, s}
    case W.Bad{}:
      W.Bad{}

def get_desc.tag(r: W.Dec<Nat>) -> W.Dec<Mod.Desc>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Mod.DUndef{}, s}
        case 1n:
          W.Got{Mod.DNull{}, s}
        case 2n:
          W.Got{Mod.DBool{}, s}
        case 3n:
          W.Got{Mod.DNum{}, s}
        case 4n:
          W.Got{Mod.DStr{}, s}
        case 5n:
          get_desc.empty(W.get_bool(s))
        case 6n:
          get_desc.keys(W.get_list(~String, ~W.get_str, s))
        case 7n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a value as the checks read it
def get_desc(s: String) -> W.Dec<Mod.Desc>:
  get_desc.tag(W.get_nat(s))

def get_txt.text(r: W.Dec<String>) -> W.Dec<Mod.Txt>:
  match r:
    case W.Got{a, s}:
      W.Got{Mod.Txt{a}, s}
    case W.Bad{}:
      W.Bad{}

def get_txt.tag(r: W.Dec<Nat>) -> W.Dec<Mod.Txt>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Mod.NoTxt{}, s}
        case 1n:
          get_txt.text(W.get_str(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a string's text, if the value is one
def get_txt(s: String) -> W.Dec<Mod.Txt>:
  get_txt.tag(W.get_nat(s))

def get_blk.mime(k: Mod.Desc, t: Mod.Txt, x: Mod.Desc, d: Mod.Desc, r: W.Dec<Mod.Desc>) -> W.Dec<Mod.Blk>:
  match r:
    case W.Got{m, s}:
      W.Got{Mod.Blk{k, t, x, d, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_blk.data(k: Mod.Desc, t: Mod.Txt, x: Mod.Desc, r: W.Dec<Mod.Desc>) -> W.Dec<Mod.Blk>:
  match r:
    case W.Got{d, s}:
      get_blk.mime(k, t, x, d, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_blk.text(k: Mod.Desc, t: Mod.Txt, r: W.Dec<Mod.Desc>) -> W.Dec<Mod.Blk>:
  match r:
    case W.Got{x, s}:
      get_blk.data(k, t, x, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_blk.kind(k: Mod.Desc, r: W.Dec<Mod.Txt>) -> W.Dec<Mod.Blk>:
  match r:
    case W.Got{t, s}:
      get_blk.text(k, t, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_blk.block(r: W.Dec<Mod.Desc>) -> W.Dec<Mod.Blk>:
  match r:
    case W.Got{k, s}:
      get_blk.kind(k, get_txt(s))
    case W.Bad{}:
      W.Bad{}

# an item of `images` or `input`
def get_blk(s: String) -> W.Dec<Mod.Blk>:
  get_blk.block(get_desc(s))

def get_q.no(id: String, q: Mod.Desc, ins: Mod.Desc, kind: Mod.Txt, json: String, c: Mod.Desc, vs: List<&2, Mod.Desc>, yes: Mod.Desc, r: W.Dec<Mod.Desc>) -> W.Dec<Mod.Q>:
  match r:
    case W.Got{no, s}:
      W.Got{Mod.Q{id, q, ins, kind, json, c, vs, yes, no}, s}
    case W.Bad{}:
      W.Bad{}

def get_q.yes(id: String, q: Mod.Desc, ins: Mod.Desc, kind: Mod.Txt, json: String, c: Mod.Desc, vs: List<&2, Mod.Desc>, r: W.Dec<Mod.Desc>) -> W.Dec<Mod.Q>:
  match r:
    case W.Got{yes, s}:
      get_q.no(id, q, ins, kind, json, c, vs, yes, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_q.values(id: String, q: Mod.Desc, ins: Mod.Desc, kind: Mod.Txt, json: String, c: Mod.Desc, r: W.Dec<List<&2, Mod.Desc>>) -> W.Dec<Mod.Q>:
  match r:
    case W.Got{vs, s}:
      get_q.yes(id, q, ins, kind, json, c, vs, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_q.criteria(id: String, q: Mod.Desc, ins: Mod.Desc, kind: Mod.Txt, json: String, r: W.Dec<Mod.Desc>) -> W.Dec<Mod.Q>:
  match r:
    case W.Got{c, s}:
      get_q.values(id, q, ins, kind, json, c, W.get_list(~Mod.Desc, ~get_desc, s))
    case W.Bad{}:
      W.Bad{}

def get_q.json(id: String, q: Mod.Desc, ins: Mod.Desc, kind: Mod.Txt, r: W.Dec<String>) -> W.Dec<Mod.Q>:
  match r:
    case W.Got{json, s}:
      get_q.criteria(id, q, ins, kind, json, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_q.kind(id: String, q: Mod.Desc, ins: Mod.Desc, r: W.Dec<Mod.Txt>) -> W.Dec<Mod.Q>:
  match r:
    case W.Got{kind, s}:
      get_q.json(id, q, ins, kind, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_q.ins(id: String, q: Mod.Desc, r: W.Dec<Mod.Desc>) -> W.Dec<Mod.Q>:
  match r:
    case W.Got{ins, s}:
      get_q.kind(id, q, ins, get_txt(s))
    case W.Bad{}:
      W.Bad{}

def get_q.q(id: String, r: W.Dec<Mod.Desc>) -> W.Dec<Mod.Q>:
  match r:
    case W.Got{q, s}:
      get_q.ins(id, q, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_q.id(r: W.Dec<String>) -> W.Dec<Mod.Q>:
  match r:
    case W.Got{id, s}:
      get_q.q(id, get_desc(s))
    case W.Bad{}:
      W.Bad{}

# a question of `questions`
def get_q(s: String) -> W.Dec<Mod.Q>:
  get_q.id(W.get_str(s))

def get_mtype.tag(r: W.Dec<Nat>) -> W.Dec<Mod.MType>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Mod.TChat{}, s}
        case 1n:
          W.Got{Mod.TImage{}, s}
        case 2n:
          W.Got{Mod.TClassifier{}, s}
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a model type
def get_mtype(s: String) -> W.Dec<Mod.MType>:
  get_mtype.tag(W.get_nat(s))

def get_found.some(r: W.Dec<Mod.MType>) -> W.Dec<Maybe<&2, Mod.MType>>:
  match r:
    case W.Got{t, s}:
      W.Got{Some{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_found.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Mod.MType>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_found.some(get_mtype(s))
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the type of the model the catalog finds, if any
def get_found(s: String) -> W.Dec<Maybe<&2, Mod.MType>>:
  get_found.tag(W.get_nat(s))

def get_call.tag(r: W.Dec<Nat>) -> W.Dec<Mod.Call>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Mod.CClassify{}, s}
        case 1n:
          W.Got{Mod.CImages{}, s}
        case 2n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a model call
def get_call(s: String) -> W.Dec<Mod.Call>:
  get_call.tag(W.get_nat(s))

# Requests
# --------

def get_classify.qs(c: Mod.Desc, st: Mod.Desc, im: Mod.Desc, bs: List<&2, Mod.Blk>, qd: Mod.Desc, r: W.Dec<List<&2, Mod.Q>>) -> W.Dec<Req>:
  match r:
    case W.Got{qs, s}:
      W.Got{QClassify{Mod.Ctx{c, st, im, bs, qd, qs}}, s}
    case W.Bad{}:
      W.Bad{}

def get_classify.questions(c: Mod.Desc, st: Mod.Desc, im: Mod.Desc, bs: List<&2, Mod.Blk>, r: W.Dec<Mod.Desc>) -> W.Dec<Req>:
  match r:
    case W.Got{qd, s}:
      get_classify.qs(c, st, im, bs, qd, W.get_list(~Mod.Q, ~get_q, s))
    case W.Bad{}:
      W.Bad{}

def get_classify.blocks(c: Mod.Desc, st: Mod.Desc, im: Mod.Desc, r: W.Dec<List<&2, Mod.Blk>>) -> W.Dec<Req>:
  match r:
    case W.Got{bs, s}:
      get_classify.questions(c, st, im, bs, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_classify.images(c: Mod.Desc, st: Mod.Desc, r: W.Dec<Mod.Desc>) -> W.Dec<Req>:
  match r:
    case W.Got{im, s}:
      get_classify.blocks(c, st, im, W.get_list(~Mod.Blk, ~get_blk, s))
    case W.Bad{}:
      W.Bad{}

def get_classify.state(c: Mod.Desc, r: W.Dec<Mod.Desc>) -> W.Dec<Req>:
  match r:
    case W.Got{st, s}:
      get_classify.images(c, st, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_classify(r: W.Dec<Mod.Desc>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_classify.state(c, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_images.blocks(c: Mod.Desc, i: Mod.Desc, r: W.Dec<List<&2, Mod.Blk>>) -> W.Dec<Req>:
  match r:
    case W.Got{bs, s}:
      W.Got{QImages{Mod.ICtx{c, i, bs}}, s}
    case W.Bad{}:
      W.Bad{}

def get_images.input(c: Mod.Desc, r: W.Dec<Mod.Desc>) -> W.Dec<Req>:
  match r:
    case W.Got{i, s}:
      get_images.blocks(c, i, W.get_list(~Mod.Blk, ~get_blk, s))
    case W.Bad{}:
      W.Bad{}

def get_images(r: W.Dec<Mod.Desc>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_images.input(c, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_resolve.classifier(c: Mod.Call, d: Bool, m: Mod.Desc, p: Mod.Txt, i: Mod.Txt, fc: Maybe<&2, Mod.MType>, fi: Maybe<&2, Mod.MType>, r: W.Dec<Maybe<&2, Mod.MType>>) -> W.Dec<Req>:
  match r:
    case W.Got{fk, s}:
      W.Got{QResolve{Mod.Res{c, d, m, p, i, fc, fi, fk}}, s}
    case W.Bad{}:
      W.Bad{}

def get_resolve.image(c: Mod.Call, d: Bool, m: Mod.Desc, p: Mod.Txt, i: Mod.Txt, fc: Maybe<&2, Mod.MType>, r: W.Dec<Maybe<&2, Mod.MType>>) -> W.Dec<Req>:
  match r:
    case W.Got{fi, s}:
      get_resolve.classifier(c, d, m, p, i, fc, fi, get_found(s))
    case W.Bad{}:
      W.Bad{}

def get_resolve.chat(c: Mod.Call, d: Bool, m: Mod.Desc, p: Mod.Txt, i: Mod.Txt, r: W.Dec<Maybe<&2, Mod.MType>>) -> W.Dec<Req>:
  match r:
    case W.Got{fc, s}:
      get_resolve.image(c, d, m, p, i, fc, get_found(s))
    case W.Bad{}:
      W.Bad{}

def get_resolve.id(c: Mod.Call, d: Bool, m: Mod.Desc, p: Mod.Txt, r: W.Dec<Mod.Txt>) -> W.Dec<Req>:
  match r:
    case W.Got{i, s}:
      get_resolve.chat(c, d, m, p, i, get_found(s))
    case W.Bad{}:
      W.Bad{}

def get_resolve.provider(c: Mod.Call, d: Bool, m: Mod.Desc, r: W.Dec<Mod.Txt>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      get_resolve.id(c, d, m, p, get_txt(s))
    case W.Bad{}:
      W.Bad{}

def get_resolve.model(c: Mod.Call, d: Bool, r: W.Dec<Mod.Desc>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      get_resolve.provider(c, d, m, get_txt(s))
    case W.Bad{}:
      W.Bad{}

def get_resolve.default(c: Mod.Call, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      get_resolve.model(c, d, get_desc(s))
    case W.Bad{}:
      W.Bad{}

def get_resolve(r: W.Dec<Mod.Call>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_resolve.default(c, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_catalog.json(n: String, a: List<&2, Mod.Desc>, k: Mod.Txt, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{j, s}:
      W.Got{QCatalog{Mod.Cat{n, a, k, j}}, s}
    case W.Bad{}:
      W.Bad{}

def get_catalog.kind(n: String, a: List<&2, Mod.Desc>, r: W.Dec<Mod.Txt>) -> W.Dec<Req>:
  match r:
    case W.Got{k, s}:
      get_catalog.json(n, a, k, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_catalog.args(n: String, r: W.Dec<List<&2, Mod.Desc>>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      get_catalog.kind(n, a, get_txt(s))
    case W.Bad{}:
      W.Bad{}

def get_catalog(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_catalog.args(n, W.get_list(~Mod.Desc, ~get_desc, s))
    case W.Bad{}:
      W.Bad{}

def get_tool(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{g, s}:
      W.Got{QTool{g}, s}
    case W.Bad{}:
      W.Bad{}

def get_result.error(c: Mod.Call, p: String, i: String, st: String, r: W.Dec<Mod.Txt>) -> W.Dec<Req>:
  match r:
    case W.Got{e, s}:
      W.Got{QResult{c, p, i, st, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_result.stop(c: Mod.Call, p: String, i: String, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{st, s}:
      get_result.error(c, p, i, st, get_txt(s))
    case W.Bad{}:
      W.Bad{}

def get_result.id(c: Mod.Call, p: String, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{i, s}:
      get_result.stop(c, p, i, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_result.provider(c: Mod.Call, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      get_result.id(c, p, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_result(r: W.Dec<Mod.Call>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_result.provider(c, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_unread.error(c: Mod.Call, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{e, s}:
      W.Got{QUnread{c, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_unread(r: W.Dec<Mod.Call>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_unread.error(c, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_classify(get_desc(s))
        case 1n:
          get_images(get_desc(s))
        case 2n:
          get_resolve(get_call(s))
        case 3n:
          get_catalog(W.get_str(s))
        case 4n:
          get_tool(W.get_str(s))
        case 5n:
          get_result(get_call(s))
        case 6n:
          get_unread(get_call(s))
        case 7n:
          W.Got{QCap{}, s}
        case 8n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a request: its tag, then its question
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# Replies
# -------

def put_problem(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{t}:
      W.put_nat(1n, W.put_str(t, ""))

def put_mtype(t: Mod.MType, rest: String) -> String:
  match t:
    case Mod.TChat{}:
      W.put_nat(0n, rest)
    case Mod.TImage{}:
      W.put_nat(1n, rest)
    case Mod.TClassifier{}:
      W.put_nat(2n, rest)

def put_call(c: Mod.Call, rest: String) -> String:
  match c:
    case Mod.CClassify{}:
      W.put_nat(0n, rest)
    case Mod.CImages{}:
      W.put_nat(1n, rest)

def put_rans(a: Mod.RAns) -> String:
  match a:
    case Mod.RFail{t}:
      W.put_nat(0n, W.put_str(t, ""))
    case Mod.RDefault{}:
      W.put_nat(1n, "")
    case Mod.RFound{}:
      W.put_nat(2n, "")

def put_cans(a: Mod.CAns) -> String:
  match a:
    case Mod.CFail{t}:
      W.put_nat(0n, W.put_str(t, ""))
    case Mod.CModels{t, g}:
      W.put_nat(1n, put_mtype(t, W.put_bool(g, "")))
    case Mod.CAvailable{t, g}:
      W.put_nat(2n, put_mtype(t, W.put_bool(g, "")))
    case Mod.COne{t}:
      W.put_nat(3n, put_mtype(t, ""))

def put_tool(m: Maybe<&2, Mod.Call>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{c}:
      W.put_nat(1n, put_call(c, ""))

def put_result(r: Bool & String) -> String:
  match r:
    case (ok, t):
      W.put_bool(ok, W.put_str(t, ""))

# the answer to a request
def answer(q: Req) -> String:
  match q:
    case QClassify{x}:
      put_problem(Mod.classify(x))
    case QImages{x}:
      put_problem(Mod.images(x))
    case QResolve{x}:
      put_rans(Mod.resolve(x))
    case QCatalog{x}:
      put_cans(Mod.catalog(x))
    case QTool{g}:
      put_tool(Mod.tool(g))
    case QResult{c, p, i, st, e}:
      put_result(Mod.result(c, p, i, st, e))
    case QUnread{c, e}:
      W.put_str(Mod.unread(c, e), "")
    case QCap{}:
      W.put_nat(Mod.max_calls(), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("codemode_models: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("codemode_models: malformed request")

# the entry: decode the request, answer it
def ffi(input: String) -> String:
  ffi.got(get_req(input))
