# ffi_context_order: the entry of the compiled Bend core for what the
# model context of a conversation is made of (bend/context_order.bend;
# Rust: crates/eukhe-durable/src/harness/context.rs and
# compaction/range.rs through `eukhe_bend::rules::context_order`). The
# request is a question (crates/eukhe-bend/WIRE.md is the grammar):
#
#   Stop  0 pending | 1 stop | 2 length | 3 toolUse | 4 error | 5 aborted
#         | 6 deferred
#   Msg   0 user | 1 system | 2 assistant: Stop, List<Nat> (call ids)
#         | 3 result: Nat (its call id)
#   Role  0 user | 1 system | 2 assistant | 3 result
#   Edit  0 none | 1 omit | 2 replace: List<Msg>
#   Ent   Bool (head marker), Edit, List<Msg> (its own)
#   Add   Bool (carries edits), Bool (head marker), Bool (edited),
#         List<Msg> (its own)
#
#   tag 0 order:  List<Msg>              -> List<Step>
#   tag 1 derive: Bool (the first entry is the head marker), List<Ent>
#                 -> List<Part>, Plan
#   tag 2 extend: List<Add>, List<Msg> (the open messages)
#                 -> 0 (derive again) | 1 List<List<Nat>>, Plan
#   tag 3 lead:   List<Role>             -> Maybe<Nat>
#
#   Step  0 Nat (take message i) | 1 Nat, Nat (the missing result of the
#         assistant at i, call j)
#   Plan  Maybe<Nat> (split), Nat (settles), List<Step>
#   Part  Nat (the entry), Keep: 0 nothing | 1 List<Nat> (its own
#         messages at) | 2 List<Nat> (its Replace edit's messages at)
#
# Malformed input, or input left after the request, answers
# `E context_order: malformed request`, never a default. Pure: no IO, no
# @unsafe.

import Base
import ./wire.bend as W
import ./context_order.bend as Co

# A request of the entry
type Req is Data:
  QOrder{ms: List<&2, Co.Msg>}
  QDerive{mark: Bool, es: List<&2, Co.Ent>}
  QExtend{ads: List<&2, Co.Add>, open: List<&2, Co.Msg>}
  QLead{rs: List<&2, Co.Role>}

# Facts
# -----

def get_stop.tag(r: W.Dec<Nat>) -> W.Dec<Co.Stop>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Co.SPending{}, s}
        case 1n:
          W.Got{Co.SStop{}, s}
        case 2n:
          W.Got{Co.SLength{}, s}
        case 3n:
          W.Got{Co.SToolUse{}, s}
        case 4n:
          W.Got{Co.SError{}, s}
        case 5n:
          W.Got{Co.SAborted{}, s}
        case 6n:
          W.Got{Co.SDeferred{}, s}
        case 7n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_stop(s: String) -> W.Dec<Co.Stop>:
  get_stop.tag(W.get_nat(s))

def get_msg.calls(st: Co.Stop, r: W.Dec<List<&2, Nat>>) -> W.Dec<Co.Msg>:
  match r:
    case W.Got{cs, s}:
      W.Got{Co.MAsst{st, cs}, s}
    case W.Bad{}:
      W.Bad{}

def get_msg.stop(r: W.Dec<Co.Stop>) -> W.Dec<Co.Msg>:
  match r:
    case W.Got{st, s}:
      get_msg.calls(st, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_msg.res(r: W.Dec<Nat>) -> W.Dec<Co.Msg>:
  match r:
    case W.Got{c, s}:
      W.Got{Co.MRes{c}, s}
    case W.Bad{}:
      W.Bad{}

def get_msg.tag(r: W.Dec<Nat>) -> W.Dec<Co.Msg>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Co.MUser{}, s}
        case 1n:
          W.Got{Co.MSystem{}, s}
        case 2n:
          get_msg.stop(get_stop(s))
        case 3n:
          get_msg.res(W.get_nat(s))
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a message: its tag, then its stop reason and call ids, or its call id
def get_msg(s: String) -> W.Dec<Co.Msg>:
  get_msg.tag(W.get_nat(s))

def get_msgs(s: String) -> W.Dec<List<&2, Co.Msg>>:
  W.get_list(~Co.Msg, ~get_msg, s)

def get_role.tag(r: W.Dec<Nat>) -> W.Dec<Co.Role>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Co.RUser{}, s}
        case 1n:
          W.Got{Co.RSystem{}, s}
        case 2n:
          W.Got{Co.RAsst{}, s}
        case 3n:
          W.Got{Co.RRes{}, s}
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_role(s: String) -> W.Dec<Co.Role>:
  get_role.tag(W.get_nat(s))

def get_edit.ms(r: W.Dec<List<&2, Co.Msg>>) -> W.Dec<Co.Edit>:
  match r:
    case W.Got{ms, s}:
      W.Got{Co.Replace{ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_edit.tag(r: W.Dec<Nat>) -> W.Dec<Co.Edit>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Co.NoEdit{}, s}
        case 1n:
          W.Got{Co.Omit{}, s}
        case 2n:
          get_edit.ms(get_msgs(s))
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_edit(s: String) -> W.Dec<Co.Edit>:
  get_edit.tag(W.get_nat(s))

def get_ent.own(h: Bool, e: Co.Edit, r: W.Dec<List<&2, Co.Msg>>) -> W.Dec<Co.Ent>:
  match r:
    case W.Got{ms, s}:
      W.Got{Co.Ent{h, e, ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_ent.edit(h: Bool, r: W.Dec<Co.Edit>) -> W.Dec<Co.Ent>:
  match r:
    case W.Got{e, s}:
      get_ent.own(h, e, get_msgs(s))
    case W.Bad{}:
      W.Bad{}

def get_ent.head(r: W.Dec<Bool>) -> W.Dec<Co.Ent>:
  match r:
    case W.Got{h, s}:
      get_ent.edit(h, get_edit(s))
    case W.Bad{}:
      W.Bad{}

# an entry: whether it is a head marker, its edit, its own messages
def get_ent(s: String) -> W.Dec<Co.Ent>:
  get_ent.head(W.get_bool(s))

def get_add.own(x: Bool, h: Bool, d: Bool, r: W.Dec<List<&2, Co.Msg>>) -> W.Dec<Co.Add>:
  match r:
    case W.Got{ms, s}:
      W.Got{Co.Add{x, h, d, ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_add.edited(x: Bool, h: Bool, r: W.Dec<Bool>) -> W.Dec<Co.Add>:
  match r:
    case W.Got{d, s}:
      get_add.own(x, h, d, get_msgs(s))
    case W.Bad{}:
      W.Bad{}

def get_add.head(x: Bool, r: W.Dec<Bool>) -> W.Dec<Co.Add>:
  match r:
    case W.Got{h, s}:
      get_add.edited(x, h, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_add.edits(r: W.Dec<Bool>) -> W.Dec<Co.Add>:
  match r:
    case W.Got{x, s}:
      get_add.head(x, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

# an added entry: whether it carries edits, is a head marker, was
# edited, then its own messages
def get_add(s: String) -> W.Dec<Co.Add>:
  get_add.edits(W.get_bool(s))

# Requests
# --------

def get_order(r: W.Dec<List<&2, Co.Msg>>) -> W.Dec<Req>:
  match r:
    case W.Got{ms, s}:
      W.Got{QOrder{ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_derive.es(m: Bool, r: W.Dec<List<&2, Co.Ent>>) -> W.Dec<Req>:
  match r:
    case W.Got{es, s}:
      W.Got{QDerive{m, es}, s}
    case W.Bad{}:
      W.Bad{}

def get_derive(r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      get_derive.es(m, W.get_list(~Co.Ent, ~get_ent, s))
    case W.Bad{}:
      W.Bad{}

def get_extend.open(ads: List<&2, Co.Add>, r: W.Dec<List<&2, Co.Msg>>) -> W.Dec<Req>:
  match r:
    case W.Got{ms, s}:
      W.Got{QExtend{ads, ms}, s}
    case W.Bad{}:
      W.Bad{}

def get_extend(r: W.Dec<List<&2, Co.Add>>) -> W.Dec<Req>:
  match r:
    case W.Got{ads, s}:
      get_extend.open(ads, get_msgs(s))
    case W.Bad{}:
      W.Bad{}

def get_lead(r: W.Dec<List<&2, Co.Role>>) -> W.Dec<Req>:
  match r:
    case W.Got{rs, s}:
      W.Got{QLead{rs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_order(get_msgs(s))
        case 1n:
          get_derive(W.get_bool(s))
        case 2n:
          get_extend(W.get_list(~Co.Add, ~get_add, s))
        case 3n:
          get_lead(W.get_list(~Co.Role, ~get_role, s))
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# a request: its tag, then its question
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# Replies
# -------

def put_step(x: Co.Step, rest: String) -> String:
  match x:
    case Co.Take{i}:
      W.put_nat(0n, W.put_nat(i, rest))
    case Co.Miss{i, j}:
      W.put_nat(1n, W.put_nat(i, W.put_nat(j, rest)))

def put_steps.items(xs: List<&2, Co.Step>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      put_step(x, put_steps.items(t, rest))

def put_steps(+xs: List<&2, Co.Step>, rest: String) -> String:
  W.put_nat(List.length(&2, Co.Step, xs), put_steps.items(xs, rest))

def put_nats.items(xs: List<&2, Nat>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      W.put_nat(x, put_nats.items(t, rest))

def put_nats(+xs: List<&2, Nat>, rest: String) -> String:
  W.put_nat(List.length(&2, Nat, xs), put_nats.items(xs, rest))

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_plan(p: Co.Plan, rest: String) -> String:
  match p:
    case Co.Plan{sp, n, xs}:
      put_mnat(sp, W.put_nat(n, put_steps(xs, rest)))

def put_keep(k: Co.Keep, rest: String) -> String:
  match k:
    case Co.Omitted{}:
      W.put_nat(0n, rest)
    case Co.Own{js}:
      W.put_nat(1n, put_nats(js, rest))
    case Co.Alt{js}:
      W.put_nat(2n, put_nats(js, rest))

def put_part(p: Co.Part, rest: String) -> String:
  match p:
    case Co.Part{i, k}:
      W.put_nat(i, put_keep(k, rest))

def put_parts.items(xs: List<&2, Co.Part>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      put_part(x, put_parts.items(t, rest))

def put_derived(d: Co.Derived) -> String:
  match d:
    case Co.Derived{+ps, p}:
      W.put_nat(List.length(&2, Co.Part, ps), put_parts.items(ps, put_plan(p, "")))

def put_keeps.items(xs: List<&2, List<&2, Nat>>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      put_nats(x, put_keeps.items(t, rest))

def put_extended(x: Co.Extended) -> String:
  match x:
    case Co.Rederive{}:
      W.put_nat(0n, "")
    case Co.Extended{+ks, p}:
      W.put_nat(1n, W.put_nat(List.length(&2, List<&2, Nat>, ks), put_keeps.items(ks, put_plan(p, ""))))

# the answer to a request
def answer(q: Req) -> String:
  match q:
    case QOrder{ms}:
      put_steps(Co.order(ms), "")
    case QDerive{m, es}:
      put_derived(Co.derive(m, es))
    case QExtend{ads, open}:
      put_extended(Co.extend(ads, open))
    case QLead{rs}:
      put_mnat(Co.lead(rs), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("context_order: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("context_order: malformed request")

# the entry: decode the request, answer it
def ffi(input: String) -> String:
  ffi.got(get_req(input))
