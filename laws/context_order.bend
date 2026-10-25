# eukhe: the laws of area context_order

import Base
import ../bend/context_order.bend as Co
import ../bend/ffi_context_order.bend as FCo
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1-R6): what the model context of one conversation is made of
# (bend/context_order.bend, the port of eukhe-durable harness/context.rs:
# `order_tool_results`, `settle`, `lead_with_system`, `select_active`,
# `contribute` with `is_excluded`, and `extend_range`'s test). Each law
# is an open claim about Co.order, Co.plan, Co.lead, Co.derive or
# Co.extend; PROOF.bend proves them (as ContextOrder.<law>) with the
# lemmas of proof/context_order/.
#
# The host sends message facts: a user message, a system message, an
# assistant answer (its stop reason and its tool calls' ids, in order),
# a tool result (its call's id); call ids are interned to Nats (equal
# ids, equal Nats). Ids are free: every law holds for every assignment,
# repeated ids included.
#
# R1: the order of messages: every message that is not a tool result
#     stays, in order; right after an assistant come its calls' results
#     in call order: the result of a call is the first tool result for
#     its id after the assistant and before the next assistant (Take of
#     its index), and a call with none gets the missing result (Miss of
#     the assistant's index and the call's position); every other tool
#     result is dropped.
# R2: the split: the index of the last assistant, when it is not the
#     first message (none without an assistant or when it is first);
#     the plan answers the order of all the messages, the split and how
#     many ordered messages the messages before the split give.
#     The order of a sequence is the order of its first part followed
#     by the order of the rest (indices shifted by the first part's
#     length) whenever the rest starts with an assistant: the host keeps
#     the ordered messages before the split and orders only the rest
#     again later.
# R3: lead: when the messages that precede the first message that is
#     not a user message are users only, there is at least one, and it
#     is a system message, it moves to the front (its index); else none.
# R4: contribution: an entry whose newest edit omits it contributes
#     nothing; one whose newest edit replaces its messages contributes
#     the replacement's messages; any other its own; always without the
#     assistant answers that stopped as error, aborted or deferred (the
#     indices of those that stay, in order).
# R5: derive: with a head marker (the first entry of the question), the
#     active entries are the marker, then every later entry that is not
#     a head marker; without one, every entry; each with its
#     contribution; and the plan of their contributed messages in order.
# R6: extend: the range derives again when an added entry carries
#     edits, is a head marker, or is the target of an edit of the range;
#     else each added entry keeps its own messages as R4 says for no
#     edit, and the plan of the open messages followed by theirs.

# Terms
# -----

def first_res.hit(b: Bool, k: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{k}
    case False{}:
      rest

# R1: the index of the first tool result for the call id c among ms (the
# first at index k), none past the next assistant
def first_res(ms: List<&2, Co.Msg>, +k: Nat, +c: Nat) -> Maybe<&2, Nat>:
  match ms:
    case Nil{}:
      None{}
    case m <> t:
      match m:
        case Co.MUser{}:
          first_res(t, 1n+k, c)
        case Co.MSystem{}:
          first_res(t, 1n+k, c)
        case Co.MAsst{s, cs}:
          None{}
        case Co.MRes{d}:
          first_res.hit(Nat.is_eq(d, c), k, first_res(t, 1n+k, c))

def call_step(r: Maybe<&2, Nat>, i: Nat, j: Nat) -> Co.Step:
  match r:
    case None{}:
      Co.Miss{i, j}
    case Some{k}:
      Co.Take{k}

# R1: the results of the calls cs (the first is call j) of the assistant
# at index i, followed by the messages t
def calls_spec(cs: List<&2, Nat>, +t: List<&2, Co.Msg>, +i: Nat, +j: Nat) -> List<&2, Co.Step>:
  match cs:
    case Nil{}:
      []
    case c <> u:
      call_step(first_res(t, 1n+i, c), i, j) <> calls_spec(u, t, i, 1n+j)

# R1: the order of ms, the first at index i
def order_spec.go(ms: List<&2, Co.Msg>, +i: Nat) -> List<&2, Co.Step>:
  match ms:
    case Nil{}:
      []
    case m <> +t:
      match m:
        case Co.MUser{}:
          Co.Take{i} <> order_spec.go(t, 1n+i)
        case Co.MSystem{}:
          Co.Take{i} <> order_spec.go(t, 1n+i)
        case Co.MAsst{s, cs}:
          Co.Take{i} <> List.append(&2, Co.Step, calls_spec(cs, t, i, 0n), order_spec.go(t, 1n+i))
        case Co.MRes{c}:
          order_spec.go(t, 1n+i)

# R1: the order of the messages ms
def order_spec(ms: List<&2, Co.Msg>) -> List<&2, Co.Step>:
  order_spec.go(ms, 0n)

def shift_step(+n: Nat, x: Co.Step) -> Co.Step:
  match x:
    case Co.Take{k}:
      Co.Take{Nat.add(n, k)}
    case Co.Miss{i, j}:
      Co.Miss{Nat.add(n, i), j}

# the steps xs with every index moved up by n
def shift(+n: Nat, xs: List<&2, Co.Step>) -> List<&2, Co.Step>:
  match xs:
    case Nil{}:
      []
    case x <> t:
      shift_step(n, x) <> shift(n, t)

# ms starts with an assistant
def starts_asst(ms: List<&2, Co.Msg>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case m <> t:
      match m:
        case Co.MUser{}:
          False{}
        case Co.MSystem{}:
          False{}
        case Co.MAsst{s, cs}:
          True{}
        case Co.MRes{c}:
          False{}

def is_asst(m: Co.Msg) -> Bool:
  match m:
    case Co.MUser{}:
      False{}
    case Co.MSystem{}:
      False{}
    case Co.MAsst{s, cs}:
      True{}
    case Co.MRes{c}:
      False{}

def last_spec.here(b: Bool, i: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{i}
    case False{}:
      None{}

def last_spec.pick(r: Maybe<&2, Nat>, b: Bool, i: Nat) -> Maybe<&2, Nat>:
  match r:
    case None{}:
      last_spec.here(b, i)
    case Some{k}:
      Some{k}

# R2: the index of the last assistant of ms (the first at index i)
def last_spec(ms: List<&2, Co.Msg>, +i: Nat) -> Maybe<&2, Nat>:
  match ms:
    case Nil{}:
      None{}
    case m <> t:
      last_spec.pick(last_spec(t, 1n+i), is_asst(m), i)

def split_spec.pos(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      match k:
        case 0n:
          None{}
        case 1n+p:
          Some{1n+p}

# R2: the split of ms
def split_spec(ms: List<&2, Co.Msg>) -> Maybe<&2, Nat>:
  split_spec.pos(last_spec(ms, 0n))

# the first n messages of ms
def prefix(n: Nat, ms: List<&2, Co.Msg>) -> List<&2, Co.Msg>:
  match n:
    case 0n:
      []
    case 1n+p:
      match ms:
        case Nil{}:
          []
        case m <> t:
          m <> prefix(p, t)

def plan_spec.at(sp: Maybe<&2, Nat>, +ms: List<&2, Co.Msg>) -> Co.Plan:
  match sp:
    case None{}:
      Co.Plan{None{}, 0n, order_spec(ms)}
    case Some{+k}:
      Co.Plan{Some{k}, List.length(&2, Co.Step, order_spec(prefix(k, ms))), order_spec(ms)}

# R2: the plan of ms
def plan_spec(+ms: List<&2, Co.Msg>) -> Co.Plan:
  plan_spec.at(split_spec(ms), ms)

# R3: how many user messages lead rs
def users(rs: List<&2, Co.Role>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case r <> t:
      match r:
        case Co.RUser{}:
          1n+users(t)
        case Co.RSystem{}:
          0n
        case Co.RAsst{}:
          0n
        case Co.RRes{}:
          0n

# R3: the message at index n of rs is a system message
def is_system(r: Co.Role) -> Bool:
  match r:
    case Co.RUser{}:
      False{}
    case Co.RSystem{}:
      True{}
    case Co.RAsst{}:
      False{}
    case Co.RRes{}:
      False{}

def system_at(n: Nat, rs: List<&2, Co.Role>) -> Bool:
  match n:
    case 0n:
      match rs:
        case Nil{}:
          False{}
        case r <> t:
          is_system(r)
    case 1n+p:
      match rs:
        case Nil{}:
          False{}
        case r <> t:
          system_at(p, t)

def lead_spec.sys(b: Bool, n: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{n}
    case False{}:
      None{}

def lead_spec.at(+n: Nat, +rs: List<&2, Co.Role>) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+p:
      lead_spec.sys(system_at(1n+p, rs), 1n+p)

# R3: the index of the system message that moves to the front of rs
def lead_spec(+rs: List<&2, Co.Role>) -> Maybe<&2, Nat>:
  lead_spec.at(users(rs), rs)

# R4: the answers that stop as error, aborted or deferred leave context
def gone_spec(s: Co.Stop) -> Bool:
  match s:
    case Co.SPending{}:
      False{}
    case Co.SStop{}:
      False{}
    case Co.SLength{}:
      False{}
    case Co.SToolUse{}:
      False{}
    case Co.SError{}:
      True{}
    case Co.SAborted{}:
      True{}
    case Co.SDeferred{}:
      True{}

def stays(m: Co.Msg) -> Bool:
  match m:
    case Co.MUser{}:
      True{}
    case Co.MSystem{}:
      True{}
    case Co.MAsst{s, cs}:
      Bool.not(gone_spec(s))
    case Co.MRes{c}:
      True{}

def stay_idx.one(b: Bool, j: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      j <> rest
    case False{}:
      rest

# R4: the indices of the messages of ms (the first at index j) that stay
def stay_idx(ms: List<&2, Co.Msg>, +j: Nat) -> List<&2, Nat>:
  match ms:
    case Nil{}:
      []
    case m <> t:
      stay_idx.one(stays(m), j, stay_idx(t, 1n+j))

def stay_msgs.one(b: Bool, m: Co.Msg, rest: List<&2, Co.Msg>) -> List<&2, Co.Msg>:
  match b:
    case True{}:
      m <> rest
    case False{}:
      rest

# R4: the messages of ms that stay
def stay_msgs(ms: List<&2, Co.Msg>) -> List<&2, Co.Msg>:
  match ms:
    case Nil{}:
      []
    case +m <> t:
      stay_msgs.one(stays(m), m, stay_msgs(t))

# R4: what an entry with the edit e and its own messages contributes
def keep_spec(e: Co.Edit, own: List<&2, Co.Msg>) -> Co.Keep:
  match e:
    case Co.NoEdit{}:
      Co.Own{stay_idx(own, 0n)}
    case Co.Omit{}:
      Co.Omitted{}
    case Co.Replace{ms}:
      Co.Alt{stay_idx(ms, 0n)}

# R4: the messages an entry with the edit e and its own messages
# contributes
def given_spec(e: Co.Edit, own: List<&2, Co.Msg>) -> List<&2, Co.Msg>:
  match e:
    case Co.NoEdit{}:
      stay_msgs(own)
    case Co.Omit{}:
      []
    case Co.Replace{ms}:
      stay_msgs(ms)

def part_spec(i: Nat, e: Co.Ent) -> Co.Part:
  match e:
    case Co.Ent{h, ed, own}:
      Co.Part{i, keep_spec(ed, own)}

def given_of(e: Co.Ent) -> List<&2, Co.Msg>:
  match e:
    case Co.Ent{h, ed, own}:
      given_spec(ed, own)

def marker_of(e: Co.Ent) -> Bool:
  match e:
    case Co.Ent{h, ed, own}:
      h

def range_parts.one(b: Bool, i: Nat, e: Co.Ent, rest: List<&2, Co.Part>) -> List<&2, Co.Part>:
  match b:
    case True{}:
      rest
    case False{}:
      part_spec(i, e) <> rest

# R5: the parts of the range entries es after a marker (the first at
# index i): every entry that is not a head marker
def range_parts(es: List<&2, Co.Ent>, +i: Nat) -> List<&2, Co.Part>:
  match es:
    case Nil{}:
      []
    case +e <> t:
      range_parts.one(marker_of(e), i, e, range_parts(t, 1n+i))

# R5: the parts of every entry of es (the first at index i)
def all_parts(es: List<&2, Co.Ent>, +i: Nat) -> List<&2, Co.Part>:
  match es:
    case Nil{}:
      []
    case e <> t:
      part_spec(i, e) <> all_parts(t, 1n+i)

def range_msgs.one(b: Bool, e: Co.Ent, rest: List<&2, Co.Msg>) -> List<&2, Co.Msg>:
  match b:
    case True{}:
      rest
    case False{}:
      List.append(&2, Co.Msg, given_of(e), rest)

# R5: the messages of the range entries es after a marker
def range_msgs(es: List<&2, Co.Ent>) -> List<&2, Co.Msg>:
  match es:
    case Nil{}:
      []
    case +e <> t:
      range_msgs.one(marker_of(e), e, range_msgs(t))

# R5: the messages of every entry of es
def all_msgs(es: List<&2, Co.Ent>) -> List<&2, Co.Msg>:
  match es:
    case Nil{}:
      []
    case e <> t:
      List.append(&2, Co.Msg, given_of(e), all_msgs(t))

# R5: the active entries' parts
def parts_spec(mark: Bool, es: List<&2, Co.Ent>) -> List<&2, Co.Part>:
  match mark:
    case True{}:
      match es:
        case Nil{}:
          []
        case e <> t:
          part_spec(0n, e) <> range_parts(t, 1n)
    case False{}:
      all_parts(es, 0n)

# R5: the messages the active entries contribute, in order
def msgs_spec(mark: Bool, es: List<&2, Co.Ent>) -> List<&2, Co.Msg>:
  match mark:
    case True{}:
      match es:
        case Nil{}:
          []
        case e <> t:
          List.append(&2, Co.Msg, given_of(e), range_msgs(t))
    case False{}:
      all_msgs(es)

# R5: what derive answers
def derive_spec(+mark: Bool, +es: List<&2, Co.Ent>) -> Co.Derived:
  Co.Derived{parts_spec(mark, es), plan_spec(msgs_spec(mark, es))}

# R6: some added entry carries edits, is a head marker or was edited
def redo_spec(ads: List<&2, Co.Add>) -> Bool:
  match ads:
    case Nil{}:
      False{}
    case a <> t:
      match a:
        case Co.Add{x, h, d, own}:
          Bool.or(x, Bool.or(h, Bool.or(d, redo_spec(t))))

# R6: the indices of the own messages each added entry keeps
def keeps_spec(ads: List<&2, Co.Add>) -> List<&2, List<&2, Nat>>:
  match ads:
    case Nil{}:
      []
    case a <> t:
      match a:
        case Co.Add{x, h, d, own}:
          stay_idx(own, 0n) <> keeps_spec(t)

# R6: the messages the added entries contribute, in order
def added_spec(ads: List<&2, Co.Add>) -> List<&2, Co.Msg>:
  match ads:
    case Nil{}:
      []
    case a <> t:
      match a:
        case Co.Add{x, h, d, own}:
          List.append(&2, Co.Msg, stay_msgs(own), added_spec(t))

def extend_spec.pick(b: Bool, +ads: List<&2, Co.Add>, open: List<&2, Co.Msg>) -> Co.Extended:
  match b:
    case True{}:
      Co.Rederive{}
    case False{}:
      Co.Extended{keeps_spec(ads), plan_spec(List.append(&2, Co.Msg, open, added_spec(ads)))}

# R6: what extend answers
def extend_spec(+ads: List<&2, Co.Add>, open: List<&2, Co.Msg>) -> Co.Extended:
  extend_spec.pick(redo_spec(ads), ads, open)

# Laws
# ----

# LAW context_order_exact: the order of every message sequence is R1's: every message that is not a tool result stays in order, each assistant followed by its calls' results in call order, each the first result for its id before the next assistant, else a missing result; other results dropped
# EXCLUDES: a result taken from past the next assistant, the last result
#   for an id instead of the first, results in arrival order instead of
#   call order, a stray result kept, a missing result not synthesized or
#   synthesized for another call, a user or system message dropped or
#   moved, an excluded index
law context_order_exact:
  for +ms: List<&2, Co.Msg>
  {Co.order(ms) == order_spec(ms) : List<&2, Co.Step>}

# LAW context_order_split: the order of a ++ b is the order of a followed by the order of b shifted by a's length whenever b starts with an assistant (what lets the host keep the settled part)
# EXCLUDES: an assistant that takes a result from after the next
#   assistant, a settled part that a later message changes
law context_order_split:
  for +a: List<&2, Co.Msg>
  for +b: List<&2, Co.Msg>
  for h: {starts_asst(b) == True{} : Bool}
  {Co.order(List.append(&2, Co.Msg, a, b)) == List.append(&2, Co.Step, Co.order(a), shift(List.length(&2, Co.Msg, a), Co.order(b))) : List<&2, Co.Step>}

# LAW context_plan_exact: the plan of every message sequence is R2's: its order, the last assistant as the split when it is not the first message, and the length of the order of the messages before it
# EXCLUDES: a split at the first assistant, at index 0, past the last
#   assistant; a settled count that splits an assistant from its results
law context_plan_exact:
  for +ms: List<&2, Co.Msg>
  {Co.plan(ms) == plan_spec(ms) : Co.Plan}

# LAW context_lead_exact: a system message moves to the front exactly when only user messages, at least one, precede it and it is the first message that is not a user message
# EXCLUDES: a system message moved past an assistant, a leading system
#   message moved, a second system message moved, a user message moved
law context_lead_exact:
  for +rs: List<&2, Co.Role>
  {Co.lead(rs) == lead_spec(rs) : Maybe<&2, Nat>}

# LAW context_derive_exact: derive answers R5's active entries, each with R4's contribution, and R2's plan of their messages
# EXCLUDES: an older head marker kept, the marker dropped or moved, a
#   head marker dropped without a marker, an omitted entry contributing,
#   a replaced entry contributing its own messages, an error, aborted or
#   deferred answer kept, a stopped or length answer dropped
law context_derive_exact:
  for +mark: Bool
  for +es: List<&2, Co.Ent>
  {Co.derive(mark, es) == derive_spec(mark, es) : Co.Derived}

# LAW context_extend_exact: extend derives again exactly when an added entry carries edits, is a head marker or was edited; else each added entry keeps its own messages without excluded answers, and the plan is R2's of the open messages followed by theirs
# EXCLUDES: an added edit or head marker extended in place (a stale
#   view), a full derive for plain entries, the added messages before the
#   open ones
law context_extend_exact:
  for +ads: List<&2, Co.Add>
  for open: List<&2, Co.Msg>
  {Co.extend(ads, open) == extend_spec(ads, open) : Co.Extended}

# LAW context_order_example: anchor: results in call order, a repeated id, a user message between, a stray result, a missing result after the next assistant's window
# EXCLUDES: a spec that is wrong on the shipped cases
law context_order_example:
  {Co.order([Co.MUser{}, Co.MAsst{Co.SToolUse{}, [5n, 6n]}, Co.MUser{}, Co.MRes{6n}, Co.MRes{5n}, Co.MRes{6n}, Co.MAsst{Co.SStop{}, [7n]}, Co.MRes{5n}]) == [Co.Take{0n}, Co.Take{1n}, Co.Take{4n}, Co.Take{3n}, Co.Take{2n}, Co.Take{6n}, Co.Miss{6n, 0n}] : List<&2, Co.Step>} &
  {Co.plan([Co.MUser{}, Co.MAsst{Co.SToolUse{}, [1n]}, Co.MRes{1n}, Co.MAsst{Co.SStop{}, []}]) == Co.Plan{Some{3n}, 3n, [Co.Take{0n}, Co.Take{1n}, Co.Take{2n}, Co.Take{3n}]} : Co.Plan} &
  {Co.plan([Co.MAsst{Co.SToolUse{}, [1n]}, Co.MUser{}]) == Co.Plan{None{}, 0n, [Co.Take{0n}, Co.Miss{0n, 0n}, Co.Take{1n}]} : Co.Plan} &
  {Co.lead([Co.RUser{}, Co.RUser{}, Co.RSystem{}, Co.RSystem{}]) == Some{2n} : Maybe<&2, Nat>} &
  {Co.lead([Co.RSystem{}, Co.RUser{}]) == None{} : Maybe<&2, Nat>} &
  {Co.lead([Co.RUser{}, Co.RAsst{}, Co.RSystem{}]) == None{} : Maybe<&2, Nat>}

# LAW context_derive_example: anchor: a marker first, an older head marker dropped, an omitted entry, an error answer left out, a replaced entry; extend with plain and with edited entries
# EXCLUDES: a spec that is wrong on the shipped cases
law context_derive_example:
  {Co.derive(True{}, [Co.Ent{True{}, Co.NoEdit{}, [Co.MUser{}]}, Co.Ent{True{}, Co.NoEdit{}, [Co.MUser{}]}, Co.Ent{False{}, Co.Omit{}, [Co.MUser{}]}, Co.Ent{False{}, Co.NoEdit{}, [Co.MAsst{Co.SError{}, []}, Co.MUser{}]}, Co.Ent{False{}, Co.Replace{[Co.MSystem{}]}, [Co.MUser{}]}]) == Co.Derived{[Co.Part{0n, Co.Own{[0n]}}, Co.Part{2n, Co.Omitted{}}, Co.Part{3n, Co.Own{[1n]}}, Co.Part{4n, Co.Alt{[0n]}}], Co.Plan{None{}, 0n, [Co.Take{0n}, Co.Take{1n}, Co.Take{2n}]}} : Co.Derived} &
  {Co.extend([Co.Add{False{}, False{}, False{}, [Co.MRes{2n}]}], [Co.MAsst{Co.SToolUse{}, [2n]}, Co.MUser{}]) == Co.Extended{[[0n]], Co.Plan{None{}, 0n, [Co.Take{0n}, Co.Take{2n}, Co.Take{1n}]}} : Co.Extended} &
  {Co.extend([Co.Add{False{}, False{}, True{}, []}], []) == Co.Rederive{} : Co.Extended}

# LAWS (R7): the entry of the compiled Bend core
# (bend/ffi_context_order.bend, called by crates/eukhe-durable
# harness/context.rs and compaction/range.rs through
# `eukhe_bend::rules::context_order`). Each law is an open claim about
# FCo.ffi, stated with spec spellers built only from the wire primitives
# of bend/wire.bend (their round trips: laws/wire.bend).
#
# R7: a request is a question: tag 0 the order of a List<Msg>; tag 1
#     derive: a Bool (the first entry is the head marker) and a
#     List<Ent>; tag 2 extend: a List<Add> and the open List<Msg>; tag 3
#     lead: a List<Role>. Stop: tags 0-6 pending, stop, length, toolUse,
#     error, aborted, deferred. Msg: 0 user, 1 system, 2 assistant (its
#     Stop, its call ids as a List<Nat>), 3 tool result (its call id).
#     Role: 0 user, 1 system, 2 assistant, 3 tool result. Edit: 0 none,
#     1 omit, 2 replace (a List<Msg>). Ent: Bool (head marker), Edit,
#     List<Msg>. Add: Bool (edits), Bool (head marker), Bool (edited),
#     List<Msg>. Answers: order: a List<Step> (Step: 0 Take i, 1 Miss i
#     j); derive: a List<Part> (Part: its entry's index, then Keep: 0
#     nothing, 1 own at a List<Nat>, 2 replacement at a List<Nat>), then
#     a Plan (a Maybe<Nat> split: 0 none or 1 then the index, the
#     settled count, a List<Step>); extend: 0 (derive again), or 1, a
#     List of List<Nat>, then a Plan; lead: a Maybe<Nat>. Every input
#     that is not exactly one request whose counts and ids fit the wire
#     answers the error form "context_order: malformed request"; never a
#     default.

# Spec spellers
# -------------

def spell_stop(s: Co.Stop, rest: String) -> String:
  match s:
    case Co.SPending{}:
      Wr.put_nat(0n, rest)
    case Co.SStop{}:
      Wr.put_nat(1n, rest)
    case Co.SLength{}:
      Wr.put_nat(2n, rest)
    case Co.SToolUse{}:
      Wr.put_nat(3n, rest)
    case Co.SError{}:
      Wr.put_nat(4n, rest)
    case Co.SAborted{}:
      Wr.put_nat(5n, rest)
    case Co.SDeferred{}:
      Wr.put_nat(6n, rest)

def spell_msg(m: Co.Msg, rest: String) -> String:
  match m:
    case Co.MUser{}:
      Wr.put_nat(0n, rest)
    case Co.MSystem{}:
      Wr.put_nat(1n, rest)
    case Co.MAsst{s, cs}:
      Wr.put_nat(2n, spell_stop(s, LawsBase.wire_spell_nats(cs, rest)))
    case Co.MRes{c}:
      Wr.put_nat(3n, Wr.put_nat(c, rest))

def spell_msgs.items(ms: List<&2, Co.Msg>, rest: String) -> String:
  match ms:
    case Nil{}:
      rest
    case m <> t:
      spell_msg(m, spell_msgs.items(t, rest))

# a list of messages: its count, then each message
def spell_msgs(+ms: List<&2, Co.Msg>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Co.Msg, ms), spell_msgs.items(ms, rest))

def spell_role(r: Co.Role, rest: String) -> String:
  match r:
    case Co.RUser{}:
      Wr.put_nat(0n, rest)
    case Co.RSystem{}:
      Wr.put_nat(1n, rest)
    case Co.RAsst{}:
      Wr.put_nat(2n, rest)
    case Co.RRes{}:
      Wr.put_nat(3n, rest)

def spell_roles.items(rs: List<&2, Co.Role>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case r <> t:
      spell_role(r, spell_roles.items(t, rest))

def spell_edit(e: Co.Edit, rest: String) -> String:
  match e:
    case Co.NoEdit{}:
      Wr.put_nat(0n, rest)
    case Co.Omit{}:
      Wr.put_nat(1n, rest)
    case Co.Replace{ms}:
      Wr.put_nat(2n, spell_msgs(ms, rest))

def spell_ent(e: Co.Ent, rest: String) -> String:
  match e:
    case Co.Ent{h, ed, own}:
      Wr.put_bool(h, spell_edit(ed, spell_msgs(own, rest)))

def spell_ents.items(es: List<&2, Co.Ent>, rest: String) -> String:
  match es:
    case Nil{}:
      rest
    case e <> t:
      spell_ent(e, spell_ents.items(t, rest))

def spell_add(a: Co.Add, rest: String) -> String:
  match a:
    case Co.Add{x, h, d, own}:
      Wr.put_bool(x, Wr.put_bool(h, Wr.put_bool(d, spell_msgs(own, rest))))

def spell_adds.items(ads: List<&2, Co.Add>, rest: String) -> String:
  match ads:
    case Nil{}:
      rest
    case a <> t:
      spell_add(a, spell_adds.items(t, rest))

# a request, then rest
def spell_req(q: FCo.Req, rest: String) -> String:
  match q:
    case FCo.QOrder{ms}:
      Wr.put_nat(0n, spell_msgs(ms, rest))
    case FCo.QDerive{mk, +es}:
      Wr.put_nat(1n, Wr.put_bool(mk, Wr.put_nat(List.length(&2, Co.Ent, es), spell_ents.items(es, rest))))
    case FCo.QExtend{+ads, open}:
      Wr.put_nat(2n, Wr.put_nat(List.length(&2, Co.Add, ads), spell_adds.items(ads, spell_msgs(open, rest))))
    case FCo.QLead{+rs}:
      Wr.put_nat(3n, Wr.put_nat(List.length(&2, Co.Role, rs), spell_roles.items(rs, rest)))

def spell_step(x: Co.Step, rest: String) -> String:
  match x:
    case Co.Take{i}:
      Wr.put_nat(0n, Wr.put_nat(i, rest))
    case Co.Miss{i, j}:
      Wr.put_nat(1n, Wr.put_nat(i, Wr.put_nat(j, rest)))

def spell_steps.items(xs: List<&2, Co.Step>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      spell_step(x, spell_steps.items(t, rest))

def spell_steps(+xs: List<&2, Co.Step>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Co.Step, xs), spell_steps.items(xs, rest))

def spell_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

def spell_plan(p: Co.Plan, rest: String) -> String:
  match p:
    case Co.Plan{sp, n, xs}:
      spell_mnat(sp, Wr.put_nat(n, spell_steps(xs, rest)))

def spell_keep(k: Co.Keep, rest: String) -> String:
  match k:
    case Co.Omitted{}:
      Wr.put_nat(0n, rest)
    case Co.Own{js}:
      Wr.put_nat(1n, LawsBase.wire_spell_nats(js, rest))
    case Co.Alt{js}:
      Wr.put_nat(2n, LawsBase.wire_spell_nats(js, rest))

def spell_part(p: Co.Part, rest: String) -> String:
  match p:
    case Co.Part{i, k}:
      Wr.put_nat(i, spell_keep(k, rest))

def spell_parts.items(ps: List<&2, Co.Part>, rest: String) -> String:
  match ps:
    case Nil{}:
      rest
    case p <> t:
      spell_part(p, spell_parts.items(t, rest))

def spell_keeps.items(ks: List<&2, List<&2, Nat>>, rest: String) -> String:
  match ks:
    case Nil{}:
      rest
    case k <> t:
      LawsBase.wire_spell_nats(k, spell_keeps.items(t, rest))

def spell_derived(d: Co.Derived) -> String:
  match d:
    case Co.Derived{+ps, p}:
      Wr.put_nat(List.length(&2, Co.Part, ps), spell_parts.items(ps, spell_plan(p, "")))

def spell_extended(x: Co.Extended) -> String:
  match x:
    case Co.Rederive{}:
      Wr.put_nat(0n, "")
    case Co.Extended{+ks, p}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, List<&2, Nat>, ks), spell_keeps.items(ks, spell_plan(p, ""))))

# the reply Rust reads: the spelled answer of the model
def spell_reply(q: FCo.Req) -> String:
  match q:
    case FCo.QOrder{ms}:
      spell_steps(Co.order(ms), "")
    case FCo.QDerive{mk, es}:
      spell_derived(Co.derive(mk, es))
    case FCo.QExtend{ads, open}:
      spell_extended(Co.extend(ads, open))
    case FCo.QLead{rs}:
      spell_mnat(Co.lead(rs), "")

# every count and id of a message fits the wire
def msg_fits(m: Co.Msg) -> Bool:
  match m:
    case Co.MUser{}:
      True{}
    case Co.MSystem{}:
      True{}
    case Co.MAsst{s, +cs}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs))
    case Co.MRes{c}:
      LawsBase.wire_fits(c)

def msgs_all(ms: List<&2, Co.Msg>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      Bool.and(msg_fits(m), msgs_all(t))

# a list of messages fits the wire: its count and every message
def msgs_fit(+ms: List<&2, Co.Msg>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Co.Msg, ms)), msgs_all(ms))

def edit_fits(e: Co.Edit) -> Bool:
  match e:
    case Co.NoEdit{}:
      True{}
    case Co.Omit{}:
      True{}
    case Co.Replace{ms}:
      msgs_fit(ms)

def ent_fits(e: Co.Ent) -> Bool:
  match e:
    case Co.Ent{h, ed, own}:
      Bool.and(edit_fits(ed), msgs_fit(own))

def ents_all(es: List<&2, Co.Ent>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(ent_fits(e), ents_all(t))

def add_fits(a: Co.Add) -> Bool:
  match a:
    case Co.Add{x, h, d, own}:
      msgs_fit(own)

def adds_all(ads: List<&2, Co.Add>) -> Bool:
  match ads:
    case Nil{}:
      True{}
    case a <> t:
      Bool.and(add_fits(a), adds_all(t))

# every count and id of the request fits the wire
def req_fits(q: FCo.Req) -> Bool:
  match q:
    case FCo.QOrder{ms}:
      msgs_fit(ms)
    case FCo.QDerive{mk, +es}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Co.Ent, es)), ents_all(es))
    case FCo.QExtend{+ads, open}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Co.Add, ads)), Bool.and(adds_all(ads), msgs_fit(open)))
    case FCo.QLead{+rs}:
      LawsBase.wire_fits(List.length(&2, Co.Role, rs))

# Laws
# ----

# LAW context_order_ffi_answers: a spelled request whose counts and ids fit the wire answers the spelled answer of the model
# EXCLUDES: a fact misread (a tag off by one, a stop reason or a flag
#   swapped, a call id lost), an answer spelled with another tag, a
#   question answered by another model function
law context_order_ffi_answers:
  for +q: FCo.Req
  for h: {req_fits(q) == True{} : Bool}
  {FCo.ffi(spell_req(q, "")) == spell_reply(q) : String}

# LAW context_order_ffi_reads: the entry's decoder reads a spelled request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law context_order_ffi_reads:
  for +q: FCo.Req
  for +rest: String
  for h: {req_fits(q) == True{} : Bool}
  {FCo.get_req(spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FCo.Req>}

# LAW context_order_ffi_exact: every input the entry does not answer with the error form is a spelled request that fits the wire
# EXCLUDES: an answer made for input that is no request (an unknown tag,
#   a missing field, a Nat of 15 or more digits, input left over)
law context_order_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCo.ffi(s)) == False{} : Bool}
  exs q: FCo.Req
  {s == spell_req(q, "") : String} & {req_fits(q) == True{} : Bool}

# LAW context_order_ffi_refuses: every error the entry answers is exactly "context_order: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law context_order_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FCo.ffi(s)) == True{} : Bool}
  {FCo.ffi(s) == Wr.err("context_order: malformed request") : String}

# LAW context_order_ffi_example: anchor: the bytes Rust sends and reads: an order, a derive, an extend, a lead, an unknown tag, input left over
# EXCLUDES: another spelling of a fact or an answer
law context_order_ffi_example:
  {[FCo.ffi("0,4,0,2,3,2,5,6,3,6,3,5,"), FCo.ffi("1,T3,T0,1,0,F0,2,2,4,0,0,F2,2,0,2,1,1,1,1,0,"), FCo.ffi("2,1,FFF1,3,2,2,2,1,1,2,0,"), FCo.ffi("2,1,FTF0,0,"), FCo.ffi("3,3,0,1,2,"), FCo.ffi("4,"), FCo.ffi("3,2,0,1,x")] == ["4,0,0,0,1,0,3,0,2,", "3,0,1,1,0,1,1,1,1,2,2,2,0,1,1,3,3,5,0,0,0,1,0,2,0,3,1,3,0,", "1,1,1,0,0,0,3,0,0,0,2,0,1,", "0,", "1,1,", Wr.err("context_order: malformed request"), Wr.err("context_order: malformed request")] : List<&2, String>}
