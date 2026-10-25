# context_order: what the model context of one conversation is made of,
# by index (the Rust host is crates/eukhe-durable/src/harness/context.rs;
# the durable harness spec §2.1). The host keeps the messages; it sends
# their facts and acts on the answers: which entries are active, which
# of an entry's messages stay, the order of the messages a request sends,
# where the settled part ends, which system message leads.
#
# Facts. A message is a user message, a system message, an assistant
# answer (its stop reason and the ids of its tool calls, in order) or a
# tool result (the id of its call). The host interns the call ids of one
# question to Nats: equal ids, equal Nats.
#
# order: each assistant's results go right after it, in call order: the
# result of a call is the first result for its id among the messages
# after the assistant and before the next assistant; a call with none
# gets a synthesized missing result (Miss{assistant, call}); every
# result not taken is dropped; every other message stays, in order.
#
# plan: the order, and the split of the messages at the last assistant
# when that is not the first message: the ordered messages before it
# never change again (a later message can only add results after the
# last assistant), so the host keeps them settled; `settles` counts the
# ordered messages the messages before the split give (the order of
# those messages; laws/context_order.bend context_order_split: they are
# the first `settles` steps of the whole order).
#
# lead: a system message that only user messages precede moves to the
# front (its index; none when it is first, or the first message that is
# not a user message is not a system message).
#
# derive: the active entries of a range (a head marker first, then the
# range's entries that are no head marker; without a marker every
# entry), each with what it contributes: nothing (an Omit edit), the
# messages of its Replace edit or its own messages (no edit), always
# without the assistant answers that stopped as error, aborted or
# deferred; and the plan of the contributed messages.
#
# extend: entries added after a range's tail: the whole range derives
# again when an added entry carries edits, is a head marker or was
# already edited; else each added entry contributes its own messages
# (without the excluded answers), and the plan of the open messages
# followed by theirs.
#
# Pure: no IO, no @unsafe. laws/context_order.bend states its laws.

import Base

# Facts
# -----

# the stop reason of an assistant answer (eukhe_types::pi_ai::StopReason)
type Stop is Data:
  SPending{}
  SStop{}
  SLength{}
  SToolUse{}
  SError{}
  SAborted{}
  SDeferred{}

# a message
type Msg is Data:
  MUser{}
  MSystem{}
  # an assistant answer: its stop reason and its tool calls' ids
  MAsst{stop: Stop, calls: List<&2, Nat>}
  # a tool result: its call's id
  MRes{call: Nat}

# the role of a message of the context
type Role is Data:
  RUser{}
  RSystem{}
  RAsst{}
  RRes{}

# the newest edit of an entry in its range
type Edit is Data:
  NoEdit{}
  Omit{}
  # the messages that replace the entry's own
  Replace{msgs: List<&2, Msg>}

# an entry of a range: whether it is a head marker, its edit, its own
# messages
type Ent is Data:
  Ent{head: Bool, edit: Edit, own: List<&2, Msg>}

# an entry added after a range's tail: whether it carries edits, whether
# it is a head marker, whether an edit of the range targets it, its own
# messages
type Add is Data:
  Add{edits: Bool, head: Bool, edited: Bool, own: List<&2, Msg>}

# Answers
# -------

# a message of the order: message i, or the missing result of call j of
# the assistant at index i
type Step is Data:
  Take{i: Nat}
  Miss{i: Nat, j: Nat}

# the order of messages, the index of the split (none: nothing settles)
# and how many ordered messages come from before it
type Plan is Data:
  Plan{split: Maybe<&2, Nat>, settles: Nat, steps: List<&2, Step>}

# what an entry contributes: nothing, its own messages at js, or its
# Replace edit's messages at js
type Keep is Data:
  Omitted{}
  Own{js: List<&2, Nat>}
  Alt{js: List<&2, Nat>}

# an active entry (its index in the question) and what it contributes
type Part is Data:
  Part{at: Nat, keep: Keep}

type Derived is Data:
  Derived{parts: List<&2, Part>, plan: Plan}

# extend: derive the range again, or what each added entry keeps of its
# own messages and the plan of the open messages followed by theirs
type Extended is Data:
  Rederive{}
  Extended{keeps: List<&2, List<&2, Nat>>, plan: Plan}

# a result in an assistant's window: its index and its call's id
type Hit is Data:
  Hit{k: Nat, call: Nat}

# Order
# -----

# the results among ms (the first at index k) before the next assistant
def window(ms: List<&2, Msg>, +k: Nat) -> List<&2, Hit>:
  match ms:
    case Nil{}:
      []
    case m <> t:
      match m:
        case MUser{}:
          window(t, 1n+k)
        case MSystem{}:
          window(t, 1n+k)
        case MAsst{s, cs}:
          []
        case MRes{c}:
          Hit{k, c} <> window(t, 1n+k)

def pick.sel(b: Bool, k: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{k}
    case False{}:
      rest

# the index of the first hit for the call id c
def pick(hs: List<&2, Hit>, +c: Nat) -> Maybe<&2, Nat>:
  match hs:
    case Nil{}:
      None{}
    case h <> t:
      match h:
        case Hit{k, d}:
          pick.sel(Nat.is_eq(d, c), k, pick(t, c))

def res(r: Maybe<&2, Nat>, i: Nat, j: Nat) -> Step:
  match r:
    case None{}:
      Miss{i, j}
    case Some{k}:
      Take{k}

# the results of the calls cs (the first is call j) of the assistant at
# index i, from its window hs
def results(cs: List<&2, Nat>, +hs: List<&2, Hit>, +i: Nat, +j: Nat) -> List<&2, Step>:
  match cs:
    case Nil{}:
      []
    case c <> t:
      res(pick(hs, c), i, j) <> results(t, hs, i, 1n+j)

# the order of ms, the first at index i
def order.go(ms: List<&2, Msg>, +i: Nat) -> List<&2, Step>:
  match ms:
    case Nil{}:
      []
    case m <> +t:
      match m:
        case MUser{}:
          Take{i} <> order.go(t, 1n+i)
        case MSystem{}:
          Take{i} <> order.go(t, 1n+i)
        case MAsst{s, cs}:
          Take{i} <> List.append(&2, Step, results(cs, window(t, 1n+i), i, 0n), order.go(t, 1n+i))
        case MRes{c}:
          order.go(t, 1n+i)

# the order of the messages ms
def order(ms: List<&2, Msg>) -> List<&2, Step>:
  order.go(ms, 0n)

# Plan
# ----

# the index of the last assistant of ms (the first at index i), else last
def last_asst(ms: List<&2, Msg>, +i: Nat, last: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match ms:
    case Nil{}:
      last
    case m <> t:
      match m:
        case MUser{}:
          last_asst(t, 1n+i, last)
        case MSystem{}:
          last_asst(t, 1n+i, last)
        case MAsst{s, cs}:
          last_asst(t, 1n+i, Some{i})
        case MRes{c}:
          last_asst(t, 1n+i, last)

def split.pos(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      match k:
        case 0n:
          None{}
        case 1n+p:
          Some{1n+p}

# the split: the last assistant, when it is not the first message
def split(ms: List<&2, Msg>) -> Maybe<&2, Nat>:
  split.pos(last_asst(ms, 0n, None{}))

def take(n: Nat, ms: List<&2, Msg>) -> List<&2, Msg>:
  match n:
    case 0n:
      []
    case 1n+p:
      match ms:
        case Nil{}:
          []
        case m <> t:
          m <> take(p, t)

def plan.at(sp: Maybe<&2, Nat>, +ms: List<&2, Msg>) -> Plan:
  match sp:
    case None{}:
      Plan{None{}, 0n, order(ms)}
    case Some{+k}:
      Plan{Some{k}, List.length(&2, Step, order(take(k, ms))), order(ms)}

# the plan of the messages ms
def plan(+ms: List<&2, Msg>) -> Plan:
  plan.at(split(ms), ms)

# Lead
# ----

def lead.sys(i: Nat) -> Maybe<&2, Nat>:
  match i:
    case 0n:
      None{}
    case 1n+p:
      Some{1n+p}

def lead.go(ks: List<&2, Role>, +i: Nat) -> Maybe<&2, Nat>:
  match ks:
    case Nil{}:
      None{}
    case k <> t:
      match k:
        case RUser{}:
          lead.go(t, 1n+i)
        case RSystem{}:
          lead.sys(i)
        case RAsst{}:
          None{}
        case RRes{}:
          None{}

# the index of the system message that moves to the front of ks
def lead(ks: List<&2, Role>) -> Maybe<&2, Nat>:
  lead.go(ks, 0n)

# Contributions
# -------------

# an assistant answer that stopped as error, aborted or deferred stays
# out of the context
def excluded(s: Stop) -> Bool:
  match s:
    case SPending{}:
      False{}
    case SStop{}:
      False{}
    case SLength{}:
      False{}
    case SToolUse{}:
      False{}
    case SError{}:
      True{}
    case SAborted{}:
      True{}
    case SDeferred{}:
      True{}

def kept(m: Msg) -> Bool:
  match m:
    case MUser{}:
      True{}
    case MSystem{}:
      True{}
    case MAsst{s, cs}:
      Bool.not(excluded(s))
    case MRes{c}:
      True{}

def keep.one(b: Bool, j: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      j <> rest
    case False{}:
      rest

# the indices of the messages of ms (the first at index j) that stay
def keep.go(ms: List<&2, Msg>, +j: Nat) -> List<&2, Nat>:
  match ms:
    case Nil{}:
      []
    case m <> t:
      keep.one(kept(m), j, keep.go(t, 1n+j))

def keep.msg(b: Bool, m: Msg, rest: List<&2, Msg>) -> List<&2, Msg>:
  match b:
    case True{}:
      m <> rest
    case False{}:
      rest

# the messages of ms that stay
def keep.msgs(ms: List<&2, Msg>) -> List<&2, Msg>:
  match ms:
    case Nil{}:
      []
    case +m <> t:
      keep.msg(kept(m), m, keep.msgs(t))

# what an entry with the edit e and its own messages contributes
def contribute(e: Edit, own: List<&2, Msg>) -> Keep:
  match e:
    case NoEdit{}:
      Own{keep.go(own, 0n)}
    case Omit{}:
      Omitted{}
    case Replace{ms}:
      Alt{keep.go(ms, 0n)}

# the messages an entry with the edit e and its own messages contributes
def contributed(e: Edit, own: List<&2, Msg>) -> List<&2, Msg>:
  match e:
    case NoEdit{}:
      keep.msgs(own)
    case Omit{}:
      []
    case Replace{ms}:
      keep.msgs(ms)

# Derive
# ------

def part(i: Nat, e: Ent) -> Part:
  match e:
    case Ent{h, ed, own}:
      Part{i, contribute(ed, own)}

def part.msgs(e: Ent) -> List<&2, Msg>:
  match e:
    case Ent{h, ed, own}:
      contributed(ed, own)

def is_head(e: Ent) -> Bool:
  match e:
    case Ent{h, ed, own}:
      h

def parts.one(skip: Bool, i: Nat, e: Ent, rest: List<&2, Part>) -> List<&2, Part>:
  match skip:
    case True{}:
      rest
    case False{}:
      part(i, e) <> rest

# the parts of the entries es (the first at index i); with a marker the
# head markers among them are not active
def parts.go(es: List<&2, Ent>, +mark: Bool, +i: Nat) -> List<&2, Part>:
  match es:
    case Nil{}:
      []
    case +e <> t:
      parts.one(Bool.and(mark, is_head(e)), i, e, parts.go(t, mark, 1n+i))

def msgs.one(skip: Bool, e: Ent, rest: List<&2, Msg>) -> List<&2, Msg>:
  match skip:
    case True{}:
      rest
    case False{}:
      List.append(&2, Msg, part.msgs(e), rest)

# the messages the active entries among es contribute, in order
def msgs.go(es: List<&2, Ent>, +mark: Bool) -> List<&2, Msg>:
  match es:
    case Nil{}:
      []
    case +e <> t:
      msgs.one(Bool.and(mark, is_head(e)), e, msgs.go(t, mark))

# the active entries' parts: with a marker (the first entry), the
# marker, then the range's entries that are no head marker; else every
# entry
def parts(mark: Bool, es: List<&2, Ent>) -> List<&2, Part>:
  match mark:
    case True{}:
      match es:
        case Nil{}:
          []
        case e <> t:
          part(0n, e) <> parts.go(t, True{}, 1n)
    case False{}:
      parts.go(es, False{}, 0n)

# the messages the active entries contribute, in order
def msgs(mark: Bool, es: List<&2, Ent>) -> List<&2, Msg>:
  match mark:
    case True{}:
      match es:
        case Nil{}:
          []
        case e <> t:
          List.append(&2, Msg, part.msgs(e), msgs.go(t, True{}))
    case False{}:
      msgs.go(es, False{})

# the parts of a range's active entries and the plan of their messages
def derive(+mark: Bool, +es: List<&2, Ent>) -> Derived:
  Derived{parts(mark, es), plan(msgs(mark, es))}

# Extend
# ------

def redo(a: Add) -> Bool:
  match a:
    case Add{x, h, d, own}:
      Bool.or(x, Bool.or(h, d))

# an added entry carries edits, is a head marker or was edited
def rederive(ads: List<&2, Add>) -> Bool:
  match ads:
    case Nil{}:
      False{}
    case a <> t:
      Bool.or(redo(a), rederive(t))

def add.keep(a: Add) -> List<&2, Nat>:
  match a:
    case Add{x, h, d, own}:
      keep.go(own, 0n)

def add.msgs(a: Add) -> List<&2, Msg>:
  match a:
    case Add{x, h, d, own}:
      keep.msgs(own)

# the indices of the own messages each added entry keeps
def keeps(ads: List<&2, Add>) -> List<&2, List<&2, Nat>>:
  match ads:
    case Nil{}:
      []
    case +a <> t:
      add.keep(a) <> keeps(t)

# the messages the added entries contribute, in order
def added(ads: List<&2, Add>) -> List<&2, Msg>:
  match ads:
    case Nil{}:
      []
    case +a <> t:
      List.append(&2, Msg, add.msgs(a), added(t))

def extend.pick(b: Bool, +ads: List<&2, Add>, open: List<&2, Msg>) -> Extended:
  match b:
    case True{}:
      Rederive{}
    case False{}:
      Extended{keeps(ads), plan(List.append(&2, Msg, open, added(ads)))}

# the entries as added after a range whose open messages are open
def extend(+ads: List<&2, Add>, open: List<&2, Msg>) -> Extended:
  extend.pick(rederive(ads), ads, open)
