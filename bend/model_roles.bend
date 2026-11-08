# model_roles: where the model of every model role comes from. The Rust
# code is crates/eukhe-core/src/models/roles.rs (`role_table`), over
# `eukhe_bend::rules::model_roles`; every role reads its model there.
#
# A role is one setting that names a model (eukhe_types ModelRole, in its
# order): the chat (`defaultProvider`/`defaultModel`), the memory
# compactor (`memory.model`), compaction and summaries (`auxiliaryModel`),
# image turns (`imageModel`), subagents (`subagentDefaultModel`), main's
# worker (`workerModel`), the phone gateway (`gateway.signal.model`),
# `rlm.query` (`rlm.queryModel`), titles, the judge, translation, speech
# and dictation
# (`modelRoles.<role>`). One more setting, `modelRoles.all`, names the
# model of every role.
#
# A role's model comes, in this order, from:
#
#   - its own setting, when it is set;
#   - else the all-roles setting, when it is set and the role takes a chat
#     model (speech and dictation take only local models: the all-roles
#     model never reaches them);
#   - else the role's default (the chat: the startup chain; the memory
#     compactor: `auxiliaryModel`, else the session model; subagents and
#     main's worker: the parent's model, never `subagentDefaultModel` for
#     the worker; the local roles: their chain; the others: the session
#     model).
#
# The table answers every role once, in the role order.

import Base

# A model role, in the eukhe_types ModelRole order.
type Role is Data:
  Chat{}
  Memory{}
  Auxiliary{}
  Image{}
  Subagent{}
  Worker{}
  Gateway{}
  Query{}
  Titles{}
  Judge{}
  Translate{}
  Speech{}
  Dictation{}

# A setting that names a model: unset, or the selector n (opaque).
type Choice is Data:
  Unset{}
  Sel{n: Nat}

# The own setting of every role, one field per role.
type Owns is Data:
  Owns{chat: Choice, memory: Choice, auxiliary: Choice, image: Choice, subagent: Choice, worker: Choice, gateway: Choice, query: Choice, titles: Choice, judge: Choice, translate: Choice, speech: Choice, dictation: Choice}

# One resolution: the roles' own settings and the all-roles setting.
type In is Data:
  In{owns: Owns, all: Choice}

# Where a role's model comes from: its own setting n, the all-roles
# setting n, or the role's default.
type Src is Data:
  Own{n: Nat}
  All{n: Nat}
  Default{}

# One row of the table.
type Row is Data:
  Row{role: Role, src: Src}

# The roles
# ---------

# Every role, in order.
def roles() -> List<&2, Role>:
  [Chat{}, Memory{}, Auxiliary{}, Image{}, Subagent{}, Worker{}, Gateway{}, Query{}, Titles{}, Judge{}, Translate{}, Speech{}, Dictation{}]

# The role takes a chat model (a remote or local text model): every role
# but speech and dictation.
def takes_chat(r: Role) -> Bool:
  match r:
    case Chat{}:
      True{}
    case Memory{}:
      True{}
    case Auxiliary{}:
      True{}
    case Image{}:
      True{}
    case Subagent{}:
      True{}
    case Worker{}:
      True{}
    case Gateway{}:
      True{}
    case Query{}:
      True{}
    case Titles{}:
      True{}
    case Judge{}:
      True{}
    case Translate{}:
      True{}
    case Speech{}:
      False{}
    case Dictation{}:
      False{}

# The own setting of role r.
def own(o: Owns, r: Role) -> Choice:
  match o:
    case Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
      match r:
        case Chat{}:
          chat
        case Memory{}:
          memory
        case Auxiliary{}:
          auxiliary
        case Image{}:
          image
        case Subagent{}:
          subagent
        case Worker{}:
          worker
        case Gateway{}:
          gateway
        case Query{}:
          query
        case Titles{}:
          titles
        case Judge{}:
          judge
        case Translate{}:
          translate
        case Speech{}:
          speech
        case Dictation{}:
          dictation

# The resolver
# ------------

# a role without its own setting: the all-roles setting when it takes a
# chat model and the setting is set, else the default
def fill(takes: Bool, all: Choice) -> Src:
  match takes:
    case True{}:
      match all:
        case Unset{}:
          Default{}
        case Sel{n}:
          All{n}
    case False{}:
      Default{}

# where the model of role r comes from, given its own setting
def source(r: Role, mine: Choice, all: Choice) -> Src:
  match mine:
    case Sel{n}:
      Own{n}
    case Unset{}:
      fill(takes_chat(r), all)

# the rows of the roles rs
def rows(rs: List<&2, Role>, +o: Owns, +all: Choice) -> List<&2, Row>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> rest:
      Row{r, source(r, own(o, r), all)} <> rows(rest, o, all)

# the table of x: every role once, in order
def resolve(x: In) -> List<&2, Row>:
  match x:
    case In{o, all}:
      rows(roles(), o, all)

# The all-roles switch
# --------------------
# `/model --all n` makes every role that takes a chat model resolve to
# n: it saves the all-roles setting n, the chat's own setting n (the
# session switch saves `defaultModel`), and clears the own setting of
# every other role that takes a chat model; speech and dictation keep
# theirs (they never take the all-roles model). These defs are the model
# of that switch for the laws (laws/model_roles.bend, all_choice_*); the
# Rust code does not call them through an entry: it clears the roles
# whose row `resolve` answers as All{_} for In{every own setting unset,
# Sel{n}}, the chat aside.

# a role other than the chat after the switch: unset when it takes a
# chat model, else its own setting
def all_own.keep(takes: Bool, mine: Choice) -> Choice:
  match takes:
    case True{}:
      Unset{}
    case False{}:
      mine

# the own setting mine of role r after the switch to n
def all_own(r: Role, mine: Choice, +n: Nat) -> Choice:
  match r:
    case Chat{}:
      Sel{n}
    case Memory{}:
      all_own.keep(takes_chat(Memory{}), mine)
    case Auxiliary{}:
      all_own.keep(takes_chat(Auxiliary{}), mine)
    case Image{}:
      all_own.keep(takes_chat(Image{}), mine)
    case Subagent{}:
      all_own.keep(takes_chat(Subagent{}), mine)
    case Worker{}:
      all_own.keep(takes_chat(Worker{}), mine)
    case Gateway{}:
      all_own.keep(takes_chat(Gateway{}), mine)
    case Query{}:
      all_own.keep(takes_chat(Query{}), mine)
    case Titles{}:
      all_own.keep(takes_chat(Titles{}), mine)
    case Judge{}:
      all_own.keep(takes_chat(Judge{}), mine)
    case Translate{}:
      all_own.keep(takes_chat(Translate{}), mine)
    case Speech{}:
      all_own.keep(takes_chat(Speech{}), mine)
    case Dictation{}:
      all_own.keep(takes_chat(Dictation{}), mine)

# the settings x after `/model --all n`
def all_in(x: In, +n: Nat) -> In:
  match x:
    case In{o, all}:
      match o:
        case Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
          In{Owns{all_own(Chat{}, chat, n), all_own(Memory{}, memory, n), all_own(Auxiliary{}, auxiliary, n), all_own(Image{}, image, n), all_own(Subagent{}, subagent, n), all_own(Worker{}, worker, n), all_own(Gateway{}, gateway, n), all_own(Query{}, query, n), all_own(Titles{}, titles, n), all_own(Judge{}, judge, n), all_own(Translate{}, translate, n), all_own(Speech{}, speech, n), all_own(Dictation{}, dictation, n)}, Sel{n}}
