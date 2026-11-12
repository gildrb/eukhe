# eukhe: the laws of area model_roles

import Base
import ../bend/model_roles.bend as Mr
import ../bend/ffi_model_roles.bend as FMr
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# Requirements
# ------------
# R1: the table answers every role once, in the role order (eukhe_types
#     ModelRole).
# R2: a role's own setting, when set, gives its model; only its own field
#     is read for it.
# R3: else the all-roles setting (`modelRoles.all`), when set, for a role
#     that takes a chat model.
# R4: else the role's default; speech and dictation never take the
#     all-roles model.
# R5-R7: the wire codec (below); R8: the entry against a spec (below).
# A1: `/model --all n` (crates/eukhe-daemon/src/model_switch.rs
#     handle_set_model with allRoles): every role the all-roles model
#     reaches (crates/eukhe-core/src/models/roles.rs all_roles_reach) runs
#     on n afterwards; every other role resolves as before the switch.
#
# The model roles
# ---------------
# bend/model_roles.bend: where the model of every model role comes from
# (the Rust `role_table`, crates/eukhe-core/src/models/roles.rs).

def mr_role_eq(a: Mr.Role, b: Mr.Role) -> Bool:
  match a b:
    case Mr.Chat{} Mr.Chat{}:
      True{}
    case Mr.Memory{} Mr.Memory{}:
      True{}
    case Mr.Auxiliary{} Mr.Auxiliary{}:
      True{}
    case Mr.Image{} Mr.Image{}:
      True{}
    case Mr.Subagent{} Mr.Subagent{}:
      True{}
    case Mr.Worker{} Mr.Worker{}:
      True{}
    case Mr.Gateway{} Mr.Gateway{}:
      True{}
    case Mr.Query{} Mr.Query{}:
      True{}
    case Mr.Titles{} Mr.Titles{}:
      True{}
    case Mr.Judge{} Mr.Judge{}:
      True{}
    case Mr.Translate{} Mr.Translate{}:
      True{}
    case Mr.Speech{} Mr.Speech{}:
      True{}
    case Mr.Dictation{} Mr.Dictation{}:
      True{}
    case _ _:
      False{}

def mr_count.add(hit: Bool, k: Nat) -> Nat:
  match hit:
    case True{}:
      1n+k
    case False{}:
      k

# how many times r occurs in rs
def mr_count(rs: List<&2, Mr.Role>, +r: Mr.Role) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{x, t}:
      mr_count.add(mr_role_eq(x, r), mr_count(t, r))

# the roles of the rows rs, in order
def mr_roles_of(rs: List<&2, Mr.Row>) -> List<&2, Mr.Role>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      match x:
        case Mr.Row{q, src}:
          q <> mr_roles_of(t)

def mr_at.pick(hit: Bool, src: Mr.Src, rest: Maybe<&2, Mr.Src>) -> Maybe<&2, Mr.Src>:
  match hit:
    case True{}:
      Some{src}
    case False{}:
      rest

# the source of the first row of role r in rs, or none
def mr_at(rs: List<&2, Mr.Row>, +r: Mr.Role) -> Maybe<&2, Mr.Src>:
  match rs:
    case Nil{}:
      None{}
    case Con{x, t}:
      match x:
        case Mr.Row{q, src}:
          mr_at.pick(mr_role_eq(q, r), src, mr_at(t, r))

# whether each role of rs takes a chat model, in order
def mr_takes(rs: List<&2, Mr.Role>) -> List<&2, Bool>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Mr.takes_chat(x) <> mr_takes(t)

# LAW roles_exact (R1): every role occurs exactly once in the role list
# EXCLUDES: a role dropped from the table, or listed twice
law roles_exact:
  for r: Mr.Role
  {mr_count(Mr.roles(), r) == 1n : Nat}

# LAW table_roles (R1): the table answers exactly the roles, in the role order, whatever the
# settings
# EXCLUDES: a row dropped, added or moved, a table whose shape depends on
#   the settings
law table_roles:
  for x: Mr.In
  {mr_roles_of(Mr.resolve(x)) == Mr.roles() : List<&2, Mr.Role>}

# LAW own_wins (R2): a role whose own setting is set takes it, whatever the all-roles setting
# EXCLUDES: the all-roles model above a role's own model, another role's
#   own setting, the all-roles selector in place of the own one
law own_wins:
  for o: Mr.Owns
  for all: Mr.Choice
  for r: Mr.Role
  for n: Nat
  for h: {Mr.own(o, r) == Mr.Sel{n} : Mr.Choice}
  {mr_at(Mr.resolve(Mr.In{o, all}), r) == Some{Mr.Own{n}} : Maybe<&2, Mr.Src>}

# LAW all_fills (R3): a role without its own setting that takes a chat model takes the
# all-roles model when it is set
# EXCLUDES: the role default above a set all-roles model, the all-roles
#   model ignored by some chat role
law all_fills:
  for o: Mr.Owns
  for r: Mr.Role
  for n: Nat
  for h: {Mr.own(o, r) == Mr.Unset{} : Mr.Choice}
  for t: {Mr.takes_chat(r) == True{} : Bool}
  {mr_at(Mr.resolve(Mr.In{o, Mr.Sel{n}}), r) == Some{Mr.All{n}} : Maybe<&2, Mr.Src>}

# LAW default_when_unset (R4): a role with neither its own nor the all-roles setting takes its
# default
# EXCLUDES: a model invented for an unset role
law default_when_unset:
  for o: Mr.Owns
  for +r: Mr.Role
  for h: {Mr.own(o, r) == Mr.Unset{} : Mr.Choice}
  {mr_at(Mr.resolve(Mr.In{o, Mr.Unset{}}), r) == Some{Mr.Default{}} : Maybe<&2, Mr.Src>}

# LAW local_roles_skip_all (R4): a role that takes no chat model and has no own setting takes its
# default, whatever the all-roles setting
# EXCLUDES: the all-roles (chat) model sent to speech or dictation
law local_roles_skip_all:
  for o: Mr.Owns
  for all: Mr.Choice
  for r: Mr.Role
  for h: {Mr.own(o, r) == Mr.Unset{} : Mr.Choice}
  for t: {Mr.takes_chat(r) == False{} : Bool}
  {mr_at(Mr.resolve(Mr.In{o, all}), r) == Some{Mr.Default{}} : Maybe<&2, Mr.Src>}

# LAW takes_chat_example (R3, R4): anchor: every role takes a chat model but speech and dictation
# EXCLUDES: a chat role cut off from the all-roles model, a local role
#   given it
law takes_chat_example:
  {mr_takes(Mr.roles()) == [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, False{}, False{}] : List<&2, Bool>}

# LAW all_reaches_every_role (R3, R1): anchor: with only the all-roles setting, the whole table is the
# all-roles model for every chat role and the default for speech and
# dictation
# EXCLUDES: a role the all-roles model misses, a wrong order, speech or
#   dictation on the all-roles model
law all_reaches_every_role:
  for n: Nat
  {Mr.resolve(Mr.In{Mr.Owns{Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}}, Mr.Sel{n}}) == [Mr.Row{Mr.Chat{}, Mr.All{n}}, Mr.Row{Mr.Memory{}, Mr.All{n}}, Mr.Row{Mr.Auxiliary{}, Mr.All{n}}, Mr.Row{Mr.Image{}, Mr.All{n}}, Mr.Row{Mr.Subagent{}, Mr.All{n}}, Mr.Row{Mr.Worker{}, Mr.All{n}}, Mr.Row{Mr.Gateway{}, Mr.All{n}}, Mr.Row{Mr.Query{}, Mr.All{n}}, Mr.Row{Mr.Titles{}, Mr.All{n}}, Mr.Row{Mr.Judge{}, Mr.All{n}}, Mr.Row{Mr.Translate{}, Mr.All{n}}, Mr.Row{Mr.Speech{}, Mr.Default{}}, Mr.Row{Mr.Dictation{}, Mr.Default{}}] : List<&2, Mr.Row>}

# LAW unset_table (R4, R1): anchor: with nothing set, every role takes its default
# EXCLUDES: a model for an unset table, a row dropped
law unset_table:
  {Mr.resolve(Mr.In{Mr.Owns{Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}}, Mr.Unset{}}) == [Mr.Row{Mr.Chat{}, Mr.Default{}}, Mr.Row{Mr.Memory{}, Mr.Default{}}, Mr.Row{Mr.Auxiliary{}, Mr.Default{}}, Mr.Row{Mr.Image{}, Mr.Default{}}, Mr.Row{Mr.Subagent{}, Mr.Default{}}, Mr.Row{Mr.Worker{}, Mr.Default{}}, Mr.Row{Mr.Gateway{}, Mr.Default{}}, Mr.Row{Mr.Query{}, Mr.Default{}}, Mr.Row{Mr.Titles{}, Mr.Default{}}, Mr.Row{Mr.Judge{}, Mr.Default{}}, Mr.Row{Mr.Translate{}, Mr.Default{}}, Mr.Row{Mr.Speech{}, Mr.Default{}}, Mr.Row{Mr.Dictation{}, Mr.Default{}}] : List<&2, Mr.Row>}

# LAW own_table (R2, R1): anchor: with every own setting set (role k: the selector k + 1) and
# the all-roles setting, every role takes its own setting
# EXCLUDES: one role's own setting read for another (a field swap), the
#   all-roles model above an own one
law own_table:
  {Mr.resolve(Mr.In{Mr.Owns{Mr.Sel{1n}, Mr.Sel{2n}, Mr.Sel{3n}, Mr.Sel{4n}, Mr.Sel{5n}, Mr.Sel{6n}, Mr.Sel{7n}, Mr.Sel{8n}, Mr.Sel{9n}, Mr.Sel{10n}, Mr.Sel{11n}, Mr.Sel{12n}, Mr.Sel{13n}}, Mr.Sel{0n}}) == [Mr.Row{Mr.Chat{}, Mr.Own{1n}}, Mr.Row{Mr.Memory{}, Mr.Own{2n}}, Mr.Row{Mr.Auxiliary{}, Mr.Own{3n}}, Mr.Row{Mr.Image{}, Mr.Own{4n}}, Mr.Row{Mr.Subagent{}, Mr.Own{5n}}, Mr.Row{Mr.Worker{}, Mr.Own{6n}}, Mr.Row{Mr.Gateway{}, Mr.Own{7n}}, Mr.Row{Mr.Query{}, Mr.Own{8n}}, Mr.Row{Mr.Titles{}, Mr.Own{9n}}, Mr.Row{Mr.Judge{}, Mr.Own{10n}}, Mr.Row{Mr.Translate{}, Mr.Own{11n}}, Mr.Row{Mr.Speech{}, Mr.Own{12n}}, Mr.Row{Mr.Dictation{}, Mr.Own{13n}}] : List<&2, Mr.Row>}

# The own setting of a role
# -------------------------

# the own setting of role r: the field of o named after r (R2)
def mr_own(o: Mr.Owns, r: Mr.Role) -> Mr.Choice:
  match o:
    case Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
      match r:
        case Mr.Chat{}:
          chat
        case Mr.Memory{}:
          memory
        case Mr.Auxiliary{}:
          auxiliary
        case Mr.Image{}:
          image
        case Mr.Subagent{}:
          subagent
        case Mr.Worker{}:
          worker
        case Mr.Gateway{}:
          gateway
        case Mr.Query{}:
          query
        case Mr.Titles{}:
          titles
        case Mr.Judge{}:
          judge
        case Mr.Translate{}:
          translate
        case Mr.Speech{}:
          speech
        case Mr.Dictation{}:
          dictation

def mr_put.pick(hit: Bool, c: Mr.Choice, old: Mr.Choice) -> Mr.Choice:
  match hit:
    case True{}:
      c
    case False{}:
      old

# the setting of the field of role k after role q's own setting is set to
# c: c when k is q, else old
def mr_put(+q: Mr.Role, k: Mr.Role, c: Mr.Choice, old: Mr.Choice) -> Mr.Choice:
  mr_put.pick(mr_role_eq(q, k), c, old)

# the own settings o with role q's own setting set to c, every other kept
def mr_set_own(o: Mr.Owns, +q: Mr.Role, +c: Mr.Choice) -> Mr.Owns:
  match o:
    case Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
      Mr.Owns{mr_put(q, Mr.Chat{}, c, chat), mr_put(q, Mr.Memory{}, c, memory), mr_put(q, Mr.Auxiliary{}, c, auxiliary), mr_put(q, Mr.Image{}, c, image), mr_put(q, Mr.Subagent{}, c, subagent), mr_put(q, Mr.Worker{}, c, worker), mr_put(q, Mr.Gateway{}, c, gateway), mr_put(q, Mr.Query{}, c, query), mr_put(q, Mr.Titles{}, c, titles), mr_put(q, Mr.Judge{}, c, judge), mr_put(q, Mr.Translate{}, c, translate), mr_put(q, Mr.Speech{}, c, speech), mr_put(q, Mr.Dictation{}, c, dictation)}

# LAW own_others_ignored (R2): for every settings, every all-roles setting
# and every two different roles q and r, changing q's own setting (to any
# setting) leaves r's row of the table unchanged: a role's source reads no
# other role's own setting
# EXCLUDES: a role that falls back to another role's own setting
#   (dictation unset reading speech's), two roles' fields swapped, a role
#   that reads a field shared with another
law own_others_ignored:
  for o: Mr.Owns
  for all: Mr.Choice
  for q: Mr.Role
  for r: Mr.Role
  for c: Mr.Choice
  for h: {mr_role_eq(q, r) == False{} : Bool}
  {mr_at(Mr.resolve(Mr.In{mr_set_own(o, q, c), all}), r) == mr_at(Mr.resolve(Mr.In{o, all}), r) : Maybe<&2, Mr.Src>}

# The all-roles switch, as Rust runs it (A1)
# ------------------------------------------
# `/model --all n` (crates/eukhe-daemon/src/model_switch.rs
# handle_set_model, allRoles true, the model saved for the chat): the
# session switch saves the chat's own model n (`defaultModel`); Rust asks
# the entry the request `role_sources(|_| false, true)` writes (every own
# setting unset, the all-roles selector 0: all_roles_reach,
# crates/eukhe-core/src/models/roles.rs) and clears the own setting of
# every role whose row answers All (save_all_roles_model,
# crates/eukhe-core/src/settings/manager.rs; the chat's own setting is
# not a cleared setting, own_decl), then saves n as the all-roles setting.
# The helpers below model those Rust steps over the table Mr.resolve
# answers (the entry answers it encoded: mrw_answers, mrw_entry_spec).

# every own setting unset
def mr_unset() -> Mr.Owns:
  Mr.Owns{Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}}

def mr_reached.src(m: Maybe<&2, Mr.Src>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      match s:
        case Mr.Own{k}:
          False{}
        case Mr.All{k}:
          True{}
        case Mr.Default{}:
          False{}

# A1: role r is one all_roles_reach lists: its row answers All for every
# own setting unset and the all-roles selector 0
def mr_reached(+r: Mr.Role) -> Bool:
  mr_reached.src(mr_at(Mr.resolve(Mr.In{mr_unset(), Mr.Sel{0n}}), r))

def mr_switched.keep(reached: Bool, mine: Mr.Choice) -> Mr.Choice:
  match reached:
    case True{}:
      Mr.Unset{}
    case False{}:
      mine

def mr_switched.chat(chat: Bool, reached: Bool, mine: Mr.Choice, +n: Nat) -> Mr.Choice:
  match chat:
    case True{}:
      Mr.Sel{n}
    case False{}:
      mr_switched.keep(reached, mine)

# A1: the own setting mine of role r after the switch to n: n for the
# chat, unset for another reached role, else kept
def mr_switched(+r: Mr.Role, mine: Mr.Choice, +n: Nat) -> Mr.Choice:
  mr_switched.chat(mr_role_eq(r, Mr.Chat{}), mr_reached(r), mine, n)

# A1: the own settings o after the switch to n
def mr_switch(o: Mr.Owns, +n: Nat) -> Mr.Owns:
  match o:
    case Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
      Mr.Owns{mr_switched(Mr.Chat{}, chat, n), mr_switched(Mr.Memory{}, memory, n), mr_switched(Mr.Auxiliary{}, auxiliary, n), mr_switched(Mr.Image{}, image, n), mr_switched(Mr.Subagent{}, subagent, n), mr_switched(Mr.Worker{}, worker, n), mr_switched(Mr.Gateway{}, gateway, n), mr_switched(Mr.Query{}, query, n), mr_switched(Mr.Titles{}, titles, n), mr_switched(Mr.Judge{}, judge, n), mr_switched(Mr.Translate{}, translate, n), mr_switched(Mr.Speech{}, speech, n), mr_switched(Mr.Dictation{}, dictation, n)}

# the selector a row runs on: its own or all-roles selector, none for the
# default
def mr_runs(m: Maybe<&2, Mr.Src>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      match s:
        case Mr.Own{k}:
          Some{k}
        case Mr.All{k}:
          Some{k}
        case Mr.Default{}:
          None{}

# LAW all_switch_runs_n (A1): for every own settings o and every n, after
# the switch as Rust runs it (the chat's own setting n, every role
# all_roles_reach lists cleared, the all-roles setting n), every role
# all_roles_reach lists runs on the selector n. Assumes the switch saves
# the chat's own model (save "chat"); a project's own setting is outside
# this model
# EXCLUDES: a role the all-roles model reaches but whose own setting is
#   left over (cleared too few roles), a reached role resolved to its
#   default, a probe that lists a role the all-roles setting does not fill
law all_switch_runs_n:
  for o: Mr.Owns
  for +n: Nat
  for r: Mr.Role
  for h: {mr_reached(r) == True{} : Bool}
  {mr_runs(mr_at(Mr.resolve(Mr.In{mr_switch(o, n), Mr.Sel{n}}), r)) == Some{n} : Maybe<&2, Nat>}

# LAW all_switch_keeps_others (A1): for every own settings o, every
# all-roles setting a before the switch and every n, a role
# all_roles_reach does not list resolves after the switch to n (as Rust
# runs it) exactly as before it
# EXCLUDES: the all-roles model sent to speech or dictation, their own
#   setting cleared or lost by the switch
law all_switch_keeps_others:
  for o: Mr.Owns
  for a: Mr.Choice
  for +n: Nat
  for r: Mr.Role
  for h: {mr_reached(r) == False{} : Bool}
  {mr_at(Mr.resolve(Mr.In{mr_switch(o, n), Mr.Sel{n}}), r) == mr_at(Mr.resolve(Mr.In{o, a}), r) : Maybe<&2, Mr.Src>}

# LAW all_switch_example (A1): anchor: the user's config (the chat on 3;
# memory, auxiliary and the gateway on 1; titles on 2; the all-roles
# setting 3) plus speech on its own 12; `/model --all 4` as Rust runs it:
# the chat on its own 4, every other chat role on the all-roles 4, speech
# on its own 12, dictation on its default
# EXCLUDES: a role with its own setting kept off the chosen model, a
#   vacuous all_switch_runs_n
law all_switch_example:
  {Mr.resolve(Mr.In{mr_switch(Mr.Owns{Mr.Sel{3n}, Mr.Sel{1n}, Mr.Sel{1n}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Sel{1n}, Mr.Unset{}, Mr.Sel{2n}, Mr.Unset{}, Mr.Unset{}, Mr.Sel{12n}, Mr.Unset{}}, 4n), Mr.Sel{4n}}) == [Mr.Row{Mr.Chat{}, Mr.Own{4n}}, Mr.Row{Mr.Memory{}, Mr.All{4n}}, Mr.Row{Mr.Auxiliary{}, Mr.All{4n}}, Mr.Row{Mr.Image{}, Mr.All{4n}}, Mr.Row{Mr.Subagent{}, Mr.All{4n}}, Mr.Row{Mr.Worker{}, Mr.All{4n}}, Mr.Row{Mr.Gateway{}, Mr.All{4n}}, Mr.Row{Mr.Query{}, Mr.All{4n}}, Mr.Row{Mr.Titles{}, Mr.All{4n}}, Mr.Row{Mr.Judge{}, Mr.All{4n}}, Mr.Row{Mr.Translate{}, Mr.All{4n}}, Mr.Row{Mr.Speech{}, Mr.Own{12n}}, Mr.Row{Mr.Dictation{}, Mr.Default{}}] : List<&2, Mr.Row>}

# The wire codec of bend/ffi_model_roles.bend (grammar: that file's
# header, crates/eukhe-bend/WIRE.md). R5: the request and every reply
# read back; R6: a well-formed request answers the table (Mr.resolve),
# encoded; R7: a malformed or overlong request answers the error form,
# never a table. Every input is free.

# what fits the wire: every Nat at most 14 digits
def mrw_choice_fits(c: Mr.Choice) -> Bool:
  match c:
    case Mr.Unset{}:
      True{}
    case Mr.Sel{n}:
      LawsBase.wire_fits(n)

def mrw_owns_fits(o: Mr.Owns) -> Bool:
  match o:
    case Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
      Bool.and(mrw_choice_fits(chat), Bool.and(mrw_choice_fits(memory), Bool.and(mrw_choice_fits(auxiliary), Bool.and(mrw_choice_fits(image), Bool.and(mrw_choice_fits(subagent), Bool.and(mrw_choice_fits(worker), Bool.and(mrw_choice_fits(gateway), Bool.and(mrw_choice_fits(query), Bool.and(mrw_choice_fits(titles), Bool.and(mrw_choice_fits(judge), Bool.and(mrw_choice_fits(translate), Bool.and(mrw_choice_fits(speech), mrw_choice_fits(dictation)))))))))))))

def mrw_in_fits(x: Mr.In) -> Bool:
  match x:
    case Mr.In{owns, all}:
      Bool.and(mrw_owns_fits(owns), mrw_choice_fits(all))

def mrw_src_fits(x: Mr.Src) -> Bool:
  match x:
    case Mr.Own{n}:
      LawsBase.wire_fits(n)
    case Mr.All{n}:
      LawsBase.wire_fits(n)
    case Mr.Default{}:
      True{}

def mrw_row_fits(x: Mr.Row) -> Bool:
  match x:
    case Mr.Row{role, src}:
      mrw_src_fits(src)

def mrw_rows_fit(rs: List<&2, Mr.Row>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(mrw_row_fits(x), mrw_rows_fit(t))

# LAW mrw_choice_round_trip (R5): a setting that fits reads back
# EXCLUDES: an unset setting read as set, a misread selector
law mrw_choice_round_trip:
  for +c: Mr.Choice
  for rest: String
  for h: {mrw_choice_fits(c) == True{} : Bool}
  {FMr.get_choice(FMr.put_choice(c, rest)) == Wr.Got{c, rest} : Wr.Dec<Mr.Choice>}

# LAW mrw_owns_round_trip (R5): the own settings that fit read back
# EXCLUDES: a role's own setting lost, misread or read as another role's
law mrw_owns_round_trip:
  for +o: Mr.Owns
  for rest: String
  for h: {mrw_owns_fits(o) == True{} : Bool}
  {FMr.get_owns(FMr.put_owns(o, rest)) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}

# LAW mrw_in_round_trip (R5): a request that fits reads back
# EXCLUDES: the all-roles setting lost or swapped with an own setting
law mrw_in_round_trip:
  for +x: Mr.In
  for rest: String
  for h: {mrw_in_fits(x) == True{} : Bool}
  {FMr.get_in(FMr.put_in(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Mr.In>}

# LAW mrw_role_round_trip (R5): a role reads back, and the rest is untouched
# EXCLUDES: two roles with one tag, a role read as another
law mrw_role_round_trip:
  for r: Mr.Role
  for rest: String
  {FMr.get_role(FMr.put_role(r, rest)) == Wr.Got{r, rest} : Wr.Dec<Mr.Role>}

# LAW mrw_src_round_trip (R5): a source that fits reads back
# EXCLUDES: an own source read as the all-roles one, or the reverse, a
#   default read as a model
law mrw_src_round_trip:
  for +x: Mr.Src
  for rest: String
  for h: {mrw_src_fits(x) == True{} : Bool}
  {FMr.get_src(FMr.put_src(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Mr.Src>}

# LAW mrw_row_round_trip (R5): a row that fits reads back
# EXCLUDES: a row's role or source lost or misread
law mrw_row_round_trip:
  for +x: Mr.Row
  for rest: String
  for h: {mrw_row_fits(x) == True{} : Bool}
  {FMr.get_row(FMr.put_row(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Mr.Row>}

# LAW mrw_rows_round_trip (R5): the reply, rows that fit of a length that fits, reads back
# EXCLUDES: rows lost, added, reordered or misread, a wrong count
law mrw_rows_round_trip:
  for +rs: List<&2, Mr.Row>
  for rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Mr.Row, rs)), mrw_rows_fit(rs)) == True{} : Bool}
  {FMr.get_res(FMr.put_res(rs, rest)) == Wr.Got{rs, rest} : Wr.Dec<List<&2, Mr.Row>>}

# LAW mrw_answers (R6): an encoded request answers the table, encoded
# EXCLUDES: an entry that resolves other than Mr.resolve, or drops a
#   setting on the way in or a row on the way out
law mrw_answers:
  for +x: Mr.In
  for h: {mrw_in_fits(x) == True{} : Bool}
  {FMr.ffi(FMr.put_in(x, "")) == FMr.put_res(Mr.resolve(x), "") : String}

# LAW mrw_malformed (R7): a malformed request answers the error form
# EXCLUDES: a table for a request it cannot read
law mrw_malformed:
  for +s: String
  for h: {FMr.get_in(s) == Wr.Bad{} : Wr.Dec<Mr.In>}
  {FMr.ffi(s) == Wr.err("model_roles: malformed request") : String}

# LAW mrw_left_over (R7): a request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law mrw_left_over:
  for +x: Mr.In
  for c: Char
  for rest: String
  for h: {mrw_in_fits(x) == True{} : Bool}
  {FMr.ffi(FMr.put_in(x, SCon{c, rest})) == Wr.err("model_roles: input left over") : String}

# LAW mrw_choice_example (R5): anchor and witness: a setting is 0 (unset) or 1, then the selector
# EXCLUDES: a vacuous mrw_choice_round_trip, tags swapped
law mrw_choice_example:
  {mrw_choice_fits(Mr.Sel{7n}) == True{} : Bool} & {FMr.put_choice(Mr.Unset{}, FMr.put_choice(Mr.Sel{7n}, "")) == "0,1,7," : String}

# LAW mrw_owns_example (R5): anchor and witness: the own settings are one setting per role, in the
# role order
# EXCLUDES: a vacuous mrw_owns_round_trip, roles in another order
law mrw_owns_example:
  {mrw_owns_fits(Mr.Owns{Mr.Sel{1n}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Sel{12n}}) == True{} : Bool} & {FMr.put_owns(Mr.Owns{Mr.Sel{1n}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Sel{12n}}, "") == "1,1,0,0,0,0,0,0,0,0,0,0,0,1,12," : String}

# LAW mrw_in_example (R5): anchor and witness: a request is the own settings, then the all-roles
# setting
# EXCLUDES: a vacuous mrw_in_round_trip or mrw_answers, the all-roles
#   setting first
law mrw_in_example:
  {mrw_in_fits(Mr.In{Mr.Owns{Mr.Sel{1n}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Sel{12n}}, Mr.Sel{0n}}) == True{} : Bool} & {FMr.put_in(Mr.In{Mr.Owns{Mr.Sel{1n}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Sel{12n}}, Mr.Sel{0n}}, "") == "1,1,0,0,0,0,0,0,0,0,0,0,0,1,12,1,0," : String}

# LAW mrw_role_example (R5): anchor: a role's tag is its place in the role order
# EXCLUDES: tags in another order than the roles'
law mrw_role_example:
  {FMr.put_role(Mr.Chat{}, FMr.put_role(Mr.Memory{}, FMr.put_role(Mr.Auxiliary{}, FMr.put_role(Mr.Image{}, FMr.put_role(Mr.Subagent{}, FMr.put_role(Mr.Worker{}, FMr.put_role(Mr.Gateway{}, FMr.put_role(Mr.Query{}, FMr.put_role(Mr.Titles{}, FMr.put_role(Mr.Judge{}, FMr.put_role(Mr.Translate{}, FMr.put_role(Mr.Speech{}, FMr.put_role(Mr.Dictation{}, ""))))))))))))) == "0,1,2,3,4,5,6,7,8,9,10,11,12," : String}

# LAW mrw_src_example (R5): anchor and witness: a source is 0, n (own) | 1, n (all roles) | 2
# (the default)
# EXCLUDES: a vacuous mrw_src_round_trip, tags in another order
law mrw_src_example:
  {mrw_src_fits(Mr.Own{3n}) == True{} : Bool} & {FMr.put_src(Mr.Own{3n}, FMr.put_src(Mr.All{4n}, FMr.put_src(Mr.Default{}, ""))) == "0,3,1,4,2," : String}

# LAW mrw_row_example (R5): anchor and witness: a row is the role, then the source
# EXCLUDES: a vacuous mrw_row_round_trip, fields in another order
law mrw_row_example:
  {mrw_row_fits(Mr.Row{Mr.Chat{}, Mr.Own{5n}}) == True{} : Bool} & {FMr.put_row(Mr.Row{Mr.Speech{}, Mr.Default{}}, FMr.put_row(Mr.Row{Mr.Chat{}, Mr.Own{5n}}, "")) == "11,2,0,0,5," : String}

# LAW mrw_rows_example (R5): anchor and witness: the reply is the count of rows, then the rows
# EXCLUDES: a vacuous mrw_rows_round_trip, a missing count
law mrw_rows_example:
  {Bool.and(LawsBase.wire_fits(2n), mrw_rows_fit([Mr.Row{Mr.Chat{}, Mr.Own{1n}}, Mr.Row{Mr.Memory{}, Mr.All{0n}}])) == True{} : Bool} & {FMr.put_res([Mr.Row{Mr.Chat{}, Mr.Own{1n}}, Mr.Row{Mr.Memory{}, Mr.All{0n}}], "") == "2,0,0,1,1,1,0," : String}

# LAW mrw_ffi_example (R6): anchor: the chat's own model and the all-roles model, end to end
# EXCLUDES: an entry that answers other bytes than the grammar's
law mrw_ffi_example:
  {FMr.ffi("1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,") == "13,0,0,1,1,1,0,2,1,0,3,1,0,4,1,0,5,1,0,6,1,0,7,1,0,8,1,0,9,1,0,10,1,0,11,2,12,2," : String}

# LAW mrw_malformed_example (R7): witness: a setting with an unknown tag is malformed
# EXCLUDES: a vacuous mrw_malformed
law mrw_malformed_example:
  {FMr.get_in("2,") == Wr.Bad{} : Wr.Dec<Mr.In>} & {FMr.ffi("2,") == Wr.err("model_roles: malformed request") : String}

# LAW mrw_choice_exact (R7): a decoded setting is exactly an encoding: any other input is Bad{}
# EXCLUDES: a selector read with leading zeros or more than 14 digits, an
#   unknown tag read as a setting, a second spelling of a setting
law mrw_choice_exact:
  for +s: String
  for +c: Mr.Choice
  for +rest: String
  for h: {FMr.get_choice(s) == Wr.Got{c, rest} : Wr.Dec<Mr.Choice>}
  {s == FMr.put_choice(c, rest) : String}

# LAW mrw_owns_exact (R7): decoded own settings are exactly an encoding: any other input is Bad{}
# EXCLUDES: a non-canonical own setting accepted, settings read in
#   another order than written
law mrw_owns_exact:
  for +s: String
  for +o: Mr.Owns
  for +rest: String
  for h: {FMr.get_owns(s) == Wr.Got{o, rest} : Wr.Dec<Mr.Owns>}
  {s == FMr.put_owns(o, rest) : String}

# LAW mrw_in_exact (R7): a decoded request is exactly an encoding: any other input is Bad{}, so the entry answers a table only for a canonical request
# EXCLUDES: a zero-padded or overlong selector answered with a table, a
#   request read from a string no encoder writes
law mrw_in_exact:
  for +s: String
  for +x: Mr.In
  for +rest: String
  for h: {FMr.get_in(s) == Wr.Got{x, rest} : Wr.Dec<Mr.In>}
  {s == FMr.put_in(x, rest) : String}

# LAW mrw_leading_zero_example (R7): anchor: a zero-padded selector is malformed, alone and in a request
# EXCLUDES: a decoder that reads 07 as 7, a vacuous mrw_choice_exact
law mrw_leading_zero_example:
  {FMr.get_choice("1,07,") == Wr.Bad{} : Wr.Dec<Mr.Choice>} & {FMr.ffi("0,0,0,0,0,0,0,0,0,0,0,0,0,1,07,") == Wr.err("model_roles: malformed request") : String}

# The entry against a spec (R8)
# -----------------------------
# R8: the entry answers every request Rust writes (every selector within
# the wire), spelled by the spec from the grammar of
# bend/ffi_model_roles.bend's header with the Wr primitives, with the
# spec's table (R1-R4 restated below: every role once in the role order;
# its own setting, else the all-roles setting for a role that takes a chat
# model, else its default), spelled by the spec; that request followed by
# more input answers `E model_roles: input left over`; every other input
# answers `E model_roles: malformed request`. The helpers below never call
# the entry's encoders or decoders, nor Mr.resolve.

# R1: every role, in the order of eukhe_types ModelRole
def mrs_roles() -> List<&2, Mr.Role>:
  [Mr.Chat{}, Mr.Memory{}, Mr.Auxiliary{}, Mr.Image{}, Mr.Subagent{}, Mr.Worker{}, Mr.Gateway{}, Mr.Query{}, Mr.Titles{}, Mr.Judge{}, Mr.Translate{}, Mr.Speech{}, Mr.Dictation{}]

# R8: the tag of a role on the wire: its place in mrs_roles
def mrs_tag(r: Mr.Role) -> Nat:
  match r:
    case Mr.Chat{}:
      0n
    case Mr.Memory{}:
      1n
    case Mr.Auxiliary{}:
      2n
    case Mr.Image{}:
      3n
    case Mr.Subagent{}:
      4n
    case Mr.Worker{}:
      5n
    case Mr.Gateway{}:
      6n
    case Mr.Query{}:
      7n
    case Mr.Titles{}:
      8n
    case Mr.Judge{}:
      9n
    case Mr.Translate{}:
      10n
    case Mr.Speech{}:
      11n
    case Mr.Dictation{}:
      12n

# R4: speech and dictation take only local models
def mrs_local(r: Mr.Role) -> Bool:
  match r:
    case Mr.Speech{}:
      True{}
    case Mr.Dictation{}:
      True{}
    case Mr.Chat{}:
      False{}
    case Mr.Memory{}:
      False{}
    case Mr.Auxiliary{}:
      False{}
    case Mr.Image{}:
      False{}
    case Mr.Subagent{}:
      False{}
    case Mr.Worker{}:
      False{}
    case Mr.Gateway{}:
      False{}
    case Mr.Query{}:
      False{}
    case Mr.Titles{}:
      False{}
    case Mr.Judge{}:
      False{}
    case Mr.Translate{}:
      False{}

# R3, R4: a role without its own setting: its default when it is local or
# the all-roles setting is unset, else the all-roles setting
def mrs_fill(local: Bool, all: Mr.Choice) -> Mr.Src:
  match local:
    case True{}:
      Mr.Default{}
    case False{}:
      match all:
        case Mr.Unset{}:
          Mr.Default{}
        case Mr.Sel{n}:
          Mr.All{n}

# R2-R4: the source of role r whose own setting is mine
def mrs_src(r: Mr.Role, mine: Mr.Choice, all: Mr.Choice) -> Mr.Src:
  match mine:
    case Mr.Sel{n}:
      Mr.Own{n}
    case Mr.Unset{}:
      mrs_fill(mrs_local(r), all)

# R8: a setting on the wire: 0 (unset) | 1, then the selector
def mrs_w_choice(c: Mr.Choice, rest: String) -> String:
  match c:
    case Mr.Unset{}:
      Wr.put_nat(0n, rest)
    case Mr.Sel{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

# R8: a request: every role's own setting in the role order, then the
# all-roles setting
def mrs_w_in(x: Mr.In, rest: String) -> String:
  match x:
    case Mr.In{o, all}:
      match o:
        case Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}:
          mrs_w_choice(chat, mrs_w_choice(memory, mrs_w_choice(auxiliary, mrs_w_choice(image, mrs_w_choice(subagent, mrs_w_choice(worker, mrs_w_choice(gateway, mrs_w_choice(query, mrs_w_choice(titles, mrs_w_choice(judge, mrs_w_choice(translate, mrs_w_choice(speech, mrs_w_choice(dictation, mrs_w_choice(all, rest))))))))))))))

# R8: a source on the wire: 0, n (own) | 1, n (all roles) | 2 (default)
def mrs_w_src(x: Mr.Src, rest: String) -> String:
  match x:
    case Mr.Own{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case Mr.All{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))
    case Mr.Default{}:
      Wr.put_nat(2n, rest)

# R8: the rows of the roles rs, each its tag then its source, then rest
def mrs_w_rows(rs: List<&2, Mr.Role>, +o: Mr.Owns, +all: Mr.Choice, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case +r <> t:
      Wr.put_nat(mrs_tag(r), mrs_w_src(mrs_src(r, mr_own(o, r), all), mrs_w_rows(t, o, all, rest)))

# R8: the reply to a request: the count of roles, then a row per role in
# the role order
def mrs_w_reply(x: Mr.In) -> String:
  match x:
    case Mr.In{+o, +all}:
      Wr.put_nat(List.length(&2, Mr.Role, mrs_roles()), mrs_w_rows(mrs_roles(), o, all, ""))

# LAW mrw_entry_spec (R8): the entry answers every request Rust spells,
# every selector within the wire, with the spec's table, spelled
# EXCLUDES: any reply other than the spec's for a request that fits (a
#   setting read for another role, a tag or source spelled otherwise, a
#   row dropped, a wrong source, a codec that agrees only with itself)
law mrw_entry_spec:
  for +x: Mr.In
  for h: {mrw_in_fits(x) == True{} : Bool}
  {FMr.ffi(mrs_w_in(x, "")) == mrs_w_reply(x) : String}

# LAW mrw_entry_left_over_spec (R8): a request Rust spells followed by
# more input answers `E model_roles: input left over`
# EXCLUDES: the input after the request ignored or read into a setting,
#   another error text
law mrw_entry_left_over_spec:
  for +x: Mr.In
  for +c: Char
  for +rest: String
  for h: {mrw_in_fits(x) == True{} : Bool}
  {FMr.ffi(mrs_w_in(x, SCon{c, rest})) == Wr.err("model_roles: input left over") : String}

# LAW mrw_entry_exact (R8): every input the entry does not answer with the
# error form is a request the spec spells, every selector within the wire
# EXCLUDES: a table for input that is no request (an unknown tag, a
#   zero-padded or 15-digit selector, a short request, input left over)
law mrw_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FMr.ffi(s)) == False{} : Bool}
  exs x: Mr.In
  {s == mrs_w_in(x, "") : String} & {mrw_in_fits(x) == True{} : Bool}

# LAW mrw_entry_left_over_exact (R8): every input the entry answers with
# `E model_roles: input left over` is a request the spec spells, every
# selector within the wire, followed by more input
# EXCLUDES: a malformed request reported as input left over
law mrw_entry_left_over_exact:
  for +s: String
  for e: {FMr.ffi(s) == Wr.err("model_roles: input left over") : String}
  exs x: Mr.In
  exs t: String
  {s == mrs_w_in(x, t) : String} & ({String.is_empty(t) == False{} : Bool} & {mrw_in_fits(x) == True{} : Bool})

# LAW mrw_entry_refuses (R8): every error the entry answers is exactly
# `E model_roles: malformed request` or `E model_roles: input left over`
# EXCLUDES: an error text that varies with the input, a third error form
law mrw_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FMr.ffi(s)) == True{} : Bool}
  {FMr.ffi(s) == Wr.err("model_roles: malformed request") : String} | {FMr.ffi(s) == Wr.err("model_roles: input left over") : String}

# LAW mrw_entry_spec_example (R8): anchor: the request Rust writes for
# speech's own setting and the all-roles setting (role k's own selector
# k + 1, so speech 12; the all-roles selector 0) is the spec's spelling,
# and the entry answers it with the spec's reply bytes: every chat role on
# the all-roles setting, speech on its own, dictation on its default; the
# same request with input left over
# EXCLUDES: a spec speller that drifts from the bytes Rust writes, a reply
#   Rust's reader refuses (an own row naming another role's selector), the
#   all-roles model sent to dictation
law mrw_entry_spec_example:
  {[mrs_w_in(Mr.In{Mr.Owns{Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Sel{12n}, Mr.Unset{}}, Mr.Sel{0n}}, ""), mrs_w_reply(Mr.In{Mr.Owns{Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Unset{}, Mr.Sel{12n}, Mr.Unset{}}, Mr.Sel{0n}}), FMr.ffi("0,0,0,0,0,0,0,0,0,0,0,1,12,0,1,0,"), FMr.ffi("0,0,0,0,0,0,0,0,0,0,0,1,12,0,1,0,x")] == ["0,0,0,0,0,0,0,0,0,0,0,1,12,0,1,0,", "13,0,1,0,1,1,0,2,1,0,3,1,0,4,1,0,5,1,0,6,1,0,7,1,0,8,1,0,9,1,0,10,1,0,11,0,12,12,2,", "13,0,1,0,1,1,0,2,1,0,3,1,0,4,1,0,5,1,0,6,1,0,7,1,0,8,1,0,9,1,0,10,1,0,11,0,12,12,2,", Wr.err("model_roles: input left over")] : List<&2, String>}
