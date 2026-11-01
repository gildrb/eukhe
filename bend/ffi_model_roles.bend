# ffi_model_roles: the entry of the compiled Bend core for the source of
# every model role's model (bend/model_roles.bend `resolve`, the Rust
# `eukhe_bend::rules::model_roles::role_sources`). The codec is the wire
# format of bend/wire.bend:
#
#   request  the own Choice of every role, in the Role order (chat,
#            memory, auxiliary, image, subagent, gateway, query, titles,
#            judge, translate, speech, dictation), then the all-roles
#            Choice
#   Choice   0 (unset) | 1, n: Nat (the selector n)
#   reply    a list of Rows (W.put_list: the count, then the rows)
#   Row      the Role's tag (0..11, the Role order), then Src
#   Src      0, n: Nat (own) | 1, n: Nat (all roles) | 2 (the default)
#
# A malformed request, or one with input left over, answers the wire's
# error form.

import Base
import ./wire.bend as W
import ./model_roles.bend as M

# Encoders
# --------

def put_choice(c: M.Choice, rest: String) -> String:
  match c:
    case M.Unset{}:
      W.put_nat(0n, rest)
    case M.Sel{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_owns(o: M.Owns, rest: String) -> String:
  match o:
    case M.Owns{chat, memory, auxiliary, image, subagent, gateway, query, titles, judge, translate, speech, dictation}:
      put_choice(chat, put_choice(memory, put_choice(auxiliary, put_choice(image, put_choice(subagent, put_choice(gateway, put_choice(query, put_choice(titles, put_choice(judge, put_choice(translate, put_choice(speech, put_choice(dictation, rest))))))))))))

def put_in(x: M.In, rest: String) -> String:
  match x:
    case M.In{owns, all}:
      put_owns(owns, put_choice(all, rest))

# the wire tag of a role: its place in M.roles()
def role_tag(r: M.Role) -> Nat:
  match r:
    case M.Chat{}:
      0n
    case M.Memory{}:
      1n
    case M.Auxiliary{}:
      2n
    case M.Image{}:
      3n
    case M.Subagent{}:
      4n
    case M.Gateway{}:
      5n
    case M.Query{}:
      6n
    case M.Titles{}:
      7n
    case M.Judge{}:
      8n
    case M.Translate{}:
      9n
    case M.Speech{}:
      10n
    case M.Dictation{}:
      11n

def put_role(r: M.Role, rest: String) -> String:
  W.put_nat(role_tag(r), rest)

def put_src(x: M.Src, rest: String) -> String:
  match x:
    case M.Own{n}:
      W.put_nat(0n, W.put_nat(n, rest))
    case M.All{n}:
      W.put_nat(1n, W.put_nat(n, rest))
    case M.Default{}:
      W.put_nat(2n, rest)

def put_row(x: M.Row, rest: String) -> String:
  match x:
    case M.Row{role, src}:
      put_role(role, put_src(src, rest))

# the reply: the rows of the table
def put_res(rs: List<&2, M.Row>, rest: String) -> String:
  W.put_list(~M.Row, ~put_row, rs, rest)

# Decoders
# --------

def get_choice.n(r: W.Dec<Nat>) -> W.Dec<M.Choice>:
  match r:
    case W.Got{n, s}:
      W.Got{M.Sel{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_choice.tag(n: Nat, s: String) -> W.Dec<M.Choice>:
  match n:
    case 0n:
      W.Got{M.Unset{}, s}
    case 1n+a:
      match a:
        case 0n:
          get_choice.n(W.get_nat(s))
        case 1n+b:
          W.Bad{}

def get_choice.go(r: W.Dec<Nat>) -> W.Dec<M.Choice>:
  match r:
    case W.Got{n, s}:
      get_choice.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_choice(s: String) -> W.Dec<M.Choice>:
  get_choice.go(W.get_nat(s))

def get_owns.dictation(chat: M.Choice, memory: M.Choice, auxiliary: M.Choice, image: M.Choice, subagent: M.Choice, gateway: M.Choice, query: M.Choice, titles: M.Choice, judge: M.Choice, translate: M.Choice, speech: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{dictation, s}:
      W.Got{M.Owns{chat, memory, auxiliary, image, subagent, gateway, query, titles, judge, translate, speech, dictation}, s}
    case W.Bad{}:
      W.Bad{}

def get_owns.speech(chat: M.Choice, memory: M.Choice, auxiliary: M.Choice, image: M.Choice, subagent: M.Choice, gateway: M.Choice, query: M.Choice, titles: M.Choice, judge: M.Choice, translate: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{speech, s}:
      get_owns.dictation(chat, memory, auxiliary, image, subagent, gateway, query, titles, judge, translate, speech, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns.translate(chat: M.Choice, memory: M.Choice, auxiliary: M.Choice, image: M.Choice, subagent: M.Choice, gateway: M.Choice, query: M.Choice, titles: M.Choice, judge: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{translate, s}:
      get_owns.speech(chat, memory, auxiliary, image, subagent, gateway, query, titles, judge, translate, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns.judge(chat: M.Choice, memory: M.Choice, auxiliary: M.Choice, image: M.Choice, subagent: M.Choice, gateway: M.Choice, query: M.Choice, titles: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{judge, s}:
      get_owns.translate(chat, memory, auxiliary, image, subagent, gateway, query, titles, judge, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns.titles(chat: M.Choice, memory: M.Choice, auxiliary: M.Choice, image: M.Choice, subagent: M.Choice, gateway: M.Choice, query: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{titles, s}:
      get_owns.judge(chat, memory, auxiliary, image, subagent, gateway, query, titles, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns.query(chat: M.Choice, memory: M.Choice, auxiliary: M.Choice, image: M.Choice, subagent: M.Choice, gateway: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{query, s}:
      get_owns.titles(chat, memory, auxiliary, image, subagent, gateway, query, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns.gateway(chat: M.Choice, memory: M.Choice, auxiliary: M.Choice, image: M.Choice, subagent: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{gateway, s}:
      get_owns.query(chat, memory, auxiliary, image, subagent, gateway, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns.subagent(chat: M.Choice, memory: M.Choice, auxiliary: M.Choice, image: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{subagent, s}:
      get_owns.gateway(chat, memory, auxiliary, image, subagent, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns.image(chat: M.Choice, memory: M.Choice, auxiliary: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{image, s}:
      get_owns.subagent(chat, memory, auxiliary, image, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns.auxiliary(chat: M.Choice, memory: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{auxiliary, s}:
      get_owns.image(chat, memory, auxiliary, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns.memory(chat: M.Choice, r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{memory, s}:
      get_owns.auxiliary(chat, memory, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns.chat(r: W.Dec<M.Choice>) -> W.Dec<M.Owns>:
  match r:
    case W.Got{chat, s}:
      get_owns.memory(chat, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_owns(s: String) -> W.Dec<M.Owns>:
  get_owns.chat(get_choice(s))

def get_in.all(owns: M.Owns, r: W.Dec<M.Choice>) -> W.Dec<M.In>:
  match r:
    case W.Got{all, s}:
      W.Got{M.In{owns, all}, s}
    case W.Bad{}:
      W.Bad{}

def get_in.go(r: W.Dec<M.Owns>) -> W.Dec<M.In>:
  match r:
    case W.Got{owns, s}:
      get_in.all(owns, get_choice(s))
    case W.Bad{}:
      W.Bad{}

def get_in(s: String) -> W.Dec<M.In>:
  get_in.go(get_owns(s))

# The replies, as the Rust Reader reads them

# the role at place n of rs
def get_role.at(rs: List<&2, M.Role>, n: Nat, s: String) -> W.Dec<M.Role>:
  match rs:
    case Nil{}:
      W.Bad{}
    case Con{r, t}:
      match n:
        case 0n:
          W.Got{r, s}
        case 1n+m:
          get_role.at(t, m, s)

def get_role.go(r: W.Dec<Nat>) -> W.Dec<M.Role>:
  match r:
    case W.Got{n, s}:
      get_role.at(M.roles(), n, s)
    case W.Bad{}:
      W.Bad{}

def get_role(s: String) -> W.Dec<M.Role>:
  get_role.go(W.get_nat(s))

def get_src.own(r: W.Dec<Nat>) -> W.Dec<M.Src>:
  match r:
    case W.Got{n, s}:
      W.Got{M.Own{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_src.all(r: W.Dec<Nat>) -> W.Dec<M.Src>:
  match r:
    case W.Got{n, s}:
      W.Got{M.All{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_src.tag(n: Nat, s: String) -> W.Dec<M.Src>:
  match n:
    case 0n:
      get_src.own(W.get_nat(s))
    case 1n+a:
      match a:
        case 0n:
          get_src.all(W.get_nat(s))
        case 1n+b:
          match b:
            case 0n:
              W.Got{M.Default{}, s}
            case 1n+c:
              W.Bad{}

def get_src.go(r: W.Dec<Nat>) -> W.Dec<M.Src>:
  match r:
    case W.Got{n, s}:
      get_src.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_src(s: String) -> W.Dec<M.Src>:
  get_src.go(W.get_nat(s))

def get_row.src(role: M.Role, r: W.Dec<M.Src>) -> W.Dec<M.Row>:
  match r:
    case W.Got{src, s}:
      W.Got{M.Row{role, src}, s}
    case W.Bad{}:
      W.Bad{}

def get_row.go(r: W.Dec<M.Role>) -> W.Dec<M.Row>:
  match r:
    case W.Got{role, s}:
      get_row.src(role, get_src(s))
    case W.Bad{}:
      W.Bad{}

def get_row(s: String) -> W.Dec<M.Row>:
  get_row.go(get_role(s))

def get_res(s: String) -> W.Dec<List<&2, M.Row>>:
  W.get_list(~M.Row, ~get_row, s)

# The entry
# ---------

def ffi.end(done: Bool, x: M.In) -> String:
  match done:
    case True{}:
      put_res(M.resolve(x), "")
    case False{}:
      W.err("model_roles: input left over")

def ffi.go(r: W.Dec<M.In>) -> String:
  match r:
    case W.Got{x, s}:
      ffi.end(W.end(s), x)
    case W.Bad{}:
      W.err("model_roles: malformed request")

# One resolution: every role's own setting and the all-roles setting in,
# the table (every role's source, in the role order) out.
def ffi(input: String) -> String:
  ffi.go(get_in(input))
