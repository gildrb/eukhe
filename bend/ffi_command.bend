# ffi_command: the entry of the compiled Bend core for the paths of the
# slash commands (bend/command.bend: resolve, menu, key). Rust
# (crates/eukhe-tui/src/command_paths.rs) sends the whole table with each
# question: names cross as strings, and the entry turns their chars into
# the codes the model reads (and the model's lines back into chars).
#
# Wire (crates/eukhe-bend/WIRE.md):
#   Ent    = a record (path: List<String>, alias: List<String>, run: Bool,
#            free: Bool, arg: Bool)
#   Sel    = tag 0 NoRow | 1 Row (Nat)
#   Press  = tag 0 Tab | 1 Enter
#   Query  = tag 0 Resolve (line: String) | 1 Menu (line: String)
#            | 2 Key (line: String, sel: Sel, press: Press)
#   request  a record (table: List<Ent>, query: Query)
#   reply    Resolve: tag 0 Runs (List<String>, String) | 1 Opens
#            (List<String>) | 2 Unknown (List<String>, String) | 3 NoCmd
#            Menu: tag 0 Names | 1 Kids (List<String>, List<Nat>) | 2 Shut
#            Key: a record (line: String, open: Bool, submit: Bool)
# A malformed request, or one with input left over, answers the error
# form.

import Base
import ./wire.bend as W
import ./command.bend as M

# An entry of the table as it crosses: its names as strings.
type EntW is Data:
  EntW{path: List<&2, String>, alias: List<&2, String>, run: Bool, free: Bool, arg: Bool}

type Query is Data:
  QResolve{line: String}
  QMenu{line: String}
  QKey{line: String, sel: M.Sel, press: M.Press}

type Req is Data:
  Req{table: List<&2, EntW>, query: Query}

# Chars and codes
# ---------------

def codes(s: String) -> List<&2, Nat>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, r}:
      U32.to_nat(Char.to_u32(c)) <> codes(r)

def text(ns: List<&2, Nat>) -> String:
  match ns:
    case Nil{}:
      SNil{}
    case Con{n, r}:
      SCon{Chr{U32.from_nat(n)}, text(r)}

def names(xs: List<&2, String>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, r}:
      codes(x) <> names(r)

def texts(xs: List<&2, List<&2, Nat>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, r}:
      text(x) <> texts(r)

def ent(e: EntW) -> M.Ent:
  match e:
    case EntW{p, a, r, f, g}:
      M.Ent{names(p), names(a), r, f, g}

def ents(t: List<&2, EntW>) -> List<&2, M.Ent>:
  match t:
    case Nil{}:
      Nil{}
    case Con{e, r}:
      ent(e) <> ents(r)

# Strings
# -------

def put_strs(xs: List<&2, String>, rest: String) -> String:
  W.put_list(~String, ~W.put_str, xs, rest)

def get_strs(s: String) -> W.Dec<List<&2, String>>:
  W.get_list(~String, ~W.get_str, s)

# Entries
# -------

def put_ent(e: EntW, rest: String) -> String:
  match e:
    case EntW{p, a, r, f, g}:
      put_strs(p, put_strs(a, W.put_bool(r, W.put_bool(f, W.put_bool(g, rest)))))

def get_ent.arg(p: List<&2, String>, a: List<&2, String>, r: Bool, f: Bool, d: W.Dec<Bool>) -> W.Dec<EntW>:
  match d:
    case W.Got{g, s}:
      W.Got{EntW{p, a, r, f, g}, s}
    case W.Bad{}:
      W.Bad{}

def get_ent.free(p: List<&2, String>, a: List<&2, String>, r: Bool, d: W.Dec<Bool>) -> W.Dec<EntW>:
  match d:
    case W.Got{f, s}:
      get_ent.arg(p, a, r, f, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ent.run(p: List<&2, String>, a: List<&2, String>, d: W.Dec<Bool>) -> W.Dec<EntW>:
  match d:
    case W.Got{r, s}:
      get_ent.free(p, a, r, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ent.alias(p: List<&2, String>, d: W.Dec<List<&2, String>>) -> W.Dec<EntW>:
  match d:
    case W.Got{a, s}:
      get_ent.run(p, a, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ent.path(d: W.Dec<List<&2, String>>) -> W.Dec<EntW>:
  match d:
    case W.Got{p, s}:
      get_ent.alias(p, get_strs(s))
    case W.Bad{}:
      W.Bad{}

def get_ent(s: String) -> W.Dec<EntW>:
  get_ent.path(get_strs(s))

def put_table(t: List<&2, EntW>, rest: String) -> String:
  W.put_list(~EntW, ~put_ent, t, rest)

def get_table(s: String) -> W.Dec<List<&2, EntW>>:
  W.get_list(~EntW, ~get_ent, s)

# Queries
# -------

def put_sel(x: M.Sel, rest: String) -> String:
  match x:
    case M.NoRow{}:
      W.put_nat(0n, rest)
    case M.Row{i}:
      W.put_nat(1n, W.put_nat(i, rest))

def get_sel.row(d: W.Dec<Nat>) -> W.Dec<M.Sel>:
  match d:
    case W.Got{i, s}:
      W.Got{M.Row{i}, s}
    case W.Bad{}:
      W.Bad{}

def get_sel.tag(t: Nat, s: String) -> W.Dec<M.Sel>:
  match t:
    case 0n:
      W.Got{M.NoRow{}, s}
    case 1n:
      get_sel.row(W.get_nat(s))
    case 2n+x:
      W.Bad{}

def get_sel.go(d: W.Dec<Nat>) -> W.Dec<M.Sel>:
  match d:
    case W.Got{t, s}:
      get_sel.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_sel(s: String) -> W.Dec<M.Sel>:
  get_sel.go(W.get_nat(s))

def put_press(k: M.Press, rest: String) -> String:
  match k:
    case M.Tab{}:
      W.put_nat(0n, rest)
    case M.Enter{}:
      W.put_nat(1n, rest)

def get_press.tag(t: Nat, s: String) -> W.Dec<M.Press>:
  match t:
    case 0n:
      W.Got{M.Tab{}, s}
    case 1n:
      W.Got{M.Enter{}, s}
    case 2n+x:
      W.Bad{}

def get_press.go(d: W.Dec<Nat>) -> W.Dec<M.Press>:
  match d:
    case W.Got{t, s}:
      get_press.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_press(s: String) -> W.Dec<M.Press>:
  get_press.go(W.get_nat(s))

def put_query(q: Query, rest: String) -> String:
  match q:
    case QResolve{l}:
      W.put_nat(0n, W.put_str(l, rest))
    case QMenu{l}:
      W.put_nat(1n, W.put_str(l, rest))
    case QKey{l, x, k}:
      W.put_nat(2n, W.put_str(l, put_sel(x, put_press(k, rest))))

def get_query.resolve(d: W.Dec<String>) -> W.Dec<Query>:
  match d:
    case W.Got{l, s}:
      W.Got{QResolve{l}, s}
    case W.Bad{}:
      W.Bad{}

def get_query.menu(d: W.Dec<String>) -> W.Dec<Query>:
  match d:
    case W.Got{l, s}:
      W.Got{QMenu{l}, s}
    case W.Bad{}:
      W.Bad{}

def get_query.press(l: String, x: M.Sel, d: W.Dec<M.Press>) -> W.Dec<Query>:
  match d:
    case W.Got{k, s}:
      W.Got{QKey{l, x, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_query.sel(l: String, d: W.Dec<M.Sel>) -> W.Dec<Query>:
  match d:
    case W.Got{x, s}:
      get_query.press(l, x, get_press(s))
    case W.Bad{}:
      W.Bad{}

def get_query.key(d: W.Dec<String>) -> W.Dec<Query>:
  match d:
    case W.Got{l, s}:
      get_query.sel(l, get_sel(s))
    case W.Bad{}:
      W.Bad{}

def get_query.tag(t: Nat, s: String) -> W.Dec<Query>:
  match t:
    case 0n:
      get_query.resolve(W.get_str(s))
    case 1n:
      get_query.menu(W.get_str(s))
    case 2n:
      get_query.key(W.get_str(s))
    case 3n+x:
      W.Bad{}

def get_query.go(d: W.Dec<Nat>) -> W.Dec<Query>:
  match d:
    case W.Got{t, s}:
      get_query.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_query(s: String) -> W.Dec<Query>:
  get_query.go(W.get_nat(s))

# The request
# -----------

def put_req(r: Req, rest: String) -> String:
  match r:
    case Req{t, q}:
      put_table(t, put_query(q, rest))

def get_req.query(t: List<&2, EntW>, d: W.Dec<Query>) -> W.Dec<Req>:
  match d:
    case W.Got{q, s}:
      W.Got{Req{t, q}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.table(d: W.Dec<List<&2, EntW>>) -> W.Dec<Req>:
  match d:
    case W.Got{t, s}:
      get_req.query(t, get_query(s))
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.table(get_table(s))

# Replies
# -------

# The answers as they cross: names and lines as strings.
type ResW is Data:
  RunsW{path: List<&2, String>, args: String}
  OpensW{path: List<&2, String>}
  UnknownW{path: List<&2, String>, word: String}
  NoCmdW{}

type MenuW is Data:
  NamesW{}
  KidsW{path: List<&2, String>, items: List<&2, Nat>}
  ShutW{}

type OutW is Data:
  OutW{line: String, open: Bool, submit: Bool}

def res_w(r: M.Res) -> ResW:
  match r:
    case M.Runs{p, a}:
      RunsW{texts(p), text(a)}
    case M.Opens{p}:
      OpensW{texts(p)}
    case M.Unknown{p, w}:
      UnknownW{texts(p), text(w)}
    case M.NoCmd{}:
      NoCmdW{}

def menu_w(m: M.Menu) -> MenuW:
  match m:
    case M.Names{}:
      NamesW{}
    case M.Kids{p, xs}:
      KidsW{texts(p), xs}
    case M.Shut{}:
      ShutW{}

def out_w(o: M.Out) -> OutW:
  match o:
    case M.Out{l, a, b}:
      OutW{text(l), a, b}

def put_res(r: ResW, rest: String) -> String:
  match r:
    case RunsW{p, a}:
      W.put_nat(0n, put_strs(p, W.put_str(a, rest)))
    case OpensW{p}:
      W.put_nat(1n, put_strs(p, rest))
    case UnknownW{p, w}:
      W.put_nat(2n, put_strs(p, W.put_str(w, rest)))
    case NoCmdW{}:
      W.put_nat(3n, rest)

def get_res.runs.args(p: List<&2, String>, d: W.Dec<String>) -> W.Dec<ResW>:
  match d:
    case W.Got{a, s}:
      W.Got{RunsW{p, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_res.runs(d: W.Dec<List<&2, String>>) -> W.Dec<ResW>:
  match d:
    case W.Got{p, s}:
      get_res.runs.args(p, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_res.opens(d: W.Dec<List<&2, String>>) -> W.Dec<ResW>:
  match d:
    case W.Got{p, s}:
      W.Got{OpensW{p}, s}
    case W.Bad{}:
      W.Bad{}

def get_res.unknown.word(p: List<&2, String>, d: W.Dec<String>) -> W.Dec<ResW>:
  match d:
    case W.Got{w, s}:
      W.Got{UnknownW{p, w}, s}
    case W.Bad{}:
      W.Bad{}

def get_res.unknown(d: W.Dec<List<&2, String>>) -> W.Dec<ResW>:
  match d:
    case W.Got{p, s}:
      get_res.unknown.word(p, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_res.tag(t: Nat, s: String) -> W.Dec<ResW>:
  match t:
    case 0n:
      get_res.runs(get_strs(s))
    case 1n:
      get_res.opens(get_strs(s))
    case 2n:
      get_res.unknown(get_strs(s))
    case 3n:
      W.Got{NoCmdW{}, s}
    case 4n+x:
      W.Bad{}

def get_res.go(d: W.Dec<Nat>) -> W.Dec<ResW>:
  match d:
    case W.Got{t, s}:
      get_res.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_res(s: String) -> W.Dec<ResW>:
  get_res.go(W.get_nat(s))

def put_menu(m: MenuW, rest: String) -> String:
  match m:
    case NamesW{}:
      W.put_nat(0n, rest)
    case KidsW{p, xs}:
      W.put_nat(1n, put_strs(p, W.put_list(~Nat, ~W.put_nat, xs, rest)))
    case ShutW{}:
      W.put_nat(2n, rest)

def get_menu.items(p: List<&2, String>, d: W.Dec<List<&2, Nat>>) -> W.Dec<MenuW>:
  match d:
    case W.Got{xs, s}:
      W.Got{KidsW{p, xs}, s}
    case W.Bad{}:
      W.Bad{}

def get_menu.kids(d: W.Dec<List<&2, String>>) -> W.Dec<MenuW>:
  match d:
    case W.Got{p, s}:
      get_menu.items(p, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_menu.tag(t: Nat, s: String) -> W.Dec<MenuW>:
  match t:
    case 0n:
      W.Got{NamesW{}, s}
    case 1n:
      get_menu.kids(get_strs(s))
    case 2n:
      W.Got{ShutW{}, s}
    case 3n+x:
      W.Bad{}

def get_menu.go(d: W.Dec<Nat>) -> W.Dec<MenuW>:
  match d:
    case W.Got{t, s}:
      get_menu.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_menu(s: String) -> W.Dec<MenuW>:
  get_menu.go(W.get_nat(s))

def put_out(o: OutW, rest: String) -> String:
  match o:
    case OutW{l, a, b}:
      W.put_str(l, W.put_bool(a, W.put_bool(b, rest)))

def get_out.submit(l: String, a: Bool, d: W.Dec<Bool>) -> W.Dec<OutW>:
  match d:
    case W.Got{b, s}:
      W.Got{OutW{l, a, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_out.open(l: String, d: W.Dec<Bool>) -> W.Dec<OutW>:
  match d:
    case W.Got{a, s}:
      get_out.submit(l, a, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_out.line(d: W.Dec<String>) -> W.Dec<OutW>:
  match d:
    case W.Got{l, s}:
      get_out.open(l, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_out(s: String) -> W.Dec<OutW>:
  get_out.line(W.get_str(s))

# the model's answer to a question about table t
def answer(+t: List<&2, M.Ent>, q: Query) -> String:
  match q:
    case QResolve{l}:
      put_res(res_w(M.resolve(t, codes(l))), "")
    case QMenu{l}:
      put_menu(menu_w(M.menu(t, codes(l))), "")
    case QKey{l, x, k}:
      put_out(out_w(M.key(t, codes(l), x, k)), "")

def ffi.run(r: Req) -> String:
  match r:
    case Req{t, q}:
      answer(ents(t), q)

def ffi.whole(r: Req, done: Bool) -> String:
  match done:
    case True{}:
      ffi.run(r)
    case False{}:
      W.err("command: input left over")

def ffi.go(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{r, s}:
      ffi.whole(r, W.end(s))
    case W.Bad{}:
      W.err("command: malformed request")

# a table and a question in, the model's answer out
def ffi(input: String) -> String:
  ffi.go(get_req(input))
