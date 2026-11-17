# ffi_agent_tree: the entry of the compiled Bend core for the decisions of
# the binary agent tree and its help leaves (bend/agent_tree.bend,
# bend/agent_crown.bend; requirements T1-T16 of spec/README.md). Grammar:
# crates/eukhe-bend/WIRE.md.
#
#   Lim      a tag: 0 Unlimited | 1 then the value (Nat)
#   Status, Dir, Refusal, Action   a tag (the constructor's index)
#   Info     status, scope (List of Bool), limit (Lim), spent (Nat),
#            deadline (Lim), patch (List of Maybe Nat)
#   Node     0 then a Leaf's Info | 1 then a Split's Info, own (List of
#            Bool), the left Node, the right Node
#   Ev       a tag (the constructor's index in agent_tree's Ev), then its
#            fields in order (a path is a List of Dir)
#   Help     at (a path), status, limit (Lim), spent (Nat), deadline (Lim)
#   Crown    the Node, then the help leaves (List of Help)
#   CEv      0 then an Ev (on the tree) | 1 then a path and an amount (a
#            help leaf asked) | 2 then a help leaf's index and an amount
#            (it spends) | 3 then a help leaf's index and a Bool (it
#            settles: T finished, F failed)
#   request  a tag, then:
#            0 Step: the bounds (max_depth, max_nodes, margin: Nats), a
#              Crown, a CEv; reply 0 then the new Crown, or 1 then the
#              Refusal
#            1 Overlay: cur, a (Lists of Maybe Nat), s (List of Bool);
#              reply overlay(cur, a, s), then conflicts(a, s)
#            2 Next: the View (message Bool, arrived Nat, own_work Bool);
#              reply the Action
#            3 Free: a Crown and a path; reply the free of the node at the
#              path, help leaves charged, as a Maybe Lim (0: no node)
#
# A Node has no length on the wire: its reader nests at most as many
# nodes as its input has chars (the fuel), and every node spends at least
# two chars, so no spelled Node runs out of fuel.
#
# Malformed input (an unknown tag, a missing field, input left after the
# request) answers `E agent_tree: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./agent_tree.bend as T
import ./agent_crown.bend as C

# A request of the entry
type Req is Data:
  QStep{b: T.Bounds, c: C.Crown, e: C.CEv}
  QOverlay{cur: List<&2, Maybe<&2, Nat>>, a: List<&2, Maybe<&2, Nat>>, s: List<&2, Bool>}
  QNext{v: T.View}
  QFree{c: C.Crown, p: List<&2, T.Dir>}

# The head of a node on the wire: its tag and the fields before its
# children
type Head is Data:
  HLeaf{i: T.Info}
  HSplit{i: T.Info, own: List<&2, Bool>}

# Where the node reader is: at a node's head, or past a split's left child
# (the left child's answer l; the right child is next)
type At is Data:
  AtHead{d: W.Dec<Head>}
  AtRight{i: T.Info, own: List<&2, Bool>, l: W.Dec<T.Node>}

# Decoders
# --------

def get_lim.value(r: W.Dec<Nat>) -> W.Dec<T.Lim>:
  match r:
    case W.Got{n, s}:
      W.Got{T.Value{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_lim.of(t: Nat, s: String) -> W.Dec<T.Lim>:
  match t:
    case 0n:
      W.Got{T.Unlimited{}, s}
    case 1n+a:
      match a:
        case 0n:
          get_lim.value(W.get_nat(s))
        case 1n+b:
          W.Bad{}

def get_lim.tag(r: W.Dec<Nat>) -> W.Dec<T.Lim>:
  match r:
    case W.Got{t, s}:
      get_lim.of(t, s)
    case W.Bad{}:
      W.Bad{}

def get_lim(s: String) -> W.Dec<T.Lim>:
  get_lim.tag(W.get_nat(s))

def get_status.of(t: Nat, s: String) -> W.Dec<T.Status>:
  match t:
    case 0n:
      W.Got{T.Running{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{T.Finished{}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{T.Failed{}, s}
            case 1n+c:
              match c:
                case 0n:
                  W.Got{T.Cancelled{}, s}
                case 1n+d:
                  W.Bad{}

def get_status.tag(r: W.Dec<Nat>) -> W.Dec<T.Status>:
  match r:
    case W.Got{t, s}:
      get_status.of(t, s)
    case W.Bad{}:
      W.Bad{}

def get_status(s: String) -> W.Dec<T.Status>:
  get_status.tag(W.get_nat(s))

def get_dir.of(t: Nat, s: String) -> W.Dec<T.Dir>:
  match t:
    case 0n:
      W.Got{T.GoL{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{T.GoR{}, s}
        case 1n+b:
          W.Bad{}

def get_dir.tag(r: W.Dec<Nat>) -> W.Dec<T.Dir>:
  match r:
    case W.Got{t, s}:
      get_dir.of(t, s)
    case W.Bad{}:
      W.Bad{}

def get_dir(s: String) -> W.Dec<T.Dir>:
  get_dir.tag(W.get_nat(s))

def get_mnat.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      W.Got{Some{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.of(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n+a:
      match a:
        case 0n:
          get_mnat.some(W.get_nat(s))
        case 1n+b:
          W.Bad{}

def get_mnat.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_mnat.of(t, s)
    case W.Bad{}:
      W.Bad{}

def get_mnat(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_mnat.tag(W.get_nat(s))

def get_bools(s: String) -> W.Dec<List<&2, Bool>>:
  W.get_list(~Bool, ~W.get_bool, s)

def get_patch(s: String) -> W.Dec<List<&2, Maybe<&2, Nat>>>:
  W.get_list(~Maybe<&2, Nat>, ~get_mnat, s)

def get_path(s: String) -> W.Dec<List<&2, T.Dir>>:
  W.get_list(~T.Dir, ~get_dir, s)

def get_info.patch(st: T.Status, sc: List<&2, Bool>, lim: T.Lim, sp: Nat, dl: T.Lim, r: W.Dec<List<&2, Maybe<&2, Nat>>>) -> W.Dec<T.Info>:
  match r:
    case W.Got{p, s}:
      W.Got{T.Info{st, sc, lim, sp, dl, p}, s}
    case W.Bad{}:
      W.Bad{}

def get_info.deadline(st: T.Status, sc: List<&2, Bool>, lim: T.Lim, sp: Nat, r: W.Dec<T.Lim>) -> W.Dec<T.Info>:
  match r:
    case W.Got{dl, s}:
      get_info.patch(st, sc, lim, sp, dl, get_patch(s))
    case W.Bad{}:
      W.Bad{}

def get_info.spent(st: T.Status, sc: List<&2, Bool>, lim: T.Lim, r: W.Dec<Nat>) -> W.Dec<T.Info>:
  match r:
    case W.Got{sp, s}:
      get_info.deadline(st, sc, lim, sp, get_lim(s))
    case W.Bad{}:
      W.Bad{}

def get_info.limit(st: T.Status, sc: List<&2, Bool>, r: W.Dec<T.Lim>) -> W.Dec<T.Info>:
  match r:
    case W.Got{lim, s}:
      get_info.spent(st, sc, lim, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_info.scope(st: T.Status, r: W.Dec<List<&2, Bool>>) -> W.Dec<T.Info>:
  match r:
    case W.Got{sc, s}:
      get_info.limit(st, sc, get_lim(s))
    case W.Bad{}:
      W.Bad{}

def get_info.status(r: W.Dec<T.Status>) -> W.Dec<T.Info>:
  match r:
    case W.Got{st, s}:
      get_info.scope(st, get_bools(s))
    case W.Bad{}:
      W.Bad{}

def get_info(s: String) -> W.Dec<T.Info>:
  get_info.status(get_status(s))

def get_head.own(i: T.Info, r: W.Dec<List<&2, Bool>>) -> W.Dec<Head>:
  match r:
    case W.Got{own, s}:
      W.Got{HSplit{i, own}, s}
    case W.Bad{}:
      W.Bad{}

def get_head.split(r: W.Dec<T.Info>) -> W.Dec<Head>:
  match r:
    case W.Got{i, s}:
      get_head.own(i, get_bools(s))
    case W.Bad{}:
      W.Bad{}

def get_head.leaf(r: W.Dec<T.Info>) -> W.Dec<Head>:
  match r:
    case W.Got{i, s}:
      W.Got{HLeaf{i}, s}
    case W.Bad{}:
      W.Bad{}

def get_head.of(t: Nat, s: String) -> W.Dec<Head>:
  match t:
    case 0n:
      get_head.leaf(get_info(s))
    case 1n+a:
      match a:
        case 0n:
          get_head.split(get_info(s))
        case 1n+b:
          W.Bad{}

def get_head.tag(r: W.Dec<Nat>) -> W.Dec<Head>:
  match r:
    case W.Got{t, s}:
      get_head.of(t, s)
    case W.Bad{}:
      W.Bad{}

def get_head(s: String) -> W.Dec<Head>:
  get_head.tag(W.get_nat(s))

# the split of i and own over the left child l and the right child's
# answer r
def get_node.join(i: T.Info, own: List<&2, Bool>, l: T.Node, r: W.Dec<T.Node>) -> W.Dec<T.Node>:
  match r:
    case W.Got{n, s}:
      W.Got{T.Split{i, own, l, n}, s}
    case W.Bad{}:
      W.Bad{}

# the node the reader at m reads, with at most f more nested reads
def get_node.go(f: Nat, m: At) -> W.Dec<T.Node>:
  match f:
    case 0n:
      W.Bad{}
    case 1n++g:
      match m:
        case AtHead{d}:
          match d:
            case W.Got{h, s}:
              match h:
                case HLeaf{i}:
                  W.Got{T.Leaf{i}, s}
                case HSplit{i, own}:
                  get_node.go(g, AtRight{i, own, get_node.go(g, AtHead{get_head(s)})})
            case W.Bad{}:
              W.Bad{}
        case AtRight{i, own, l}:
          match l:
            case W.Got{n, s}:
              get_node.join(i, own, n, get_node.go(g, AtHead{get_head(s)}))
            case W.Bad{}:
              W.Bad{}

# the node at the start of s; the fuel is the length of s
def get_node(+s: String) -> W.Dec<T.Node>:
  get_node.go(String.length(s), AtHead{get_head(s)})

def get_bounds.margin(d: Nat, n: Nat, r: W.Dec<Nat>) -> W.Dec<T.Bounds>:
  match r:
    case W.Got{m, s}:
      W.Got{T.Bounds{d, n, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_bounds.nodes(d: Nat, r: W.Dec<Nat>) -> W.Dec<T.Bounds>:
  match r:
    case W.Got{n, s}:
      get_bounds.margin(d, n, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_bounds.depth(r: W.Dec<Nat>) -> W.Dec<T.Bounds>:
  match r:
    case W.Got{d, s}:
      get_bounds.nodes(d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_bounds(s: String) -> W.Dec<T.Bounds>:
  get_bounds.depth(W.get_nat(s))

def get_view.work(m: Bool, n: Nat, r: W.Dec<Bool>) -> W.Dec<T.View>:
  match r:
    case W.Got{w, s}:
      W.Got{T.View{m, n, w}, s}
    case W.Bad{}:
      W.Bad{}

def get_view.arrived(m: Bool, r: W.Dec<Nat>) -> W.Dec<T.View>:
  match r:
    case W.Got{n, s}:
      get_view.work(m, n, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_view.message(r: W.Dec<Bool>) -> W.Dec<T.View>:
  match r:
    case W.Got{m, s}:
      get_view.arrived(m, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_view(s: String) -> W.Dec<T.View>:
  get_view.message(W.get_bool(s))

def get_ev.split_hold(at: List<&2, T.Dir>, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, r: W.Dec<Nat>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{hold, s}:
      W.Got{T.EvSplit{at, own, ls, rs, hold}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.split_rs(at: List<&2, T.Dir>, own: List<&2, Bool>, ls: List<&2, Bool>, r: W.Dec<List<&2, Bool>>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{rs, s}:
      get_ev.split_hold(at, own, ls, rs, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.split_ls(at: List<&2, T.Dir>, own: List<&2, Bool>, r: W.Dec<List<&2, Bool>>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{ls, s}:
      get_ev.split_rs(at, own, ls, get_bools(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.split_own(at: List<&2, T.Dir>, r: W.Dec<List<&2, Bool>>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{own, s}:
      get_ev.split_ls(at, own, get_bools(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.spend(at: List<&2, T.Dir>, r: W.Dec<Nat>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{n, s}:
      W.Got{T.EvSpend{at, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.finish(at: List<&2, T.Dir>, r: W.Dec<List<&2, Maybe<&2, Nat>>>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{p, s}:
      W.Got{T.EvFinish{at, p}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.fail(at: List<&2, T.Dir>, r: W.Dec<List<&2, Maybe<&2, Nat>>>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{p, s}:
      W.Got{T.EvFail{at, p}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.redo_extra(at: List<&2, T.Dir>, side: T.Dir, r: W.Dec<Nat>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{x, s}:
      W.Got{T.EvRedo{at, side, x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.redo_side(at: List<&2, T.Dir>, r: W.Dec<T.Dir>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{side, s}:
      get_ev.redo_extra(at, side, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.tick(r: W.Dec<Nat>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{n, s}:
      W.Got{T.EvTick{n}, s}
    case W.Bad{}:
      W.Bad{}

# the fields after the path of the event of tag t (0 to 5)
def get_ev.of(t: Nat, at: List<&2, T.Dir>, s: String) -> W.Dec<T.Ev>:
  match t:
    case 0n:
      get_ev.split_own(at, get_bools(s))
    case 1n+a:
      match a:
        case 0n:
          get_ev.spend(at, W.get_nat(s))
        case 1n+b:
          match b:
            case 0n:
              get_ev.finish(at, get_patch(s))
            case 1n+c:
              match c:
                case 0n:
                  get_ev.fail(at, get_patch(s))
                case 1n+d:
                  match d:
                    case 0n:
                      W.Got{T.EvCancel{at}, s}
                    case 1n+e:
                      match e:
                        case 0n:
                          get_ev.redo_side(at, get_dir(s))
                        case 1n+f:
                          W.Bad{}

def get_ev.at(t: Nat, r: W.Dec<List<&2, T.Dir>>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{at, s}:
      get_ev.of(t, at, s)
    case W.Bad{}:
      W.Bad{}

# an event of tag t: 0 to 5 start with a path, 6 is a tick
def get_ev.tagged(t: Nat, s: String) -> W.Dec<T.Ev>:
  match t:
    case 0n:
      get_ev.at(0n, get_path(s))
    case 1n+a:
      match a:
        case 0n:
          get_ev.at(1n, get_path(s))
        case 1n+b:
          match b:
            case 0n:
              get_ev.at(2n, get_path(s))
            case 1n+c:
              match c:
                case 0n:
                  get_ev.at(3n, get_path(s))
                case 1n+d:
                  match d:
                    case 0n:
                      get_ev.at(4n, get_path(s))
                    case 1n+e:
                      match e:
                        case 0n:
                          get_ev.at(5n, get_path(s))
                        case 1n+f:
                          match f:
                            case 0n:
                              get_ev.tick(W.get_nat(s))
                            case 1n+g:
                              W.Bad{}

def get_ev.tag(r: W.Dec<Nat>) -> W.Dec<T.Ev>:
  match r:
    case W.Got{t, s}:
      get_ev.tagged(t, s)
    case W.Bad{}:
      W.Bad{}

def get_ev(s: String) -> W.Dec<T.Ev>:
  get_ev.tag(W.get_nat(s))

def get_help.deadline(at: List<&2, T.Dir>, st: T.Status, lim: T.Lim, sp: Nat, r: W.Dec<T.Lim>) -> W.Dec<C.Help>:
  match r:
    case W.Got{dl, s}:
      W.Got{C.Help{at, st, lim, sp, dl}, s}
    case W.Bad{}:
      W.Bad{}

def get_help.spent(at: List<&2, T.Dir>, st: T.Status, lim: T.Lim, r: W.Dec<Nat>) -> W.Dec<C.Help>:
  match r:
    case W.Got{sp, s}:
      get_help.deadline(at, st, lim, sp, get_lim(s))
    case W.Bad{}:
      W.Bad{}

def get_help.limit(at: List<&2, T.Dir>, st: T.Status, r: W.Dec<T.Lim>) -> W.Dec<C.Help>:
  match r:
    case W.Got{lim, s}:
      get_help.spent(at, st, lim, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_help.status(at: List<&2, T.Dir>, r: W.Dec<T.Status>) -> W.Dec<C.Help>:
  match r:
    case W.Got{st, s}:
      get_help.limit(at, st, get_lim(s))
    case W.Bad{}:
      W.Bad{}

def get_help.at(r: W.Dec<List<&2, T.Dir>>) -> W.Dec<C.Help>:
  match r:
    case W.Got{at, s}:
      get_help.status(at, get_status(s))
    case W.Bad{}:
      W.Bad{}

def get_help(s: String) -> W.Dec<C.Help>:
  get_help.at(get_path(s))

def get_helps(s: String) -> W.Dec<List<&2, C.Help>>:
  W.get_list(~C.Help, ~get_help, s)

def get_crown.helps(t: T.Node, r: W.Dec<List<&2, C.Help>>) -> W.Dec<C.Crown>:
  match r:
    case W.Got{hs, s}:
      W.Got{C.Crown{t, hs}, s}
    case W.Bad{}:
      W.Bad{}

def get_crown.node(r: W.Dec<T.Node>) -> W.Dec<C.Crown>:
  match r:
    case W.Got{t, s}:
      get_crown.helps(t, get_helps(s))
    case W.Bad{}:
      W.Bad{}

def get_crown(s: String) -> W.Dec<C.Crown>:
  get_crown.node(get_node(s))

def get_cev.on(r: W.Dec<T.Ev>) -> W.Dec<C.CEv>:
  match r:
    case W.Got{e, s}:
      W.Got{C.OnTree{e}, s}
    case W.Bad{}:
      W.Bad{}

def get_cev.help_n(at: List<&2, T.Dir>, r: W.Dec<Nat>) -> W.Dec<C.CEv>:
  match r:
    case W.Got{n, s}:
      W.Got{C.EvHelp{at, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_cev.help_at(r: W.Dec<List<&2, T.Dir>>) -> W.Dec<C.CEv>:
  match r:
    case W.Got{at, s}:
      get_cev.help_n(at, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_cev.spend_n(k: Nat, r: W.Dec<Nat>) -> W.Dec<C.CEv>:
  match r:
    case W.Got{n, s}:
      W.Got{C.EvHelpSpend{k, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_cev.spend_k(r: W.Dec<Nat>) -> W.Dec<C.CEv>:
  match r:
    case W.Got{k, s}:
      get_cev.spend_n(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_cev.end_ok(k: Nat, r: W.Dec<Bool>) -> W.Dec<C.CEv>:
  match r:
    case W.Got{ok, s}:
      W.Got{C.EvHelpEnd{k, ok}, s}
    case W.Bad{}:
      W.Bad{}

def get_cev.end_k(r: W.Dec<Nat>) -> W.Dec<C.CEv>:
  match r:
    case W.Got{k, s}:
      get_cev.end_ok(k, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_cev.of(t: Nat, s: String) -> W.Dec<C.CEv>:
  match t:
    case 0n:
      get_cev.on(get_ev(s))
    case 1n+a:
      match a:
        case 0n:
          get_cev.help_at(get_path(s))
        case 1n+b:
          match b:
            case 0n:
              get_cev.spend_k(W.get_nat(s))
            case 1n+c:
              match c:
                case 0n:
                  get_cev.end_k(W.get_nat(s))
                case 1n+d:
                  W.Bad{}

def get_cev.tag(r: W.Dec<Nat>) -> W.Dec<C.CEv>:
  match r:
    case W.Got{t, s}:
      get_cev.of(t, s)
    case W.Bad{}:
      W.Bad{}

def get_cev(s: String) -> W.Dec<C.CEv>:
  get_cev.tag(W.get_nat(s))

def get_req.step_ev(b: T.Bounds, c: C.Crown, r: W.Dec<C.CEv>) -> W.Dec<Req>:
  match r:
    case W.Got{e, s}:
      W.Got{QStep{b, c, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.step_crown(b: T.Bounds, r: W.Dec<C.Crown>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_req.step_ev(b, c, get_cev(s))
    case W.Bad{}:
      W.Bad{}

def get_req.step(r: W.Dec<T.Bounds>) -> W.Dec<Req>:
  match r:
    case W.Got{b, s}:
      get_req.step_crown(b, get_crown(s))
    case W.Bad{}:
      W.Bad{}

def get_req.overlay_s(cur: List<&2, Maybe<&2, Nat>>, a: List<&2, Maybe<&2, Nat>>, r: W.Dec<List<&2, Bool>>) -> W.Dec<Req>:
  match r:
    case W.Got{sc, s}:
      W.Got{QOverlay{cur, a, sc}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.overlay_a(cur: List<&2, Maybe<&2, Nat>>, r: W.Dec<List<&2, Maybe<&2, Nat>>>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      get_req.overlay_s(cur, a, get_bools(s))
    case W.Bad{}:
      W.Bad{}

def get_req.overlay(r: W.Dec<List<&2, Maybe<&2, Nat>>>) -> W.Dec<Req>:
  match r:
    case W.Got{cur, s}:
      get_req.overlay_a(cur, get_patch(s))
    case W.Bad{}:
      W.Bad{}

def get_req.next(r: W.Dec<T.View>) -> W.Dec<Req>:
  match r:
    case W.Got{v, s}:
      W.Got{QNext{v}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.free_path(c: C.Crown, r: W.Dec<List<&2, T.Dir>>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      W.Got{QFree{c, p}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.free(r: W.Dec<C.Crown>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_req.free_path(c, get_path(s))
    case W.Bad{}:
      W.Bad{}

def get_req.of(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_req.step(get_bounds(s))
    case 1n+a:
      match a:
        case 0n:
          get_req.overlay(get_patch(s))
        case 1n+b:
          match b:
            case 0n:
              get_req.next(get_view(s))
            case 1n+c:
              match c:
                case 0n:
                  get_req.free(get_crown(s))
                case 1n+d:
                  W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.of(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# Encoders
# --------

def put_lim(l: T.Lim, rest: String) -> String:
  match l:
    case T.Unlimited{}:
      W.put_nat(0n, rest)
    case T.Value{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def status_tag(st: T.Status) -> Nat:
  match st:
    case T.Running{}:
      0n
    case T.Finished{}:
      1n
    case T.Failed{}:
      2n
    case T.Cancelled{}:
      3n

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_bools(xs: List<&2, Bool>, rest: String) -> String:
  W.put_list(~Bool, ~W.put_bool, xs, rest)

def put_patch(xs: List<&2, Maybe<&2, Nat>>, rest: String) -> String:
  W.put_list(~Maybe<&2, Nat>, ~put_mnat, xs, rest)

def dir_tag(d: T.Dir) -> Nat:
  match d:
    case T.GoL{}:
      0n
    case T.GoR{}:
      1n

def put_dir(d: T.Dir, rest: String) -> String:
  W.put_nat(dir_tag(d), rest)

def put_path(ps: List<&2, T.Dir>, rest: String) -> String:
  W.put_list(~T.Dir, ~put_dir, ps, rest)

def put_info(i: T.Info, rest: String) -> String:
  match i:
    case T.Info{st, sc, lim, sp, dl, p}:
      W.put_nat(status_tag(st), put_bools(sc, put_lim(lim, W.put_nat(sp, put_lim(dl, put_patch(p, rest))))))

def put_node(t: T.Node, rest: String) -> String:
  match t:
    case T.Leaf{i}:
      W.put_nat(0n, put_info(i, rest))
    case T.Split{i, own, l, r}:
      W.put_nat(1n, put_info(i, put_bools(own, put_node(l, put_node(r, rest)))))

def refusal_tag(w: T.Refusal) -> Nat:
  match w:
    case T.NoNode{}:
      0n
    case T.NotRunning{}:
      1n
    case T.NotLeaf{}:
      2n
    case T.TooDeep{}:
      3n
    case T.TooMany{}:
      4n
    case T.BadScopes{}:
      5n
    case T.NoBudget{}:
      6n
    case T.Unsettled{}:
      7n
    case T.NotRedoable{}:
      8n

def action_tag(a: T.Action) -> Nat:
  match a:
    case T.ReadMessage{}:
      0n
    case T.Integrate{}:
      1n
    case T.WorkOwn{}:
      2n
    case T.Waits{}:
      3n

def put_help(h: C.Help, rest: String) -> String:
  match h:
    case C.Help{at, st, lim, sp, dl}:
      put_path(at, W.put_nat(status_tag(st), put_lim(lim, W.put_nat(sp, put_lim(dl, rest)))))

def put_helps(hs: List<&2, C.Help>, rest: String) -> String:
  W.put_list(~C.Help, ~put_help, hs, rest)

def put_crown(c: C.Crown, rest: String) -> String:
  match c:
    case C.Crown{t, hs}:
      put_node(t, put_helps(hs, rest))

def put_cstep(s: C.CStep) -> String:
  match s:
    case C.CTook{c}:
      W.put_nat(0n, put_crown(c, ""))
    case C.CRefused{w}:
      W.put_nat(1n, W.put_nat(refusal_tag(w), ""))

def put_mlim(m: Maybe<&2, T.Lim>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{l}:
      W.put_nat(1n, put_lim(l, ""))

# The entry
# ---------

# the model's answer to a request, spelled
def answer(q: Req) -> String:
  match q:
    case QStep{b, c, e}:
      put_cstep(C.hstep(b, c, e))
    case QOverlay{cur, +a, +s}:
      put_patch(T.overlay(cur, a, s), put_bools(T.conflicts(a, s), ""))
    case QNext{v}:
      W.put_nat(action_tag(T.next(v)), "")
    case QFree{c, p}:
      put_mlim(C.cfree(c, p))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("agent_tree: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("agent_tree: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
