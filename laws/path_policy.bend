# eukhe: the laws of area path_policy

import Base
import ../bend/ffi_path_policy.bend as FPp
import ../bend/path_policy.bend as Pp
import ../bend/tools.bend as Tl
import ../bend/wire.bend as Wr
import ../bend/wire_flat.bend as Fl
import ./base.bend as LawsBase

# ---- path_policy ----

# LAWS (G1): the path policy. Each law is an open claim about the model
# in bend/path_policy.bend; PROOF.bend proves them (as PathPolicy.<law>) with the
# lemmas of proof/path_policy/.

# (G1) Path policy
# ----------------
# one policy for the `bash` tool and the document
# tools (crates/eukhe-types/src/path_policy.rs). A path is a list of
# segments from `/`; the symlinks are free (any location, any target,
# from `/` or from the link's directory, loops included); the policy is
# free (any roots, protected rules and secret entries). An access is
# judged on the real path; its effects run unasked only when the auto
# set (`shell.autoEffects`, any value) allows each of them. The user's
# answer is free: yes, no, or none (no client answered).

# LAW path_real_has_no_link: a path is judged by its real path: unless its links looped, no
# prefix of the path a resolution reaches is a symlink (each link it met
# was replaced by its target)
law path_real_has_no_link:
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  {Bool.or(Pp.Res.looped(Pp.real(ls, segs)), Pp.linkfree(ls, Pp.Res.at(Pp.real(ls, segs)))) == True{} : Bool}

# LAW path_secret_wins: a path whose real path is under a secret entry is Secret, whatever
# else covers it
law path_secret_wins:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for hit: {Pp.any_under(Pp.Pol.secret(pol), Pp.Res.at(Pp.real(ls, segs))) == True{} : Bool}
  {Pp.class(pol, ls, segs) == Pp.Secret{} : Pp.Cls}

# LAW path_inside_is_safe: a path is Inside only when its links did not loop, no secret
# covers its real path, no rule protects it, it is no ancestor of a
# protected or secret entry, and a workspace root holds it
law path_inside_is_safe:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for inside: {Pp.class(pol, ls, segs) == Pp.Inside{} : Pp.Cls}
  {Pp.safe(pol, Pp.real(ls, segs)) == True{} : Bool}

# LAW path_ancestor_guarded: an ancestor of a protected or secret entry (a move or a removal of
# it moves or removes the entry) is Protected or Secret
law path_ancestor_guarded:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for anc: {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(Pp.Pol.rules(pol)), Pp.Pol.secret(pol)), Pp.Res.at(Pp.real(ls, segs))) == True{} : Bool}
  {Pp.Cls.guarded(Pp.class(pol, ls, segs)) == True{} : Bool}

# LAW path_judge_class: the one call the shell and the document gate make on a path they
# resolved answers its class as the policy judges a real path: a loop
# demotes Inside to Outside, and the laws above hold for it
# EXCLUDES: a caller-side class that skips the loop demotion or judges a
#   second resolution
law path_judge_class:
  for +pol: Pp.Pol
  for +r: Pp.Res
  {Pp.Judged.cls(Pp.judge(pol, r)) == Pp.class_res(pol, r) : Pp.Cls}

# LAW path_judge_holds: and answers that the path holds a secret exactly when its real
# path is under a secret entry or is an ancestor of one (a recursive read
# of it reads the secret)
# EXCLUDES: a holds test that misses a directory above a secret, or that
#   flags a sibling of one
law path_judge_holds:
  for +pol: Pp.Pol
  for +r: Pp.Res
  {Pp.Judged.holds(Pp.judge(pol, r)) == Bool.or(Pp.any_under(Pp.Pol.secret(pol), Pp.Res.at(r)), Pp.any_ancestor(Pp.Pol.secret(pol), Pp.Res.at(r))) : Bool}

# (changed 2026-10-27 by the user: secrets never ask again) a secret
# access gates like any access: the auto set decides, the user's yes runs
# it regardless. The store laws that needed a yes for a secret
# (gate_write_auto_never_secret, gate_secret_read_needs_yes,
# secrets_need_yes) are gone with the gate they pinned.

# LAW gate_yes_runs: the user's yes runs any access
law gate_yes_runs:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  {Pp.runs(c, a, auto, Pp.Yes{}) == True{} : Bool}

# LAW path_policy_ffi_request_round_trip (compiled core): the path judgment entry (bend/ffi_path_policy.bend) reads back
# a policy and a resolved path as Rust writes it, and leaves what follows untouched
# EXCLUDES: a request field misread, dropped, reordered or shifted; a
#   decoder that eats the input after the request
law path_policy_ffi_request_round_trip:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +at: List<&2, Nat>
  for +l: Bool
  for +rest: String
  for h: {Bool.and(Bool.and(Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(ro))), LawsBase.wire_nats_fit(Fl.flat(ro))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(FPp.rules(ru)))), LawsBase.wire_nats_fit(Fl.flat(FPp.rules(ru))))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(se))), LawsBase.wire_nats_fit(Fl.flat(se)))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, at)), LawsBase.wire_nats_fit(at))) == True{} : Bool}
  {FPp.get_req(FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest)) == Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest} : Wr.Dec<FPp.Req>}

# LAW path_policy_ffi_answers (compiled core): the path judgment entry answers a whole request with the
# model's judgment (class, holds a secret)
# EXCLUDES: an entry that answers another rule, a default, or a reply for
#   a request it misread
law path_policy_ffi_answers:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +at: List<&2, Nat>
  for +l: Bool
  for h: {Bool.and(Bool.and(Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(ro))), LawsBase.wire_nats_fit(Fl.flat(ro))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(FPp.rules(ru)))), LawsBase.wire_nats_fit(Fl.flat(FPp.rules(ru))))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(se))), LawsBase.wire_nats_fit(Fl.flat(se)))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, at)), LawsBase.wire_nats_fit(at))) == True{} : Bool}
  {FPp.ffi(FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, "")) == FPp.put_judged(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), "") : String}

# LAW path_policy_ffi_rejects_malformed (compiled core): the path judgment entry answers a malformed request with
# the error form, never a default
# EXCLUDES: a decision made on input that is no request
law path_policy_ffi_rejects_malformed:
  for +s: String
  for bad: {FPp.get_req(s) == Wr.Bad{} : Wr.Dec<FPp.Req>}
  {LawsBase.wire_opens_err(FPp.ffi(s)) == True{} : Bool}

# LAW path_policy_ffi_rejects_left_over (compiled core): and a request followed by more input with the error
# form
# EXCLUDES: an entry that ignores input left over (a second request, a
#   truncated one)
law path_policy_ffi_rejects_left_over:
  for +s: String
  for +q: FPp.Req
  for +r: String
  for got: {FPp.get_req(s) == Wr.Got{q, r} : Wr.Dec<FPp.Req>}
  for more: {String.is_empty(r) == False{} : Bool}
  {LawsBase.wire_opens_err(FPp.ffi(s)) == True{} : Bool}

# ---- the judgment, whole (spec) ----
#
# The class and the secret test of a resolved path, restated from (G1)
# with helpers of this file only (a path is its names, deepest first):
#   Secret     a secret entry is the path or one of its ancestors
#   Protected  else: a rule covers the path (Tree p: p is the path or an
#              ancestor of it; Dir p: p is the path or its parent;
#              Named n: n is one of the path's names below the deepest
#              workspace root that holds it, all its names when none
#              does), or the path is a strict ancestor of a rule's entry
#              (Tree or Dir) or of a secret entry
#   Inside     else: a workspace root is the path or one of its ancestors,
#              and its links did not loop
#   Outside    else
# The path holds a secret when a secret entry is the path, one of its
# ancestors, or one of its descendants.

# a and b are the same names, in the same order
def pp_same(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yr:
      False{}
    case x <> xr Nil{}:
      False{}
    case x <> xr y <> yr:
      Bool.and(Nat.is_eq(x, y), pp_same(xr, yr))

# p is one of the paths ps
def pp_in(+p: List<&2, Nat>, ps: List<&2, List<&2, Nat>>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case q <> rest:
      Bool.or(pp_same(p, q), pp_in(p, rest))

# the path, then each of its ancestors, up to `/`
def pp_lineage(at: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match at:
    case Nil{}:
      [Nil{}]
    case +x <> +r:
      (x <> r) <> pp_lineage(r)

# an entry of ps is the path at or one of its ancestors
def pp_under_any(ps: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(pp_in(p, pp_lineage(at)), pp_under_any(rest, at))

# the path at is a strict ancestor of an entry of ps
def pp_above_any(ps: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case +p <> rest:
      Bool.or(Bool.and(pp_in(at, pp_lineage(p)), Bool.not(pp_same(at, p))), pp_above_any(rest, at))

# the entries the rules name (Tree and Dir paths)
def pp_entries(rs: List<&2, Pp.Rule>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Pp.Tree{p}:
          p <> pp_entries(rest)
        case Pp.Dir{p}:
          p <> pp_entries(rest)
        case Pp.Named{n}:
          pp_entries(rest)

def pp_below.at(root: Bool, x: Nat, names: List<&2, Nat>) -> List<&2, Nat>:
  match root:
    case True{}:
      Nil{}
    case False{}:
      x <> names

# the names of the path at below the deepest root that holds it: walking
# up from at, its names before the first path that is a root
def pp_below(+roots: List<&2, List<&2, Nat>>, at: List<&2, Nat>) -> List<&2, Nat>:
  match at:
    case Nil{}:
      Nil{}
    case +x <> +r:
      pp_below.at(pp_in(x <> r, roots), x, pp_below(roots, r))

# n is one of the names ns
def pp_has(ns: List<&2, Nat>, +n: Nat) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case m <> rest:
      Bool.or(Nat.is_eq(m, n), pp_has(rest, n))

# p is the parent of the path at
def pp_parent_is(at: List<&2, Nat>, +p: List<&2, Nat>) -> Bool:
  match at:
    case Nil{}:
      False{}
    case x <> r:
      pp_same(r, p)

# the rule r covers the path at, whose names below its root are low
def pp_covers(r: Pp.Rule, +at: List<&2, Nat>, +low: List<&2, Nat>) -> Bool:
  match r:
    case Pp.Tree{p}:
      pp_in(p, pp_lineage(at))
    case Pp.Dir{+p}:
      Bool.or(pp_same(at, p), pp_parent_is(at, p))
    case Pp.Named{n}:
      pp_has(low, n)

def pp_covers_any(rs: List<&2, Pp.Rule>, +at: List<&2, Nat>, +low: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> rest:
      Bool.or(pp_covers(r, at, low), pp_covers_any(rest, at, low))

# the class from its three tests (secret, protected, inside) and the loop
def pp_pick(sec: Bool, prot: Bool, ins: Bool, looped: Bool) -> Pp.Cls:
  match sec:
    case True{}:
      Pp.Secret{}
    case False{}:
      match prot:
        case True{}:
          Pp.Protected{}
        case False{}:
          match ins:
            case True{}:
              match looped:
                case True{}:
                  Pp.Outside{}
                case False{}:
                  Pp.Inside{}
            case False{}:
              Pp.Outside{}

# the class of a resolved path under a policy
def pp_class(pol: Pp.Pol, r: Pp.Res) -> Pp.Cls:
  match pol r:
    case Pp.Pol{+ro, +ru, +se} Pp.Res{+at, l}:
      pp_pick(pp_under_any(se, at), Bool.or(pp_covers_any(ru, at, pp_below(ro, at)), pp_above_any(List.append(&2, List<&2, Nat>, pp_entries(ru), se), at)), pp_under_any(ro, at), l)

# the real path at is a secret, under one, or a directory that holds one
def pp_holds(pol: Pp.Pol, +at: List<&2, Nat>) -> Bool:
  match pol:
    case Pp.Pol{ro, ru, +se}:
      Bool.or(pp_under_any(se, at), pp_above_any(se, at))

# LAW path_class_spec: the class of every resolved path under every policy
# is the spec's (secret first, then protected, then inside unless its links
# looped, else outside)
# EXCLUDES: a Named rule judged on the names below the wrong root (the
#   shallowest, or none), a Dir rule that covers grandchildren or misses
#   the directory, a Tree rule that covers a sibling, a strict-ancestor test
#   that flags the entry's sibling, the tests in another order, a loop that
#   demotes a protected path (path_inside_is_safe and the others pin only
#   one side, through the model's own helpers)
law path_class_spec:
  for +pol: Pp.Pol
  for +r: Pp.Res
  {Pp.class_res(pol, r) == pp_class(pol, r) : Pp.Cls}

# LAW path_holds_spec: the path holds a secret exactly as the spec says
# EXCLUDES: a holds test that misses a directory above a secret, or flags a
#   sibling of one (path_judge_holds states it through the model's helpers)
law path_holds_spec:
  for +pol: Pp.Pol
  for +at: List<&2, Nat>
  {Pp.holds_at(pol, at) == pp_holds(pol, at) : Bool}

# ---- the real path, whole (spec) ----
#
# The resolution of a path, restated from (G1) and
# crates/eukhe-types/src/path_policy.rs `resolve` with helpers of this
# file only (a path is its names, deepest first). The segments are walked
# from `/`. A name steps into it; when a link sits there (the first link
# of the list located there) and fewer than 40 links (MAX_LINKS) have been
# followed, the link is followed instead: its target, then the segments
# left, are walked from `/` (an absolute target) or from the link's
# directory. Past 40 links, a link met is kept as a name and the path
# loops. `..` steps to the parent, and `..` of `/` is `/`; `.` stays.

def pp_link_pick(hit: Bool, l: Pp.Link, rest: Maybe<&2, Pp.Link>) -> Maybe<&2, Pp.Link>:
  match hit:
    case True{}:
      Some{l}
    case False{}:
      rest

# the link located at the path at, if any: the first of ls there
def pp_link_at(ls: List<&2, Pp.Link>, +at: List<&2, Nat>) -> Maybe<&2, Pp.Link>:
  match ls:
    case Nil{}:
      None{}
    case l <> rest:
      match l:
        case Pp.Link{+la, abs, to}:
          pp_link_pick(pp_same(la, at), Pp.Link{la, abs, to}, pp_link_at(rest, at))

# the parent of the path at; `/` is its own parent
def pp_parent(at: List<&2, Nat>) -> List<&2, Nat>:
  match at:
    case Nil{}:
      Nil{}
    case x <> r:
      r

# the walk after a name: the one that follows the link m there, or, with
# no link there, the one that steps into the name
def pp_hop(m: Maybe<&2, Pp.Link>, followed: Pp.Res, stepped: Pp.Res) -> Pp.Res:
  match m:
    case None{}:
      stepped
    case Some{l}:
      followed

# what a followed link leaves to walk: its target, then the segments rest
def pp_hop_segs(m: Maybe<&2, Pp.Link>, rest: List<&2, Tl.Seg>) -> List<&2, Tl.Seg>:
  match m:
    case None{}:
      rest
    case Some{l}:
      match l:
        case Pp.Link{la, abs, to}:
          List.append(&2, Tl.Seg, to, rest)

# where a followed link's target is walked from: `/` when absolute, else
# the link's directory dir
def pp_hop_from(m: Maybe<&2, Pp.Link>, dir: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case None{}:
      dir
    case Some{l}:
      match l:
        case Pp.Link{la, abs, to}:
          match abs:
            case True{}:
              Nil{}
            case False{}:
              dir

# walk segs from the path at with fuel links left to follow; looped: a
# link was met with none left
def pp_resolve(+fuel: Nat, segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, +looped: Bool) -> Pp.Res:
  match fuel:
    case 0n:
      match segs:
        case Nil{}:
          Pp.Res{at, looped}
        case s <> rest:
          match s:
            case Tl.Name{+n}:
              pp_resolve(0n, rest, ls, n <> at, Bool.or(looped, Maybe.is_some(&2, Pp.Link, pp_link_at(ls, n <> at))))
            case Tl.Up{}:
              pp_resolve(0n, rest, ls, pp_parent(at), looped)
            case Tl.Here{}:
              pp_resolve(0n, rest, ls, at, looped)
    case 1n+f:
      match segs:
        case Nil{}:
          Pp.Res{at, looped}
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              +m = pp_link_at(ls, n <> at)
              pp_hop(m, pp_resolve(f, pp_hop_segs(m, rest), ls, pp_hop_from(m, at), looped), pp_resolve(1n+f, rest, ls, n <> at, looped))
            case Tl.Up{}:
              pp_resolve(1n+f, rest, ls, pp_parent(at), looped)
            case Tl.Here{}:
              pp_resolve(1n+f, rest, ls, at, looped)

# the real path of segs: walked from `/`, 40 links to follow, no loop yet
def pp_real(+ls: List<&2, Pp.Link>, segs: List<&2, Tl.Seg>) -> Pp.Res:
  pp_resolve(40n, segs, ls, Nil{}, False{})

# LAW path_real_spec (G1): the real path of every path under every set of
# links (and whether its links looped) is the spec's resolution
# EXCLUDES: a resolver that sends every path to `/` (or to the path as
#   written) and never loops (path_real_has_no_link, path_secret_wins,
#   path_inside_is_safe and path_ancestor_guarded read it only through
#   their hypotheses, so it passed them all); a relative link followed
#   from `/` or an absolute one from its directory; a link's target walked
#   without the segments after it; `..` of `/` that fails or drops a name
#   twice; more or fewer than 40 links followed; a link met past the limit
#   followed, dropped, or not marked as looped; the last link located at a
#   path picked instead of the first
law path_real_spec:
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  {Pp.real(ls, segs) == pp_real(ls, segs) : Pp.Res}

# ---- the gate, whole (spec) ----
#
# An access's effects, restated from (G1) with the codes of
# bend/path_policy.bend's header (read 0, write 1, outside 4, protected 5,
# secret 6): a read, a list or a search reads (0), a write writes (1). A
# read or a list of a Secret path, and a search of a Secret path or of a
# directory that holds a secret, also has the secret effect (6). A write
# also has the effect of its class: 4 Outside, 5 Protected, 6 Secret,
# none Inside. The access runs when the user said yes, or when each of
# its effects is a code (below 7) the auto set holds.

# what a read adds for a class: the secret effect for a Secret path only
def pp_read_mark(c: Pp.Cls) -> List<&2, Nat>:
  match c:
    case Pp.Inside{}:
      Nil{}
    case Pp.Outside{}:
      Nil{}
    case Pp.Protected{}:
      Nil{}
    case Pp.Secret{}:
      [6n]

# what a write adds for a class
def pp_write_mark(c: Pp.Cls) -> List<&2, Nat>:
  match c:
    case Pp.Inside{}:
      Nil{}
    case Pp.Outside{}:
      [4n]
    case Pp.Protected{}:
      [5n]
    case Pp.Secret{}:
      [6n]

# the effects of access a to a path of class c
def pp_effs(c: Pp.Cls, a: Pp.Acc) -> List<&2, Nat>:
  match a:
    case Pp.Rd{}:
      0n <> pp_read_mark(c)
    case Pp.Ls{}:
      0n <> pp_read_mark(c)
    case Pp.Sr{h}:
      match h:
        case True{}:
          [0n, 6n]
        case False{}:
          0n <> pp_read_mark(c)
    case Pp.Wr{}:
      1n <> pp_write_mark(c)

# each effect of es is a code below 7 that the auto set holds
def pp_auto_holds(+auto: List<&2, Nat>, es: List<&2, Nat>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Bool.and(Nat.is_lt(e, 7n), pp_has(auto, e)), pp_auto_holds(auto, rest))

# the user said yes (no and no answer are not)
def pp_said_yes(ans: Pp.Ans) -> Bool:
  match ans:
    case Pp.Yes{}:
      True{}
    case Pp.No{}:
      False{}
    case Pp.Gone{}:
      False{}

# the access runs: the auto set holds its effects, or the user said yes
def pp_runs(c: Pp.Cls, a: Pp.Acc, +auto: List<&2, Nat>, ans: Pp.Ans) -> Bool:
  Bool.or(pp_auto_holds(auto, pp_effs(c, a)), pp_said_yes(ans))

# LAW gate_effs_spec (G1): the effects of every access to a path of every
# class are the spec's
# EXCLUDES: a write of any class that has only the write effect (so a
#   Protected, Secret or Outside write runs unasked when the auto set is
#   {1}: gate_yes_runs and gate_inside_write_runs pinned only a yes and an
#   Inside write); a read, list or search of a Secret path, or a search of
#   a directory that holds a secret, without the secret effect; a read
#   with the outside or protected effect; the codes swapped
law gate_effs_spec:
  for c: Pp.Cls
  for a: Pp.Acc
  {Pp.effs(c, a) == pp_effs(c, a) : List<&2, Nat>}

# LAW gate_runs_spec (G1): every access, under every auto set and every
# answer of the user, runs exactly as the spec says
# EXCLUDES: a gate that runs every access (or every write) unasked, that
#   runs on a no or on no answer, that checks only the access's first
#   effect, or that grants a code the auto set does not hold
law gate_runs_spec:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  {Pp.runs(c, a, auto, ans) == pp_runs(c, a, auto, ans) : Bool}

# ---- the entry, whole (spec) ----
#
# The request as Rust writes it, spelled with the spellers of
# laws/base.bend and the wire primitives: lists of paths cross as one list
# of Nats, each name as 1 + name and each path closed by 0 (the format of
# bend/wire_flat.bend's header); a rule is 0 then its path (Tree), 1 then
# its path (Dir), or 2 then its name (Named). The reply is the class (0
# Inside, 1 Outside, 2 Protected, 3 Secret), then whether the path holds a
# secret.

# 1 + each name of xs
def pp_succ(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      (1n+x) <> pp_succ(rest)

# a list of paths as one list of Nats: each path's names (1 + name), then 0
def pp_flat(xss: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match xss:
    case Nil{}:
      Nil{}
    case xs <> rest:
      List.append(&2, Nat, pp_succ(xs), 0n <> pp_flat(rest))

# a rule as a path
def pp_rule(r: Pp.Rule) -> List<&2, Nat>:
  match r:
    case Pp.Tree{p}:
      0n <> p
    case Pp.Dir{p}:
      1n <> p
    case Pp.Named{n}:
      [2n, n]

def pp_rules(rs: List<&2, Pp.Rule>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      pp_rule(r) <> pp_rules(rest)

# a request: the roots, the rules, the secret entries, the path (each a
# list of Nats), then whether its links looped
def pp_spell_req(q: FPp.Req, rest: String) -> String:
  match q:
    case FPp.Req{p, r}:
      match p r:
        case Pp.Pol{ro, ru, se} Pp.Res{at, l}:
          LawsBase.wire_spell_nats(pp_flat(ro), LawsBase.wire_spell_nats(pp_flat(pp_rules(ru)), LawsBase.wire_spell_nats(pp_flat(se), LawsBase.wire_spell_nats(at, Wr.put_bool(l, rest)))))

# a list of Nats fits the wire: its count and each item
def pp_ns_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# every list of the request fits the wire
def pp_req_fits(q: FPp.Req) -> Bool:
  match q:
    case FPp.Req{p, r}:
      match p r:
        case Pp.Pol{ro, ru, se} Pp.Res{at, l}:
          Bool.and(Bool.and(Bool.and(pp_ns_fit(pp_flat(ro)), pp_ns_fit(pp_flat(pp_rules(ru)))), pp_ns_fit(pp_flat(se))), pp_ns_fit(at))

# the wire code of a class
def pp_code(c: Pp.Cls) -> Nat:
  match c:
    case Pp.Inside{}:
      0n
    case Pp.Outside{}:
      1n
    case Pp.Protected{}:
      2n
    case Pp.Secret{}:
      3n

# the reply to a request: the spec's class, then whether the path holds a
# secret
def pp_spell_reply(q: FPp.Req) -> String:
  match q:
    case FPp.Req{+p, r}:
      match r:
        case Pp.Res{+at, l}:
          Wr.put_nat(pp_code(pp_class(p, Pp.Res{at, l})), Wr.put_bool(pp_holds(p, at), ""))

# LAW path_policy_ffi_decides: a request Rust spells that fits the wire is
# answered with the spec's class and secret test, spelled
# EXCLUDES: a field misread or swapped (roots read as secrets), a reply in
#   another code or order, any judgment other than the spec's
law path_policy_ffi_decides:
  for +q: FPp.Req
  for fit: {pp_req_fits(q) == True{} : Bool}
  {FPp.ffi(pp_spell_req(q, "")) == pp_spell_reply(q) : String}

# LAW path_policy_ffi_spelled_left_over: a spelled request followed by more
# input answers exactly the left-over error
# EXCLUDES: trailing input ignored or read as part of the request
law path_policy_ffi_spelled_left_over:
  for +q: FPp.Req
  for +rest: String
  for fit: {pp_req_fits(q) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FPp.ffi(pp_spell_req(q, rest)) == Wr.err("path_policy: input left over") : String}

# LAW path_policy_ffi_exact: every input answered with a value is a
# spelled request that fits the wire, whole
# EXCLUDES: a decoder that reads a guessed field, an unknown rule tag, a
#   name after the last end mark, a 15-digit number, or input left over
law path_policy_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FPp.ffi(s)) == False{} : Bool}
  exs q: FPp.Req
  {s == pp_spell_req(q, "") : String} & {pp_req_fits(q) == True{} : Bool}

# LAW path_policy_ffi_malformed_unless_request: every answer but the
# malformed error comes from an input that begins with a spelled request
# that fits
# EXCLUDES: the left-over error, another error text or a reply for input
#   that holds no request
law path_policy_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FPp.ffi(s), Wr.err("path_policy: malformed request")) == False{} : Bool}
  exs q: FPp.Req
  exs rest: String
  {(s, pp_req_fits(q)) == (pp_spell_req(q, rest), True{}) : String & Bool}

# LAW path_policy_ffi_example: anchor: under the root /1/5, a Named rule 7
# protects /1/5/7, and /1 holds the secret /1/9 (so it is protected); a
# Dir rule /1/5 covers /1/5/7 but not /1/5/7/8 (Inside); a looped path is
# Outside; a rule tag 3, a name after the last end mark and input left
# over are refused; under the roots /1 and /1/5 a Named rule 5 does not
# cover /1/5/7 (its deepest root is /1/5)
# EXCLUDES: the wire codes or field order swapped; a Dir rule that covers
#   a grandchild; a Named rule judged below the shallowest root
law path_policy_ffi_example:
  {[FPp.ffi("5,2,0,6,2,0,3,3,6,0,0,3,7,5,1,F"), FPp.ffi("3,6,2,0,3,3,8,0,3,10,2,0,3,7,5,1,F"), FPp.ffi("3,6,2,0,0,3,10,2,0,1,1,F"), FPp.ffi("3,6,2,0,4,2,6,2,0,0,3,7,5,1,F"), FPp.ffi("3,6,2,0,4,2,6,2,0,0,4,8,7,5,1,F"), FPp.ffi("3,6,2,0,0,0,3,7,5,1,T"), FPp.ffi("0,4,4,6,2,0,0,0,F"), FPp.ffi("1,5,0,0,0,F"), FPp.ffi("0,0,0,0,Fx")] == ["0,F", "2,F", "2,T", "2,F", "0,F", "1,F", Wr.err("path_policy: malformed request"), Wr.err("path_policy: malformed request"), Wr.err("path_policy: input left over")] : List<&2, String>}
