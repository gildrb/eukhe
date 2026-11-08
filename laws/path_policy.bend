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
# docs/tools.md S7: one policy for the `bash` tool and the document
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

# LAW gate_write_auto_never_secret (changed 2026-10-23 by the user: no prompts, like omp): a write
# without the user's yes never lands on a secret, whatever the auto set
# holds
law gate_write_auto_never_secret:
  for c: Pp.Cls
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for ran: {Pp.runs(c, Pp.Wr{}, auto, ans) == True{} : Bool}
  for no: {Pp.Ans.yes(ans) == False{} : Bool}
  {Pp.Cls.secret(c) == False{} : Bool}

# LAW gate_secret_read_needs_yes: a read of a secret (a read or a list of one, a search of a
# directory that holds one) runs only on the user's yes, whatever the auto
# set holds
law gate_secret_read_needs_yes:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for s: {Pp.secret_read(c, a) == True{} : Bool}
  for ran: {Pp.runs(c, a, auto, ans) == True{} : Bool}
  {Pp.Ans.yes(ans) == True{} : Bool}

# LAW gate_yes_runs: the user's yes runs any access
law gate_yes_runs:
  for c: Pp.Cls
  for a: Pp.Acc
  for +auto: List<&2, Nat>
  {Pp.runs(c, a, auto, Pp.Yes{}) == True{} : Bool}

# LAW secrets_need_yes (changed 2026-10-23 by the user: no prompts, like omp): no sequence of
# agent writes through any paths, each judged by the gate on its real
# path and landing there, without a yes of the user, changes a secret:
# the secrets stay as they were, whatever the auto set holds
law secrets_need_yes:
  for es: List<&2, Pp.Put>
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  for no: {Pp.any_yes(es) == False{} : Bool}
  {Pp.secrets(Pp.run(es, pol, ls, auto, cs), pol) == Pp.secrets(cs, pol) : List<&2, Pp.Cell>}

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

# (G1) Path policy against an independent spec
# --------------------------------------------
# The laws above reach the secret entries through the model's own
# projection and scans (Pp.Pol.secret, Pp.any_under, Pp.any_ancestor,
# Pp.secrets, Pp.any_yes): a model whose projection forgets the secret
# entries passes every one of them (no path is ever secret). The laws
# below state the claims over the policy's own fields Pol{ro, ru, se} with
# the spec helpers here, which never call the model. A path is a list of
# names, deepest first; Nil{} is `/`.

# xs and ys name the same path: the same names in the same order
def pp_same(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case y <> yr:
          False{}
    case x <> xr:
      match ys:
        case Nil{}:
          False{}
        case y <> yr:
          Bool.and(Nat.is_eq(x, y), pp_same(xr, yr))

# p is the path at or one of its ancestors (deepest first: p is a suffix
# of at)
def pp_at_or_above(+p: List<&2, Nat>, at: List<&2, Nat>) -> Bool:
  match at:
    case Nil{}:
      pp_same(p, Nil{})
    case +x <> +r:
      Bool.or(pp_same(p, x <> r), pp_at_or_above(p, r))

# some entry of ps is at or above the path at
def pp_under_any(ps: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(pp_at_or_above(p, at), pp_under_any(rest, at))

# the path at is a strict ancestor of some entry of ps
def pp_above_any(ps: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case +p <> rest:
      Bool.or(Bool.and(pp_at_or_above(at, p), Bool.not(pp_same(at, p))), pp_above_any(rest, at))

# no write of es carries the user's yes
def pp_no_yes(es: List<&2, Pp.Put>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> rest:
      match e:
        case Pp.Put{s, v, a}:
          match a:
            case Pp.Yes{}:
              False{}
            case Pp.No{}:
              pp_no_yes(rest)
            case Pp.Gone{}:
              pp_no_yes(rest)

# v when the cell is at the location, else the rest's answer
def pp_cell_pick(hit: Bool, v: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      rest

# the content of the first cell of cs at the location at, if any
def pp_cell(cs: List<&2, Pp.Cell>, +at: List<&2, Nat>) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      None{}
    case c <> rest:
      match c:
        case Pp.Cell{a, v}:
          pp_cell_pick(pp_same(a, at), v, pp_cell(rest, at))

# c in front of rest when hit, else rest
def pp_keep(hit: Bool, c: Pp.Cell, rest: List<&2, Pp.Cell>) -> List<&2, Pp.Cell>:
  match hit:
    case True{}:
      c <> rest
    case False{}:
      rest

# the cells of cs at a location at or under an entry of se, in order
def pp_secret_cells(+se: List<&2, List<&2, Nat>>, cs: List<&2, Pp.Cell>) -> List<&2, Pp.Cell>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c:
        case Pp.Cell{+a, v}:
          pp_keep(pp_under_any(se, a), Pp.Cell{a, v}, pp_secret_cells(se, rest))

# some link of ls sits at the location k
def pp_link_at(ls: List<&2, Pp.Link>, +k: List<&2, Nat>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case l <> rest:
      match l:
        case Pp.Link{a, b, t}:
          Bool.or(pp_same(a, k), pp_link_at(rest, k))

# no prefix of at (it, its parent, ..., but `/`) is the location of a link
# of ls
def pp_linkfree(+ls: List<&2, Pp.Link>, at: List<&2, Nat>) -> Bool:
  match at:
    case Nil{}:
      True{}
    case +a <> +above:
      Bool.and(Bool.not(pp_link_at(ls, a <> above)), pp_linkfree(ls, above))

# a chain of n links: /n -> /n-1 -> ... -> /1 -> /0 (each absolute), /0
# no link
def pp_chain(n: Nat) -> List<&2, Pp.Link>:
  match n:
    case 0n:
      Nil{}
    case 1n++k:
      Pp.Link{[1n+k], True{}, [Tl.Name{k}]} <> pp_chain(k)

# LAW path_real_reaches_no_link: unless its links looped, no prefix of the real path a resolution
# reaches is the location of a link (by the spec's own link lookup: each
# link met was followed to its target)
# EXCLUDES: a resolution that stops at a link or skips one, a link lookup
#   that misses a link (reads another location, finds none, picks the
#   wrong one), which path_real_has_no_link cannot see as it reads the
#   model's own lookup
law path_real_reaches_no_link:
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  {Bool.or(Pp.Res.looped(Pp.real(ls, segs)), pp_linkfree(ls, Pp.Res.at(Pp.real(ls, segs)))) == True{} : Bool}

# LAW path_real_links_example: anchor: an absolute link /1 -> /2 is followed (/1/3 is /2/3), a
# relative link /2/1 -> 4 is followed from its directory (/2/1 is /2/4),
# neither loops; a link /1 -> /1 loops; a chain of 40 links (Rust's
# MAX_LINKS) resolves to its end without a loop, a chain of 41 loops at
# the link where the count ran out; the spec sees the link in /1/3
# EXCLUDES: links not followed or not found, a relative target read from
#   `/`, a link limit other than 40 (fewer: a 40 chain loops; more: a 41
#   chain resolves), a resolution that never loops
law path_real_links_example:
  {[Pp.real([Pp.Link{[1n], True{}, [Tl.Name{2n}]}], [Tl.Name{1n}, Tl.Name{3n}]), Pp.real([Pp.Link{[1n, 2n], False{}, [Tl.Name{4n}]}], [Tl.Name{2n}, Tl.Name{1n}]), Pp.real([Pp.Link{[1n], True{}, [Tl.Name{1n}]}], [Tl.Name{1n}]), Pp.real(pp_chain(40n), [Tl.Name{40n}]), Pp.real(pp_chain(41n), [Tl.Name{41n}])] == [Pp.Res{[3n, 2n], False{}}, Pp.Res{[4n, 2n], False{}}, Pp.Res{[1n], True{}}, Pp.Res{[0n], False{}}, Pp.Res{[1n], True{}}] : List<&2, Pp.Res>} & {pp_linkfree([Pp.Link{[1n], True{}, [Tl.Name{2n}]}], [3n, 1n]) == False{} : Bool}

# LAW path_judge_secret_exact: the judgment of a resolved path, under any policy and whether or
# not its links looped, is Secret exactly when one of the policy's secret
# entries is the path or one of its ancestors
# EXCLUDES: a model that drops, ignores or misreads the policy's secret
#   entries (no path secret, every path secret), a secret test that misses
#   a path below an entry or flags a sibling or ancestor of one, a loop
#   that changes a Secret class
law path_judge_secret_exact:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +at: List<&2, Nat>
  for +l: Bool
  {Pp.Cls.secret(Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}))) == pp_under_any(se, at) : Bool}

# LAW path_judge_holds_exact: the judgment says the path holds a secret exactly when one of the
# policy's secret entries is the path or one of its ancestors, or the path
# is a strict ancestor of one of them
# EXCLUDES: a holds answer computed from anything but the policy's own
#   secret entries (none, all), a holds test that misses a directory above
#   a secret or flags a sibling of one
law path_judge_holds_exact:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +at: List<&2, Nat>
  for +l: Bool
  {Pp.Judged.holds(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == Bool.or(pp_under_any(se, at), pp_above_any(se, at)) : Bool}

# LAW path_judge_guards_secret_ancestor: a path that is a strict ancestor of one of the policy's
# secret entries (a move or a removal of it moves or removes the secret) is
# judged Protected or Secret, whether or not its links looped
# EXCLUDES: a directory above a secret judged Inside or Outside, because the
#   model forgot or misread the secret entries
law path_judge_guards_secret_ancestor:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +at: List<&2, Nat>
  for +l: Bool
  for anc: {pp_above_any(se, at) == True{} : Bool}
  {Pp.Cls.guarded(Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}))) == True{} : Bool}

# LAW secrets_kept_without_yes: any sequence of agent writes through any paths and any links,
# none with the user's yes, whatever the auto set holds, leaves the content
# at every location at or under a secret entry of the policy as it was (the
# first cell there, or none)
# EXCLUDES: a write without a yes that lands on a secret, because the model
#   forgot or misread the secret entries, or the gate, the resolution or
#   the store lets one through
law secrets_kept_without_yes:
  for es: List<&2, Pp.Put>
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  for +at: List<&2, Nat>
  for sec: {pp_under_any(se, at) == True{} : Bool}
  for no: {pp_no_yes(es) == True{} : Bool}
  {pp_cell(Pp.run(es, Pp.Pol{ro, ru, se}, ls, auto, cs), at) == pp_cell(cs, at) : Maybe<&2, Nat>}

# LAW secrets_are_secret_cells: the cells the store counts as secrets (the ones secrets_need_yes
# keeps) are exactly the cells at a location at or under a secret entry of
# the policy, in order
# EXCLUDES: a secrets view that drops or invents cells or reads other
#   entries than the policy's secret ones (a vacuous secrets_need_yes)
law secrets_are_secret_cells:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +cs: List<&2, Pp.Cell>
  {Pp.secrets(cs, Pp.Pol{ro, ru, se}) == pp_secret_cells(se, cs) : List<&2, Pp.Cell>}

# LAW path_judge_secret_example: anchor and witness: with the secret /3/5, /3/5 is Secret and
# holds a secret, its parent /3 is Protected and holds one, its sibling /3/7
# is Outside and holds none; the spec helpers agree, and a write without a
# yes exists (the premises of the laws above are satisfiable)
# EXCLUDES: vacuous path_judge_guards_secret_ancestor or
#   secrets_kept_without_yes, a judgment that forgets the secret entries
law path_judge_secret_example:
  {[Pp.judge(Pp.Pol{Nil{}, Nil{}, [[5n, 3n]]}, Pp.Res{[5n, 3n], False{}}), Pp.judge(Pp.Pol{Nil{}, Nil{}, [[5n, 3n]]}, Pp.Res{[3n], False{}}), Pp.judge(Pp.Pol{Nil{}, Nil{}, [[5n, 3n]]}, Pp.Res{[7n, 3n], False{}})] == [Pp.Judged{Pp.Secret{}, True{}}, Pp.Judged{Pp.Protected{}, True{}}, Pp.Judged{Pp.Outside{}, False{}}] : List<&2, Pp.Judged>} & {[pp_under_any([[5n, 3n]], [5n, 3n]), pp_above_any([[5n, 3n]], [3n]), pp_under_any([[5n, 3n]], [7n, 3n]), pp_above_any([[5n, 3n]], [7n, 3n]), pp_no_yes([Pp.Put{[Tl.Name{3n}, Tl.Name{5n}], 1n, Pp.No{}}])] == [True{}, True{}, False{}, False{}, True{}] : List<&2, Bool>}

# LAW secrets_kept_example: anchor: under roots [/3] and the secret /3/5, with write in the auto
# set, a write of 1 to /3/5 without a yes leaves its 0, the same write with
# a yes lands, a write of 2 to /3/7 without a yes lands, and the store's
# secrets of /3/5 and /3/7 are the /3/5 cell
# EXCLUDES: a vacuous secrets_kept_without_yes (no write runs at all), a
#   gate that ignores the user's yes
law secrets_kept_example:
  {[pp_cell(Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{5n}], 1n, Pp.No{}}], Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [1n], [Pp.Cell{[5n, 3n], 0n}]), [5n, 3n]), pp_cell(Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{5n}], 1n, Pp.Yes{}}], Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [1n], [Pp.Cell{[5n, 3n], 0n}]), [5n, 3n]), pp_cell(Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{7n}], 2n, Pp.No{}}], Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [1n], Nil{}), [7n, 3n])] == [Some{0n}, Some{1n}, Some{2n}] : List<&2, Maybe<&2, Nat>>} & {Pp.secrets([Pp.Cell{[5n, 3n], 0n}, Pp.Cell{[7n, 3n], 1n}], Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}) == [Pp.Cell{[5n, 3n], 0n}] : List<&2, Pp.Cell>}

# (G1) The path judgment entry, spelled
# -------------------------------------
# The entry laws above read and write through the entry's own encoders
# (FPp.put_req, FPp.rules, Fl.flat, FPp.put_judged): a tag drift both
# sides share (class tags swapped, holds flipped, rule tags swapped)
# passes them. The laws below spell the request and the reply with the
# wire primitives as Rust writes and reads them (crates/eukhe-shell/src/
# paths.rs `decide`): the roots, the rules, the secret entries, each a
# wire list of Nats (every path's names as 1 + name, each path ended by
# 0; a rule is 0 then its path for Tree, 1 then its path for Dir, 2 then
# the name for Named), the path (a wire list of names), looped (a Bool);
# the reply is the class (0 Inside, 1 Outside, 2 Protected, 3 Secret),
# then whether the path holds a secret.

# the wire items of the path xs (each 1 + name), its end 0, then rest
def pp_flat_one(xs: List<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      0n <> rest
    case x <> t:
      {1n+x : Nat} <> pp_flat_one(t, rest)

# the wire items of the paths xss, in order
def pp_flat(xss: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match xss:
    case Nil{}:
      Nil{}
    case xs <> t:
      pp_flat_one(xs, pp_flat(t))

# a rule as Rust writes it: 0 then the path (Tree), 1 then the path (Dir),
# 2 then the name (Named)
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

# a wire list of Nats fits: its count and every item
def pp_nats_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# a request as Rust spells it, then rest
def pp_spell_req(q: FPp.Req, rest: String) -> String:
  match q:
    case FPp.Req{p, r}:
      match p r:
        case Pp.Pol{ro, ru, se} Pp.Res{at, l}:
          LawsBase.wire_spell_nats(pp_flat(ro), LawsBase.wire_spell_nats(pp_flat(pp_rules(ru)), LawsBase.wire_spell_nats(pp_flat(se), LawsBase.wire_spell_nats(at, Wr.put_bool(l, rest)))))

# every count and number of a request fits the wire
def pp_req_fits(q: FPp.Req) -> Bool:
  match q:
    case FPp.Req{p, r}:
      match p r:
        case Pp.Pol{ro, ru, se} Pp.Res{at, l}:
          Bool.and(Bool.and(Bool.and(pp_nats_fit(pp_flat(ro)), pp_nats_fit(pp_flat(pp_rules(ru)))), pp_nats_fit(pp_flat(se))), pp_nats_fit(at))

# the tag Rust reads for a class
def pp_cls_tag(c: Pp.Cls) -> Nat:
  match c:
    case Pp.Inside{}:
      0n
    case Pp.Outside{}:
      1n
    case Pp.Protected{}:
      2n
    case Pp.Secret{}:
      3n

# the reply to a request as Rust reads it: the class the model judges,
# then whether the path holds a secret by the spec (an entry at or above
# it, or one below it)
def pp_spell_answer(q: FPp.Req) -> String:
  match q:
    case FPp.Req{p, r}:
      match p r:
        case Pp.Pol{ro, ru, +se} Pp.Res{+at, l}:
          Wr.put_nat(pp_cls_tag(Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}))), Wr.put_bool(Bool.or(pp_under_any(se, at), pp_above_any(se, at)), ""))

# LAW path_policy_ffi_answers_spelled: a request spelled as Rust writes it, every count and number
# within the wire, is answered with the class the model judges, in the tag
# Rust reads, then whether the path holds a secret by the spec
# EXCLUDES: a request or reply tag drift both sides of the Bend entry share
#   (rule tags, class tags swapped), a holds Bool flipped or computed
#   from anything but the policy's secret entries, a path or list item
#   offset other than Rust's
law path_policy_ffi_answers_spelled:
  for +q: FPp.Req
  for fits: {pp_req_fits(q) == True{} : Bool}
  {FPp.ffi(pp_spell_req(q, "")) == pp_spell_answer(q) : String}

# LAW path_policy_ffi_left_over_spelled: a spelled request that fits, followed by any more input,
# answers the error form "path_policy: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request
law path_policy_ffi_left_over_spelled:
  for +q: FPp.Req
  for fits: {pp_req_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FPp.ffi(pp_spell_req(q, SCon{c, t})) == Wr.err("path_policy: input left over") : String}

# LAW path_policy_ffi_reads_only_requests: an answer that is not the error form answers a request: the
# input is exactly the spelling of a request whose counts and numbers fit
# the wire, and the answer is the spelled reply to it
# EXCLUDES: a decoder that accepts an unknown rule tag, a path list with
#   items after its last end mark, a missing field or input left over, and
#   answers it anyway (a default instead of the error form)
law path_policy_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FPp.ffi(s)) == False{} : Bool}
  exs q: FPp.Req
  {(s, (pp_req_fits(q), FPp.ffi(s))) == (pp_spell_req(q, ""), (True{}, pp_spell_answer(q))) : String & (Bool & String)}

# LAW path_policy_ffi_malformed_unless_request: every answer but the error form "path_policy:
# malformed request" comes from an input that begins with a spelled request
# that fits (with path_policy_ffi_answers_spelled and
# path_policy_ffi_left_over_spelled: every other input answers exactly that
# error, a spelled request that fits never does)
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law path_policy_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FPp.ffi(s), Wr.err("path_policy: malformed request")) == False{} : Bool}
  exs q: FPp.Req
  exs rest: String
  {(s, pp_req_fits(q)) == (pp_spell_req(q, rest), True{}) : String & Bool}

# LAW path_policy_ffi_tags_example: anchor: the bytes Rust sends and reads: a path under the root
# /1 is Inside (0), a loop makes it Outside (1), no root Outside; with the
# secret /3/5, /3/5 is Secret (3) and holds one, /3 is Protected (2) and
# holds one; /7/8/9 is Protected under a Tree /7 rule or a Named 9 rule,
# Outside under a Dir /7 rule; an unknown rule tag (3) is malformed;
# input after the Bool is left over
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust does
#   not (class, rule or Bool tags), an unknown tag read as a known one
law path_policy_ffi_tags_example:
  {[FPp.ffi("2,2,0,0,0,1,1,F"), FPp.ffi("2,2,0,0,0,1,1,T"), FPp.ffi("0,0,0,1,1,F"), FPp.ffi("0,0,3,6,4,0,2,5,3,F"), FPp.ffi("0,0,3,6,4,0,1,3,F"), FPp.ffi("0,3,1,8,0,0,3,9,8,7,F"), FPp.ffi("0,3,2,8,0,0,3,9,8,7,F"), FPp.ffi("0,3,3,10,0,0,3,9,8,7,F"), FPp.ffi("0,2,4,0,0,0,F"), FPp.ffi("0,0,0,0,Fx")] == ["0,F", "1,F", "1,F", "3,T", "2,T", "2,F", "1,F", "2,F", Wr.err("path_policy: malformed request"), Wr.err("path_policy: input left over")] : List<&2, String>}

# (G1) The class, against an independent spec
# -------------------------------------------
# path_secret_wins, path_ancestor_guarded and path_inside_is_safe read the
# model's own entries, root choice and rule tests (Pp.entries, Pp.root.of,
# Pp.protects): a model that drops a rule's entry, or picks another root
# for a Named rule, passes them. The law below pins the whole class of a
# resolved path to docs/tools.md G1.2 and G1.3, spelled here: the first
# class that applies wins (Secret, Protected, Inside, Outside), a loop
# never leaves a path Inside, and a Named rule looks at the names of the
# path strictly below its deepest workspace root (all of them when no root
# holds it).

# some entry of ps is the path p
def pp_is_root(ps: List<&2, List<&2, Nat>>, +p: List<&2, Nat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case q <> rest:
      Bool.or(pp_same(q, p), pp_is_root(rest, p))

# no names when the path is a root, else x in front of the names above
def pp_below_pick(hit: Bool, x: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      Nil{}
    case False{}:
      x <> rest

# the names of at strictly below the deepest root at or above it (deepest
# first), or all of at's names when no root is: at's names up to the
# first of its ancestors (itself first) that is a root
def pp_below_root(+ro: List<&2, List<&2, Nat>>, at: List<&2, Nat>) -> List<&2, Nat>:
  match at:
    case Nil{}:
      Nil{}
    case +x <> +r:
      pp_below_pick(pp_is_root(ro, x <> r), x, pp_below_root(ro, r))

# n is one of the names xs
def pp_has_name(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, n), pp_has_name(rest, n))

# the parent of at is p (`/` has no parent)
def pp_parent_is(at: List<&2, Nat>, +p: List<&2, Nat>) -> Bool:
  match at:
    case Nil{}:
      False{}
    case x <> r:
      pp_same(r, p)

# rule r covers the path at whose names below its root are low: a Tree its
# path and everything under it, a Dir its directory and its direct
# entries, a Named rule a path with that name below its root
def pp_covers(r: Pp.Rule, +at: List<&2, Nat>, +low: List<&2, Nat>) -> Bool:
  match r:
    case Pp.Tree{p}:
      pp_at_or_above(p, at)
    case Pp.Dir{+p}:
      Bool.or(pp_same(at, p), pp_parent_is(at, p))
    case Pp.Named{n}:
      pp_has_name(low, n)

def pp_covers_any(rs: List<&2, Pp.Rule>, +at: List<&2, Nat>, +low: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> rest:
      Bool.or(pp_covers(r, at, low), pp_covers_any(rest, at, low))

# the entries of the rules: a Tree's or a Dir's path (a Named rule has none)
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

# the first class that applies
def pp_cls_pick(sec: Bool, prot: Bool, ins: Bool) -> Pp.Cls:
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
              Pp.Inside{}
            case False{}:
              Pp.Outside{}

# the class of the real path at (looped: l) under the policy ro, ru, se:
# Secret under a secret entry; else Protected when a rule covers it or it
# is a strict ancestor of a Tree or Dir entry or of a secret entry; else
# Inside under a workspace root when its links did not loop; else Outside
def pp_class(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, l: Bool) -> Pp.Cls:
  pp_cls_pick(pp_under_any(se, at), Bool.or(pp_covers_any(ru, at, pp_below_root(ro, at)), Bool.or(pp_above_any(pp_entries(ru), at), pp_above_any(se, at))), Bool.and(pp_under_any(ro, at), Bool.not(l)))

# LAW path_judge_class_exact: the class the judgment of a resolved path answers, under any policy,
# is the spec's: Secret under a secret entry; else Protected when a Tree
# rule's path is at or above it, it is a Dir rule's directory or directly
# in it, a Named rule's name is one of its names strictly below its
# deepest workspace root (any of its names when no root holds it), or it
# is a strict ancestor of a Tree or Dir entry or of a secret entry; else
# Inside when a workspace root is at or above it and its links did not
# loop; else Outside
# EXCLUDES: a dropped or misread rule entry (an ancestor of a protected
#   entry left Inside), a Named rule read below a root other than the
#   deepest one (or on the root's own name), a Dir rule that covers a
#   grandchild or misses a child, a Tree rule that misses a path below it,
#   classes in another order, a loop that leaves a path Inside
law path_judge_class_exact:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +at: List<&2, Nat>
  for +l: Bool
  {Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == pp_class(ro, ru, se, at, l) : Pp.Cls}

# LAW path_judge_class_example: anchor: under the root /1, /1/2 is Inside and Outside when its
# links looped, /3/2 (no root) is Outside; with the secret /1/4, /1/4/7 is
# Secret and /1 Protected; with a Dir /1 rule, /1/2 is Protected and
# /1/2/3 Inside; with a Tree /1/6 rule, /1 and /1/6/8 are Protected; with
# the nested roots /1 and /1/2 and a Named 2 rule, /1/2/5 is Inside (no 2
# below its deepest root /1/2), /1/5/2 is Protected, and the root /1/2
# itself is Inside
# EXCLUDES: a vacuous path_judge_guards_secret_ancestor, a Named rule read
#   below the outer root, a Dir rule that covers a grandchild
law path_judge_class_example:
  {[Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], Nil{}, Nil{}}, Pp.Res{[2n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], Nil{}, Nil{}}, Pp.Res{[2n, 1n], True{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{Nil{}, Nil{}, Nil{}}, Pp.Res{[2n, 3n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], Nil{}, [[4n, 1n]]}, Pp.Res{[7n, 4n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], Nil{}, [[4n, 1n]]}, Pp.Res{[1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], [Pp.Dir{[1n]}], Nil{}}, Pp.Res{[2n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], [Pp.Dir{[1n]}], Nil{}}, Pp.Res{[3n, 2n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], [Pp.Tree{[6n, 1n]}], Nil{}}, Pp.Res{[1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], [Pp.Tree{[6n, 1n]}], Nil{}}, Pp.Res{[8n, 6n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n], [2n, 1n]], [Pp.Named{2n}], Nil{}}, Pp.Res{[5n, 2n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n], [2n, 1n]], [Pp.Named{2n}], Nil{}}, Pp.Res{[2n, 5n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n], [2n, 1n]], [Pp.Named{2n}], Nil{}}, Pp.Res{[2n, 1n], False{}}))] == [Pp.Inside{}, Pp.Outside{}, Pp.Outside{}, Pp.Secret{}, Pp.Protected{}, Pp.Protected{}, Pp.Inside{}, Pp.Protected{}, Pp.Protected{}, Pp.Inside{}, Pp.Protected{}, Pp.Inside{}] : List<&2, Pp.Cls>}

# (G1) The real path, against an independent spec
# -----------------------------------------------
# path_real_has_no_link and path_real_reaches_no_link are one-way (the path
# a resolution reaches stands on no link unless it looped) and
# path_real_links_example has no `..` or `.`: a resolution that reads `..`
# as `.` passes them, and the class, gate and store laws judge whatever path
# it reaches (/3/7/../5 judged at /3/7/5, so a secret /3/5 read unasked).
# The laws below pin the whole resolution to Rust's (crates/eukhe-types/
# src/path_policy.rs `resolve`), spelled here: from `/`, a name enters the
# directory, `.` stays, `..` goes to the parent of the real directory (`..`
# of `/` is `/`); a name at the location of a link is replaced by the link's
# target, read from `/` (absolute) or from the link's directory (relative),
# for at most 40 links (MAX_LINKS); past them every link met is kept as a
# name and the path loops.

# the parent of the path at; `/` is its own parent
def pp_parent(at: List<&2, Nat>) -> List<&2, Nat>:
  match at:
    case Nil{}:
      Nil{}
    case x <> r:
      r

# l when hit, else the rest's answer
def pp_link_pick(hit: Bool, l: Pp.Link, rest: Maybe<&2, Pp.Link>) -> Maybe<&2, Pp.Link>:
  match hit:
    case True{}:
      Some{l}
    case False{}:
      rest

# the first link of ls at the location k, if any
def pp_link_of(ls: List<&2, Pp.Link>, +k: List<&2, Nat>) -> Maybe<&2, Pp.Link>:
  match ls:
    case Nil{}:
      None{}
    case l <> rest:
      match l:
        case Pp.Link{+a, b, t}:
          pp_link_pick(pp_same(a, k), Pp.Link{a, b, t}, pp_link_of(rest, k))

# the link the first segment of segs enters from the directory at, if any
# (`..` and `.` enter none)
def pp_link_next(+ls: List<&2, Pp.Link>, segs: List<&2, Tl.Seg>, at: List<&2, Nat>) -> Maybe<&2, Pp.Link>:
  match segs:
    case Nil{}:
      None{}
    case s <> rest:
      match s:
        case Tl.Name{n}:
          pp_link_of(ls, n <> at)
        case Tl.Up{}:
          None{}
        case Tl.Here{}:
          None{}

# segs walked from the directory at once no link is left to follow: a name
# enters it (a link there is kept as a name, and the path loops), `.`
# stays, `..` goes to the parent; l: the path looped already
def pp_walk_past(segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, l: Bool) -> Pp.Res:
  match segs:
    case Nil{}:
      Pp.Res{at, l}
    case s <> rest:
      match s:
        case Tl.Name{+n}:
          pp_walk_past(rest, ls, n <> at, Bool.or(l, pp_link_at(ls, n <> at)))
        case Tl.Up{}:
          pp_walk_past(rest, ls, pp_parent(at), l)
        case Tl.Here{}:
          pp_walk_past(rest, ls, at, l)

# segs walked from the directory at with n links left to follow: a name at
# a link's location continues with the link's target, then the rest, from
# `/` (absolute) or from at (relative), one link fewer; hit is
# pp_link_next(ls, segs, at) (Bend matches only parameters)
def pp_walk(n: Nat, segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, hit: Maybe<&2, Pp.Link>) -> Pp.Res:
  match n:
    case 0n:
      pp_walk_past(segs, ls, at, False{})
    case 1n+k:
      match segs:
        case Nil{}:
          Pp.Res{at, False{}}
        case s <> +rest:
          match s:
            case Tl.Name{+x}:
              match hit:
                case None{}:
                  pp_walk(1n+k, rest, ls, x <> at, pp_link_next(ls, rest, x <> at))
                case Some{lk}:
                  match lk:
                    case Pp.Link{la, abs, +to}:
                      match abs:
                        case True{}:
                          pp_walk(k, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, pp_link_next(ls, List.append(&2, Tl.Seg, to, rest), Nil{}))
                        case False{}:
                          pp_walk(k, List.append(&2, Tl.Seg, to, rest), ls, at, pp_link_next(ls, List.append(&2, Tl.Seg, to, rest), at))
            case Tl.Up{}:
              pp_walk(1n+k, rest, ls, pp_parent(at), pp_link_next(ls, rest, pp_parent(at)))
            case Tl.Here{}:
              pp_walk(1n+k, rest, ls, at, pp_link_next(ls, rest, at))

# the real path of segs (from `/`, 40 links at most) and whether its links
# looped
def pp_real(+ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>) -> Pp.Res:
  pp_walk(40n, segs, ls, Nil{}, pp_link_next(ls, segs, Nil{}))

# the path segs leads to from the directory at when no link is anywhere: a
# name enters it, `.` stays, `..` goes to the parent
def pp_walk_plain(segs: List<&2, Tl.Seg>, at: List<&2, Nat>) -> List<&2, Nat>:
  match segs:
    case Nil{}:
      at
    case s <> rest:
      match s:
        case Tl.Name{n}:
          pp_walk_plain(rest, n <> at)
        case Tl.Up{}:
          pp_walk_plain(rest, pp_parent(at))
        case Tl.Here{}:
          pp_walk_plain(rest, at)

# LAW path_real_exact: the resolution of any path under any links is the spec's: from `/`, a
# name enters the directory, `.` stays, `..` goes to the parent of the real
# directory (`/` stays `/`), a name at a link's location (the first link
# there) is replaced by the link's target, read from `/` or from the link's
# directory, for at most 40 links; past them every link met is kept as a
# name and the path loops
# EXCLUDES: `..` read as `.`, as two levels up, or from the path as written
#   (before its links); `..` of `/` anything but `/`; a relative target
#   read from `/` or from the link itself; a link limit other than 40; a
#   loop flag lost or invented; a link skipped, or followed at another
#   location
law path_real_exact:
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  {Pp.real(ls, segs) == pp_real(ls, segs) : Pp.Res}

# LAW path_real_no_links_exact: with no link anywhere, the real path of any path is its plain walk
# from `/` (a name enters, `.` stays, `..` goes to the parent, `/` stays
# `/`), and it never loops
# EXCLUDES: `..` read as `.` or as two levels up, `.` read as anything but
#   staying, a loop with no link
law path_real_no_links_exact:
  for +segs: List<&2, Tl.Seg>
  {Pp.real(Nil{}, segs) == Pp.Res{pp_walk_plain(segs, Nil{}), False{}} : Pp.Res}

# LAW path_real_dots_at_root: under any links, `..` and `.` at `/` change nothing: the path
# resolves as without them
# EXCLUDES: `..` of `/` read as an error, a name or a loop
law path_real_dots_at_root:
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  {[Pp.real(ls, Tl.Up{} <> segs), Pp.real(ls, Tl.Here{} <> segs)] == [Pp.real(ls, segs), Pp.real(ls, segs)] : List<&2, Pp.Res>}

# LAW path_real_dots_example: anchor: under the root /3 with the secret /3/5, /3/7/../5 is
# /3/5 and Secret, /3/5/../7 is /3/7 and Inside; /../1/./2 is /1/2; a
# relative link /1/2/3 -> ../4 makes /1/2/3/5 /1/4/5 (from the link's
# directory /1/2); `..` after an absolute link /1/2 -> /9/8 goes up from
# the target (/1/2/../6 is /9/6); a relative link /1 -> ./3/../4 makes /1/7
# /4/7; none loops; the spec agrees on the first and the last two
# EXCLUDES: `..` read as `.` (the secret /3/5 judged at /3/7/5, Inside),
#   from the path as written, or as two levels up; a relative target read
#   from `/` or from the link itself
law path_real_dots_example:
  {[Pp.real(Nil{}, [Tl.Name{3n}, Tl.Name{7n}, Tl.Up{}, Tl.Name{5n}]), Pp.real(Nil{}, [Tl.Name{3n}, Tl.Name{5n}, Tl.Up{}, Tl.Name{7n}]), Pp.real(Nil{}, [Tl.Up{}, Tl.Name{1n}, Tl.Here{}, Tl.Name{2n}]), Pp.real([Pp.Link{[3n, 2n, 1n], False{}, [Tl.Up{}, Tl.Name{4n}]}], [Tl.Name{1n}, Tl.Name{2n}, Tl.Name{3n}, Tl.Name{5n}]), Pp.real([Pp.Link{[2n, 1n], True{}, [Tl.Name{9n}, Tl.Name{8n}]}], [Tl.Name{1n}, Tl.Name{2n}, Tl.Up{}, Tl.Name{6n}]), Pp.real([Pp.Link{[1n], False{}, [Tl.Here{}, Tl.Name{3n}, Tl.Up{}, Tl.Name{4n}]}], [Tl.Name{1n}, Tl.Name{7n}])] == [Pp.Res{[5n, 3n], False{}}, Pp.Res{[7n, 3n], False{}}, Pp.Res{[2n, 1n], False{}}, Pp.Res{[5n, 4n, 1n], False{}}, Pp.Res{[6n, 9n], False{}}, Pp.Res{[7n, 4n], False{}}] : List<&2, Pp.Res>} & {[Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{7n}, Tl.Up{}, Tl.Name{5n}]), Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{5n}, Tl.Up{}, Tl.Name{7n}])] == [Pp.Secret{}, Pp.Inside{}] : List<&2, Pp.Cls>} & {[pp_real(Nil{}, [Tl.Name{3n}, Tl.Name{7n}, Tl.Up{}, Tl.Name{5n}]), pp_real([Pp.Link{[2n, 1n], True{}, [Tl.Name{9n}, Tl.Name{8n}]}], [Tl.Name{1n}, Tl.Name{2n}, Tl.Up{}, Tl.Name{6n}]), pp_real([Pp.Link{[1n], False{}, [Tl.Here{}, Tl.Name{3n}, Tl.Up{}, Tl.Name{4n}]}], [Tl.Name{1n}, Tl.Name{7n}])] == [Pp.Res{[5n, 3n], False{}}, Pp.Res{[6n, 9n], False{}}, Pp.Res{[7n, 4n], False{}}] : List<&2, Pp.Res>}
