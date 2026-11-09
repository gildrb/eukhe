# eukhe: the laws of area path_policy: the real path, the judgment, the store, the entry

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../base.bend as LawsBase

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
# projection and scans (Pp.Pol.secret, Pp.any_under, Pp.any_ancestor): a
# model whose projection forgets the secret entries passes every one of
# them (no path is ever secret). The laws below state the claims over the
# policy's own fields Pol{ro, ru, se}, an entry and a path given by list
# splits, never by a scan of the spec's own (a scan of the entries written
# here would be a copy of Pp.any_under or Pp.any_ancestor, and a bug copied
# into both would pass): an entry s of the secret entries is se ==
# se1 ++ s :: se2; a path at s or under it is k ++ s; a path strictly above
# s is at with s == m :: k ++ at. A path is a list of names, deepest first;
# Nil{} is `/`.

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

# LAW path_judge_secret_under: under a policy whose secret entries are se1 ++ s :: se2, the entry s
# and every path under it (k ++ s, any names k) are judged Secret, whatever
# the roots, the rules and the other entries, and whether or not the
# path's links looped (docs/tools.md G1.2 item 1)
# EXCLUDES: a model that drops, ignores or misreads the policy's secret
#   entries (no path secret), a secret test that misses the entry itself
#   or a path below it, or reads only some of the entries, a rule or a
#   root that overrides a secret, a loop that changes a Secret class
law path_judge_secret_under:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se1: List<&2, List<&2, Nat>>
  for +s: List<&2, Nat>
  for +se2: List<&2, List<&2, Nat>>
  for +k: List<&2, Nat>
  for +l: Bool
  {Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, List.append(&2, List<&2, Nat>, se1, s <> se2)}, Pp.Res{List.append(&2, Nat, k, s), l})) == Pp.Secret{} : Pp.Cls}

# LAW path_judge_secret_has_entry: a path judged Secret is a secret entry of the policy or under one:
# the secret entries are se1 ++ s :: se2 and the path is k ++ s
# (docs/tools.md G1.2 item 1: nothing else is Secret)
# EXCLUDES: a secret test that flags a sibling or an ancestor of an entry,
#   every path, a path no entry is at or above, or a path a rule or a root
#   covers
law path_judge_secret_has_entry:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +at: List<&2, Nat>
  for +l: Bool
  for sec: {Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == Pp.Secret{} : Pp.Cls}
  exs se1: List<&2, List<&2, Nat>>
  exs s: List<&2, Nat>
  exs se2: List<&2, List<&2, Nat>>
  exs k: List<&2, Nat>
  {se == List.append(&2, List<&2, Nat>, se1, s <> se2) : List<&2, List<&2, Nat>>} & {at == List.append(&2, Nat, k, s) : List<&2, Nat>}

# LAW path_holds_at_or_under_secret: a secret entry of the policy, and every path under it, holds a
# secret, whatever the other entries and whether or not its links looped
# EXCLUDES: a holds answer computed from anything but the policy's own
#   secret entries (none), a holds test that misses a secret file or a
#   directory inside a secret one
law path_holds_at_or_under_secret:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se1: List<&2, List<&2, Nat>>
  for +s: List<&2, Nat>
  for +se2: List<&2, List<&2, Nat>>
  for +k: List<&2, Nat>
  for +l: Bool
  {Pp.Judged.holds(Pp.judge(Pp.Pol{ro, ru, List.append(&2, List<&2, Nat>, se1, s <> se2)}, Pp.Res{List.append(&2, Nat, k, s), l})) == True{} : Bool}

# LAW path_holds_above_secret: a directory strictly above a secret entry of the policy holds a
# secret (a recursive read of it reads the secret)
# EXCLUDES: a holds test that misses a directory above a secret (a search
#   of the home dir reads ~/.ssh unasked)
law path_holds_above_secret:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se1: List<&2, List<&2, Nat>>
  for +m: Nat
  for +k: List<&2, Nat>
  for +at: List<&2, Nat>
  for +se2: List<&2, List<&2, Nat>>
  for +l: Bool
  {Pp.Judged.holds(Pp.judge(Pp.Pol{ro, ru, List.append(&2, List<&2, Nat>, se1, (m <> List.append(&2, Nat, k, at)) <> se2)}, Pp.Res{at, l})) == True{} : Bool}

# LAW path_holds_only_with_secret: a path holds a secret only when one of the policy's secret
# entries s and it are on one line: some location (k1 ++ s, k2 ++ at) is
# at or under both, so the entry is the path, above it or below it
# EXCLUDES: a holds test that flags a sibling of a secret, or every path
#   (all), or reads entries other than the policy's
law path_holds_only_with_secret:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +at: List<&2, Nat>
  for +l: Bool
  for holds: {Pp.Judged.holds(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == True{} : Bool}
  exs se1: List<&2, List<&2, Nat>>
  exs s: List<&2, Nat>
  exs se2: List<&2, List<&2, Nat>>
  exs k1: List<&2, Nat>
  exs k2: List<&2, Nat>
  {se == List.append(&2, List<&2, Nat>, se1, s <> se2) : List<&2, List<&2, Nat>>} & {List.append(&2, Nat, k1, s) == List.append(&2, Nat, k2, at) : List<&2, Nat>}

# LAW path_judge_guards_secret_ancestor: a path strictly above a secret entry of the policy (the
# entries are se1 ++ (m :: k ++ at) :: se2: a move or a removal of the path
# moves or removes the secret) is judged Protected or Secret, whatever the
# roots, the rules and the other entries, and whether or not its links
# looped (docs/tools.md G1.2 item 2)
# EXCLUDES: a directory above a secret judged Inside or Outside, because the
#   model forgot or misread the secret entries, read them in the wrong
#   direction (a path below an entry guarded instead of one above), or
#   reads only some of them
law path_judge_guards_secret_ancestor:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se1: List<&2, List<&2, Nat>>
  for +m: Nat
  for +k: List<&2, Nat>
  for +at: List<&2, Nat>
  for +se2: List<&2, List<&2, Nat>>
  for +l: Bool
  {Pp.Cls.guarded(Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, List.append(&2, List<&2, Nat>, se1, (m <> List.append(&2, Nat, k, at)) <> se2)}, Pp.Res{at, l}))) == True{} : Bool}

# LAW secrets_kept_without_yes: under a policy whose secret entries are se1 ++ s :: se2, any sequence
# of agent writes through any paths and any links, none with the user's
# yes, whatever the roots, the rules and the auto set hold, leaves the
# content at the entry s and at every location under it (k ++ s) as it was
# (the first cell there, or none) (docs/tools.md G1.6, G1.7)
# EXCLUDES: a write without a yes that lands on a secret entry or under
#   it, because the model forgot or misread the secret entries, or the
#   gate, the resolution or the store lets one through
law secrets_kept_without_yes:
  for es: List<&2, Pp.Put>
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se1: List<&2, List<&2, Nat>>
  for +s: List<&2, Nat>
  for +se2: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  for +k: List<&2, Nat>
  for no: {pp_no_yes(es) == True{} : Bool}
  {pp_cell(Pp.run(es, Pp.Pol{ro, ru, List.append(&2, List<&2, Nat>, se1, s <> se2)}, ls, auto, cs), List.append(&2, Nat, k, s)) == pp_cell(cs, List.append(&2, Nat, k, s)) : Maybe<&2, Nat>}

# LAW path_judge_secret_example: anchor and witness: with the secret /3/5, /3/5 is Secret and
# holds a secret, its parent /3 is Protected and holds one, its sibling /3/7
# is Outside and holds none (the premise of path_judge_secret_has_entry is
# satisfiable), and a write without a yes exists (the premise of
# secrets_kept_without_yes is satisfiable)
# EXCLUDES: vacuous path_judge_secret_has_entry or secrets_kept_without_yes,
#   a judgment that forgets the secret entries
law path_judge_secret_example:
  {[Pp.judge(Pp.Pol{Nil{}, Nil{}, [[5n, 3n]]}, Pp.Res{[5n, 3n], False{}}), Pp.judge(Pp.Pol{Nil{}, Nil{}, [[5n, 3n]]}, Pp.Res{[3n], False{}}), Pp.judge(Pp.Pol{Nil{}, Nil{}, [[5n, 3n]]}, Pp.Res{[7n, 3n], False{}})] == [Pp.Judged{Pp.Secret{}, True{}}, Pp.Judged{Pp.Protected{}, True{}}, Pp.Judged{Pp.Outside{}, False{}}] : List<&2, Pp.Judged>} & {pp_no_yes([Pp.Put{[Tl.Name{3n}, Tl.Name{5n}], 1n, Pp.No{}}]) == True{} : Bool}

# LAW secrets_kept_example: anchor: under roots [/3] and the secret /3/5, with write in the auto
# set, a write of 1 to /3/5 without a yes leaves its 0, the same write with
# a yes lands, and a write of 2 to /3/7 without a yes lands
# EXCLUDES: a vacuous secrets_kept_without_yes (no write runs at all), a
#   gate that ignores the user's yes
law secrets_kept_example:
  {[pp_cell(Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{5n}], 1n, Pp.No{}}], Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [1n], [Pp.Cell{[5n, 3n], 0n}]), [5n, 3n]), pp_cell(Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{5n}], 1n, Pp.Yes{}}], Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [1n], [Pp.Cell{[5n, 3n], 0n}]), [5n, 3n]), pp_cell(Pp.run([Pp.Put{[Tl.Name{3n}, Tl.Name{7n}], 2n, Pp.No{}}], Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [1n], Nil{}), [7n, 3n])] == [Some{0n}, Some{1n}, Some{2n}] : List<&2, Maybe<&2, Nat>>}

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
# then whether the model judges that the path holds a secret (pinned
# against the policy's own secret entries by the path_holds_* laws)
def pp_spell_answer(q: FPp.Req) -> String:
  match q:
    case FPp.Req{p, r}:
      match p r:
        case Pp.Pol{+ro, +ru, +se} Pp.Res{+at, +l}:
          Wr.put_nat(pp_cls_tag(Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}))), Wr.put_bool(Pp.Judged.holds(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})), ""))

# LAW path_policy_ffi_answers_spelled: a request spelled as Rust writes it, every count and number
# within the wire, is answered with the class the model judges, in the tag
# Rust reads, then whether the model judges that the path holds a secret
# EXCLUDES: a request or reply tag drift both sides of the Bend entry share
#   (rule tags, class tags swapped), a holds Bool flipped or dropped, a
#   path or list item offset other than Rust's
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

# (G1) The class, clause by clause
# --------------------------------
# path_secret_wins, path_ancestor_guarded and path_inside_is_safe read the
# model's own entries, root choice and rule tests (Pp.entries, Pp.root.of,
# Pp.protects): a model that drops a rule's entry, or picks another root
# for a Named rule, passes them; and a Pp.class that drops every rule's
# cover (a Tree rule's path read as Inside), with a Pp.safe that drops it
# too, passed every law (an adversary found this gap). The laws below state
# each clause of docs/tools.md G1.2 and G1.3 for the class of a path through
# any links (Pp.class: the class the gate and the store judge), over the
# policy's own fields Pol{ro, ru, se} and its real path, with constructors
# and list splits (a path p is at or above q when q is k ++ p, names deepest
# first): each rule protects what it covers, a strict ancestor of an entry
# is protected, a root holds what is under it, nothing else is protected or
# Inside, a loop never leaves a path Inside. A Named rule looks at the names
# of the path strictly below its deepest workspace root (all of them when
# no root holds it).

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

# a Tree (tree) or a Dir rule on the path p
def pp_entry_rule(tree: Bool, p: List<&2, Nat>) -> Pp.Rule:
  match tree:
    case True{}:
      Pp.Tree{p}
    case False{}:
      Pp.Dir{p}

# LAW path_tree_rule_protects: a path whose real path is a Tree rule's path or under it is
# Protected, unless it is Secret, whatever the other rules, roots and links
# EXCLUDES: a Tree rule that misses its own path (a workspace's .git judged
#   Inside) or a path below it, a class that drops a rule's cover
law path_tree_rule_protects:
  for +ro: List<&2, List<&2, Nat>>
  for +ru1: List<&2, Pp.Rule>
  for +p: List<&2, Nat>
  for +ru2: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for +k: List<&2, Nat>
  for +l: Bool
  for res: {Pp.real(ls, segs) == Pp.Res{List.append(&2, Nat, k, p), l} : Pp.Res}
  for ns: {Pp.class(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, Pp.Tree{p} <> ru2), se}, ls, segs) != Pp.Secret{} : Pp.Cls}
  {Pp.class(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, Pp.Tree{p} <> ru2), se}, ls, segs) == Pp.Protected{} : Pp.Cls}

# LAW path_dir_rule_protects: a path whose real path is a Dir rule's directory or an entry directly
# in it (k ++ p with at most one name k) is Protected, unless it is Secret
# EXCLUDES: a Dir rule that misses its directory or a child (the agent
#   dir's settings.json judged Inside)
law path_dir_rule_protects:
  for +ro: List<&2, List<&2, Nat>>
  for +ru1: List<&2, Pp.Rule>
  for +p: List<&2, Nat>
  for +ru2: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for +k: List<&2, Nat>
  for +l: Bool
  for one: {Nat.is_lt(List.length(&2, Nat, k), 2n) == True{} : Bool}
  for res: {Pp.real(ls, segs) == Pp.Res{List.append(&2, Nat, k, p), l} : Pp.Res}
  for ns: {Pp.class(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, Pp.Dir{p} <> ru2), se}, ls, segs) != Pp.Secret{} : Pp.Cls}
  {Pp.class(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, Pp.Dir{p} <> ru2), se}, ls, segs) == Pp.Protected{} : Pp.Cls}

# LAW path_named_rule_protects: a path that has a Named rule's name among the names of its real
# path below its deepest workspace root (all its names when no root holds
# it) is Protected, unless it is Secret
# EXCLUDES: a Named rule that misses a `.git` or `.eukhe` directory below
#   the root, or the files in it
law path_named_rule_protects:
  for +ro: List<&2, List<&2, Nat>>
  for +ru1: List<&2, Pp.Rule>
  for +n: Nat
  for +ru2: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for +at: List<&2, Nat>
  for +l: Bool
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  for res: {Pp.real(ls, segs) == Pp.Res{at, l} : Pp.Res}
  for named: {pp_below_root(ro, at) == List.append(&2, Nat, xs, n <> ys) : List<&2, Nat>}
  for ns: {Pp.class(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, Pp.Named{n} <> ru2), se}, ls, segs) != Pp.Secret{} : Pp.Cls}
  {Pp.class(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, Pp.Named{n} <> ru2), se}, ls, segs) == Pp.Protected{} : Pp.Cls}

# LAW path_entry_ancestor_protects: a path whose real path is a strict ancestor of a Tree or Dir
# rule's path is Protected, unless it is Secret (moving or removing it
# moves or removes the entry)
# EXCLUDES: a dropped or misread rule entry (an ancestor of a protected
#   entry left Inside)
law path_entry_ancestor_protects:
  for +ro: List<&2, List<&2, Nat>>
  for +ru1: List<&2, Pp.Rule>
  for +tree: Bool
  for +m: Nat
  for +k: List<&2, Nat>
  for +ru2: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for +at: List<&2, Nat>
  for +l: Bool
  for res: {Pp.real(ls, segs) == Pp.Res{at, l} : Pp.Res}
  for ns: {Pp.class(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, pp_entry_rule(tree, m <> List.append(&2, Nat, k, at)) <> ru2), se}, ls, segs) != Pp.Secret{} : Pp.Cls}
  {Pp.class(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, pp_entry_rule(tree, m <> List.append(&2, Nat, k, at)) <> ru2), se}, ls, segs) == Pp.Protected{} : Pp.Cls}

# LAW path_protected_has_cause: a path is never Protected without a cause: when no Tree rule's
# path is at or above its real path, no Dir rule's directory is it or its
# parent, no Named rule's name is among its names below its deepest root,
# and it is no strict ancestor of a Tree or Dir rule's path or of a secret
# entry, it is not Protected
# EXCLUDES: a rule that protects a path it does not cover (a Dir rule's
#   grandchild, a Tree rule's sibling or parent, a Named rule's name at or
#   above the root), a path protected with no rule at all
law path_protected_has_cause:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for +at: List<&2, Nat>
  for +l: Bool
  for res: {Pp.real(ls, segs) == Pp.Res{at, l} : Pp.Res}
  for tree: @ru1: List<&2, Pp.Rule> -> @p: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> @k: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Tree{p} <> ru2) : List<&2, Pp.Rule>} -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>} -> Empty
  for dir: @ru1: List<&2, Pp.Rule> -> @p: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> @k: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Dir{p} <> ru2) : List<&2, Pp.Rule>} -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>} -> {Nat.is_lt(List.length(&2, Nat, k), 2n) == True{} : Bool} -> Empty
  for named: @ru1: List<&2, Pp.Rule> -> @n: Nat -> @ru2: List<&2, Pp.Rule> -> @xs: List<&2, Nat> -> @ys: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Named{n} <> ru2) : List<&2, Pp.Rule>} -> {pp_below_root(ro, at) == List.append(&2, Nat, xs, n <> ys) : List<&2, Nat>} -> Empty
  for entry: @ru1: List<&2, Pp.Rule> -> @t: Bool -> @m: Nat -> @k: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> {ru == List.append(&2, Pp.Rule, ru1, pp_entry_rule(t, m <> List.append(&2, Nat, k, at)) <> ru2) : List<&2, Pp.Rule>} -> Empty
  for secret: @se1: List<&2, List<&2, Nat>> -> @m: Nat -> @k: List<&2, Nat> -> @se2: List<&2, List<&2, Nat>> -> {se == List.append(&2, List<&2, Nat>, se1, (m <> List.append(&2, Nat, k, at)) <> se2) : List<&2, List<&2, Nat>>} -> Empty
  {Pp.class(Pp.Pol{ro, ru, se}, ls, segs) != Pp.Protected{} : Pp.Cls}

# LAW path_root_inside: a path whose links did not loop and whose real path is a workspace root or
# under one is Inside, unless it is Protected or Secret
# EXCLUDES: a root that holds nothing (every path Outside), a root read
#   from the written path
law path_root_inside:
  for +ro1: List<&2, List<&2, Nat>>
  for +q: List<&2, Nat>
  for +ro2: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for +k: List<&2, Nat>
  for res: {Pp.real(ls, segs) == Pp.Res{List.append(&2, Nat, k, q), False{}} : Pp.Res}
  for np: {Pp.class(Pp.Pol{List.append(&2, List<&2, Nat>, ro1, q <> ro2), ru, se}, ls, segs) != Pp.Protected{} : Pp.Cls}
  for ns: {Pp.class(Pp.Pol{List.append(&2, List<&2, Nat>, ro1, q <> ro2), ru, se}, ls, segs) != Pp.Secret{} : Pp.Cls}
  {Pp.class(Pp.Pol{List.append(&2, List<&2, Nat>, ro1, q <> ro2), ru, se}, ls, segs) == Pp.Inside{} : Pp.Cls}

# LAW path_inside_needs_root: a path is Inside only when one of the workspace roots is its real
# path or above it
# EXCLUDES: a path outside every root (or no root at all) judged Inside
law path_inside_needs_root:
  for +ro: List<&2, List<&2, Nat>>
  for +ru: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for +at: List<&2, Nat>
  for +l: Bool
  for res: {Pp.real(ls, segs) == Pp.Res{at, l} : Pp.Res}
  for inside: {Pp.class(Pp.Pol{ro, ru, se}, ls, segs) == Pp.Inside{} : Pp.Cls}
  exs ro1: List<&2, List<&2, Nat>>
  exs q: List<&2, Nat>
  exs ro2: List<&2, List<&2, Nat>>
  exs k: List<&2, Nat>
  {ro == List.append(&2, List<&2, Nat>, ro1, q <> ro2) : List<&2, List<&2, Nat>>} & {at == List.append(&2, Nat, k, q) : List<&2, Nat>}

# LAW path_looped_never_inside: a path whose links looped is never Inside, whatever the policy
# EXCLUDES: a loop that leaves a path Inside (the rest of a looping path
#   trusted)
law path_looped_never_inside:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for +at: List<&2, Nat>
  for res: {Pp.real(ls, segs) == Pp.Res{at, True{}} : Pp.Res}
  {Pp.class(pol, ls, segs) != Pp.Inside{} : Pp.Cls}

# LAW path_rule_never_unprotects: adding a rule anywhere in a policy's rules (ru1 ++ r :: ru2 in
# place of ru1 ++ ru2) never turns a Protected path into another class
# EXCLUDES: a rule that hides or overrides another rule's cover, or an
#   entry's ancestor, wherever it is added (a cover read from the first or
#   the last rule alone)
law path_rule_never_unprotects:
  for +ro: List<&2, List<&2, Nat>>
  for +ru1: List<&2, Pp.Rule>
  for +r: Pp.Rule
  for +ru2: List<&2, Pp.Rule>
  for +se: List<&2, List<&2, Nat>>
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for prot: {Pp.class(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, ru2), se}, ls, segs) == Pp.Protected{} : Pp.Cls}
  {Pp.class(Pp.Pol{ro, List.append(&2, Pp.Rule, ru1, r <> ru2), se}, ls, segs) == Pp.Protected{} : Pp.Cls}

# LAW path_judge_class_example: anchor: under the root /1, /1/2 is Inside and Outside when its
# links looped, /3/2 (no root) is Outside; with the secret /1/4, /1/4/7 is
# Secret and /1 Protected; with a Dir /1 rule, /1/2 is Protected and
# /1/2/3 Inside; with a Tree /1/6 rule, /1 and /1/6/8 are Protected; with
# the nested roots /1 and /1/2 and a Named 2 rule, /1/2/5 is Inside (no 2
# below its deepest root /1/2), /1/5/2 is Protected, and the root /1/2
# itself is Inside
# EXCLUDES: a Named rule read below the outer root, a Dir rule that covers
#   a grandchild
law path_judge_class_example:
  {[Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], Nil{}, Nil{}}, Pp.Res{[2n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], Nil{}, Nil{}}, Pp.Res{[2n, 1n], True{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{Nil{}, Nil{}, Nil{}}, Pp.Res{[2n, 3n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], Nil{}, [[4n, 1n]]}, Pp.Res{[7n, 4n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], Nil{}, [[4n, 1n]]}, Pp.Res{[1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], [Pp.Dir{[1n]}], Nil{}}, Pp.Res{[2n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], [Pp.Dir{[1n]}], Nil{}}, Pp.Res{[3n, 2n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], [Pp.Tree{[6n, 1n]}], Nil{}}, Pp.Res{[1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n]], [Pp.Tree{[6n, 1n]}], Nil{}}, Pp.Res{[8n, 6n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n], [2n, 1n]], [Pp.Named{2n}], Nil{}}, Pp.Res{[5n, 2n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n], [2n, 1n]], [Pp.Named{2n}], Nil{}}, Pp.Res{[2n, 5n, 1n], False{}})), Pp.Judged.cls(Pp.judge(Pp.Pol{[[1n], [2n, 1n]], [Pp.Named{2n}], Nil{}}, Pp.Res{[2n, 1n], False{}}))] == [Pp.Inside{}, Pp.Outside{}, Pp.Outside{}, Pp.Secret{}, Pp.Protected{}, Pp.Protected{}, Pp.Inside{}, Pp.Protected{}, Pp.Protected{}, Pp.Inside{}, Pp.Protected{}, Pp.Inside{}] : List<&2, Pp.Cls>}

# (G1) The real path, by its properties
# -------------------------------------
# path_real_has_no_link and path_real_reaches_no_link are one-way (the path
# a resolution reaches stands on no link unless it looped) and
# path_real_links_example has no `..` or `.`: a resolution that reads `..`
# as `.` passes them, and the class, gate and store laws judge whatever path
# it reaches (/3/7/../5 judged at /3/7/5, so a secret /3/5 read unasked).
# The laws below state the resolution of docs/tools.md G1.1 (Rust's
# crates/eukhe-types/src/path_policy.rs `resolve`) by what it does to a
# path, never by a second walker: `.` stays; `..` after a name that is no
# link goes back, and `..` of `/` is `/`; with no link a path never loops
# and a path of names resolves to those names; a name at the location of a
# link (the first link of ls there) resolves as the link's target then the
# rest, read from `/` (absolute) or from the link's directory (relative); a
# chain of links resolves to its end for at most 40 links (MAX_LINKS, as
# Linux) and loops past them. With no link, these pin the real path of
# every path: drop each `.`, cancel each name followed by `..`, drop each
# `..` at `/`, and what is left is names.

# where a link's target is read from: `/` for an absolute link, the
# directory p leads to (the link's directory) for a relative one
def pp_link_from(abs: Bool, p: List<&2, Tl.Seg>) -> List<&2, Tl.Seg>:
  match abs:
    case True{}:
      Nil{}
    case False{}:
      p

# the path written as the names xs from `/`, in order (the first name is
# the one right under `/`)
def pp_names(xs: List<&2, Nat>) -> List<&2, Tl.Seg>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      Tl.Name{x} <> pp_names(rest)

# LAW path_real_here_stays: under any links, a `.` anywhere in a path changes nothing: the path
# resolves as without it
# EXCLUDES: `.` read as a name, as `..`, or as a loop
law path_real_here_stays:
  for +ls: List<&2, Pp.Link>
  for +p: List<&2, Tl.Seg>
  for +r: List<&2, Tl.Seg>
  {Pp.real(ls, List.append(&2, Tl.Seg, p, Tl.Here{} <> r)) == Pp.real(ls, List.append(&2, Tl.Seg, p, r)) : Pp.Res}

# LAW path_real_up_cancels_name: under any links, where p resolves to at, a name n that is no link
# there followed by `..` changes nothing: `..` goes back to the real
# directory
# EXCLUDES: `..` read as `.` (the secret /3/5 judged at /3/7/5) or as two
#   levels up
law path_real_up_cancels_name:
  for +ls: List<&2, Pp.Link>
  for +p: List<&2, Tl.Seg>
  for +n: Nat
  for +r: List<&2, Tl.Seg>
  for +at: List<&2, Nat>
  for +l: Bool
  for reach: {Pp.real(ls, p) == Pp.Res{at, l} : Pp.Res}
  for plain: {pp_link_at(ls, n <> at) == False{} : Bool}
  {Pp.real(ls, List.append(&2, Tl.Seg, p, Tl.Name{n} <> Tl.Up{} <> r)) == Pp.real(ls, List.append(&2, Tl.Seg, p, r)) : Pp.Res}

# LAW path_real_up_at_root: under any links, where p resolves to `/`, a `..` after it changes
# nothing: `..` of `/` is `/`
# EXCLUDES: `..` of `/` read as an error, a name or a loop
law path_real_up_at_root:
  for +ls: List<&2, Pp.Link>
  for +p: List<&2, Tl.Seg>
  for +r: List<&2, Tl.Seg>
  for +l: Bool
  for reach: {Pp.real(ls, p) == Pp.Res{Nil{}, l} : Pp.Res}
  {Pp.real(ls, List.append(&2, Tl.Seg, p, Tl.Up{} <> r)) == Pp.real(ls, List.append(&2, Tl.Seg, p, r)) : Pp.Res}

# LAW path_real_link_followed: where p resolves to at without a loop, a name n whose location n/at
# holds a link (the first link of the links there) resolves, when the whole
# path does not loop, as the link's target then the rest r, read from `/`
# for an absolute link and from at (the link's directory) for a relative
# one; `..` in r then goes up from the target, not from the written name
# EXCLUDES: a link skipped or followed at another location, a relative
#   target read from `/` or from the link itself, `..` after a link read
#   from the path as written
law path_real_link_followed:
  for +ls1: List<&2, Pp.Link>
  for +n: Nat
  for +at: List<&2, Nat>
  for +abs: Bool
  for +to: List<&2, Tl.Seg>
  for +ls2: List<&2, Pp.Link>
  for +p: List<&2, Tl.Seg>
  for +r: List<&2, Tl.Seg>
  for +x: List<&2, Nat>
  for first: {pp_link_at(ls1, n <> at) == False{} : Bool}
  for reach: {Pp.real(List.append(&2, Pp.Link, ls1, Pp.Link{n <> at, abs, to} <> ls2), p) == Pp.Res{at, False{}} : Pp.Res}
  for ok: {Pp.real(List.append(&2, Pp.Link, ls1, Pp.Link{n <> at, abs, to} <> ls2), List.append(&2, Tl.Seg, p, Tl.Name{n} <> r)) == Pp.Res{x, False{}} : Pp.Res}
  {Pp.real(List.append(&2, Pp.Link, ls1, Pp.Link{n <> at, abs, to} <> ls2), List.append(&2, Tl.Seg, pp_link_from(abs, p), List.append(&2, Tl.Seg, to, r))) == Pp.Res{x, False{}} : Pp.Res}

# LAW path_real_chain_within: a chain of at most 40 links (/k -> /k-1 -> ... -> /0, Rust's
# MAX_LINKS, as Linux) resolves to its end without a loop
# EXCLUDES: a link limit below 40, a loop flag invented
law path_real_chain_within:
  for +k: Nat
  for le: {Nat.is_le(k, 40n) == True{} : Bool}
  {Pp.real(pp_chain(k), [Tl.Name{k}]) == Pp.Res{[0n], False{}} : Pp.Res}

# LAW path_real_chain_past: a chain of more than 40 links (41 + j) loops, at the link where the
# count ran out (/1+j kept as a name)
# EXCLUDES: a link limit above 40, a resolution that never loops, a loop
#   flag lost
law path_real_chain_past:
  for +j: Nat
  {Pp.real(pp_chain(Nat.add(41n, j)), [Tl.Name{Nat.add(41n, j)}]) == Pp.Res{[1n+j], True{}} : Pp.Res}

# LAW path_real_no_link_never_loops: with no link anywhere, no path loops (docs/tools.md G1.1: only
# links past MAX_LINKS loop)
# EXCLUDES: a loop flag set with no link (by a `..` at `/`, a long path, a
#   fuel spent on names)
law path_real_no_link_never_loops:
  for +segs: List<&2, Tl.Seg>
  {Pp.Res.looped(Pp.real(Nil{}, segs)) == False{} : Bool}

# LAW path_real_names_resolve: with no link anywhere, a path of names only resolves to those
# names (the real path lists them deepest first: Base List.reverse of the
# written order), and does not loop
# EXCLUDES: a name dropped, repeated or reordered, a resolution that starts
#   anywhere but `/`, a loop with no link
law path_real_names_resolve:
  for +xs: List<&2, Nat>
  {Pp.real(Nil{}, pp_names(xs)) == Pp.Res{List.reverse(&2, Nat, xs), False{}} : Pp.Res}

# LAW path_real_dots_example: anchor: under the root /3 with the secret /3/5, /3/7/../5 is
# /3/5 and Secret, /3/5/../7 is /3/7 and Inside; /../1/./2 is /1/2; a
# relative link /1/2/3 -> ../4 makes /1/2/3/5 /1/4/5 (from the link's
# directory /1/2); `..` after an absolute link /1/2 -> /9/8 goes up from
# the target (/1/2/../6 is /9/6); a relative link /1 -> ./3/../4 makes /1/7
# /4/7; none loops
# EXCLUDES: `..` read as `.` (the secret /3/5 judged at /3/7/5, Inside),
#   from the path as written, or as two levels up; a relative target read
#   from `/` or from the link itself
law path_real_dots_example:
  {[Pp.real(Nil{}, [Tl.Name{3n}, Tl.Name{7n}, Tl.Up{}, Tl.Name{5n}]), Pp.real(Nil{}, [Tl.Name{3n}, Tl.Name{5n}, Tl.Up{}, Tl.Name{7n}]), Pp.real(Nil{}, [Tl.Up{}, Tl.Name{1n}, Tl.Here{}, Tl.Name{2n}]), Pp.real([Pp.Link{[3n, 2n, 1n], False{}, [Tl.Up{}, Tl.Name{4n}]}], [Tl.Name{1n}, Tl.Name{2n}, Tl.Name{3n}, Tl.Name{5n}]), Pp.real([Pp.Link{[2n, 1n], True{}, [Tl.Name{9n}, Tl.Name{8n}]}], [Tl.Name{1n}, Tl.Name{2n}, Tl.Up{}, Tl.Name{6n}]), Pp.real([Pp.Link{[1n], False{}, [Tl.Here{}, Tl.Name{3n}, Tl.Up{}, Tl.Name{4n}]}], [Tl.Name{1n}, Tl.Name{7n}])] == [Pp.Res{[5n, 3n], False{}}, Pp.Res{[7n, 3n], False{}}, Pp.Res{[2n, 1n], False{}}, Pp.Res{[5n, 4n, 1n], False{}}, Pp.Res{[6n, 9n], False{}}, Pp.Res{[7n, 4n], False{}}] : List<&2, Pp.Res>} & {[Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{7n}, Tl.Up{}, Tl.Name{5n}]), Pp.class(Pp.Pol{[[3n]], Nil{}, [[5n, 3n]]}, Nil{}, [Tl.Name{3n}, Tl.Name{5n}, Tl.Up{}, Tl.Name{7n}])] == [Pp.Secret{}, Pp.Inside{}] : List<&2, Pp.Cls>}

# (G1) The safety of a path
# -------------------------
# path_inside_is_safe concludes the model's own Pp.safe: a Pp.class that
# drops every rule's cover (a Tree rule's path read as Inside), with a
# Pp.safe that drops it too, passed every law (an adversary found this
# gap). The law below makes safe and Inside one: with path_inside_is_safe,
# a path is safe exactly when it is Inside, which the laws of the class
# section state clause by clause.

# LAW path_safe_is_inside: a path is safe to write unasked (path_inside_is_safe's conclusion) only
# when it is Inside
# EXCLUDES: a safe test that misses a rule's cover, a secret, an entry
#   below the path, a loop or a missing root
law path_safe_is_inside:
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +segs: List<&2, Tl.Seg>
  for safe: {Pp.safe(pol, Pp.real(ls, segs)) == True{} : Bool}
  {Pp.class(pol, ls, segs) == Pp.Inside{} : Pp.Cls}

# LAW path_class_example: anchor: the adversary's input: under the root /3 with a Tree /3/9 rule
# (a workspace's .git), /3/9 and /3/9/1 are Protected and /3/7 Inside; /3/9
# is not safe, /3/7 is
# EXCLUDES: a class or a safe test that drops a rule's cover
law path_class_example:
  {[Pp.class(Pp.Pol{[[3n]], [Pp.Tree{[9n, 3n]}], Nil{}}, Nil{}, [Tl.Name{3n}, Tl.Name{9n}]), Pp.class(Pp.Pol{[[3n]], [Pp.Tree{[9n, 3n]}], Nil{}}, Nil{}, [Tl.Name{3n}, Tl.Name{9n}, Tl.Name{1n}]), Pp.class(Pp.Pol{[[3n]], [Pp.Tree{[9n, 3n]}], Nil{}}, Nil{}, [Tl.Name{3n}, Tl.Name{7n}])] == [Pp.Protected{}, Pp.Protected{}, Pp.Inside{}] : List<&2, Pp.Cls>} & {[Pp.safe(Pp.Pol{[[3n]], [Pp.Tree{[9n, 3n]}], Nil{}}, Pp.Res{[9n, 3n], False{}}), Pp.safe(Pp.Pol{[[3n]], [Pp.Tree{[9n, 3n]}], Nil{}}, Pp.Res{[7n, 3n], False{}})] == [False{}, True{}] : List<&2, Bool>}
