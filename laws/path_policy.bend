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

# LAW gate_write_auto_only_inside: a write runs without the user's yes only Inside the workspace:
# never Outside, never to eukhe's config or credentials, never to a
# secret, whatever the auto set holds
law gate_write_auto_only_inside:
  for c: Pp.Cls
  for +auto: List<&2, Nat>
  for ans: Pp.Ans
  for ran: {Pp.runs(c, Pp.Wr{}, auto, ans) == True{} : Bool}
  for no: {Pp.Ans.yes(ans) == False{} : Bool}
  {c == Pp.Inside{} : Pp.Cls}

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

# LAW config_needs_yes: no sequence of agent writes through any paths, each judged by the
# gate on its real path and landing there, without a yes of the user,
# changes a guarded location: eukhe's config (where the auto set,
# ssh.hosts and mcpServers live) and the secrets stay as they were,
# whatever the auto set holds
law config_needs_yes:
  for es: List<&2, Pp.Put>
  for +pol: Pp.Pol
  for +ls: List<&2, Pp.Link>
  for +auto: List<&2, Nat>
  for +cs: List<&2, Pp.Cell>
  for no: {Pp.any_yes(es) == False{} : Bool}
  {Pp.guarded(Pp.run(es, pol, ls, auto, cs), pol) == Pp.guarded(cs, pol) : List<&2, Pp.Cell>}

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
