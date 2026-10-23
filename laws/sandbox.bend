# eukhe: the laws of area sandbox

import Base
import ../bend/ffi_sandbox.bend as FSb
import ../bend/sandbox.bend as Sb
import ./base.bend as LawsBase

# (S3) The host and the sandbox
# -----------------------------
# docs/runtime.md S3, the model in bend/sandbox.bend. Every input is
# free: any frames of any length and kind, any limits, any workspaces of
# the parent, the base and the child.

# LAW proto_one_reply_each: every frame gets exactly one reply, in order
law proto_one_reply_each:
  for +fs: List<&2, Sb.Frame>
  for +max: Nat
  for +allowed: List<&2, Nat>
  {Sb.reply.ids(Sb.Host.replies(Sb.serve(fs, max, allowed))) == Sb.frame.ids(fs) : List<&2, Nat>}

# LAW proto_runs_only_accepted: the host runs only frames it accepts: within the size limit and of
# an allowed kind
law proto_runs_only_accepted:
  for +fs: List<&2, Sb.Frame>
  for +max: Nat
  for +allowed: List<&2, Nat>
  {Sb.all_ok(Sb.Host.ran(Sb.serve(fs, max, allowed)), max, allowed) == True{} : Bool}

# LAW proto_runs_every_accepted: and it runs every frame it accepts
law proto_runs_every_accepted:
  for +fs: List<&2, Sb.Frame>
  for +max: Nat
  for +allowed: List<&2, Nat>
  {List.length(&2, Sb.Frame, Sb.Host.ran(Sb.serve(fs, max, allowed))) == Sb.oks(fs, max, allowed) : Nat}

# LAW proto_rejects_oversize: a frame over the size limit gets an error and runs nothing
law proto_rejects_oversize:
  for +i: Nat
  for +l: Nat
  for +k: Nat
  for +max: Nat
  for +allowed: List<&2, Nat>
  for over: {Nat.is_lt(max, l) == True{} : Bool}
  {Sb.serve([Sb.Frame{i, l, k}], max, allowed) == Sb.Host{[Sb.Err{i}], Nil{}} : Sb.Host}

# LAW cow_keeps_parent: a path the child did not change keeps the parent's content
law cow_keeps_parent:
  for +ks: List<&2, Nat>
  for +par: List<&2, Sb.Doc>
  for +base: List<&2, Sb.Doc>
  for +child: List<&2, Sb.Doc>
  for +k: Nat
  for listed: {Sb.elem(ks, k) == True{} : Bool}
  for calm: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == True{} : Bool}
  {Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k) == Sb.read(par, k) : Maybe<&2, Nat>}

# LAW cow_takes_child: a path only the child changed gets the child's content
law cow_takes_child:
  for +ks: List<&2, Nat>
  for +par: List<&2, Sb.Doc>
  for +base: List<&2, Sb.Doc>
  for +child: List<&2, Sb.Doc>
  for +k: Nat
  for listed: {Sb.elem(ks, k) == True{} : Bool}
  for moved: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == False{} : Bool}
  for still: {Sb.m.eq(Sb.read(par, k), Sb.read(base, k)) == True{} : Bool}
  {Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k) == Sb.read(child, k) : Maybe<&2, Nat>}

# LAW cow_conflict_reported: a path both changed to different contents keeps the parent's
# content and is reported as a conflict: no change is lost in silence
law cow_conflict_reported:
  for +ks: List<&2, Nat>
  for +par: List<&2, Sb.Doc>
  for +base: List<&2, Sb.Doc>
  for +child: List<&2, Sb.Doc>
  for +k: Nat
  for listed: {Sb.elem(ks, k) == True{} : Bool}
  for moved: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == False{} : Bool}
  for also: {Sb.m.eq(Sb.read(par, k), Sb.read(base, k)) == False{} : Bool}
  for apart: {Sb.m.eq(Sb.read(par, k), Sb.read(child, k)) == False{} : Bool}
  {Bool.and(Sb.m.eq(Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k), Sb.read(par, k)), Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k)) == True{} : Bool}

# LAW cow_conflict_is_real: a conflict is real: both changed the path, to different contents
law cow_conflict_is_real:
  for +ks: List<&2, Nat>
  for +par: List<&2, Sb.Doc>
  for +base: List<&2, Sb.Doc>
  for +child: List<&2, Sb.Doc>
  for +k: Nat
  for clash: {Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k) == True{} : Bool}
  {Bool.or(Bool.or(Sb.m.eq(Sb.read(child, k), Sb.read(base, k)), Sb.m.eq(Sb.read(par, k), Sb.read(base, k))), Sb.m.eq(Sb.read(par, k), Sb.read(child, k))) == False{} : Bool}

# The plan of one path the Rust hand-back runs (bend/sandbox.bend
# `plan`): the parent's content stays (taken: both made the same change),
# a conflict, the child's file goes in, or the child's removal does.

def CowPlan.go(calm: Bool, still: Bool, same: Bool, c: Maybe<&2, Nat>) -> Sb.Plan:
  match calm:
    case True{}:
      Sb.Keep{False{}}
    case False{}:
      match still:
        case True{}:
          match c:
            case None{}:
              Sb.Drop{}
            case Some{x}:
              Sb.Take{}
        case False{}:
          match same:
            case True{}:
              Sb.Keep{True{}}
            case False{}:
              Sb.Clash{}

# the child did not change the path: keep; only the child changed it:
# its file (or its removal) goes in; both changed it alike: keep, taken;
# both changed it differently: a conflict
def CowPlan(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> Sb.Plan:
  CowPlan.go(Sb.m.eq(c, b), Sb.m.eq(p, b), Sb.m.eq(p, c), c)

# LAW cow_plan: the plan of a path is the copy-on-write rule
# EXCLUDES: a lost change of either side, a conflict reported as taken, a
# removal written as a file
law cow_plan:
  for +p: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for +c: Maybe<&2, Nat>
  {Sb.plan(p, b, c) == CowPlan(p, b, c) : Sb.Plan}

# LAW cow_plan_is_merge: the plan carries out the merge of the path, so the hand-back laws
# above hold for the Rust hand-back
law cow_plan_is_merge:
  for +p: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for +c: Maybe<&2, Nat>
  {Sb.Plan.merge(Sb.plan(p, b, c), p, c) == Sb.merge1(p, b, c) : Sb.One}

# ---- core_w6 ----

# LAWS: the entries of the compiled Bend core for the child task, the jobs,
# the goal's progress check and the hand-back (bend/ffi_child.bend,
# bend/ffi_job.bend, bend/ffi_progress.bend, bend/ffi_sandbox.bend). Each
# entry, on the request Rust writes (`put_req`, every number within the
# wire), answers the encoding of the model's decision: the codec loses,
# invents and reorders nothing, and the Rust rule is the proven model.

# LAW cow_entry: the sandbox entry answers the plan of the path
law cow_entry:
  for +p: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for +c: Maybe<&2, Nat>
  for hp: {LawsBase.wire_mfits(p) == True{} : Bool}
  for hb: {LawsBase.wire_mfits(b) == True{} : Bool}
  for hc: {LawsBase.wire_mfits(c) == True{} : Bool}
  {FSb.ffi(FSb.put_req(p, b, c)) == FSb.put_plan(Sb.plan(p, b, c), "") : String}
