# eukhe: the laws of area sandbox

import Base
import ../bend/ffi_frames.bend as FFr
import ../bend/ffi_sandbox.bend as FSb
import ../bend/sandbox.bend as Sb
import ../bend/wire.bend as Wr
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

# ---- frames entry ----

# LAWS (S3, compiled core): the gate of one host-request frame of a
# kernel's stream (bend/sandbox.bend `admit`) runs as the compiled model
# (bend/ffi_frames.bend; Rust: crates/eukhe-bend/src/rules/frames.rs,
# called by crates/eukhe-core/src/kernel/manager/frames.rs `Gate::admit`
# for each host request the stream's splitter cuts). The laws pin `admit`
# to the protocol model (`accepts`) and the entry to `admit`, with spec
# spellers built only from the wire primitives of bend/wire.bend.
#
# R1: a frame whose id was seen before is refused as a duplicate; a fresh
#     frame past the limit is refused as oversized; a fresh frame within
#     it is served when its type is one the host serves, else refused (no
#     type, or a type not served); a fresh frame is served exactly when
#     the protocol model accepts it.
# R2: the entry answers that decision on every request Rust writes, and
#     exactly the error form "frames: malformed request" on any other
#     input.
# Every input is free: any limit, any length, any id freshness, any type.

# the verdict on a fresh frame within the limit, by its type
def kind_spec(k: Sb.Typed) -> Sb.Verdict:
  match k:
    case Sb.Unnamed{}:
      Sb.Kindless{}
    case Sb.Named{s}:
      match s:
        case True{}:
          Sb.Serve{}
        case False{}:
          Sb.NotServed{}

# LAW frames_admit_seen: a frame whose id was seen before is refused as a duplicate, whatever its length and type
# EXCLUDES: a repeated id served (its handler runs twice, a reply settles
#   the request in flight), a duplicate refused as another error
law frames_admit_seen:
  for +max: Nat
  for +len: Nat
  for k: Sb.Typed
  {Sb.admit(max, False{}, len, k) == Sb.Duplicate{} : Sb.Verdict}

# LAW frames_admit_oversize: a fresh frame past the limit is refused as oversized, whatever its type
# EXCLUDES: an oversized frame served or refused for its type
law frames_admit_oversize:
  for +max: Nat
  for +len: Nat
  for k: Sb.Typed
  for over: {Nat.is_lt(max, len) == True{} : Bool}
  {Sb.admit(max, True{}, len, k) == Sb.Oversize{} : Sb.Verdict}

# LAW frames_admit_within: a fresh frame within the limit is served when the host serves its type, else refused for having no type or a type the host does not serve
# EXCLUDES: a frame of an unserved type served, a served type refused, a
#   frame exactly at the limit refused, the two refusals swapped
law frames_admit_within:
  for +max: Nat
  for +len: Nat
  for +k: Sb.Typed
  for fits: {Nat.is_le(len, max) == True{} : Bool}
  {Sb.admit(max, True{}, len, k) == kind_spec(k) : Sb.Verdict}

# LAW frames_admit_serves_accepted: a fresh frame is served exactly when the protocol model accepts it (within the limit, of a kind the host allows)
# EXCLUDES: a per-frame gate that drifts from `serve`, whose laws
#   (proto_*) pin what the host runs
law frames_admit_serves_accepted:
  for +max: Nat
  for +allowed: List<&2, Nat>
  for +i: Nat
  for +len: Nat
  for +k: Nat
  {Sb.Verdict.serve(Sb.admit(max, True{}, len, Sb.Named{Sb.elem(allowed, k)})) == Sb.accepts(max, allowed, Sb.Frame{i, len, k}) : Bool}

# a verdict serves the frame: only Serve does
def serve_spec(v: Sb.Verdict) -> Bool:
  match v:
    case Sb.Serve{}:
      True{}
    case Sb.Duplicate{}:
      False{}
    case Sb.Oversize{}:
      False{}
    case Sb.Kindless{}:
      False{}
    case Sb.NotServed{}:
      False{}

# LAW frames_verdict_serve_exact: a verdict serves its frame exactly when it is Serve
# EXCLUDES: a duplicate, oversized, typeless or unserved frame read as
#   served through `Verdict.serve` (frames_admit_serves_accepted reads
#   through it; a fresh blind adversary's `serve` of Duplicate and
#   Kindless passed every other law)
law frames_verdict_serve_exact:
  for v: Sb.Verdict
  {Sb.Verdict.serve(v) == serve_spec(v) : Bool}

# Spec spellers
# -------------

def fr_spell_kind(k: Sb.Typed, rest: String) -> String:
  match k:
    case Sb.Unnamed{}:
      Wr.put_nat(0n, rest)
    case Sb.Named{s}:
      Wr.put_nat(1n, Wr.put_bool(s, rest))

# the request q as Rust writes it, then rest
def fr_spell_req(q: FFr.Req, rest: String) -> String:
  match q:
    case FFr.Req{m, f, l, k}:
      Wr.put_nat(m, Wr.put_bool(f, Wr.put_nat(l, fr_spell_kind(k, rest))))

# every number of a request fits the wire
def fr_req_fits(q: FFr.Req) -> Bool:
  match q:
    case FFr.Req{m, f, l, k}:
      Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(l))

def fr_spell_verdict(v: Sb.Verdict) -> String:
  match v:
    case Sb.Serve{}:
      Wr.put_nat(0n, "")
    case Sb.Duplicate{}:
      Wr.put_nat(1n, "")
    case Sb.Oversize{}:
      Wr.put_nat(2n, "")
    case Sb.Kindless{}:
      Wr.put_nat(3n, "")
    case Sb.NotServed{}:
      Wr.put_nat(4n, "")

# the model's decision on q, spelled
def fr_spell_answer(q: FFr.Req) -> String:
  match q:
    case FFr.Req{m, f, l, k}:
      fr_spell_verdict(Sb.admit(m, f, l, k))

def fr_malformed() -> String:
  SCon{'E', SCon{' ', "frames: malformed request"}}

# Reader: the requests, read with the wire primitives

def fr_read_named(r: Wr.Dec<Bool>) -> Wr.Dec<Sb.Typed>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{Sb.Named{b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr_read_kind.tag(t: Nat, s: String) -> Wr.Dec<Sb.Typed>:
  match t:
    case 0n:
      Wr.Got{Sb.Unnamed{}, s}
    case 1n:
      fr_read_named(Wr.get_bool(s))
    case 2n+u:
      Wr.Bad{}

def fr_read_kind(r: Wr.Dec<Nat>) -> Wr.Dec<Sb.Typed>:
  match r:
    case Wr.Got{t, s}:
      fr_read_kind.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def fr_read_req.kind(m: Nat, f: Bool, l: Nat, r: Wr.Dec<Sb.Typed>) -> Wr.Dec<FFr.Req>:
  match r:
    case Wr.Got{k, s}:
      Wr.Got{FFr.Req{m, f, l, k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def fr_read_req.len(m: Nat, f: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<FFr.Req>:
  match r:
    case Wr.Got{l, s}:
      fr_read_req.kind(m, f, l, fr_read_kind(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def fr_read_req.fresh(m: Nat, r: Wr.Dec<Bool>) -> Wr.Dec<FFr.Req>:
  match r:
    case Wr.Got{f, s}:
      fr_read_req.len(m, f, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def fr_read_req.max(r: Wr.Dec<Nat>) -> Wr.Dec<FFr.Req>:
  match r:
    case Wr.Got{m, s}:
      fr_read_req.fresh(m, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with, and what follows it
def fr_read_req(s: String) -> Wr.Dec<FFr.Req>:
  fr_read_req.max(Wr.get_nat(s))

def fr_spec.end(whole: Bool, q: FFr.Req) -> String:
  match whole:
    case True{}:
      fr_spell_answer(q)
    case False{}:
      fr_malformed()

def fr_spec.run(r: Wr.Dec<FFr.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      fr_spec.end(Wr.end(s), q)
    case Wr.Bad{}:
      fr_malformed()

# the reply to s: the model's decision on the request s is exactly, else
# the error form
def fr_spec(s: String) -> String:
  fr_spec.run(fr_read_req(s))

# LAW frames_ffi_exact: on every input the entry answers the model's verdict on the request the input is exactly, and exactly the error form "frames: malformed request" on any other input
# EXCLUDES: a verdict other than the model's, a default for malformed
#   input, a request misread, input left over ignored, another error text
law frames_ffi_exact:
  for +s: String
  {FFr.ffi(s) == fr_spec(s) : String}

# LAW frames_ffi_answers: every request Rust writes (every number within the wire) gets the model's verdict
# EXCLUDES: a request Rust writes refused or misread
law frames_ffi_answers:
  for +q: FFr.Req
  for fits: {fr_req_fits(q) == True{} : Bool}
  {FFr.ffi(fr_spell_req(q, "")) == fr_spell_answer(q) : String}

# LAW frames_ffi_left_over: a request Rust writes followed by more input gets exactly the error form
# EXCLUDES: a second request or trailing bytes read past or ignored
law frames_ffi_left_over:
  for +q: FFr.Req
  for +more: String
  for fits: {fr_req_fits(q) == True{} : Bool}
  for some: {String.is_empty(more) == False{} : Bool}
  {FFr.ffi(fr_spell_req(q, more)) == fr_malformed() : String}

# LAW frames_ffi_example: anchor: the strings Rust sends: a fresh frame at the 100-byte limit of a served type; a seen id; a frame past the limit; a fresh frame with no type; one of a type not served; a type tag 2 is refused
# EXCLUDES: another spelling of a request or a verdict
law frames_ffi_example:
  {FFr.ffi("100,T100,1,T") == "0," : String} &
  {FFr.ffi("100,F10,1,T") == "1," : String} &
  {FFr.ffi("100,T101,0,") == "2," : String} &
  {FFr.ffi("100,T10,0,") == "3," : String} &
  {FFr.ffi("100,T10,1,F") == "4," : String} &
  {FFr.ffi("100,T10,2,") == fr_malformed() : String}
