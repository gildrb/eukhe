# eukhe: the laws of area sandbox

import Base
import ../bend/ffi_frames.bend as FFr
import ../bend/ffi_sandbox.bend as FSb
import ../bend/sandbox.bend as Sb
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S3) The host and the sandbox
# -----------------------------
# the model in bend/sandbox.bend. Every input is
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

# LAW cow_same_means_equal: the hand-back counts two contents of a path as the same only when
# they are equal: both absent, or the same id. The laws above that read Sb.m.eq then
# speak of real equality.
# EXCLUDES: a file one side created or removed taken as unchanged (an absent and a
#   present content counted the same), two different ids counted the same
law cow_same_means_equal:
  for +a: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for same: {Sb.m.eq(a, b) == True{} : Bool}
  {a == b : Maybe<&2, Nat>}

# LAW cow_equal_is_same: every content of a path is the same as itself
# EXCLUDES: an unchanged path counted as changed (a spurious take, removal or
#   conflict)
law cow_equal_is_same:
  for +a: Maybe<&2, Nat>
  {Sb.m.eq(a, a) == True{} : Bool}

# The laws above read the model through its helpers: list membership
# (Sb.elem), the content of a path in a workspace (Sb.read), the ids of
# frames and replies, the accepted frames (Sb.all_ok, Sb.oks) and the
# parts of a Host and a Back. The laws below pin each helper by what it
# means, over constructors, so the laws above speak of real membership,
# contents, ids and counts (a fresh blind adversary's `elem` that is
# never true made the hand-back laws vacuous and the protocol model
# accept no frame).

# LAW sandbox_elem_listed: a value listed anywhere in a list is a member of it
# EXCLUDES: a membership test that misses a listed value (no frame of an
#   allowed kind accepted, a listed path left out of the hand-back)
law sandbox_elem_listed:
  for +pre: List<&2, Nat>
  for +x: Nat
  for +post: List<&2, Nat>
  {Sb.elem(List.append(&2, Nat, pre, x <> post), x) == True{} : Bool}

# LAW sandbox_elem_only_listed: a value is a member of a list only where the list lists it
# EXCLUDES: a membership test that finds a value the list does not hold
law sandbox_elem_only_listed:
  for +xs: List<&2, Nat>
  for +x: Nat
  for h: {Sb.elem(xs, x) == True{} : Bool}
  exs pre: List<&2, Nat>
  exs post: List<&2, Nat>
  {xs == List.append(&2, Nat, pre, x <> post) : List<&2, Nat>}

# LAW sandbox_read_empty: an empty workspace has no file at any path
# EXCLUDES: a content read out of nothing
law sandbox_read_empty:
  for +p: Nat
  {Sb.read(Nil{}, p) == None{} : Maybe<&2, Nat>}

# LAW sandbox_read_first: a workspace whose first file is at path p has that file's content at p
# EXCLUDES: a read that misses a file, or answers another content
law sandbox_read_first:
  for +p: Nat
  for +b: Nat
  for +rest: List<&2, Sb.Doc>
  {Sb.read(Sb.Doc{p, b} <> rest, p) == Some{b} : Maybe<&2, Nat>}

# LAW sandbox_read_skips: a file at another path does not change what a path reads
# EXCLUDES: a read that answers the first file whatever its path
law sandbox_read_skips:
  for +q: Nat
  for +b: Nat
  for +rest: List<&2, Sb.Doc>
  for +p: Nat
  for other: {Nat.is_eq(q, p) == False{} : Bool}
  {Sb.read(Sb.Doc{q, b} <> rest, p) == Sb.read(rest, p) : Maybe<&2, Nat>}

# LAW sandbox_back_parts: a hand-back's workspace and conflicts are the ones it was built with
# EXCLUDES: a hand-back read as another workspace or no conflicts
law sandbox_back_parts:
  for +w: List<&2, Sb.Doc>
  for +c: List<&2, Nat>
  {Sb.Back.ws(Sb.Back{w, c}) == w : List<&2, Sb.Doc>} & {Sb.Back.clashes(Sb.Back{w, c}) == c : List<&2, Nat>}

# LAW proto_frame_ids: the ids of frames are each frame's id, in order: the ids of two lists
# joined are their ids joined, and a frame's id is its own
# EXCLUDES: ids dropped, invented, reordered or read from another field
law proto_frame_ids:
  for +a: List<&2, Sb.Frame>
  for +b: List<&2, Sb.Frame>
  for +i: Nat
  for +l: Nat
  for +k: Nat
  {Sb.frame.ids(List.append(&2, Sb.Frame, a, b)) == List.append(&2, Nat, Sb.frame.ids(a), Sb.frame.ids(b)) : List<&2, Nat>} & {Sb.frame.ids([Sb.Frame{i, l, k}]) == [i] : List<&2, Nat>}

# LAW proto_reply_ids: the ids of replies are each reply's id, an Ok's or an Err's, in order
# EXCLUDES: ids dropped, invented or reordered, an Err's id lost
law proto_reply_ids:
  for +a: List<&2, Sb.Reply>
  for +b: List<&2, Sb.Reply>
  for +i: Nat
  {Sb.reply.ids(List.append(&2, Sb.Reply, a, b)) == List.append(&2, Nat, Sb.reply.ids(a), Sb.reply.ids(b)) : List<&2, Nat>} & ({Sb.reply.ids([Sb.Ok{i}]) == [i] : List<&2, Nat>} & {Sb.reply.ids([Sb.Err{i}]) == [i] : List<&2, Nat>})

# LAW proto_all_ok_each: every frame of a list that is all accepted is accepted
# EXCLUDES: a refused frame counted as accepted (a host that runs it passes
#   proto_runs_only_accepted)
law proto_all_ok_each:
  for +pre: List<&2, Sb.Frame>
  for +f: Sb.Frame
  for +post: List<&2, Sb.Frame>
  for +max: Nat
  for +allowed: List<&2, Nat>
  for h: {Sb.all_ok(List.append(&2, Sb.Frame, pre, f <> post), max, allowed) == True{} : Bool}
  {Sb.accepts(max, allowed, f) == True{} : Bool}

# LAW proto_all_ok_when: a list that is not all accepted holds a refused frame
# EXCLUDES: a list of accepted frames (or none) counted as not all accepted
law proto_all_ok_when:
  for +fs: List<&2, Sb.Frame>
  for +max: Nat
  for +allowed: List<&2, Nat>
  for h: {Sb.all_ok(fs, max, allowed) == False{} : Bool}
  exs pre: List<&2, Sb.Frame>
  exs f: Sb.Frame
  exs post: List<&2, Sb.Frame>
  {fs == List.append(&2, Sb.Frame, pre, f <> post) : List<&2, Sb.Frame>} & {Sb.accepts(max, allowed, f) == False{} : Bool}

# LAW proto_oks_adds: the accepted frames of two lists joined are those of each, added
# EXCLUDES: a count that drops or doubles frames of a longer list
law proto_oks_adds:
  for +a: List<&2, Sb.Frame>
  for +b: List<&2, Sb.Frame>
  for +max: Nat
  for +allowed: List<&2, Nat>
  {Sb.oks(List.append(&2, Sb.Frame, a, b), max, allowed) == Nat.add(Sb.oks(a, max, allowed), Sb.oks(b, max, allowed)) : Nat}

# LAW proto_oks_one: one frame counts once when it is accepted, and not at all when it is refused
# EXCLUDES: a refused frame counted (a host that runs it passes
#   proto_runs_every_accepted), an accepted frame not counted
law proto_oks_one:
  for +f: Sb.Frame
  for +max: Nat
  for +allowed: List<&2, Nat>
  {Sb.oks([f], max, allowed) == Bool.pick(Nat, Sb.accepts(max, allowed, f), 1n, 0n) : Nat}

# LAW proto_host_parts: a host's replies and the frames it ran are the ones it was built with
# EXCLUDES: a host read as other replies or no frames run
law proto_host_parts:
  for +r: List<&2, Sb.Reply>
  for +x: List<&2, Sb.Frame>
  {Sb.Host.replies(Sb.Host{r, x}) == r : List<&2, Sb.Reply>} & {Sb.Host.ran(Sb.Host{r, x}) == x : List<&2, Sb.Frame>}

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

# ---- the hand-back entry: spelled requests (bend/ffi_sandbox.bend, id 17) ----
#
# LAWS: the plan the Rust hand-back asks for each path
# (crates/eukhe-core/src/child_workspace/merge.rs `plan`), on requests
# spelled from the primitives of bend/wire.bend (not the entry's own
# codecs), read by the laws' own reader, answered from the laws' own rule.
#
# C1: two contents are the same exactly when both are absent, or both are
#     present with the same id (the equality every cow law above reads:
#     cow_same_means_equal, cow_equal_is_same).
# C2: on every input that is exactly one request (the parent's, the
#     base's and the child's content, each 0 (no file) or 1 then its id,
#     nothing after) the entry answers the copy-on-write plan (CowPlan's
#     rule over C1's equality): its tag (Keep 0, then T|F taken; Clash 1;
#     Take 2; Drop 3) (cow_ffi_answers); on any other input exactly the
#     error form naming the first part that does not read: "sandbox: bad
#     parent content", "sandbox: bad base content", "sandbox: bad child
#     content", or "sandbox: input left over" (a whole request with more
#     after it) (the cow_entry_* laws of the section below).

# the same content: both absent, or both present with the same id
def cow_same_spec(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case None{} Some{y}:
      False{}
    case Some{x} None{}:
      False{}
    case Some{x} Some{y}:
      Nat.is_eq(x, y)

# the plan of a path: CowPlan's rule over the same content of C1
def cow_plan_spec(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> Sb.Plan:
  CowPlan.go(cow_same_spec(c, b), cow_same_spec(p, b), cow_same_spec(p, c), c)

# a content as Rust writes it: 0 no file, 1 then its id
def cow_spell_doc(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

# the request Rust writes: the parent's, the base's, the child's content
def cow_spell_req(p: Maybe<&2, Nat>, b: Maybe<&2, Nat>, c: Maybe<&2, Nat>, rest: String) -> String:
  cow_spell_doc(p, cow_spell_doc(b, cow_spell_doc(c, rest)))

# the reply Rust reads: the plan's tag, then Keep's taken
def cow_spell_plan(x: Sb.Plan) -> String:
  match x:
    case Sb.Keep{t}:
      Wr.put_nat(0n, Wr.put_bool(t, ""))
    case Sb.Clash{}:
      Wr.put_nat(1n, "")
    case Sb.Take{}:
      Wr.put_nat(2n, "")
    case Sb.Drop{}:
      Wr.put_nat(3n, "")

# every id of the request fits the wire
def cow_req_fits(p: Maybe<&2, Nat>, b: Maybe<&2, Nat>, c: Maybe<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_mfits(p), Bool.and(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c)))

# the error form with text t
def cow_err(t: String) -> String:
  SCon{'E', SCon{' ', t}}

# The laws' reader: a content, from the decode of its tag

def cow_read_doc.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Some{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cow_read_doc.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      cow_read_doc.some(Wr.get_nat(s))
    case 2n+q:
      Wr.Bad{}

def cow_read_doc(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      cow_read_doc.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# LAW cow_ffi_answers (C2): every request Rust writes (every id within the wire) gets the plan of its path
# EXCLUDES: a request Rust writes refused or misread
law cow_ffi_answers:
  for +p: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for +c: Maybe<&2, Nat>
  for fits: {cow_req_fits(p, b, c) == True{} : Bool}
  {FSb.ffi(cow_spell_req(p, b, c, "")) == cow_spell_plan(cow_plan_spec(p, b, c)) : String}

# LAW cow_ffi_example (C2): anchor: the strings Rust sends and the plans: only the child changed the file; only the child removed it; both changed it alike; both changed it differently; no side changed it; and one malformed input per error text
# EXCLUDES: another spelling of a request or a plan
law cow_ffi_example:
  {[FSb.ffi("1,5,1,5,1,6,"), FSb.ffi("1,5,1,5,0,"), FSb.ffi("1,6,1,4,1,6,"), FSb.ffi("1,5,1,4,1,6,"), FSb.ffi("0,0,0,")] == ["2,", "3,", "0,T", "1,", "0,F"] : List<&2, String>} &
  {[FSb.ffi(""), FSb.ffi("2,"), FSb.ffi("0,1,x"), FSb.ffi("0,0,3,"), FSb.ffi("0,0,0,x")] == [cow_err("sandbox: bad parent content"), cow_err("sandbox: bad parent content"), cow_err("sandbox: bad base content"), cow_err("sandbox: bad child content"), cow_err("sandbox: input left over")] : List<&2, String>}

# LAW cow_req_fits_example: witness: requests with and without files fit the wire (cow_ffi_answers is not vacuous)
law cow_req_fits_example:
  {[cow_req_fits(Some{5n}, None{}, Some{6n}), cow_req_fits(None{}, None{}, None{})] == [True{}, True{}] : List<&2, Bool>}

# The hand-back entry, spelled
# ----------------------------
# R1: every request Rust writes (crates/eukhe-core/src/child_workspace/
#     merge.rs `ask`: the parent's, the base's and the child's content,
#     each 0 for no file or 1 then its id; every id within the wire) gets
#     the plan of the path (Sb.plan, which cow_plan pins) spelled as Rust
#     reads it: the tag Keep 0 (then taken, T or F), Clash 1, Take 2,
#     Drop 3.
# R2: any other input answers exactly the error form naming the first
#     field that is not a content ("sandbox: bad parent content", "bad
#     base content", "bad child content"), or "sandbox: input left over"
#     when more input follows the three contents.
# The spellers and the reader (cow_spell_doc, cow_spell_req, cow_spell_plan,
# cow_read_doc, shared with the section above) are built from the wire
# primitives of bend/wire.bend only, never from the entry's put_*/get_*.

# the plan of the path, spelled
def cow_spell_answer(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> String:
  cow_spell_plan(Sb.plan(p, b, c))

# LAW cow_entry_answers_spelled: every request Rust writes (every id within the wire) gets the spelled plan of the path
# EXCLUDES: a request Rust writes refused or misread, a plan spelled
#   another way than Rust reads it
law cow_entry_answers_spelled:
  for +p: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for +c: Maybe<&2, Nat>
  for hp: {LawsBase.wire_mfits(p) == True{} : Bool}
  for hb: {LawsBase.wire_mfits(b) == True{} : Bool}
  for hc: {LawsBase.wire_mfits(c) == True{} : Bool}
  {FSb.ffi(cow_spell_req(p, b, c, "")) == cow_spell_answer(p, b, c) : String}

# LAW cow_entry_left_over: a request Rust writes followed by more input gets exactly "sandbox: input left over"
# EXCLUDES: trailing bytes ignored, or read as part of the request
law cow_entry_left_over:
  for +p: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for +c: Maybe<&2, Nat>
  for hp: {LawsBase.wire_mfits(p) == True{} : Bool}
  for hb: {LawsBase.wire_mfits(b) == True{} : Bool}
  for hc: {LawsBase.wire_mfits(c) == True{} : Bool}
  for +more: String
  for some: {String.is_empty(more) == False{} : Bool}
  {FSb.ffi(cow_spell_req(p, b, c, more)) == Wr.err("sandbox: input left over") : String}

# LAW cow_entry_malformed_unless_parent: every answer but "sandbox: bad parent content" comes from input that begins with a spelled content (0 no file, or 1 then an id within the wire)
# EXCLUDES: a malformed parent content (a tag past 1, a leading zero, an id
#   past the wire, a cut field, no input) read as a content or answered with
#   a plan, the base's, the child's or the left-over error
law cow_entry_malformed_unless_parent:
  for +s: String
  for other: {String.eq(FSb.ffi(s), Wr.err("sandbox: bad parent content")) == False{} : Bool}
  exs m: Maybe<&2, Nat>
  exs rest: String
  {s == cow_spell_doc(m, rest) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}

# LAW cow_entry_malformed_unless_base: after a spelled parent content that fits, every answer but "sandbox: bad base content" comes from input that goes on with a spelled content
# EXCLUDES: a malformed base content read as a content or answered with a
#   plan, the parent's, the child's or the left-over error
law cow_entry_malformed_unless_base:
  for +p: Maybe<&2, Nat>
  for hp: {LawsBase.wire_mfits(p) == True{} : Bool}
  for +t: String
  for other: {String.eq(FSb.ffi(cow_spell_doc(p, t)), Wr.err("sandbox: bad base content")) == False{} : Bool}
  exs m: Maybe<&2, Nat>
  exs rest: String
  {t == cow_spell_doc(m, rest) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}

# LAW cow_entry_malformed_unless_child: after spelled parent and base contents that fit, every answer but "sandbox: bad child content" comes from input that goes on with a spelled content
# EXCLUDES: a malformed child content read as a content or answered with a
#   plan, the parent's, the base's or the left-over error
law cow_entry_malformed_unless_child:
  for +p: Maybe<&2, Nat>
  for hp: {LawsBase.wire_mfits(p) == True{} : Bool}
  for +b: Maybe<&2, Nat>
  for hb: {LawsBase.wire_mfits(b) == True{} : Bool}
  for +t: String
  for other: {String.eq(FSb.ffi(cow_spell_doc(p, cow_spell_doc(b, t))), Wr.err("sandbox: bad child content")) == False{} : Bool}
  exs m: Maybe<&2, Nat>
  exs rest: String
  {t == cow_spell_doc(m, rest) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}

# LAW cow_entry_malformed_unless_request: every answer but the three field errors ("sandbox: bad parent content", "bad base content", "bad child content") answers an input that begins with a request Rust writes: three contents, every id within the wire, then any rest
# EXCLUDES: a malformed content read and answered (a tag past 1, a leading
#   zero, an id past the wire, a cut field) with a plan or the left-over
#   error, instead of the error naming its field
law cow_entry_malformed_unless_request:
  for +s: String
  for np: {String.eq(FSb.ffi(s), Wr.err("sandbox: bad parent content")) == False{} : Bool}
  for nb: {String.eq(FSb.ffi(s), Wr.err("sandbox: bad base content")) == False{} : Bool}
  for nc: {String.eq(FSb.ffi(s), Wr.err("sandbox: bad child content")) == False{} : Bool}
  exs p: Maybe<&2, Nat>
  exs b: Maybe<&2, Nat>
  exs c: Maybe<&2, Nat>
  exs rest: String
  {(s, Bool.and(LawsBase.wire_mfits(p), Bool.and(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c)))) == (cow_spell_req(p, b, c, rest), True{}) : String & Bool}

# LAW cow_entry_tags_example: anchor: the bytes Rust sends and reads: no file anywhere (keep);
# both changed the path alike (keep, taken); only the child changed it, to a file (take) or by
# removing it (drop); both changed it differently (clash); then no input, a content tag 2, a cut
# base, a child tag 2 and left-over input
# EXCLUDES: another spelling of a request or a plan, a swapped plan tag or
#   taken flag, an unknown content tag read as a content, two error texts
#   swapped
law cow_entry_tags_example:
  {[FSb.ffi("0,0,0,"), FSb.ffi("1,0,1,1,1,0,"), FSb.ffi("1,0,1,0,1,2,"), FSb.ffi("1,0,1,0,0,"), FSb.ffi("1,0,1,1,1,2,"), FSb.ffi(""), FSb.ffi("2,0,0,"), FSb.ffi("0,1,"), FSb.ffi("0,0,2,"), FSb.ffi("0,0,0,0,")] == ["0,F", "0,T", "2,", "3,", "1,", "E sandbox: bad parent content", "E sandbox: bad parent content", "E sandbox: bad base content", "E sandbox: bad child content", "E sandbox: input left over"] : List<&2, String>}

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

# the model's decision on q, spelled (`admit` is fixed for every input by
# frames_admit_seen, frames_admit_oversize and frames_admit_within)
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
