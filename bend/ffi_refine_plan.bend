# ffi_refine_plan: the entry of the compiled Bend core for the /refine
# planner (bend/refine_plan.bend; Rust: eukhe-bend rules/refine_plan.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   verb     0 create | 1 update | 2 delete
#   comp     0 prompt | 1 memory | 2 skill | 3 subagent | 4 factory
#   val      0 missing | 1 null | 2 object | 3 other
#   pyref    type, import, python_import, callable, call_pattern (each a
#            Maybe<String>)
#   args     dag, machine (each a val)
#   ed       action (Maybe<verb>), kind (Maybe<comp>), id, title (each a
#            Maybe<String>), has content (Bool), reference (Maybe<pyref>),
#            arguments (Maybe<args>), stored, changed since the baseline,
#            held by the session's memory (each a Bool)
#   opts     factory enabled, baseline given (each a Bool)
#   was      applied, has before, has after (each a Bool)
#   win      context window, max tokens, output reserve, system prompt
#            length (each a Nat)
#   search   0 full | 1 probe: low, high, length (Nats) | 2 final
#   request  a question, its tag then its fields:
#            0 ids: List<ed>              reply: List<Maybe<String>>
#            1 plan: opts, List<ed>       reply: plan
#            2 back: the result id, List<was>
#                                         reply: back
#            3 norm: summary, rationale, expected outcome (each a
#              Maybe<String>)             reply: texts
#            4 scan: the text             reply: Bool
#            5 fit: win, the conversation length, search, the prompt
#              length                     reply: step
#   out      0 invalid: the message | 1 refused: the message | 2 removed |
#            3 written
#   row      verb, comp, id (String), out
#   plan     List<row>, the change lines (List<String>)
#   pick     the row's index (Nat), verb
#   back     summary, rationale, expected outcome, reason (each a
#            String), List<pick>
#   texts    summary, rationale, expected outcome (each a String)
#   step     0 try: the length, search | 1 ok: the max tokens | 2 no
#            room: the text
#
# Malformed input, or input left after the request, answers
# `E refine_plan: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./refine_plan.bend as Rp

# A request of the entry
type Req is Data:
  QIds{eds: List<&2, Rp.Ed>}
  QPlan{opts: Rp.Opts, eds: List<&2, Rp.Ed>}
  QBack{id: String, was: List<&2, Rp.Was>}
  QNorm{summary: Maybe<&2, String>, rationale: Maybe<&2, String>, outcome: Maybe<&2, String>}
  QScan{text: String}
  QFit{win: Rp.Win, conv: Nat, search: Rp.Search, plen: Nat}

# Requests
# --------

def get_verb.tag(t: Nat, s: String) -> W.Dec<Rp.Verb>:
  match t:
    case 0n:
      W.Got{Rp.ACreate{}, s}
    case 1n:
      W.Got{Rp.AUpdate{}, s}
    case 2n:
      W.Got{Rp.ADelete{}, s}
    case 3n+u:
      W.Bad{}

def get_verb.start(r: W.Dec<Nat>) -> W.Dec<Rp.Verb>:
  match r:
    case W.Got{t, s}:
      get_verb.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_verb(s: String) -> W.Dec<Rp.Verb>:
  get_verb.start(W.get_nat(s))

def get_comp.tag(t: Nat, s: String) -> W.Dec<Rp.Comp>:
  match t:
    case 0n:
      W.Got{Rp.KPrompt{}, s}
    case 1n:
      W.Got{Rp.KMemory{}, s}
    case 2n:
      W.Got{Rp.KSkill{}, s}
    case 3n:
      W.Got{Rp.KSubagent{}, s}
    case 4n:
      W.Got{Rp.KFactory{}, s}
    case 5n+u:
      W.Bad{}

def get_comp.start(r: W.Dec<Nat>) -> W.Dec<Rp.Comp>:
  match r:
    case W.Got{t, s}:
      get_comp.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_comp(s: String) -> W.Dec<Rp.Comp>:
  get_comp.start(W.get_nat(s))

def get_val.tag(t: Nat, s: String) -> W.Dec<Rp.Val>:
  match t:
    case 0n:
      W.Got{Rp.VMissing{}, s}
    case 1n:
      W.Got{Rp.VNull{}, s}
    case 2n:
      W.Got{Rp.VObject{}, s}
    case 3n:
      W.Got{Rp.VOther{}, s}
    case 4n+u:
      W.Bad{}

def get_val.start(r: W.Dec<Nat>) -> W.Dec<Rp.Val>:
  match r:
    case W.Got{t, s}:
      get_val.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_val(s: String) -> W.Dec<Rp.Val>:
  get_val.start(W.get_nat(s))

def get_ms.some(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ms.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_ms.some(W.get_str(s))
    case 2n+u:
      W.Bad{}

def get_ms.start(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      get_ms.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_ms(s: String) -> W.Dec<Maybe<&2, String>>:
  get_ms.start(W.get_nat(s))

def get_pyref.f5(v1: Maybe<&2, String>, v2: Maybe<&2, String>, v3: Maybe<&2, String>, v4: Maybe<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Rp.Pyref>:
  match r:
    case W.Got{v5, s}:
      W.Got{Rp.Pyref{v1, v2, v3, v4, v5}, s}
    case W.Bad{}:
      W.Bad{}

def get_pyref.f4(v1: Maybe<&2, String>, v2: Maybe<&2, String>, v3: Maybe<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Rp.Pyref>:
  match r:
    case W.Got{v4, s}:
      get_pyref.f5(v1, v2, v3, v4, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_pyref.f3(v1: Maybe<&2, String>, v2: Maybe<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Rp.Pyref>:
  match r:
    case W.Got{v3, s}:
      get_pyref.f4(v1, v2, v3, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_pyref.f2(v1: Maybe<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Rp.Pyref>:
  match r:
    case W.Got{v2, s}:
      get_pyref.f3(v1, v2, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_pyref.f1(r: W.Dec<Maybe<&2, String>>) -> W.Dec<Rp.Pyref>:
  match r:
    case W.Got{v1, s}:
      get_pyref.f2(v1, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_pyref(s: String) -> W.Dec<Rp.Pyref>:
  get_pyref.f1(get_ms(s))

def get_args.f2(v1: Rp.Val, r: W.Dec<Rp.Val>) -> W.Dec<Rp.Args>:
  match r:
    case W.Got{v2, s}:
      W.Got{Rp.Args{v1, v2}, s}
    case W.Bad{}:
      W.Bad{}

def get_args.f1(r: W.Dec<Rp.Val>) -> W.Dec<Rp.Args>:
  match r:
    case W.Got{v1, s}:
      get_args.f2(v1, get_val(s))
    case W.Bad{}:
      W.Bad{}

def get_args(s: String) -> W.Dec<Rp.Args>:
  get_args.f1(get_val(s))

def get_mverb.some(r: W.Dec<Rp.Verb>) -> W.Dec<Maybe<&2, Rp.Verb>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mverb.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Rp.Verb>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mverb.some(get_verb(s))
    case 2n+u:
      W.Bad{}

def get_mverb.start(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Rp.Verb>>:
  match r:
    case W.Got{t, s}:
      get_mverb.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_mverb(s: String) -> W.Dec<Maybe<&2, Rp.Verb>>:
  get_mverb.start(W.get_nat(s))

def get_mcomp.some(r: W.Dec<Rp.Comp>) -> W.Dec<Maybe<&2, Rp.Comp>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mcomp.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Rp.Comp>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mcomp.some(get_comp(s))
    case 2n+u:
      W.Bad{}

def get_mcomp.start(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Rp.Comp>>:
  match r:
    case W.Got{t, s}:
      get_mcomp.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_mcomp(s: String) -> W.Dec<Maybe<&2, Rp.Comp>>:
  get_mcomp.start(W.get_nat(s))

def get_mpyref.some(r: W.Dec<Rp.Pyref>) -> W.Dec<Maybe<&2, Rp.Pyref>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mpyref.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Rp.Pyref>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mpyref.some(get_pyref(s))
    case 2n+u:
      W.Bad{}

def get_mpyref.start(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Rp.Pyref>>:
  match r:
    case W.Got{t, s}:
      get_mpyref.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_mpyref(s: String) -> W.Dec<Maybe<&2, Rp.Pyref>>:
  get_mpyref.start(W.get_nat(s))

def get_margs.some(r: W.Dec<Rp.Args>) -> W.Dec<Maybe<&2, Rp.Args>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_margs.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Rp.Args>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_margs.some(get_args(s))
    case 2n+u:
      W.Bad{}

def get_margs.start(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Rp.Args>>:
  match r:
    case W.Got{t, s}:
      get_margs.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_margs(s: String) -> W.Dec<Maybe<&2, Rp.Args>>:
  get_margs.start(W.get_nat(s))

def get_ed.f10(v1: Maybe<&2, Rp.Verb>, v2: Maybe<&2, Rp.Comp>, v3: Maybe<&2, String>, v4: Maybe<&2, String>, v5: Bool, v6: Maybe<&2, Rp.Pyref>, v7: Maybe<&2, Rp.Args>, v8: Bool, v9: Bool, r: W.Dec<Bool>) -> W.Dec<Rp.Ed>:
  match r:
    case W.Got{v10, s}:
      W.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, s}
    case W.Bad{}:
      W.Bad{}

def get_ed.f9(v1: Maybe<&2, Rp.Verb>, v2: Maybe<&2, Rp.Comp>, v3: Maybe<&2, String>, v4: Maybe<&2, String>, v5: Bool, v6: Maybe<&2, Rp.Pyref>, v7: Maybe<&2, Rp.Args>, v8: Bool, r: W.Dec<Bool>) -> W.Dec<Rp.Ed>:
  match r:
    case W.Got{v9, s}:
      get_ed.f10(v1, v2, v3, v4, v5, v6, v7, v8, v9, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ed.f8(v1: Maybe<&2, Rp.Verb>, v2: Maybe<&2, Rp.Comp>, v3: Maybe<&2, String>, v4: Maybe<&2, String>, v5: Bool, v6: Maybe<&2, Rp.Pyref>, v7: Maybe<&2, Rp.Args>, r: W.Dec<Bool>) -> W.Dec<Rp.Ed>:
  match r:
    case W.Got{v8, s}:
      get_ed.f9(v1, v2, v3, v4, v5, v6, v7, v8, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ed.f7(v1: Maybe<&2, Rp.Verb>, v2: Maybe<&2, Rp.Comp>, v3: Maybe<&2, String>, v4: Maybe<&2, String>, v5: Bool, v6: Maybe<&2, Rp.Pyref>, r: W.Dec<Maybe<&2, Rp.Args>>) -> W.Dec<Rp.Ed>:
  match r:
    case W.Got{v7, s}:
      get_ed.f8(v1, v2, v3, v4, v5, v6, v7, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ed.f6(v1: Maybe<&2, Rp.Verb>, v2: Maybe<&2, Rp.Comp>, v3: Maybe<&2, String>, v4: Maybe<&2, String>, v5: Bool, r: W.Dec<Maybe<&2, Rp.Pyref>>) -> W.Dec<Rp.Ed>:
  match r:
    case W.Got{v6, s}:
      get_ed.f7(v1, v2, v3, v4, v5, v6, get_margs(s))
    case W.Bad{}:
      W.Bad{}

def get_ed.f5(v1: Maybe<&2, Rp.Verb>, v2: Maybe<&2, Rp.Comp>, v3: Maybe<&2, String>, v4: Maybe<&2, String>, r: W.Dec<Bool>) -> W.Dec<Rp.Ed>:
  match r:
    case W.Got{v5, s}:
      get_ed.f6(v1, v2, v3, v4, v5, get_mpyref(s))
    case W.Bad{}:
      W.Bad{}

def get_ed.f4(v1: Maybe<&2, Rp.Verb>, v2: Maybe<&2, Rp.Comp>, v3: Maybe<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Rp.Ed>:
  match r:
    case W.Got{v4, s}:
      get_ed.f5(v1, v2, v3, v4, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ed.f3(v1: Maybe<&2, Rp.Verb>, v2: Maybe<&2, Rp.Comp>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Rp.Ed>:
  match r:
    case W.Got{v3, s}:
      get_ed.f4(v1, v2, v3, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_ed.f2(v1: Maybe<&2, Rp.Verb>, r: W.Dec<Maybe<&2, Rp.Comp>>) -> W.Dec<Rp.Ed>:
  match r:
    case W.Got{v2, s}:
      get_ed.f3(v1, v2, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_ed.f1(r: W.Dec<Maybe<&2, Rp.Verb>>) -> W.Dec<Rp.Ed>:
  match r:
    case W.Got{v1, s}:
      get_ed.f2(v1, get_mcomp(s))
    case W.Bad{}:
      W.Bad{}

def get_ed(s: String) -> W.Dec<Rp.Ed>:
  get_ed.f1(get_mverb(s))

def get_eds(s: String) -> W.Dec<List<&2, Rp.Ed>>:
  W.get_list(~Rp.Ed, ~get_ed, s)

def get_opts.f2(v1: Bool, r: W.Dec<Bool>) -> W.Dec<Rp.Opts>:
  match r:
    case W.Got{v2, s}:
      W.Got{Rp.Opts{v1, v2}, s}
    case W.Bad{}:
      W.Bad{}

def get_opts.f1(r: W.Dec<Bool>) -> W.Dec<Rp.Opts>:
  match r:
    case W.Got{v1, s}:
      get_opts.f2(v1, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_opts(s: String) -> W.Dec<Rp.Opts>:
  get_opts.f1(W.get_bool(s))

def get_was.f3(v1: Bool, v2: Bool, r: W.Dec<Bool>) -> W.Dec<Rp.Was>:
  match r:
    case W.Got{v3, s}:
      W.Got{Rp.Was{v1, v2, v3}, s}
    case W.Bad{}:
      W.Bad{}

def get_was.f2(v1: Bool, r: W.Dec<Bool>) -> W.Dec<Rp.Was>:
  match r:
    case W.Got{v2, s}:
      get_was.f3(v1, v2, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_was.f1(r: W.Dec<Bool>) -> W.Dec<Rp.Was>:
  match r:
    case W.Got{v1, s}:
      get_was.f2(v1, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_was(s: String) -> W.Dec<Rp.Was>:
  get_was.f1(W.get_bool(s))

def get_wl(s: String) -> W.Dec<List<&2, Rp.Was>>:
  W.get_list(~Rp.Was, ~get_was, s)

def get_win.f4(v1: Nat, v2: Nat, v3: Nat, r: W.Dec<Nat>) -> W.Dec<Rp.Win>:
  match r:
    case W.Got{v4, s}:
      W.Got{Rp.Win{v1, v2, v3, v4}, s}
    case W.Bad{}:
      W.Bad{}

def get_win.f3(v1: Nat, v2: Nat, r: W.Dec<Nat>) -> W.Dec<Rp.Win>:
  match r:
    case W.Got{v3, s}:
      get_win.f4(v1, v2, v3, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_win.f2(v1: Nat, r: W.Dec<Nat>) -> W.Dec<Rp.Win>:
  match r:
    case W.Got{v2, s}:
      get_win.f3(v1, v2, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_win.f1(r: W.Dec<Nat>) -> W.Dec<Rp.Win>:
  match r:
    case W.Got{v1, s}:
      get_win.f2(v1, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_win(s: String) -> W.Dec<Rp.Win>:
  get_win.f1(W.get_nat(s))

def get_search.sprobe.f3(v1: Nat, v2: Nat, r: W.Dec<Nat>) -> W.Dec<Rp.Search>:
  match r:
    case W.Got{v3, s}:
      W.Got{Rp.SProbe{v1, v2, v3}, s}
    case W.Bad{}:
      W.Bad{}

def get_search.sprobe.f2(v1: Nat, r: W.Dec<Nat>) -> W.Dec<Rp.Search>:
  match r:
    case W.Got{v2, s}:
      get_search.sprobe.f3(v1, v2, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_search.sprobe.f1(r: W.Dec<Nat>) -> W.Dec<Rp.Search>:
  match r:
    case W.Got{v1, s}:
      get_search.sprobe.f2(v1, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_search.tag(t: Nat, s: String) -> W.Dec<Rp.Search>:
  match t:
    case 0n:
      W.Got{Rp.SFull{}, s}
    case 1n:
      get_search.sprobe.f1(W.get_nat(s))
    case 2n:
      W.Got{Rp.SFinal{}, s}
    case 3n+u:
      W.Bad{}

def get_search.start(r: W.Dec<Nat>) -> W.Dec<Rp.Search>:
  match r:
    case W.Got{t, s}:
      get_search.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_search(s: String) -> W.Dec<Rp.Search>:
  get_search.start(W.get_nat(s))

def get_req.qids.f1(r: W.Dec<List<&2, Rp.Ed>>) -> W.Dec<Req>:
  match r:
    case W.Got{v1, s}:
      W.Got{QIds{v1}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.qplan.f2(v1: Rp.Opts, r: W.Dec<List<&2, Rp.Ed>>) -> W.Dec<Req>:
  match r:
    case W.Got{v2, s}:
      W.Got{QPlan{v1, v2}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.qplan.f1(r: W.Dec<Rp.Opts>) -> W.Dec<Req>:
  match r:
    case W.Got{v1, s}:
      get_req.qplan.f2(v1, get_eds(s))
    case W.Bad{}:
      W.Bad{}

def get_req.qback.f2(v1: String, r: W.Dec<List<&2, Rp.Was>>) -> W.Dec<Req>:
  match r:
    case W.Got{v2, s}:
      W.Got{QBack{v1, v2}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.qback.f1(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{v1, s}:
      get_req.qback.f2(v1, get_wl(s))
    case W.Bad{}:
      W.Bad{}

def get_req.qnorm.f3(v1: Maybe<&2, String>, v2: Maybe<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{v3, s}:
      W.Got{QNorm{v1, v2, v3}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.qnorm.f2(v1: Maybe<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{v2, s}:
      get_req.qnorm.f3(v1, v2, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_req.qnorm.f1(r: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{v1, s}:
      get_req.qnorm.f2(v1, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_req.qscan.f1(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{v1, s}:
      W.Got{QScan{v1}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.qfit.f4(v1: Rp.Win, v2: Nat, v3: Rp.Search, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{v4, s}:
      W.Got{QFit{v1, v2, v3, v4}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.qfit.f3(v1: Rp.Win, v2: Nat, r: W.Dec<Rp.Search>) -> W.Dec<Req>:
  match r:
    case W.Got{v3, s}:
      get_req.qfit.f4(v1, v2, v3, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.qfit.f2(v1: Rp.Win, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{v2, s}:
      get_req.qfit.f3(v1, v2, get_search(s))
    case W.Bad{}:
      W.Bad{}

def get_req.qfit.f1(r: W.Dec<Rp.Win>) -> W.Dec<Req>:
  match r:
    case W.Got{v1, s}:
      get_req.qfit.f2(v1, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_req.qids.f1(get_eds(s))
    case 1n:
      get_req.qplan.f1(get_opts(s))
    case 2n:
      get_req.qback.f1(W.get_str(s))
    case 3n:
      get_req.qnorm.f1(get_ms(s))
    case 4n:
      get_req.qscan.f1(W.get_str(s))
    case 5n:
      get_req.qfit.f1(get_win(s))
    case 6n+u:
      W.Bad{}

def get_req.start(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.start(W.get_nat(s))

# Replies
# -------

def put_verb(x: Rp.Verb, rest: String) -> String:
  match x:
    case Rp.ACreate{}:
      W.put_nat(0n, rest)
    case Rp.AUpdate{}:
      W.put_nat(1n, rest)
    case Rp.ADelete{}:
      W.put_nat(2n, rest)

def put_comp(x: Rp.Comp, rest: String) -> String:
  match x:
    case Rp.KPrompt{}:
      W.put_nat(0n, rest)
    case Rp.KMemory{}:
      W.put_nat(1n, rest)
    case Rp.KSkill{}:
      W.put_nat(2n, rest)
    case Rp.KSubagent{}:
      W.put_nat(3n, rest)
    case Rp.KFactory{}:
      W.put_nat(4n, rest)

def put_ms(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_str(x, rest))

def put_mss.items(xs: List<&2, Maybe<&2, String>>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, u}:
      put_ms(x, put_mss.items(u, rest))

def put_mss(+xs: List<&2, Maybe<&2, String>>, rest: String) -> String:
  W.put_nat(List.length(&2, Maybe<&2, String>, xs), put_mss.items(xs, rest))

def put_out(x: Rp.Out, rest: String) -> String:
  match x:
    case Rp.OInvalid{msg}:
      W.put_nat(0n, W.put_str(msg, rest))
    case Rp.ORefused{msg}:
      W.put_nat(1n, W.put_str(msg, rest))
    case Rp.ORemoved{}:
      W.put_nat(2n, rest)
    case Rp.OWritten{}:
      W.put_nat(3n, rest)

def put_row(x: Rp.Row, rest: String) -> String:
  match x:
    case Rp.Row{verb, comp, id, out}:
      put_verb(verb, put_comp(comp, W.put_str(id, put_out(out, rest))))

def put_rows.items(xs: List<&2, Rp.Row>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, u}:
      put_row(x, put_rows.items(u, rest))

def put_rows(+xs: List<&2, Rp.Row>, rest: String) -> String:
  W.put_nat(List.length(&2, Rp.Row, xs), put_rows.items(xs, rest))

def put_strs.items(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, u}:
      W.put_str(x, put_strs.items(u, rest))

def put_strs(+xs: List<&2, String>, rest: String) -> String:
  W.put_nat(List.length(&2, String, xs), put_strs.items(xs, rest))

def put_plan(x: Rp.Plan, rest: String) -> String:
  match x:
    case Rp.Plan{rows, changes}:
      put_rows(rows, put_strs(changes, rest))

def put_pick(x: Rp.Pick, rest: String) -> String:
  match x:
    case Rp.Pick{at, verb}:
      W.put_nat(at, put_verb(verb, rest))

def put_picks.items(xs: List<&2, Rp.Pick>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, u}:
      put_pick(x, put_picks.items(u, rest))

def put_picks(+xs: List<&2, Rp.Pick>, rest: String) -> String:
  W.put_nat(List.length(&2, Rp.Pick, xs), put_picks.items(xs, rest))

def put_back(x: Rp.Back, rest: String) -> String:
  match x:
    case Rp.Back{summary, rationale, outcome, reason, picks}:
      W.put_str(summary, W.put_str(rationale, W.put_str(outcome, W.put_str(reason, put_picks(picks, rest)))))

def put_texts(x: Rp.Texts, rest: String) -> String:
  match x:
    case Rp.Texts{summary, rationale, outcome}:
      W.put_str(summary, W.put_str(rationale, W.put_str(outcome, rest)))

def put_search(x: Rp.Search, rest: String) -> String:
  match x:
    case Rp.SFull{}:
      W.put_nat(0n, rest)
    case Rp.SProbe{low, high, len}:
      W.put_nat(1n, W.put_nat(low, W.put_nat(high, W.put_nat(len, rest))))
    case Rp.SFinal{}:
      W.put_nat(2n, rest)

def put_step(x: Rp.Step, rest: String) -> String:
  match x:
    case Rp.TTry{len, next}:
      W.put_nat(0n, W.put_nat(len, put_search(next, rest)))
    case Rp.TOk{max}:
      W.put_nat(1n, W.put_nat(max, rest))
    case Rp.TNo{text}:
      W.put_nat(2n, W.put_str(text, rest))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QIds{eds}:
      put_mss(Rp.ids(eds), "")
    case QPlan{opts, eds}:
      put_plan(Rp.plan(opts, eds), "")
    case QBack{id, was}:
      put_back(Rp.back(id, was), "")
    case QNorm{summary, rationale, outcome}:
      put_texts(Rp.norm(summary, rationale, outcome), "")
    case QScan{text}:
      W.put_bool(Rp.incomplete(text), "")
    case QFit{win, conv, search, plen}:
      put_step(Rp.fit(win, conv, search, plen), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("refine_plan: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("refine_plan: malformed request")

# the entry: decode the request, answer the model's answer
def ffi(input: String) -> String:
  ffi.got(get_req(input))
