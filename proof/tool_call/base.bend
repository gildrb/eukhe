# eukhe: lemmas the proofs of area tool_call share
#
# The stepper opens taking reports (tp.opened). From there, by induction
# on the events, every reply is S2's: tp.taking while no end came,
# tp.over after it. The journal laws then speak of S2's replies only
# (tp.j_over, tp.s_open, tp.k_over, tp.k_open). The entry reads every
# input as the laws' reader does (tp.read); a spelled event runs the
# model's step (tp.spelled).
#
# The gate: a spelled question runs the model's gate (ep.spelled), and
# the entry reads every input as the laws' reader does (ep.read). The
# world: every history from w0 is one of seven shapes (ep.from_w0), and
# each world law holds of every shape.

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../spec/harness/effect.bend as Sp

# Logic
# -----

def tp.MD(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def tp.none_some(-A: Data, -G: Type, -r: A, h: {None{} == Some{r} : Maybe<&2, A>}) -> G:
  %h : tp.MD(A, _, G)
  Unit{}

def tp.get(-A: Data, m: Maybe<&2, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def tp.some_inj(-A: Data, +a: A, +b: A, h: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => tp.get(A, m, a), Some{a}, Some{b}, h)

# The stepper's replies
# ---------------------

# after the end, every reply is S2's for an ended call
def tp.over(es: List<&2, Tc.Ev>) -> {ToolCall.tc_replies(es, FTc.Call{Tc.Ended{}}) == ToolCall.tc_spec(es, True{}) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tc.Report{}:
          %tp.over(rest) : {"1," <> ToolCall.tc_replies(rest, FTc.Call{Tc.Ended{}}) == "1," <> _ : List<&2, String>}
          {==}
        case Tc.End{t, a}:
          match t a:
            case True{} True{}:
              %tp.over(rest) : {"3," <> ToolCall.tc_replies(rest, FTc.Call{Tc.Ended{}}) == "3," <> _ : List<&2, String>}
              {==}
            case True{} False{}:
              %tp.over(rest) : {"3," <> ToolCall.tc_replies(rest, FTc.Call{Tc.Ended{}}) == "3," <> _ : List<&2, String>}
              {==}
            case False{} True{}:
              %tp.over(rest) : {"3," <> ToolCall.tc_replies(rest, FTc.Call{Tc.Ended{}}) == "3," <> _ : List<&2, String>}
              {==}
            case False{} False{}:
              %tp.over(rest) : {"3," <> ToolCall.tc_replies(rest, FTc.Call{Tc.Ended{}}) == "3," <> _ : List<&2, String>}
              {==}

# while no end came, every reply is S2's for a running call
def tp.taking(es: List<&2, Tc.Ev>) -> {ToolCall.tc_replies(es, FTc.Call{Tc.Taking{}}) == ToolCall.tc_spec(es, False{}) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tc.Report{}:
          %tp.taking(rest) : {"0," <> ToolCall.tc_replies(rest, FTc.Call{Tc.Taking{}}) == "0," <> _ : List<&2, String>}
          {==}
        case Tc.End{t, a}:
          match t a:
            case True{} True{}:
              %tp.over(rest) : {"2,2," <> ToolCall.tc_replies(rest, FTc.Call{Tc.Ended{}}) == "2,2," <> _ : List<&2, String>}
              {==}
            case True{} False{}:
              %tp.over(rest) : {"2,1," <> ToolCall.tc_replies(rest, FTc.Call{Tc.Ended{}}) == "2,1," <> _ : List<&2, String>}
              {==}
            case False{} True{}:
              %tp.over(rest) : {"2,0," <> ToolCall.tc_replies(rest, FTc.Call{Tc.Ended{}}) == "2,0," <> _ : List<&2, String>}
              {==}
            case False{} False{}:
              %tp.over(rest) : {"2,0," <> ToolCall.tc_replies(rest, FTc.Call{Tc.Ended{}}) == "2,0," <> _ : List<&2, String>}
              {==}

# an open, of a first attempt or a rerun, takes reports
def tp.opened(first: Bool) -> {FTc.Call{Tc.Taking{}} == ToolCall.tc_opened(first) : FTc.St}:
  match first:
    case True{}:
      {==}
    case False{}:
      {==}

# the stepper as opened answers S2's replies
def tp.model(+first: Bool, +es: List<&2, Tc.Ev>) -> {ToolCall.tc_spec(es, False{}) == ToolCall.tc_replies(es, ToolCall.tc_opened(first)) : List<&2, String>}:
  %tp.opened(first) : {ToolCall.tc_spec(es, False{}) == ToolCall.tc_replies(es, _) : List<&2, String>}
  Equal.sym(List<&2, String>, ToolCall.tc_replies(es, FTc.Call{Tc.Taking{}}), ToolCall.tc_spec(es, False{}), tp.taking(es))

# The journal of S2's replies
# ---------------------------

# after the end, no reply journals a settle
def tp.j_over(es: List<&2, Tc.Ev>) -> {0n == List.length(&2, String, ToolCall.tc_journaled(ToolCall.tc_spec(es, True{}))) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Tc.Report{}:
          tp.j_over(rest)
        case Tc.End{t, a}:
          tp.j_over(rest)

# before the end, the replies journal one settle when an end comes, else
# none
def tp.s_open(es: List<&2, Tc.Ev>) -> {ToolCall.tc_once(ToolCall.tc_ends(es)) == List.length(&2, String, ToolCall.tc_journaled(ToolCall.tc_spec(es, False{}))) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tc.Report{}:
          tp.s_open(rest)
        case Tc.End{t, a}:
          %tp.j_over(rest) : {1n == 1n+_ : Nat}
          {==}

# one record and at most one more is at most two
def tp.le_once(b: Bool) -> {Nat.is_le(1n+ToolCall.tc_once(b), 2n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# after the end, no report is stored, as none comes before the end
def tp.k_over(es: List<&2, Tc.Ev>) -> {ToolCall.tc_kept(es, ToolCall.tc_spec(es, True{})) == ToolCall.tc_before_end(es, True{}) : List<&2, Bool>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tc.Report{}:
          %tp.k_over(rest) : {False{} <> ToolCall.tc_kept(rest, ToolCall.tc_spec(rest, True{})) == False{} <> _ : List<&2, Bool>}
          {==}
        case Tc.End{t, a}:
          tp.k_over(rest)

# before the end, every report is stored, as it comes before the end
def tp.k_open(es: List<&2, Tc.Ev>) -> {ToolCall.tc_kept(es, ToolCall.tc_spec(es, False{})) == ToolCall.tc_before_end(es, False{}) : List<&2, Bool>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tc.Report{}:
          %tp.k_open(rest) : {True{} <> ToolCall.tc_kept(rest, ToolCall.tc_spec(rest, False{})) == True{} <> _ : List<&2, Bool>}
          {==}
        case Tc.End{t, a}:
          tp.k_over(rest)

# The entry
# ---------

def tp.read_aborted(t: Bool, r: Wr.Dec<Bool>) -> {ToolCall.tc_read.aborted(t, r) == FTc.get_ev.aborted(t, r) : Wr.Dec<Tc.Ev>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tp.read_threw(r: Wr.Dec<Bool>) -> {ToolCall.tc_read.threw(r) == FTc.get_ev.threw(r) : Wr.Dec<Tc.Ev>}:
  match r:
    case Wr.Got{t, s}:
      tp.read_aborted(t, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def tp.read_tag(n: Nat, s: String) -> {ToolCall.tc_read.tag(n, s) == FTc.get_ev.tag(n, s) : Wr.Dec<Tc.Ev>}:
  match n:
    case 0n:
      {==}
    case 1n:
      tp.read_threw(Wr.get_bool(s))
    case 2n+p:
      {==}

# the entry reads every event as the laws' reader does
def tp.read(r: Wr.Dec<Nat>) -> {ToolCall.tc_read.go(r) == FTc.get_ev.go(r) : Wr.Dec<Tc.Ev>}:
  match r:
    case Wr.Got{n, s}:
      tp.read_tag(n, s)
    case Wr.Bad{}:
      {==}

# a spelled event is read whole: the stepper runs the model's step
def tp.spelled(c: Tc.C, e: Tc.Ev) -> {FTc.step.reply(Tc.step(c, e)) == FTc.step(FTc.Call{c}, ToolCall.tc_spell(e)) : FTc.St & String}:
  match e:
    case Tc.Report{}:
      {==}
    case Tc.End{t, a}:
      match t a:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}

# a spelled open is read whole
def tp.open_spelled(b: Bool) -> {FTc.open.end(True{}, b) == FTc.open(ToolCall.tc_spell_open(b)) : FTc.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# The gate
# --------

def ep.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def ep.true_false(-G: Type, h: {True{} == False{} : Bool}) -> G:
  %h : ep.BT(_, G)
  Unit{}

# a spelled question is read whole: the entry answers the model's gate
def ep.spelled(+q: Tc.Gate) -> {FTc.put_go(Tc.gate(q)) == FTc.ffi(ToolCall.tc_spell_gate(q)) : String}:
  match q:
    case Tc.Enter{f, t}:
      match f:
        case True{}:
          match t:
            case Tc.Gone{}:
              {==}
            case Tc.Offered{tr}:
              match tr:
                case Tc.Safe{}:
                  {==}
                case Tc.Unsafe{}:
                  {==}
        case False{}:
          match t:
            case Tc.Gone{}:
              {==}
            case Tc.Offered{tr}:
              match tr:
                case Tc.Safe{}:
                  {==}
                case Tc.Unsafe{}:
                  {==}
    case Tc.Recover{f, p, t}:
      match f:
        case True{}:
          match p:
            case Tc.Safe{}:
              match t:
                case Tc.Gone{}:
                  {==}
                case Tc.Offered{tr}:
                  match tr:
                    case Tc.Safe{}:
                      {==}
                    case Tc.Unsafe{}:
                      {==}
            case Tc.Unsafe{}:
              match t:
                case Tc.Gone{}:
                  {==}
                case Tc.Offered{tr}:
                  match tr:
                    case Tc.Safe{}:
                      {==}
                    case Tc.Unsafe{}:
                      {==}
        case False{}:
          match p:
            case Tc.Safe{}:
              match t:
                case Tc.Gone{}:
                  {==}
                case Tc.Offered{tr}:
                  match tr:
                    case Tc.Safe{}:
                      {==}
                    case Tc.Unsafe{}:
                      {==}
            case Tc.Unsafe{}:
              match t:
                case Tc.Gone{}:
                  {==}
                case Tc.Offered{tr}:
                  match tr:
                    case Tc.Safe{}:
                      {==}
                    case Tc.Unsafe{}:
                      {==}
    case Tc.Stop{f, x, i}:
      match f:
        case True{}:
          match x:
            case True{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match x:
            case True{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}

# The entry reads every gate question as the laws' reader does

def ep.rd_replay_tag(n: Nat, s: String) -> {ToolCall.tc_rg_replay.tag(n, s) == FTc.get_replay.tag(n, s) : Wr.Dec<Tc.Replay>}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def ep.rd_replay(r: Wr.Dec<Nat>) -> {ToolCall.tc_rg_replay.go(r) == FTc.get_replay.go(r) : Wr.Dec<Tc.Replay>}:
  match r:
    case Wr.Got{n, s}:
      ep.rd_replay_tag(n, s)
    case Wr.Bad{}:
      {==}

def ep.rd_offered(r: Wr.Dec<Tc.Replay>) -> {ToolCall.tc_rg_now.offered(r) == FTc.get_now.offered(r) : Wr.Dec<Tc.Now>}:
  match r:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ep.rd_off(+s: String) -> {ToolCall.tc_rg_now.offered(ToolCall.tc_rg_replay(s)) == FTc.get_now.offered(FTc.get_replay(s)) : Wr.Dec<Tc.Now>}:
  %ep.rd_replay(Wr.get_nat(s)) : {ToolCall.tc_rg_now.offered(ToolCall.tc_rg_replay(s)) == FTc.get_now.offered(_) : Wr.Dec<Tc.Now>}
  ep.rd_offered(ToolCall.tc_rg_replay(s))

def ep.rd_now_tag(n: Nat, +s: String) -> {ToolCall.tc_rg_now.tag(n, s) == FTc.get_now.tag(n, s) : Wr.Dec<Tc.Now>}:
  match n:
    case 0n:
      {==}
    case 1n:
      ep.rd_off(s)
    case 2n+p:
      {==}

def ep.rd_now(r: Wr.Dec<Nat>) -> {ToolCall.tc_rg_now.go(r) == FTc.get_now.go(r) : Wr.Dec<Tc.Now>}:
  match r:
    case Wr.Got{n, s}:
      ep.rd_now_tag(n, s)
    case Wr.Bad{}:
      {==}

def ep.rd_enter(f: Bool, d: Wr.Dec<Tc.Now>) -> {ToolCall.tc_rg.enter(f, d) == FTc.get_gate.enter(f, d) : Wr.Dec<Tc.Gate>}:
  match d:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ep.rd_recover(f: Bool, p: Tc.Replay, d: Wr.Dec<Tc.Now>) -> {ToolCall.tc_rg.recover(f, p, d) == FTc.get_gate.recover(f, p, d) : Wr.Dec<Tc.Gate>}:
  match d:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ep.rd_stored(+f: Bool, d: Wr.Dec<Tc.Replay>) -> {ToolCall.tc_rg.stored(f, d) == FTc.get_gate.stored(f, d) : Wr.Dec<Tc.Gate>}:
  match d:
    case Wr.Got{+p, +s}:
      %ep.rd_now(Wr.get_nat(s)) : {ToolCall.tc_rg.recover(f, p, ToolCall.tc_rg_now(s)) == FTc.get_gate.recover(f, p, _) : Wr.Dec<Tc.Gate>}
      ep.rd_recover(f, p, ToolCall.tc_rg_now(s))
    case Wr.Bad{}:
      {==}

def ep.rd_intent(f: Bool, x: Bool, d: Wr.Dec<Bool>) -> {ToolCall.tc_rg.intent(f, x, d) == FTc.get_gate.intent(f, x, d) : Wr.Dec<Tc.Gate>}:
  match d:
    case Wr.Got{i, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ep.rd_restart(+f: Bool, d: Wr.Dec<Bool>) -> {ToolCall.tc_rg.restart(f, d) == FTc.get_gate.restart(f, d) : Wr.Dec<Tc.Gate>}:
  match d:
    case Wr.Got{x, s}:
      ep.rd_intent(f, x, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ep.rd_found(n: Nat, r: Wr.Dec<Bool>) -> {ToolCall.tc_rg.found(n, r) == FTc.get_gate.found(n, r) : Wr.Dec<Tc.Gate>}:
  match n:
    case 0n:
      match r:
        case Wr.Got{+f, +s}:
          %ep.rd_now(Wr.get_nat(s)) : {ToolCall.tc_rg.enter(f, ToolCall.tc_rg_now(s)) == FTc.get_gate.enter(f, _) : Wr.Dec<Tc.Gate>}
          ep.rd_enter(f, ToolCall.tc_rg_now(s))
        case Wr.Bad{}:
          {==}
    case 1n:
      match r:
        case Wr.Got{+f, +s}:
          %ep.rd_replay(Wr.get_nat(s)) : {ToolCall.tc_rg.stored(f, ToolCall.tc_rg_replay(s)) == FTc.get_gate.stored(f, _) : Wr.Dec<Tc.Gate>}
          ep.rd_stored(f, ToolCall.tc_rg_replay(s))
        case Wr.Bad{}:
          {==}
    case 2n:
      match r:
        case Wr.Got{f, s}:
          ep.rd_restart(f, Wr.get_bool(s))
        case Wr.Bad{}:
          {==}
    case 3n+p:
      {==}

# the entry reads every gate question as the laws' reader does
def ep.read(r: Wr.Dec<Nat>) -> {ToolCall.tc_rg.go(r) == FTc.get_gate.go(r) : Wr.Dec<Tc.Gate>}:
  match r:
    case Wr.Got{n, s}:
      ep.rd_found(n, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

# The world
# ---------
# From w0, every history reaches one of seven shapes (ep.step: the world
# after one event of a shape is the shape after it; ep.run: by induction
# on the events). Each world law holds of every shape (ep.early, ep.once,
# ep.settles), and a history without a commit stays at w0 (ep.inert).

# The worlds a history reaches
type Shape is Data:
  ShA{}                 # w0: nothing committed
  ShB{}                 # committed, at the call checkpoint
  ShCU{r: Bool}         # unsafe intent recorded, run once (r: running)
  ShCS{r: Bool, n: Nat} # safe intent recorded, run 1+n times
  ShD0{}                # settled before any intent
  ShDU{}                # settled after an unsafe intent, run once
  ShDS{n: Nat}          # settled after a safe intent, run 1+n times

def embed(s: Shape) -> Sp.World:
  match s:
    case ShA{}:
      Sp.Wd{False{}, Sp.NoTask{}, False{}, 0n, 0n, 0n}
    case ShB{}:
      Sp.Wd{True{}, Sp.AtCall{}, False{}, 0n, 0n, 0n}
    case ShCU{r}:
      Sp.Wd{True{}, Sp.AtExecute{Tc.Unsafe{}}, r, 1n, 0n, 0n}
    case ShCS{r, n}:
      Sp.Wd{True{}, Sp.AtExecute{Tc.Safe{}}, r, 1n+n, 0n, 0n}
    case ShD0{}:
      Sp.Wd{True{}, Sp.Settled{None{}}, False{}, 0n, 1n, 0n}
    case ShDU{}:
      Sp.Wd{True{}, Sp.Settled{Some{Tc.Unsafe{}}}, False{}, 1n, 1n, 0n}
    case ShDS{n}:
      Sp.Wd{True{}, Sp.Settled{Some{Tc.Safe{}}}, False{}, 1n+n, 1n, 0n}

def shstep.b(t: Tc.Now) -> Shape:
  match t:
    case Tc.Gone{}:
      ShD0{}
    case Tc.Offered{p}:
      match p:
        case Tc.Safe{}:
          ShCS{True{}, 0n}
        case Tc.Unsafe{}:
          ShCU{True{}}

def shstep.cs_t(t: Tc.Now, n: Nat) -> Shape:
  match t:
    case Tc.Gone{}:
      ShDS{n}
    case Tc.Offered{p}:
      match p:
        case Tc.Safe{}:
          ShCS{True{}, 1n+n}
        case Tc.Unsafe{}:
          ShDS{n}

def shstep.cu(r: Bool, e: Sp.Ev) -> Shape:
  match r:
    case True{}:
      match e:
        case Sp.Delta{}:
          ShCU{True{}}
        case Sp.Commit{}:
          ShCU{True{}}
        case Sp.Start{t}:
          ShCU{True{}}
        case Sp.Finish{}:
          ShDU{}
        case Sp.Crash{}:
          ShCU{False{}}
        case Sp.Abort{k}:
          ShDU{}
    case False{}:
      match e:
        case Sp.Delta{}:
          ShCU{False{}}
        case Sp.Commit{}:
          ShCU{False{}}
        case Sp.Start{t}:
          ShDU{}
        case Sp.Finish{}:
          ShCU{False{}}
        case Sp.Crash{}:
          ShCU{False{}}
        case Sp.Abort{k}:
          ShDU{}

def shstep.cs(r: Bool, n: Nat, e: Sp.Ev) -> Shape:
  match r:
    case True{}:
      match e:
        case Sp.Delta{}:
          ShCS{True{}, n}
        case Sp.Commit{}:
          ShCS{True{}, n}
        case Sp.Start{t}:
          ShCS{True{}, n}
        case Sp.Finish{}:
          ShDS{n}
        case Sp.Crash{}:
          ShCS{False{}, n}
        case Sp.Abort{k}:
          ShDS{n}
    case False{}:
      match e:
        case Sp.Delta{}:
          ShCS{False{}, n}
        case Sp.Commit{}:
          ShCS{False{}, n}
        case Sp.Start{t}:
          shstep.cs_t(t, n)
        case Sp.Finish{}:
          ShCS{False{}, n}
        case Sp.Crash{}:
          ShCS{False{}, n}
        case Sp.Abort{k}:
          ShDS{n}

# the shape after one event
def shstep(s: Shape, e: Sp.Ev) -> Shape:
  match s:
    case ShA{}:
      match e:
        case Sp.Delta{}:
          ShA{}
        case Sp.Commit{}:
          ShB{}
        case Sp.Start{t}:
          ShA{}
        case Sp.Finish{}:
          ShA{}
        case Sp.Crash{}:
          ShA{}
        case Sp.Abort{k}:
          ShA{}
    case ShB{}:
      match e:
        case Sp.Delta{}:
          ShB{}
        case Sp.Commit{}:
          ShB{}
        case Sp.Start{t}:
          shstep.b(t)
        case Sp.Finish{}:
          ShB{}
        case Sp.Crash{}:
          ShB{}
        case Sp.Abort{k}:
          ShD0{}
    case ShCU{r}:
      shstep.cu(r, e)
    case ShCS{r, n}:
      shstep.cs(r, n, e)
    case ShD0{}:
      ShD0{}
    case ShDU{}:
      ShDU{}
    case ShDS{n}:
      ShDS{n}

# the shape after the events es, in order, from s
def shrun(es: List<&2, Sp.Ev>, s: Shape) -> Shape:
  match es:
    case Nil{}:
      s
    case e <> rest:
      shrun(rest, shstep(s, e))

def ep.step_cu(+r: Bool, +e: Sp.Ev) -> {embed(shstep.cu(r, e)) == ToolCall.ef_step(embed(ShCU{r}), e) : Sp.World}:
  match r:
    case True{}:
      match e:
        case Sp.Delta{}:
          {==}
        case Sp.Commit{}:
          {==}
        case Sp.Start{t}:
          {==}
        case Sp.Finish{}:
          {==}
        case Sp.Crash{}:
          {==}
        case Sp.Abort{k}:
          match k:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match e:
        case Sp.Delta{}:
          {==}
        case Sp.Commit{}:
          {==}
        case Sp.Start{t}:
          {==}
        case Sp.Finish{}:
          {==}
        case Sp.Crash{}:
          {==}
        case Sp.Abort{k}:
          match k:
            case True{}:
              {==}
            case False{}:
              {==}

def ep.step_cs(+r: Bool, +n: Nat, +e: Sp.Ev) -> {embed(shstep.cs(r, n, e)) == ToolCall.ef_step(embed(ShCS{r, n}), e) : Sp.World}:
  match r:
    case True{}:
      match e:
        case Sp.Delta{}:
          {==}
        case Sp.Commit{}:
          {==}
        case Sp.Start{t}:
          {==}
        case Sp.Finish{}:
          {==}
        case Sp.Crash{}:
          {==}
        case Sp.Abort{k}:
          match k:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match e:
        case Sp.Delta{}:
          {==}
        case Sp.Commit{}:
          {==}
        case Sp.Start{t}:
          match t:
            case Tc.Gone{}:
              {==}
            case Tc.Offered{tr}:
              match tr:
                case Tc.Safe{}:
                  {==}
                case Tc.Unsafe{}:
                  {==}
        case Sp.Finish{}:
          {==}
        case Sp.Crash{}:
          {==}
        case Sp.Abort{k}:
          match k:
            case True{}:
              {==}
            case False{}:
              {==}

# the world after one event of a shape is the shape after it
def ep.step(+s: Shape, +e: Sp.Ev) -> {embed(shstep(s, e)) == ToolCall.ef_step(embed(s), e) : Sp.World}:
  match s:
    case ShA{}:
      match e:
        case Sp.Delta{}:
          {==}
        case Sp.Commit{}:
          {==}
        case Sp.Start{t}:
          {==}
        case Sp.Finish{}:
          {==}
        case Sp.Crash{}:
          {==}
        case Sp.Abort{k}:
          {==}
    case ShB{}:
      match e:
        case Sp.Delta{}:
          {==}
        case Sp.Commit{}:
          {==}
        case Sp.Start{t}:
          match t:
            case Tc.Gone{}:
              {==}
            case Tc.Offered{tr}:
              match tr:
                case Tc.Safe{}:
                  {==}
                case Tc.Unsafe{}:
                  {==}
        case Sp.Finish{}:
          {==}
        case Sp.Crash{}:
          {==}
        case Sp.Abort{k}:
          match k:
            case True{}:
              {==}
            case False{}:
              {==}
    case ShCU{r}:
      ep.step_cu(r, e)
    case ShCS{r, n}:
      ep.step_cs(r, n, e)
    case ShD0{}:
      match e:
        case Sp.Delta{}:
          {==}
        case Sp.Commit{}:
          {==}
        case Sp.Start{t}:
          {==}
        case Sp.Finish{}:
          {==}
        case Sp.Crash{}:
          {==}
        case Sp.Abort{k}:
          {==}
    case ShDU{}:
      match e:
        case Sp.Delta{}:
          {==}
        case Sp.Commit{}:
          {==}
        case Sp.Start{t}:
          {==}
        case Sp.Finish{}:
          {==}
        case Sp.Crash{}:
          {==}
        case Sp.Abort{k}:
          {==}
    case ShDS{n}:
      match e:
        case Sp.Delta{}:
          {==}
        case Sp.Commit{}:
          {==}
        case Sp.Start{t}:
          {==}
        case Sp.Finish{}:
          {==}
        case Sp.Crash{}:
          {==}
        case Sp.Abort{k}:
          {==}

# every history from a shape is the shapes it reaches
def ep.run(es: List<&2, Sp.Ev>, +s: Shape) -> {ToolCall.ef_run(es, embed(s)) == embed(shrun(es, s)) : Sp.World}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      %ep.step(s, e) : {ToolCall.ef_run(rest, _) == embed(shrun(rest, shstep(s, e))) : Sp.World}
      ep.run(rest, shstep(s, e))

# every history from w0 is a shape
def ep.from_w0(+es: List<&2, Sp.Ev>) -> {ToolCall.ef_run(es, Sp.w0()) == embed(shrun(es, ShA{})) : Sp.World}:
  ep.run(es, ShA{})

# no shape holds an early run
def ep.early(s: Shape) -> {Sp.early(embed(s)) == 0n : Nat}:
  match s:
    case ShA{}:
      {==}
    case ShB{}:
      {==}
    case ShCU{r}:
      {==}
    case ShCS{r, n}:
      {==}
    case ShD0{}:
      {==}
    case ShDU{}:
      {==}
    case ShDS{n}:
      {==}

# every shape ran at most once, or recorded a safe intent
def ep.once(s: Shape) -> {Bool.or(Sp.safe_intent(embed(s)), Nat.is_le(Sp.effects(embed(s)), 1n)) == True{} : Bool}:
  match s:
    case ShA{}:
      {==}
    case ShB{}:
      {==}
    case ShCU{r}:
      {==}
    case ShCS{r, n}:
      {==}
    case ShD0{}:
      {==}
    case ShDU{}:
      {==}
    case ShDS{n}:
      {==}

# every shape settled at most once
def ep.settles(s: Shape) -> {Nat.is_le(Sp.settles(embed(s)), 1n) == True{} : Bool}:
  match s:
    case ShA{}:
      {==}
    case ShB{}:
      {==}
    case ShCU{r}:
      {==}
    case ShCS{r, n}:
      {==}
    case ShD0{}:
      {==}
    case ShDU{}:
      {==}
    case ShDS{n}:
      {==}

# a history without a commit stays at w0
def ep.inert(es: List<&2, Sp.Ev>, no: {Sp.commits(es) == False{} : Bool}) -> {shrun(es, ShA{}) == ShA{} : Shape}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Sp.Delta{}:
          ep.inert(rest, no)
        case Sp.Commit{}:
          ep.true_false({shrun(rest, ShB{}) == ShA{} : Shape}, no)
        case Sp.Start{t}:
          ep.inert(rest, no)
        case Sp.Finish{}:
          ep.inert(rest, no)
        case Sp.Crash{}:
          ep.inert(rest, no)
        case Sp.Abort{k}:
          ep.inert(rest, no)
