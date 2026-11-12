# eukhe: lemmas the proofs of area tool_call share
#
# The stepper opens taking reports (tp.opened). From there, by induction
# on the events, every reply is S2's (tp.spec, a proof-side scaffold the
# laws do not read):
# tp.taking while no end came, tp.over after it. The journal laws then
# speak of S2's replies only (tp.j_over, tp.s_open, tp.k_over,
# tp.k_open). After any events the stepper holds a call ended exactly
# when an end came (tp.fed_taking, tp.fed_over), and one more event is
# answered as S2 asks (tp.answer).
#
# The world: every history from w0 is one of seven shapes (ep.from_w0),
# and each world law holds of every shape.

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../spec/harness/effect.bend as Sp

# Logic
# -----

# s spelled up to a field a is s spelled up to its spelling b
def tp.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

def tp.FT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True
def tp.no(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : tp.FT(_, G)
  Unit{}

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

# S2's replies, spelled; ended: an end came before
def tp.spec(es: List<&2, Tc.Ev>, ended: Bool) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Tc.Report{}:
          match ended:
            case False{}:
              "0," <> tp.spec(rest, False{})
            case True{}:
              "1," <> tp.spec(rest, True{})
        case Tc.End{t, a}:
          match ended:
            case False{}:
              SCon{'2', SCon{',', ToolCall.tc_how_spec(t, a)}} <> tp.spec(rest, True{})
            case True{}:
              "3," <> tp.spec(rest, True{})

# The stepper's replies
# ---------------------

# after the end, every reply is S2's for an ended call
def tp.over(es: List<&2, Tc.Ev>) -> {ToolCall.tc_replies(es, FTc.Call{Tc.Ended{}}) == tp.spec(es, True{}) : List<&2, String>}:
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
def tp.taking(es: List<&2, Tc.Ev>) -> {ToolCall.tc_replies(es, FTc.Call{Tc.Taking{}}) == tp.spec(es, False{}) : List<&2, String>}:
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
def tp.model(+first: Bool, +es: List<&2, Tc.Ev>) -> {tp.spec(es, False{}) == ToolCall.tc_replies(es, ToolCall.tc_opened(first)) : List<&2, String>}:
  %tp.opened(first) : {tp.spec(es, False{}) == ToolCall.tc_replies(es, _) : List<&2, String>}
  Equal.sym(List<&2, String>, ToolCall.tc_replies(es, FTc.Call{Tc.Taking{}}), tp.spec(es, False{}), tp.taking(es))

# The journal of S2's replies
# ---------------------------

# after the end, no reply journals a settle
def tp.j_over(es: List<&2, Tc.Ev>) -> {0n == List.length(&2, String, ToolCall.tc_journaled(tp.spec(es, True{}))) : Nat}:
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
def tp.s_open(es: List<&2, Tc.Ev>) -> {ToolCall.tc_once(ToolCall.tc_ends(es)) == List.length(&2, String, ToolCall.tc_journaled(tp.spec(es, False{}))) : Nat}:
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
def tp.k_over(es: List<&2, Tc.Ev>) -> {ToolCall.tc_kept(es, tp.spec(es, True{})) == ToolCall.tc_before_end(es, True{}) : List<&2, Bool>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tc.Report{}:
          %tp.k_over(rest) : {False{} <> ToolCall.tc_kept(rest, tp.spec(rest, True{})) == False{} <> _ : List<&2, Bool>}
          {==}
        case Tc.End{t, a}:
          tp.k_over(rest)

# before the end, every report is stored, as it comes before the end
def tp.k_open(es: List<&2, Tc.Ev>) -> {ToolCall.tc_kept(es, tp.spec(es, False{})) == ToolCall.tc_before_end(es, False{}) : List<&2, Bool>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tc.Report{}:
          %tp.k_open(rest) : {True{} <> ToolCall.tc_kept(rest, tp.spec(rest, False{})) == True{} <> _ : List<&2, Bool>}
          {==}
        case Tc.End{t, a}:
          tp.k_over(rest)


# The stepper after a history
# ---------------------------

# the call the stepper holds: ended or taking reports
def tp.cof(b: Bool) -> Tc.C:
  match b:
    case True{}:
      Tc.Ended{}
    case False{}:
      Tc.Taking{}

# after the end, every event keeps the call ended
def tp.fed_over(pre: List<&2, Tc.Ev>) -> {ToolCall.tc_fed(pre, FTc.Call{Tc.Ended{}}) == FTc.Call{Tc.Ended{}} : FTc.St}:
  match pre:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Tc.Report{}:
          tp.fed_over(rest)
        case Tc.End{t, a}:
          match t a:
            case True{} True{}:
              tp.fed_over(rest)
            case True{} False{}:
              tp.fed_over(rest)
            case False{} True{}:
              tp.fed_over(rest)
            case False{} False{}:
              tp.fed_over(rest)

# from a call taking reports, the events leave it ended exactly when an
# end is among them
def tp.fed_taking(pre: List<&2, Tc.Ev>) -> {ToolCall.tc_fed(pre, FTc.Call{Tc.Taking{}}) == FTc.Call{tp.cof(ToolCall.tc_ends(pre))} : FTc.St}:
  match pre:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Tc.Report{}:
          tp.fed_taking(rest)
        case Tc.End{t, a}:
          match t a:
            case True{} True{}:
              tp.fed_over(rest)
            case True{} False{}:
              tp.fed_over(rest)
            case False{} True{}:
              tp.fed_over(rest)
            case False{} False{}:
              tp.fed_over(rest)

# one event, to a call ended (b) or not, is answered as S2 asks
def tp.answer(b: Bool, e: Tc.Ev) -> {ToolCall.tc_reply(FTc.step(FTc.Call{tp.cof(b)}, ToolCall.tc_spell(e))) == ToolCall.tc_answer(b, e) : String}:
  match b:
    case True{}:
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
    case False{}:
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

# The world
# ---------
# From w0, every history reaches one of seven shapes (ep.step: the world
# after one event of a shape is the shape after it; ep.run: by induction
# on the events). Each world law holds of every shape (ep.early, ep.once),
# and a history without a commit stays at w0 (ep.inert).

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
