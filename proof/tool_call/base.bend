# eukhe: lemmas the proofs of area tool_call share
#
# The stepper opens taking reports (tp.opened). From there, by induction
# on the events, every reply is S2's: tp.taking while no end came,
# tp.over after it. The journal laws then speak of S2's replies only
# (tp.j_over, tp.s_open, tp.k_over, tp.k_open). The entry reads every
# input as the laws' reader does (tp.read); a spelled event runs the
# model's step (tp.spelled).

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall

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
