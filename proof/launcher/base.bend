# eukhe: lemmas the proofs of area launcher share: the entry's reader
# answers what the laws' reader answers on every input (one lemma per
# stage, each a case split on the stage's input), the entry reads back the
# answers the laws spell, and its commit is the laws' "every answer is
# quiesced".

import Base
import ../../bend/ffi_launcher.bend as FLa
import ../../bend/launcher.bend as La
import ../../bend/wire.bend as Wr
import ../../laws/launcher.bend as Launcher

# Logic
# -----

def la.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# a claim that Some is None proves anything
def la.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : la.if_none(A, _, G)
  Unit{}

# The reader, stage by stage
# --------------------------

def la.prompt(r: Wr.Dec<Bool>) -> {Launcher.read_prompt(r) == FLa.get_prompt(r) : Wr.Dec<La.Ask>}:
  match r:
    case Wr.Got{c, s}:
      {==}
    case Wr.Bad{}:
      {==}

def la.quiesce_closed(b: Bool, r: Wr.Dec<Bool>) -> {Launcher.read_quiesce.closed(b, r) == FLa.get_quiesce.closed(b, r) : Wr.Dec<La.Ask>}:
  match r:
    case Wr.Got{c, s}:
      {==}
    case Wr.Bad{}:
      {==}

def la.quiesce(r: Wr.Dec<Bool>) -> {Launcher.read_quiesce(r) == FLa.get_quiesce(r) : Wr.Dec<La.Ask>}:
  match r:
    case Wr.Got{b, s}:
      la.quiesce_closed(b, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def la.answers_cons(a: Bool, r: Wr.Dec<List<&2, Bool>>) -> {Launcher.read_answers.cons(a, r) == FLa.get_answers.cons(a, r) : Wr.Dec<List<&2, Bool>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def la.answers(n: Nat, cur: Wr.Dec<Bool>) -> {Launcher.read_answers(n, cur) == FLa.get_answers.go(n, cur) : Wr.Dec<List<&2, Bool>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{a, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+a, +s}:
          %la.answers(m, Wr.get_bool(s)) : {Launcher.read_answers.cons(a, Launcher.read_answers(m, Wr.get_bool(s))) == FLa.get_answers.cons(a, _) : Wr.Dec<List<&2, Bool>>}
          %la.answers_cons(a, Launcher.read_answers(m, Wr.get_bool(s))) : {Launcher.read_answers.cons(a, Launcher.read_answers(m, Wr.get_bool(s))) == _ : Wr.Dec<List<&2, Bool>>}
          {==}
        case Wr.Bad{}:
          {==}

def la.commit_answers(r: Wr.Dec<List<&2, Bool>>) -> {Launcher.read_commit.answers(r) == FLa.get_commit.answers(r) : Wr.Dec<La.Ask>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def la.commit(r: Wr.Dec<Nat>) -> {Launcher.read_commit(r) == FLa.get_commit(r) : Wr.Dec<La.Ask>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %la.answers(m, Wr.get_bool(s)) : {Launcher.read_commit.answers(Launcher.read_answers(m, Wr.get_bool(s))) == FLa.get_commit.answers(_) : Wr.Dec<La.Ask>}
          %la.commit_answers(Launcher.read_answers(m, Wr.get_bool(s))) : {Launcher.read_commit.answers(Launcher.read_answers(m, Wr.get_bool(s))) == _ : Wr.Dec<La.Ask>}
          {==}
    case Wr.Bad{}:
      {==}

def la.adopt_some(r: Wr.Dec<Nat>) -> {Launcher.read_adopt.some(r) == FLa.get_adopt.some(r) : Wr.Dec<La.Ask>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def la.adopt_tag(t: Nat, s: String) -> {Launcher.read_adopt.tag(t, s) == FLa.get_adopt.tag(t, s) : Wr.Dec<La.Ask>}:
  match t:
    case 0n:
      {==}
    case 1n:
      la.adopt_some(Wr.get_nat(s))
    case 2n+p:
      {==}

def la.adopt(r: Wr.Dec<Nat>) -> {Launcher.read_adopt(r) == FLa.get_adopt(r) : Wr.Dec<La.Ask>}:
  match r:
    case Wr.Got{t, s}:
      la.adopt_tag(t, s)
    case Wr.Bad{}:
      {==}

def la.ask_tag(t: Nat, s: String) -> {Launcher.read_ask.tag(t, s) == FLa.get_ask.tag(t, s) : Wr.Dec<La.Ask>}:
  match t:
    case 0n:
      la.prompt(Wr.get_bool(s))
    case 1n:
      la.quiesce(Wr.get_bool(s))
    case 2n:
      la.commit(Wr.get_nat(s))
    case 3n:
      la.adopt(Wr.get_nat(s))
    case 4n+p:
      {==}

# the entry reads every input as the laws' reader does
def la.ask(r: Wr.Dec<Nat>) -> {Launcher.read_ask.go(r) == FLa.get_ask.go(r) : Wr.Dec<La.Ask>}:
  match r:
    case Wr.Got{t, s}:
      la.ask_tag(t, s)
    case Wr.Bad{}:
      {==}

# Round trip and the commit
# -------------------------

# the answers after the first read back, the first one being a
def la.bools_rt(t: List<&2, Bool>, +a: Bool, +rest: String) -> {Wr.Got{a <> t, rest} == FLa.get_answers.go(List.length(&2, Bool, t), Wr.get_bool(Wr.put_bool(a, Launcher.spell_bools(t, rest)))) : Wr.Dec<List<&2, Bool>>}:
  match t:
    case Nil{}:
      match a:
        case True{}:
          {==}
        case False{}:
          {==}
    case +x <> +u:
      match a:
        case True{}:
          %la.bools_rt(u, x, rest) : {Wr.Got{True{} <> x <> u, rest} == FLa.get_answers.cons(True{}, _) : Wr.Dec<List<&2, Bool>>}
          {==}
        case False{}:
          %la.bools_rt(u, x, rest) : {Wr.Got{False{} <> x <> u, rest} == FLa.get_answers.cons(False{}, _) : Wr.Dec<List<&2, Bool>>}
          {==}

# the commit is "every answer is quiesced"
def la.commits(xs: List<&2, Bool>) -> {Launcher.all_quiesced(xs) == La.commits(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case a <> t:
      %la.commits(t) : {Bool.and(a, Launcher.all_quiesced(t)) == Bool.and(a, _) : Bool}
      {==}

# the adoption of a worker that reports build n
def la.adopt_n(n: Nat) -> {FLa.put_adoption(La.adoption(0n, Some{n}), "") == Wr.put_nat(Launcher.adopt_spec(Some{n}), "") : String}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}
