# eukhe: lemmas the proofs of laws/stop/entry.bend share: the entry's
# decoder is the laws' reader, stage by stage (sex.ask); so the entry is
# the laws' entry on every input (sex.exact)

import Base
import ../../../bend/stop.bend as S
import ../../../bend/ffi_stop.bend as FS
import ../../../bend/wire.bend as Wr
import ../../../laws/stop.bend as Stop
import ../../../laws/stop/entry.bend as StopEntry
import ../base.bend as LAStop

def sex.pending(+c: Bool, +t: Bool, +b: Bool, d: Wr.Dec<Bool>) -> {FS.get_walk.pending(c, t, b, d) == StopEntry.st.r_walk.pending(c, t, b, d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{p, r}:
      {==}
    case Wr.Bad{}:
      {==}

def sex.broken(+c: Bool, +t: Bool, d: Wr.Dec<Bool>) -> {FS.get_walk.broken(c, t, d) == StopEntry.st.r_walk.broken(c, t, d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{b, r}:
      sex.pending(c, t, b, Wr.get_bool(r))
    case Wr.Bad{}:
      {==}

def sex.text(+c: Bool, d: Wr.Dec<Bool>) -> {FS.get_walk.text(c, d) == StopEntry.st.r_walk.text(c, d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{t, r}:
      sex.broken(c, t, Wr.get_bool(r))
    case Wr.Bad{}:
      {==}

def sex.walk(d: Wr.Dec<Bool>) -> {FS.get_walk(d) == StopEntry.st.r_walk.cut(d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{c, r}:
      sex.text(c, Wr.get_bool(r))
    case Wr.Bad{}:
      {==}

def sex.cap(+a: Nat, +t: Nat, +w: Nat, d: Wr.Dec<Nat>) -> {FS.get_cut.cap(a, t, w, d) == StopEntry.st.r_note.cap(a, t, w, d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{k, r}:
      {==}
    case Wr.Bad{}:
      {==}

def sex.row(+a: Nat, +t: Nat, d: Wr.Dec<Nat>) -> {FS.get_cut.row(a, t, d) == StopEntry.st.r_note.row(a, t, d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{w, r}:
      sex.cap(a, t, w, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def sex.tokens(+a: Nat, d: Wr.Dec<Nat>) -> {FS.get_cut(a, d) == StopEntry.st.r_note.tokens(a, d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{t, r}:
      sex.row(a, t, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def sex.note(d: Wr.Dec<Nat>) -> {FS.get_note(d) == StopEntry.st.r_note.attempt(d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{a, r}:
      sex.tokens(a, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def sex.done(+m: Nat, d: Wr.Dec<Nat>) -> {FS.get_rounds.done(m, d) == StopEntry.st.r_rounds.done(m, d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{n, r}:
      {==}
    case Wr.Bad{}:
      {==}

def sex.rounds(d: Wr.Dec<Nat>) -> {FS.get_rounds(d) == StopEntry.st.r_rounds.max(d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{m, r}:
      sex.done(m, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def sex.tag(d: Wr.Dec<Nat>) -> {FS.get_ask.tag(d) == StopEntry.st.r_ask.tag(d) : Wr.Dec<FS.Ask>}:
  match d:
    case Wr.Got{n, +r}:
      match n:
        case 0n:
          sex.walk(Wr.get_bool(r))
        case 1n:
          sex.note(Wr.get_nat(r))
        case 2n:
          sex.rounds(Wr.get_nat(r))
        case 3n+k:
          {==}
    case Wr.Bad{}:
      {==}

# the entry reads every input as the laws' reader does
def sex.ask(+s: String) -> {FS.get_ask(s) == StopEntry.st.r_ask(s) : Wr.Dec<FS.Ask>}:
  sex.tag(Wr.get_nat(s))

def sex.end(whole: Bool, +a: FS.Ask) -> {FS.ffi.done(a, whole) == StopEntry.st.entry.end(whole, a) : String}:
  match whole:
    case True{}:
      LAStop.stb.reply(a)
    case False{}:
      {==}

def sex.go(d: Wr.Dec<FS.Ask>) -> {FS.ffi.got(d) == StopEntry.st.entry.go(d) : String}:
  match d:
    case Wr.Got{a, +r}:
      sex.end(Wr.end(r), a)
    case Wr.Bad{}:
      {==}

# the entry is the laws' entry on every input
def sex.exact(+s: String) -> {FS.ffi(s) == StopEntry.st.entry(s) : String}:
  %Equal.sym(Wr.Dec<FS.Ask>, FS.get_ask(s), StopEntry.st.r_ask(s), sex.ask(s)) : {FS.ffi.got(_) == StopEntry.st.entry(s) : String}
  sex.go(StopEntry.st.r_ask(s))
