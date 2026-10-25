# eukhe: the laws of area slash_suggest

import Base
import ../bend/slash_suggest.bend as Ss
import ../bend/ffi_slash_suggest.bend as FSs
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (D1) The command a mistyped slash command meant
# -----------------------------------------------
# bend/slash_suggest.bend, run as the compiled core by
# bend/ffi_slash_suggest.bend (eukhe-bend rules/slash.rs; asked by the TUI,
# the CLI and the Signal gateway when a typed name is no command). Every
# input is free: any typed name, any list of candidate names.
#
# R1: the distance between two names is the Levenshtein distance in chars:
#     the fewest insertions, deletions and substitutions of one char that
#     turn one into the other.
# R2: the candidate considered is the first one, in the given order, of
#     the smallest distance from the typed name; none without candidates.
# R3: it is suggested only when its distance is at most the limit of the
#     typed name's length in UTF-8 bytes n: 1 when n is at most 3, else n
#     divided by 3 (rounded down) but at least 2; else nothing is.
# R4: the entry answers each request Rust writes (the typed name and the
#     candidates, every length within the wire) with the suggestion of
#     R1-R3 (the candidate's index), reads exactly the request and nothing
#     after it, and answers any other input with the exact error form
#     `E slash_suggest: malformed request`.

# Spec helpers
# ------------

def sp_pick(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

def sp_min(+x: Nat, +y: Nat) -> Nat:
  sp_pick(Nat.is_le(x, y), x, y)

def sp_cost(b: Bool) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n

# R1: the Levenshtein distance, by its recursive definition
def sp_lev(a: String, b: String) -> Nat:
  match a b:
    case SNil{} _:
      String.length(b)
    case SCon{c, t} SNil{}:
      Nat.add(1n, String.length(t))
    case SCon{+c, +t} SCon{+x, +u}:
      sp_min(sp_min(Nat.add(1n, sp_lev(t, SCon{x, u})), Nat.add(1n, sp_lev(SCon{c, t}, u))), Nat.add(sp_lev(t, u), sp_cost(Char.is_eq(c, x))))

# R3: the UTF-8 length of a char and of a text
def sp_utf8(c: Char) -> Nat:
  match c:
    case Chr{+x}:
      sp_pick(U32.is_lt(x, 128), 1n, sp_pick(U32.is_lt(x, 2048), 2n, sp_pick(U32.is_lt(x, 65536), 3n, 4n)))

def sp_bytes(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{c, t}:
      Nat.add(sp_utf8(c), sp_bytes(t))

# R3: the most edits a suggestion may take from a name of n bytes
def sp_limit(+n: Nat) -> Nat:
  +q = Nat.div(n, 3n)
  sp_pick(Nat.is_le(n, 3n), 1n, sp_pick(Nat.is_le(2n, q), q, 2n))

# R2: the index and distance of the first candidate of the fewest edits
def sp_first.won(b: Bool, j: Nat, e: Nat, d: Nat) -> Ss.Near:
  match b:
    case True{}:
      Ss.Near{Nat.add(1n, j), e}
    case False{}:
      Ss.Near{0n, d}

def sp_first.of(+d: Nat, m: Maybe<&2, Ss.Near>) -> Ss.Near:
  match m:
    case None{}:
      Ss.Near{0n, d}
    case Some{n}:
      match n:
        case Ss.Near{j, +e}:
          sp_first.won(Nat.is_lt(e, d), j, e, d)

def sp_first(+w: String, cs: List<&2, String>) -> Maybe<&2, Ss.Near>:
  match cs:
    case Nil{}:
      None{}
    case x <> t:
      Some{sp_first.of(sp_lev(w, x), sp_first(w, t))}

def sp_within(b: Bool, j: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{j}
    case False{}:
      None{}

# R2, R3: the index of the candidate suggested, if any
def sp_suggest.of(+w: String, m: Maybe<&2, Ss.Near>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      match n:
        case Ss.Near{j, e}:
          sp_within(Nat.is_le(e, sp_limit(sp_bytes(w))), j)

def sp_suggest(+w: String, cs: List<&2, String>) -> Maybe<&2, Nat>:
  sp_suggest.of(w, sp_first(w, cs))

# R4: the spelling of a request and of its reply

def sp_w_req(q: FSs.Req, rest: String) -> String:
  match q:
    case FSs.QSuggest{w, cs}:
      Wr.put_str(w, Wr.put_list(~String, ~Wr.put_str, cs, rest))

def sp_w_answer(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{j}:
      Wr.put_nat(1n, Wr.put_nat(j, ""))

def sp_w_reply(q: FSs.Req) -> String:
  match q:
    case FSs.QSuggest{w, cs}:
      sp_w_answer(sp_suggest(w, cs))

# every length of xs fits the wire
def sp_fit_strs(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(LawsBase.wire_fits(String.length(x)), sp_fit_strs(t))

# every number and length of the request fits the wire
def sp_fit_req(q: FSs.Req) -> Bool:
  match q:
    case FSs.QSuggest{w, +cs}:
      Bool.and(LawsBase.wire_fits(String.length(w)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), sp_fit_strs(cs)))

# Laws: the suggestion
# --------------------

# LAW slash_suggest_distance (R1): the distance between every two names is
# the Levenshtein distance of its recursive definition
# EXCLUDES: a distance in bytes, a substitution counted twice, a
#   transposition counted as one edit, a row that forgets a suffix
law slash_suggest_distance:
  for +a: String
  for +b: String
  {Ss.dist(a, b) == sp_lev(a, b) : Nat}

# LAW slash_suggest_spec (R1, R2, R3): the suggestion for every typed name
# and every list of candidates is the spec's
# EXCLUDES: a later candidate winning a tie, a farther candidate, a limit
#   counted in chars, a limit off by one, a suggestion past the limit, an
#   index shifted by one
law slash_suggest_spec:
  for +w: String
  for +cs: List<&2, String>
  {Ss.suggest(w, cs) == sp_suggest(w, cs) : Maybe<&2, Nat>}

# LAW slash_suggest_example (R1, R2, R3): anchor: Rust's vectors, short:
# a swapped pair, a far name, a tie, no candidates, names of 2 chars but 4
# bytes and of 1 char of 4 bytes (limit 2: chars would give 1), a name of
# 3 bytes (limit 1)
# EXCLUDES: a spec that drifts from the Rust it replaced
law slash_suggest_example:
  {[Ss.suggest("modle", ["new", "model"]), Ss.suggest("comapct", ["compact"]), Ss.suggest("zzzzzz", ["model"]), Ss.suggest("ab", ["ac", "ad"]), Ss.suggest("x", []), Ss.suggest("éé", ["ab"]), Ss.suggest("😀", ["ab"]), Ss.suggest("abc", ["a"])] == [Some{1n}, Some{0n}, None{}, Some{0n}, None{}, Some{0n}, Some{0n}, None{}] : List<&2, Maybe<&2, Nat>>}

# LAW slash_suggest_distance_example (R1): anchor: Rust's vectors
# EXCLUDES: a spec distance other than Levenshtein's
law slash_suggest_distance_example:
  {[sp_lev("abc", "abc"), sp_lev("ab", "ac"), sp_lev("", "abc"), sp_lev("abc", ""), sp_lev("ab", "ba")] == [0n, 1n, 3n, 3n, 2n] : List<&2, Nat>}

# Laws: the entry (R4)
# --------------------

# LAW slash_suggest_entry_answers (R4): the entry answers every request
# Rust spells, every length within the wire, with the spelled suggestion of
# the spec
# EXCLUDES: the typed name and the candidates swapped, a candidate dropped,
#   a default
law slash_suggest_entry_answers:
  for +q: FSs.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FSs.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW slash_suggest_entry_reads (R4): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law slash_suggest_entry_reads:
  for +q: FSs.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FSs.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSs.Req>}

# LAW slash_suggest_entry_exact (R4): every input the entry does not
# answer with the error form is a spelled request that fits the wire
# EXCLUDES: a suggestion made on input that is no request (a malformed
#   field, input left over)
law slash_suggest_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSs.ffi(s)) == False{} : Bool}
  exs r: FSs.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW slash_suggest_entry_refuses (R4): every error the entry answers is
# exactly `E slash_suggest: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law slash_suggest_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FSs.ffi(s)) == True{} : Bool}
  {FSs.ffi(s) == Wr.err("slash_suggest: malformed request") : String}

# LAW slash_suggest_entry_example (R4): anchor: the wire strings Rust sends
# and the replies it reads; input left over and a malformed request
# EXCLUDES: a field order other than Rust's, another reply spelling
law slash_suggest_entry_example:
  {[FSs.ffi("5,modle2,3,new5,model"), FSs.ffi("2,zz1,5,model"), FSs.ffi("2,zz0,"), FSs.ffi("5,modle2,3,new5,modelx"), FSs.ffi("x")] == ["1,1,", "0,", "0,", Wr.err("slash_suggest: malformed request"), Wr.err("slash_suggest: malformed request")] : List<&2, String>}
