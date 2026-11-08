# eukhe: the laws of area privacy, section entry: the entry of the
# compiled core for the outbound scrubber (bend/ffi_privacy.bend): the call
# (the IP addresses of a text) and the stepper (the token map)

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../bend/privacy/token.bend as Tk
import ../../bend/ffi_privacy.bend as FP
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# LAWS (H7, compiled core): the scrubber's IP grammar and its token map
# run as the compiled model (bend/ffi_privacy.bend; Rust: crates/
# eukhe-bend/src/rules/privacy.rs, asked by eukhe-ai privacy/detect.rs and
# privacy/mod.rs). Each law is an open claim about the functions the core
# runs (FP.ffi, FP.open, FP.step), stated with spec spellers built only
# from the wire primitives of bend/wire.bend:
#
# R7: the call answers every request Rust spells (the before and rest of
#     each candidate, every string within the wire) with Ip.ip of each
#     candidate, in order (0: none, 1 + its length); an odd count of
#     strings answers exactly the error form "privacy: malformed request".
# R8: the map opens empty, and its reply names the classes whose tokens
#     map back (PERSON, EMAIL, PHONE, IP, ID): Rust reads a literal token
#     of only those classes.
# R9: a live map answers every Scrub Rust spells with the tokens of
#     Tk.scrub_vals (an index, or 0: one way) and moves to the map after
#     them; every Restore with the values of Tk.restore_toks, map kept;
#     an event with an unknown class, or lists of two lengths, answers
#     exactly the error form "privacy: malformed event" and keeps the map.
# R10: every input is answered as the laws' readers (built from the wire
#     primitives) read it: the call answers a whole request (strings in
#     pairs, nothing left over) as R7 and any other input with its error
#     form; the open answers no input as R8 and any input with the
#     refused state and "privacy: the open takes no input"; a live map
#     answers a whole event as R9 and any other input as malformed; the
#     refused state answers every step "privacy: the open was refused".
#     A class's wire code is the one WIRE.md names (0 PERSON, 1 EMAIL,
#     2 PHONE, 3 IP, 4 ID, 5 KEY, 6 CARD, 7 IBAN).

# Spec spellers
# -------------

# the strings of the candidates: the before, then the rest, of each
def cand_strs(cs: List<&2, FP.Cand>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c:
        case FP.Cand{b, r}:
          b <> r <> cand_strs(rest)

# a request of the call
def spell_cands(+cs: List<&2, FP.Cand>) -> String:
  LawsBase.wire_spell_strs(cand_strs(cs), "")

def cands_fit(+cs: List<&2, FP.Cand>) -> Bool:
  LawsBase.wire_strs_fit(cand_strs(cs))

def answer(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{n}:
      1n+n

def answers(cs: List<&2, FP.Cand>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c:
        case FP.Cand{b, r}:
          answer(Ip.ip(b, r)) <> answers(rest)

# the reply of the call: the answer of each candidate
def spell_answers(cs: List<&2, FP.Cand>) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, answers(cs), "")

def val_tags(vs: List<&2, Tk.Val>) -> List<&2, Nat>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> rest:
      match v:
        case Tk.Val{c, x}:
          Tk.Class.tag(c) <> val_tags(rest)

def val_texts(vs: List<&2, Tk.Val>) -> List<&2, String>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> rest:
      match v:
        case Tk.Val{c, x}:
          x <> val_texts(rest)

# a Scrub event: tag 0, the classes, the values
def spell_scrub(+vs: List<&2, Tk.Val>) -> String:
  Wr.put_nat(0n, LawsBase.wire_spell_nats(val_tags(vs), LawsBase.wire_spell_strs(val_texts(vs), "")))

def vals_fit(+vs: List<&2, Tk.Val>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Tk.Val, vs)), LawsBase.wire_strs_fit(val_texts(vs)))

def ref_tags(rs: List<&2, Tk.Ref>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Tk.Ref{c, i}:
          Tk.Class.tag(c) <> ref_tags(rest)

def ref_indexes(rs: List<&2, Tk.Ref>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Tk.Ref{c, i}:
          i <> ref_indexes(rest)

# a Restore event: tag 1, the classes, the indexes
def spell_restore(+rs: List<&2, Tk.Ref>) -> String:
  Wr.put_nat(1n, LawsBase.wire_spell_nats(ref_tags(rs), LawsBase.wire_spell_nats(ref_indexes(rs), "")))

def refs_fit(+rs: List<&2, Tk.Ref>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Tk.Ref, rs)), LawsBase.wire_nats_fit(ref_indexes(rs)))

def tok_code(t: Tk.Tok) -> Nat:
  match t:
    case Tk.Mapped{i}:
      i
    case Tk.OneWay{}:
      0n

def tok_codes(ts: List<&2, Tk.Tok>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      tok_code(t) <> tok_codes(rest)

# the reply of a Scrub, and the map after it
def scrub_reply(r: Tk.Toks) -> FP.St & String:
  match r:
    case Tk.Toks{b, ts}:
      (FP.Live{b}, Wr.put_list(~Nat, ~Wr.put_nat, tok_codes(ts), ""))

def found_items(fs: List<&2, Maybe<&2, String>>) -> String:
  match fs:
    case Nil{}:
      ""
    case f <> more:
      match f:
        case None{}:
          Wr.put_nat(0n, found_items(more))
        case Some{v}:
          Wr.put_nat(1n, Wr.put_str(v, found_items(more)))

# the reply of a Restore: the count, then each value found
def spell_found(+fs: List<&2, Maybe<&2, String>>) -> String:
  Wr.put_nat(List.length(&2, Maybe<&2, String>, fs), found_items(fs))

# Spec readers (R10)
# ------------------

# the wire code of a class (crates/eukhe-bend/WIRE.md)
def class_code(c: Tk.Class) -> Nat:
  match c:
    case Tk.Person{}:
      0n
    case Tk.Email{}:
      1n
    case Tk.Phone{}:
      2n
    case Tk.Ip{}:
      3n
    case Tk.Id{}:
      4n
    case Tk.ApiKey{}:
      5n
    case Tk.Card{}:
      6n
    case Tk.Iban{}:
      7n

# the class of a wire code
def read_class(n: Nat) -> Maybe<&2, Tk.Class>:
  match n:
    case 0n:
      Some{Tk.Person{}}
    case 1n:
      Some{Tk.Email{}}
    case 2n:
      Some{Tk.Phone{}}
    case 3n:
      Some{Tk.Ip{}}
    case 4n:
      Some{Tk.Id{}}
    case 5n:
      Some{Tk.ApiKey{}}
    case 6n:
      Some{Tk.Card{}}
    case 7n:
      Some{Tk.Iban{}}
    case 8n+u:
      None{}

def read_pairs.cons(c: FP.Cand, m: Maybe<&2, List<&2, FP.Cand>>) -> Maybe<&2, List<&2, FP.Cand>>:
  match m:
    case None{}:
      None{}
    case Some{cs}:
      Some{c <> cs}

# strings read as candidates: before, then rest, of each; an odd count is
# none
def read_pairs(xs: List<&2, String>) -> Maybe<&2, List<&2, FP.Cand>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case b <> more:
      match more:
        case Nil{}:
          None{}
        case r <> t:
          read_pairs.cons(FP.Cand{b, r}, read_pairs(t))

def read_cands.end(whole: Bool, xs: List<&2, String>) -> Maybe<&2, List<&2, FP.Cand>>:
  match whole:
    case True{}:
      read_pairs(xs)
    case False{}:
      None{}

def read_cands.whole(d: Wr.Dec<List<&2, String>>) -> Maybe<&2, List<&2, FP.Cand>>:
  match d:
    case Wr.Got{xs, +s}:
      read_cands.end(Wr.end(s), xs)
    case Wr.Bad{}:
      None{}

# the candidates s spells whole: a list of strings, in pairs, with
# nothing after it
def read_cands(s: String) -> Maybe<&2, List<&2, FP.Cand>>:
  read_cands.whole(Wr.get_list(~String, ~Wr.get_str, s))

# the reply of the call to the candidates read, or to no request
def call_reply(m: Maybe<&2, List<&2, FP.Cand>>) -> String:
  match m:
    case Some{cs}:
      spell_answers(cs)
    case None{}:
      Wr.err("privacy: malformed request")

# the reply of the call to input s
def call_spec(s: String) -> String:
  call_reply(read_cands(s))

# the open of input s: no input opens the empty map; any input opens the
# refused state
def open_spec(s: String) -> FP.St & String:
  match s:
    case SNil{}:
      (FP.Live{Tk.Book.empty()}, "5,0,1,2,3,4,")
    case SCon{c, t}:
      (FP.Refused{}, Wr.err("privacy: the open takes no input"))

def read_vals.cons(k: Maybe<&2, Tk.Class>, v: String, m: Maybe<&2, List<&2, Tk.Val>>) -> Maybe<&2, List<&2, Tk.Val>>:
  match k:
    case None{}:
      None{}
    case Some{c}:
      match m:
        case None{}:
          None{}
        case Some{vs}:
          Some{Tk.Val{c, v} <> vs}

# codes and texts read as values, one each: a code that names no class, or
# lists of two lengths, are none
def read_vals(cs: List<&2, Nat>, xs: List<&2, String>) -> Maybe<&2, List<&2, Tk.Val>>:
  match cs:
    case Nil{}:
      match xs:
        case Nil{}:
          Some{Nil{}}
        case x <> xt:
          None{}
    case c <> ct:
      match xs:
        case Nil{}:
          None{}
        case x <> xt:
          read_vals.cons(read_class(c), x, read_vals(ct, xt))

def read_refs.cons(k: Maybe<&2, Tk.Class>, i: Nat, m: Maybe<&2, List<&2, Tk.Ref>>) -> Maybe<&2, List<&2, Tk.Ref>>:
  match k:
    case None{}:
      None{}
    case Some{c}:
      match m:
        case None{}:
          None{}
        case Some{rs}:
          Some{Tk.Ref{c, i} <> rs}

# codes and indexes read as tokens, one each
def read_refs(cs: List<&2, Nat>, ns: List<&2, Nat>) -> Maybe<&2, List<&2, Tk.Ref>>:
  match cs:
    case Nil{}:
      match ns:
        case Nil{}:
          Some{Nil{}}
        case i <> it:
          None{}
    case c <> ct:
      match ns:
        case Nil{}:
          None{}
        case i <> it:
          read_refs.cons(read_class(c), i, read_refs(ct, it))

def read_ev.scrub_of(m: Maybe<&2, List<&2, Tk.Val>>) -> Maybe<&2, FP.Ev>:
  match m:
    case Some{vs}:
      Some{FP.Scrub{vs}}
    case None{}:
      None{}

def read_ev.restore_of(m: Maybe<&2, List<&2, Tk.Ref>>) -> Maybe<&2, FP.Ev>:
  match m:
    case Some{rs}:
      Some{FP.Restore{rs}}
    case None{}:
      None{}

def read_ev.end(whole: Bool, m: Maybe<&2, FP.Ev>) -> Maybe<&2, FP.Ev>:
  match whole:
    case True{}:
      m
    case False{}:
      None{}

def read_ev.texts(cs: List<&2, Nat>, d: Wr.Dec<List<&2, String>>) -> Maybe<&2, FP.Ev>:
  match d:
    case Wr.Got{xs, +s}:
      read_ev.end(Wr.end(s), read_ev.scrub_of(read_vals(cs, xs)))
    case Wr.Bad{}:
      None{}

def read_ev.indexes(cs: List<&2, Nat>, d: Wr.Dec<List<&2, Nat>>) -> Maybe<&2, FP.Ev>:
  match d:
    case Wr.Got{ns, +s}:
      read_ev.end(Wr.end(s), read_ev.restore_of(read_refs(cs, ns)))
    case Wr.Bad{}:
      None{}

def read_ev.scrub(d: Wr.Dec<List<&2, Nat>>) -> Maybe<&2, FP.Ev>:
  match d:
    case Wr.Got{cs, s}:
      read_ev.texts(cs, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      None{}

def read_ev.restore(d: Wr.Dec<List<&2, Nat>>) -> Maybe<&2, FP.Ev>:
  match d:
    case Wr.Got{cs, s}:
      read_ev.indexes(cs, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      None{}

def read_ev.tag(d: Wr.Dec<Nat>) -> Maybe<&2, FP.Ev>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          read_ev.scrub(Wr.get_list(~Nat, ~Wr.get_nat, s))
        case 1n:
          read_ev.restore(Wr.get_list(~Nat, ~Wr.get_nat, s))
        case 2n+u:
          None{}
    case Wr.Bad{}:
      None{}

# the event s spells whole: tag 0, codes, texts (a Scrub) or tag 1,
# codes, indexes (a Restore), with nothing after it
def read_ev(s: String) -> Maybe<&2, FP.Ev>:
  read_ev.tag(Wr.get_nat(s))

# the step of a live map b on the event read, or on no event
def ev_reply(+b: Tk.Book, m: Maybe<&2, FP.Ev>) -> FP.St & String:
  match m:
    case None{}:
      (FP.Live{b}, Wr.err("privacy: malformed event"))
    case Some{e}:
      match e:
        case FP.Scrub{vs}:
          scrub_reply(Tk.scrub_vals(vs, b))
        case FP.Restore{rs}:
          (FP.Live{b}, spell_found(Tk.restore_toks(rs, b)))

# the step of a live map b on input s
def step_spec(+b: Tk.Book, s: String) -> FP.St & String:
  ev_reply(b, read_ev(s))

# Laws: the call (R7)
# -------------------

# LAW privacy_ip_entry_answers (R7): every request Rust spells, every
# string within the wire, answers Ip.ip of each candidate, in order
# EXCLUDES: before and rest swapped, a candidate skipped, reordered or
#   answered twice, a default answer, another reply spelling
law privacy_ip_entry_answers:
  for +cs: List<&2, FP.Cand>
  for +fit: {cands_fit(cs) == True{} : Bool}
  {FP.ffi(spell_cands(cs)) == spell_answers(cs) : String}

# LAW privacy_ip_entry_odd (R7): a request with an odd count of strings
# answers exactly the error form
# EXCLUDES: a last before read with an empty rest (an answer Rust never
#   asked for)
law privacy_ip_entry_odd:
  for +cs: List<&2, FP.Cand>
  for +b: String
  for +fit: {LawsBase.wire_strs_fit(List.append(&2, String, cand_strs(cs), [b])) == True{} : Bool}
  {FP.ffi(LawsBase.wire_spell_strs(List.append(&2, String, cand_strs(cs), [b]), "")) == Wr.err("privacy: malformed request") : String}

# Laws: the map (R8, R9)
# ----------------------

# LAW privacy_entry_open (R8): the map opens empty, and its reply names
# exactly PERSON, EMAIL, PHONE, IP and ID
# EXCLUDES: IP left out (Rust would scrub a literal IP_1 one way, and the
#   restore would never read IP tokens), a credential class named, a map
#   that opens with values
law privacy_entry_open:
  {FP.open("") == (FP.Live{Tk.Book.empty()}, "5,0,1,2,3,4,") : FP.St & String}

# LAW privacy_entry_scrub (R9): from every map, every Scrub Rust spells
# answers the tokens of Tk.scrub_vals and moves to the map after them
# EXCLUDES: a class or a value misread, a token of another value, a map
#   that forgets or does not grow
law privacy_entry_scrub:
  for +b: Tk.Book
  for +vs: List<&2, Tk.Val>
  for +fit: {vals_fit(vs) == True{} : Bool}
  {FP.step(FP.Live{b}, spell_scrub(vs)) == scrub_reply(Tk.scrub_vals(vs, b)) : FP.St & String}

# LAW privacy_entry_restore (R9): from every map, every Restore Rust
# spells answers the values of Tk.restore_toks and keeps the map
# EXCLUDES: a token restored to another value, a credential restored, a
#   map changed by a restore
law privacy_entry_restore:
  for +b: Tk.Book
  for +rs: List<&2, Tk.Ref>
  for +fit: {refs_fit(rs) == True{} : Bool}
  {FP.step(FP.Live{b}, spell_restore(rs)) == (FP.Live{b}, spell_found(Tk.restore_toks(rs, b))) : FP.St & String}

# LAW privacy_ip_entry_spec (R7, R10): every input, whatever its bytes,
# answers as the laws' reader reads it: a whole request with Ip.ip of
# each candidate, in order (Ip.ip pinned by laws/privacy/ip.bend), any
# other input exactly the error form
# EXCLUDES: input left over after the request ignored, a malformed list
#   or an odd count answered with a value, a default answer, another
#   error text
law privacy_ip_entry_spec:
  for +s: String
  {FP.ffi(s) == call_spec(s) : String}

# LAW privacy_entry_open_spec (R8, R10): every open input opens as the
# spec says: no input the empty map naming the classes that map back, any
# input the refused state with its error form
# EXCLUDES: an open with input that opens a live map (or one with
#   values), another error text
law privacy_entry_open_spec:
  for +s: String
  {FP.open(s) == open_spec(s) : FP.St & String}

# LAW privacy_entry_refused (R10): the refused state answers every step
# with exactly its error form, and stays refused
# EXCLUDES: a refused open that scrubs, restores or comes alive
law privacy_entry_refused:
  for +s: String
  {FP.step(FP.Refused{}, s) == (FP.Refused{}, Wr.err("privacy: the open was refused")) : FP.St & String}

# LAW privacy_entry_step_spec (R9, R10): from every map, every input,
# whatever its bytes, answers as the laws' reader reads it: a whole Scrub
# with the tokens of Tk.scrub_vals and the map after them, a whole Restore
# with the values of Tk.restore_toks and the map kept (both pinned by
# laws/privacy/token.bend), any other input exactly the malformed form
# with the map kept
# EXCLUDES: input left over ignored, an unknown class or lists of two
#   lengths read as an event, a map changed by a malformed event, another
#   error text
law privacy_entry_step_spec:
  for +b: Tk.Book
  for +s: String
  {FP.step(FP.Live{b}, s) == step_spec(b, s) : FP.St & String}

# LAW privacy_class_tags (R10): every class is spelled with the code
# WIRE.md names for it
# EXCLUDES: two classes' codes swapped (Rust reads a card as an IBAN, a
#   key as a mapped class), a code no class has
law privacy_class_tags:
  for +c: Tk.Class
  {Tk.Class.tag(c) == class_code(c) : Nat}

# LAW privacy_entry_example (R7-R9): anchor: the bytes Rust sends and the
# replies: a call over `a::before`, `203.0.113.7` and `::sync::Arc`; a
# scrub of an address, a key and a literal IP_1; the restore of IP 1,
# IP 2 and a key; an unknown tag and lists of two lengths refused
# EXCLUDES: another spelling of a request, an event or a reply
law privacy_entry_example:
  {FP.ffi("6,0,11,a::before {11,ssh deploy@11,203.0.113.73,std11,::sync::Arc") == "3,0,12,0," : String} & ({FP.ffi("1,0,") == Wr.err("privacy: malformed request") : String} & ({FP.step(FP.Live{Tk.Book.empty()}, "0,3,3,5,3,3,11,203.0.113.76,sk-abc4,IP_1") == (FP.Live{Tk.Book{[Tk.Ent{Tk.Ip{}, "IP_1"}, Tk.Ent{Tk.Ip{}, "203.0.113.7"}]}}, "3,1,0,2,") : FP.St & String} & ({FP.step(FP.Live{Tk.Book{[Tk.Ent{Tk.Ip{}, "IP_1"}, Tk.Ent{Tk.Ip{}, "203.0.113.7"}]}}, "1,3,3,3,5,3,1,2,7,") == (FP.Live{Tk.Book{[Tk.Ent{Tk.Ip{}, "IP_1"}, Tk.Ent{Tk.Ip{}, "203.0.113.7"}]}}, "3,1,11,203.0.113.71,4,IP_10,") : FP.St & String} & ({FP.step(FP.Live{Tk.Book.empty()}, "9,") == (FP.Live{Tk.Book.empty()}, Wr.err("privacy: malformed event")) : FP.St & String} & {FP.step(FP.Live{Tk.Book.empty()}, "0,1,3,0,") == (FP.Live{Tk.Book.empty()}, Wr.err("privacy: malformed event")) : FP.St & String}))))

# LAW privacy_ip_entry_assignment_example (R7): anchor: the call over a
# config line `host = 203.0.113.9` takes the address after the `= `
# EXCLUDES: an assignment read as version context (the IP sent in clear)
law privacy_ip_entry_assignment_example:
  {FP.ffi("2,7,host = 11,203.0.113.9") == "1,12," : String}
