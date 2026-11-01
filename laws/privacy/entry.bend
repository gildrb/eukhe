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

# LAW privacy_entry_example (R7-R9): anchor: the bytes Rust sends and the
# replies: a call over `a::before`, `203.0.113.7` and `::sync::Arc`; a
# scrub of an address, a key and a literal IP_1; the restore of IP 1,
# IP 2 and a key; an unknown tag and lists of two lengths refused
# EXCLUDES: another spelling of a request, an event or a reply
law privacy_entry_example:
  {FP.ffi("6,0,11,a::before {11,ssh deploy@11,203.0.113.73,std11,::sync::Arc") == "3,0,12,0," : String} & ({FP.ffi("1,0,") == Wr.err("privacy: malformed request") : String} & ({FP.step(FP.Live{Tk.Book.empty()}, "0,3,3,5,3,3,11,203.0.113.76,sk-abc4,IP_1") == (FP.Live{Tk.Book{[Tk.Ent{Tk.Ip{}, "IP_1"}, Tk.Ent{Tk.Ip{}, "203.0.113.7"}]}}, "3,1,0,2,") : FP.St & String} & ({FP.step(FP.Live{Tk.Book{[Tk.Ent{Tk.Ip{}, "IP_1"}, Tk.Ent{Tk.Ip{}, "203.0.113.7"}]}}, "1,3,3,3,5,3,1,2,7,") == (FP.Live{Tk.Book{[Tk.Ent{Tk.Ip{}, "IP_1"}, Tk.Ent{Tk.Ip{}, "203.0.113.7"}]}}, "3,1,11,203.0.113.71,4,IP_10,") : FP.St & String} & ({FP.step(FP.Live{Tk.Book.empty()}, "9,") == (FP.Live{Tk.Book.empty()}, Wr.err("privacy: malformed event")) : FP.St & String} & {FP.step(FP.Live{Tk.Book.empty()}, "0,1,3,0,") == (FP.Live{Tk.Book.empty()}, Wr.err("privacy: malformed event")) : FP.St & String}))))
