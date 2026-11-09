# ffi_privacy: the entry of the compiled Bend core for the outbound
# scrubber (privacy.anonymizeRemote; bend/privacy/ip.bend,
# bend/privacy/token.bend; Rust: eukhe-bend rules/privacy.rs, asked by
# eukhe-ai privacy/detect.rs and privacy/mod.rs). Grammar:
# crates/eukhe-bend/WIRE.md.
#
# The call answers the IP addresses at the candidate positions of one
# text:
#
#   request  List<String>: before, then rest, of each candidate
#   reply    List<Nat>: 0 when rest starts with no address, else 1 + the
#            address's length in chars (`Ip.ip`)
#
# The stepper is the token map of one session (`Tk.Book`, kept in the Bend
# heap for the session's life; eukhe-ai privacy/mod.rs `TokenMap`):
#
#   open     nothing         reply: List<Nat>, the tags of the classes
#                            whose tokens map back (`Tk.mapped_classes`)
#   step     Ev              reply: Scrub: List<Nat>, each value's token
#                            (its index, or 0: one way); Restore: the count
#                            of tokens, then each one's value: `0,` (none)
#                            or `1,` and the value (a String)
#   Ev       0, classes: List<Nat>, values: List<String> (Scrub: the
#                            values of one text, in order)
#            | 1, classes: List<Nat>, indexes: List<Nat> (Restore: the
#                            tokens of one text, in order)
#   class    0 PERSON | 1 EMAIL | 2 PHONE | 3 IP | 4 ID | 5 KEY | 6 CARD
#            | 7 IBAN
#
# A malformed request (an odd count of strings, input left over) answers
# `E privacy: malformed request`; a malformed event (an unknown tag or
# class, lists of two lengths, input left over) answers
# `E privacy: malformed event` and keeps the map; an open with input opens
# the refused state, which answers every step
# `E privacy: the open was refused`. laws/privacy/ pins the entry. Pure:
# no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./privacy/ip.bend as Ip
import ./privacy/token.bend as Tk

# The call
# --------

# a candidate position: the text before it, the text from it
type Cand is Data:
  Cand{before: String, rest: String}

def pairs.cons(c: Cand, m: Maybe<&2, List<&2, Cand>>) -> Maybe<&2, List<&2, Cand>>:
  match m:
    case None{}:
      None{}
    case Some{cs}:
      Some{c <> cs}

# the candidates of a list of strings: before, then rest, of each
def pairs(xs: List<&2, String>) -> Maybe<&2, List<&2, Cand>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case b <> more:
      match more:
        case Nil{}:
          None{}
        case r <> t:
          pairs.cons(Cand{b, r}, pairs(t))

# an answer on the wire: 0 for none, else 1 + the length
def code(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{n}:
      1n+n

# the answer of each candidate, in order
def answers(cs: List<&2, Cand>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c:
        case Cand{b, r}:
          code(Ip.ip(b, r)) <> answers(rest)

def ffi.end(whole: Bool, m: Maybe<&2, List<&2, Cand>>) -> String:
  match whole:
    case True{}:
      match m:
        case Some{cs}:
          W.put_list(~Nat, ~W.put_nat, answers(cs), "")
        case None{}:
          W.err("privacy: malformed request")
    case False{}:
      W.err("privacy: malformed request")

def ffi.got(r: W.Dec<List<&2, String>>) -> String:
  match r:
    case W.Got{xs, s}:
      ffi.end(W.end(s), pairs(xs))
    case W.Bad{}:
      W.err("privacy: malformed request")

# the call: the address at each candidate position
def ffi(input: String) -> String:
  ffi.got(W.get_list(~String, ~W.get_str, input))

# Events
# ------

type Ev is Data:
  Scrub{vs: List<&2, Tk.Val>}
  Restore{rs: List<&2, Tk.Ref>}

def zip_vals.cons(k: Maybe<&2, Tk.Class>, v: String, m: Maybe<&2, List<&2, Tk.Val>>) -> Maybe<&2, List<&2, Tk.Val>>:
  match k:
    case None{}:
      None{}
    case Some{c}:
      match m:
        case None{}:
          None{}
        case Some{vs}:
          Some{Tk.Val{c, v} <> vs}

# the values of classes cs and texts xs, one each
def zip_vals(cs: List<&2, Nat>, xs: List<&2, String>) -> Maybe<&2, List<&2, Tk.Val>>:
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
          zip_vals.cons(Tk.Class.of(c), x, zip_vals(ct, xt))

def zip_refs.cons(k: Maybe<&2, Tk.Class>, i: Nat, m: Maybe<&2, List<&2, Tk.Ref>>) -> Maybe<&2, List<&2, Tk.Ref>>:
  match k:
    case None{}:
      None{}
    case Some{c}:
      match m:
        case None{}:
          None{}
        case Some{rs}:
          Some{Tk.Ref{c, i} <> rs}

# the tokens of classes cs and indexes ns, one each
def zip_refs(cs: List<&2, Nat>, ns: List<&2, Nat>) -> Maybe<&2, List<&2, Tk.Ref>>:
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
          zip_refs.cons(Tk.Class.of(c), i, zip_refs(ct, it))

def ev.of(m: Maybe<&2, Ev>, s: String) -> W.Dec<Ev>:
  match m:
    case Some{e}:
      W.Got{e, s}
    case None{}:
      W.Bad{}

def scrub.of(m: Maybe<&2, List<&2, Tk.Val>>) -> Maybe<&2, Ev>:
  match m:
    case Some{vs}:
      Some{Scrub{vs}}
    case None{}:
      None{}

def restore.of(m: Maybe<&2, List<&2, Tk.Ref>>) -> Maybe<&2, Ev>:
  match m:
    case Some{rs}:
      Some{Restore{rs}}
    case None{}:
      None{}

def get_scrub.vals(cs: List<&2, Nat>, r: W.Dec<List<&2, String>>) -> W.Dec<Ev>:
  match r:
    case W.Got{xs, s}:
      ev.of(scrub.of(zip_vals(cs, xs)), s)
    case W.Bad{}:
      W.Bad{}

def get_scrub(r: W.Dec<List<&2, Nat>>) -> W.Dec<Ev>:
  match r:
    case W.Got{cs, s}:
      get_scrub.vals(cs, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_restore.refs(cs: List<&2, Nat>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Ev>:
  match r:
    case W.Got{ns, s}:
      ev.of(restore.of(zip_refs(cs, ns)), s)
    case W.Bad{}:
      W.Bad{}

def get_restore(r: W.Dec<List<&2, Nat>>) -> W.Dec<Ev>:
  match r:
    case W.Got{cs, s}:
      get_restore.refs(cs, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(r: W.Dec<Nat>) -> W.Dec<Ev>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_scrub(W.get_list(~Nat, ~W.get_nat, s))
        case 1n:
          get_restore(W.get_list(~Nat, ~W.get_nat, s))
        case 2n+p:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the event at the start of s
def get_ev(s: String) -> W.Dec<Ev>:
  get_ev.tag(W.get_nat(s))

# Replies
# -------

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

def put_found.items(fs: List<&2, Maybe<&2, String>>, rest: String) -> String:
  match fs:
    case Nil{}:
      rest
    case f <> more:
      match f:
        case None{}:
          W.put_nat(0n, put_found.items(more, rest))
        case Some{v}:
          W.put_nat(1n, W.put_str(v, put_found.items(more, rest)))

# the values found: their count, then each
def put_found(+fs: List<&2, Maybe<&2, String>>) -> String:
  W.put_nat(List.length(&2, Maybe<&2, String>, fs), put_found.items(fs, ""))

def class_tags(cs: List<&2, Tk.Class>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      Tk.Class.tag(c) <> class_tags(rest)

# The stepper
# -----------

# the map, or a refused open
type St is Data:
  Live{b: Tk.Book}
  Refused{}

def open.end(whole: Bool) -> St & String:
  match whole:
    case True{}:
      (Live{Tk.Book.empty()}, W.put_list(~Nat, ~W.put_nat, class_tags(Tk.mapped_classes()), ""))
    case False{}:
      (Refused{}, W.err("privacy: the open takes no input"))

# open: an empty map; the reply names the classes whose tokens map back
def open(input: String) -> St & String:
  open.end(W.end(input))

def step.scrub(r: Tk.Toks) -> St & String:
  match r:
    case Tk.Toks{b, ts}:
      (Live{b}, W.put_list(~Nat, ~W.put_nat, tok_codes(ts), ""))

# the reply to an event, and the map after it
def apply(+b: Tk.Book, e: Ev) -> St & String:
  match e:
    case Scrub{vs}:
      step.scrub(Tk.scrub_vals(vs, b))
    case Restore{rs}:
      (Live{b}, put_found(Tk.restore_toks(rs, b)))

def step.end(whole: Bool, +b: Tk.Book, e: Ev) -> St & String:
  match whole:
    case True{}:
      apply(b, e)
    case False{}:
      (Live{b}, W.err("privacy: malformed event"))

def step.ev(+b: Tk.Book, r: W.Dec<Ev>) -> St & String:
  match r:
    case W.Got{e, rest}:
      step.end(W.end(rest), b, e)
    case W.Bad{}:
      (Live{b}, W.err("privacy: malformed event"))

# step: one event; the reply is the tokens of its values, or the values of
# its tokens
def step(st: St, input: String) -> St & String:
  match st:
    case Live{b}:
      step.ev(b, get_ev(input))
    case Refused{}:
      (Refused{}, W.err("privacy: the open was refused"))
