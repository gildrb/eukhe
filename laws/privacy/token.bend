# eukhe: the laws of area privacy, section token: the token map of the
# outbound scrubber, a text scrubbed and restored, and the texts a
# failover sends (bend/privacy/token.bend)

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy.bend as S
import ../../spec/harness/privacy_map.bend as Sm

# (H7) The outbound scrubber gives every byte back
# ------------------------------------------------
# spec/README.md H7. The scrubber once hashed IP addresses one way: the
# model read the token, wrote it back in an edit, and the file kept it.
# And the failover re-dispatch scrubbed the already scrubbed context, so a
# local sibling read tokens. The token map now runs as the compiled core
# (bend/ffi_privacy.bend's stepper, one per session: eukhe-ai
# privacy/mod.rs `TokenMap`, for the session's life): one step asks the
# tokens of a text's values (Tk.scrub_vals), one the values of a text's
# tokens (Tk.restore_toks); a
# text as Rust reads it is a list of pieces (Tk.scrub, Tk.restore are those
# steps over it). spec/harness/privacy.bend restates the rule (S4-S6).
# Every input is free: any map, any text, any answer, any failover.
#
# R4: PERSON, EMAIL, PHONE, IP, ID map back; KEY, CARD, IBAN go one way.
# R5: from every map, a text scrubbed and then restored is the text with
#     every credential hidden by its one-way token, and nothing else
#     changed; scrubbed, no value is in clear; restoring any text never
#     brings a credential back; the same text scrubbed again gives the
#     same bytes and the same map; a token keeps its value for the map's
#     life.
# R6: every attempt of a failover sends the raw text: a remote attempt
#     the one scrub of it (never a scrub of a scrub), a local one the text
#     itself.
# R12: the map is the spec's state machine (spec/harness/privacy_map.bend,
#     M1-M5): from every map the stepper can hold (it opens empty, and no
#     class holds a value twice), the tokens of a text's values and the
#     map after them are the spec's, and from every map the values of a
#     text's tokens are the spec's. A text scrubbed, restored and sent is
#     the spec's text over that map (M5): one index space per class, from
#     1, in the order first scrubbed; and from every map the text scrubber
#     gives each value the stepper's token and leaves the stepper's map.
#
# What is pinned of the shipped failover: the dispatch rule (Tk.send), a
# model; eukhe-core's provider runtime (durable/models/provider.rs
# `send_private`) hands every dispatch the raw context, and its test
# `a_loopback_sibling_of_a_remote_primary_reads_the_raw_text` checks it.

# Laws: the classes (R4)
# ----------------------

# LAW privacy_classes (R4): a class's tokens map back exactly when the
# spec says: PERSON, EMAIL, PHONE, IP, ID do; KEY, CARD, IBAN do not
# EXCLUDES: IP hashed one way (the old scrubber: an edit wrote the token
#   into a file), a credential that maps back
law privacy_classes:
  for +c: Tk.Class
  {Tk.reversible(c) == S.reversible(c) : Bool}

# Laws: a text (R5)
# -----------------

# LAW privacy_round_trip_exact (R5): from every map, a text scrubbed, then
# its scrub restored against the map after it, is the text with each
# credential hidden by its one-way token: every other piece comes back as
# it was
# EXCLUDES: a token restored to another value, a value of a personal
#   class lost (one way), a credential restored, plain text changed,
#   pieces reordered, dropped or added
law privacy_round_trip_exact:
  for +m: Tk.Book
  for +xs: List<&2, Tk.Piece>
  {Tk.restore(Tk.Out.m(Tk.scrub(m, xs)), Tk.Out.ys(Tk.scrub(m, xs))) == S.mask(xs) : List<&2, Tk.Seg>}

# LAW privacy_round_trip (R5): from every map, a text with no credential,
# scrubbed and restored, is the text, piece for piece
# EXCLUDES: an IP address (or any personal value) that never comes back,
#   so the model's edit writes its token into a file
law privacy_round_trip:
  for +m: Tk.Book
  for +xs: List<&2, Tk.Piece>
  for +ok: {S.no_secret(xs) == True{} : Bool}
  {Tk.restore(Tk.Out.m(Tk.scrub(m, xs)), Tk.Out.ys(Tk.scrub(m, xs))) == S.raw(xs) : List<&2, Tk.Seg>}

# LAW privacy_scrub_hides (R5): from every map, a scrubbed text is its
# plain text and, for each value, a token of the value's class: mapped for
# a personal value, one way for a credential; no value is left in clear
# EXCLUDES: a value sent in clear, a credential mapped, a token of
#   another class, plain text changed
law privacy_scrub_hides:
  for +m: Tk.Book
  for +xs: List<&2, Tk.Piece>
  {S.erase(Tk.Out.ys(Tk.scrub(m, xs))) == S.shape(xs) : List<&2, Tk.Seg>}

# LAW privacy_secret_never_restored (R5): from every map, restoring any
# text (the model's answer) leaves every piece of a one-way class as it
# was: no credential comes back
# EXCLUDES: a credential's token mapped back to the secret, a hidden
#   credential dropped
law privacy_secret_never_restored:
  for +m: Tk.Book
  for +ys: List<&2, Tk.Seg>
  {S.creds(Tk.restore(m, ys)) == S.creds(ys) : List<&2, Tk.Seg>}

# LAW privacy_token_stable (R5): from every map, the same text scrubbed
# again against the map after its scrub gives the same text and the same
# map: the same raw text and map give the same bytes
# EXCLUDES: a value that takes a new index each time (no stable cache
#   prefix, two tokens for one value), a map that grows on a text it holds
law privacy_token_stable:
  for +m: Tk.Book
  for +xs: List<&2, Tk.Piece>
  {Tk.scrub(Tk.Out.m(Tk.scrub(m, xs)), xs) == Tk.scrub(m, xs) : Tk.Out}

# LAW privacy_tokens_kept (R5): a token the map holds keeps its value
# after any text is scrubbed
# EXCLUDES: an index reused for a new value (an older answer restored to
#   the wrong value), a map that forgets
law privacy_tokens_kept:
  for +m: Tk.Book
  for +xs: List<&2, Tk.Piece>
  for +c: Tk.Class
  for +i: Nat
  for +v: String
  for +h: {Tk.restore_tok(m, c, i) == Some{v} : Maybe<&2, String>}
  {Tk.restore_tok(Tk.Out.m(Tk.scrub(m, xs)), c, i) == Some{v} : Maybe<&2, String>}

# Laws: the map as a state machine (R12)
# --------------------------------------

# LAW privacy_map_scrub_spec (R12, M1, M2): from every map whose classes
# hold no value twice, the tokens of a text's values, and the map after
# them, are the spec's: a held value keeps its place, a new one takes the
# next place of its class, a credential goes one way
# EXCLUDES: an index shared by classes or skipping places, a held value
#   given a new index, a value of another class taken for it, a
#   credential added to the map, a map that forgets or reorders
law privacy_map_scrub_spec:
  for +b: Tk.Book
  for +vs: List<&2, Tk.Val>
  for +ok: {Sm.book_distinct(b) == True{} : Bool}
  {Tk.scrub_vals(vs, b) == Sm.scrub_vals(vs, b) : Tk.Toks}

# LAW privacy_map_restore_spec (R12, M3): from every map, the values of a
# text's tokens are the spec's: the value at the token's place among its
# class's values, else none
# EXCLUDES: a token restored to a value of another class or place, a
#   credential restored, a place the map does not hold restored
law privacy_map_restore_spec:
  for +b: Tk.Book
  for +rs: List<&2, Tk.Ref>
  {Tk.restore_toks(rs, b) == Sm.restore_toks(rs, b) : List<&2, Maybe<&2, String>>}

# LAW privacy_map_distinct_kept (R12, M4): the map opens with no value
# held twice, and every scrub from such a map leaves one: every map the
# stepper can hold meets the premise of privacy_map_scrub_spec
# EXCLUDES: a vacuous scrub law (a premise the stepper's maps can fail)
law privacy_map_distinct_kept:
  for +b: Tk.Book
  for +vs: List<&2, Tk.Val>
  for +ok: {Sm.book_distinct(b) == True{} : Bool}
  {Sm.book_distinct(Tk.Book.empty()) == True{} : Bool} & {Sm.book_distinct(Sm.toks_book(Sm.scrub_vals(vs, b))) == True{} : Bool}

# Laws: a text over the map (R12, M5)
# -----------------------------------

# LAW privacy_scrub_text_spec (R12, M5): from every map whose classes hold
# no value twice, a text scrubbed is the spec's: each value replaced by
# the token of its place among its class's values, in the order they were
# first scrubbed, one index space per class from 1; and the map after it
# is the spec's
# EXCLUDES: one index space shared by every class (an EMAIL before an IP
#   making it IP_2), an index that skips, a text token that is not the
#   stepper's, a map that grows differently from the stepper's
law privacy_scrub_text_spec:
  for +m: Tk.Book
  for +xs: List<&2, Tk.Piece>
  for +ok: {Sm.book_distinct(m) == True{} : Bool}
  {Tk.scrub(m, xs) == Sm.scrub_text(xs, m) : Tk.Out}

# LAW privacy_scrub_text_stepper (R12, M5): from every map, a text scrubbed
# is the text with each value replaced by the token the stepper gives the
# text's values in one step, and the map after it is the stepper's
# EXCLUDES: a text scrubber and a stepper that number the same values
#   apart (a token Rust's text path sends that the stepper never issued)
law privacy_scrub_text_stepper:
  for +m: Tk.Book
  for +xs: List<&2, Tk.Piece>
  {Tk.scrub(m, xs) == Sm.text(xs, Tk.scrub_vals(Sm.vals(xs), m)) : Tk.Out}

# LAW privacy_restore_text_spec (R12, M3, M5): from every map, a text
# restored is the spec's: each token replaced by the value at its place
# among its class's values, when the class holds one there; every other
# piece as it was
# EXCLUDES: a token restored by a global index (IP_1 after an EMAIL left
#   as a token), a token of another class restored, a piece changed
law privacy_restore_text_spec:
  for +m: Tk.Book
  for +ys: List<&2, Tk.Seg>
  {Tk.restore(m, ys) == Sm.restore_text(ys, m) : List<&2, Tk.Seg>}

# LAW privacy_restore_tok_spec (R12, M3): from every map, the value of one
# token is the spec's
# EXCLUDES: a token value read by another index rule than the stepper's
law privacy_restore_tok_spec:
  for +m: Tk.Book
  for +c: Tk.Class
  for +i: Nat
  {Tk.restore_tok(m, c, i) == Sm.restore1(m, c, i) : Maybe<&2, String>}

# LAW privacy_send_spec (R6, R12, M5): from every map whose classes hold no
# value twice, the texts of a failover's attempts and the map after them
# are the spec's
# EXCLUDES: a remote attempt numbering tokens apart from the map, a map
#   after the failover that is not the one the attempts left
law privacy_send_spec:
  for +ts: List<&2, Bool>
  for +m: Tk.Book
  for +xs: List<&2, Tk.Piece>
  for +ok: {Sm.book_distinct(m) == True{} : Bool}
  {Tk.send(ts, m, xs) == Sm.send(ts, m, xs) : Tk.Sent}

# Laws: failover (R6)
# -------------------

# LAW privacy_failover_raw (R6): from every map, every attempt of a
# request sends the raw text: each remote attempt exactly the one scrub of
# it, each local attempt the text itself
# EXCLUDES: an attempt that sends the text another attempt sent (a scrub
#   of a scrub: tokens of tokens; a local sibling reading tokens), a
#   remote attempt in clear
law privacy_failover_raw:
  for +ts: List<&2, Bool>
  for +m: Tk.Book
  for +xs: List<&2, Tk.Piece>
  {Tk.Sent.yss(Tk.send(ts, m, xs)) == S.sends(ts, Tk.Out.ys(Tk.scrub(m, xs)), S.raw(xs)) : List<&2, List<&2, Tk.Seg>>}

# Anchors (R4-R6)
# ---------------

# a text: an IP address, a credential, a literal that reads as a token,
# the address again
def round_text() -> List<&2, Tk.Piece>:
  [Tk.Plain{"ssh "}, Tk.Value{Tk.Ip{}, "203.0.113.7"}, Tk.Plain{" key "}, Tk.Value{Tk.ApiKey{}, "sk-abc"}, Tk.Value{Tk.Ip{}, "IP_1"}, Tk.Value{Tk.Ip{}, "203.0.113.7"}]

# LAW privacy_round_trip_example (R5): anchor: the address takes IP 1 both
# times, the literal IP_1 takes IP 2, the key goes one way; restored, the
# address and the literal come back, the key stays hidden
# EXCLUDES: a literal token read as a token (restored to the address)
law privacy_round_trip_example:
  {Tk.Out.ys(Tk.scrub(Tk.Book.empty(), round_text())) == [Tk.Txt{"ssh "}, Tk.Tok{Tk.Ip{}, 1n}, Tk.Txt{" key "}, Tk.Hash{Tk.ApiKey{}, "sk-abc"}, Tk.Tok{Tk.Ip{}, 2n}, Tk.Tok{Tk.Ip{}, 1n}] : List<&2, Tk.Seg>} & {Tk.restore(Tk.Out.m(Tk.scrub(Tk.Book.empty(), round_text())), Tk.Out.ys(Tk.scrub(Tk.Book.empty(), round_text()))) == [Tk.Txt{"ssh "}, Tk.Clear{Tk.Ip{}, "203.0.113.7"}, Tk.Txt{" key "}, Tk.Hash{Tk.ApiKey{}, "sk-abc"}, Tk.Clear{Tk.Ip{}, "IP_1"}, Tk.Clear{Tk.Ip{}, "203.0.113.7"}] : List<&2, Tk.Seg>}

# LAW privacy_failover_example (R6): anchor: a remote primary, then a
# local sibling, then a remote one: the local sibling reads the address,
# both remote attempts send IP 1
# EXCLUDES: the local sibling reading the remote attempt's tokens
law privacy_failover_example:
  {Tk.Sent.yss(Tk.send([True{}, False{}, True{}], Tk.Book.empty(), [Tk.Plain{"ping "}, Tk.Value{Tk.Ip{}, "10.0.0.7"}])) == [[Tk.Txt{"ping "}, Tk.Tok{Tk.Ip{}, 1n}], [Tk.Txt{"ping "}, Tk.Clear{Tk.Ip{}, "10.0.0.7"}], [Tk.Txt{"ping "}, Tk.Tok{Tk.Ip{}, 1n}]] : List<&2, List<&2, Tk.Seg>>}

# an EMAIL, then an IP: each the first value of its class
def classes_text() -> List<&2, Tk.Piece>:
  [Tk.Value{Tk.Email{}, "ann@x.io"}, Tk.Plain{" from "}, Tk.Value{Tk.Ip{}, "203.0.113.7"}]

# LAW privacy_scrub_classes_example (R12, M5): anchor: an EMAIL and then an
# IP take EMAIL 1 and IP 1, and IP 1 restores the address
# EXCLUDES: one index space shared by every class (IP_2)
law privacy_scrub_classes_example:
  {Tk.Out.ys(Tk.scrub(Tk.Book.empty(), classes_text())) == [Tk.Tok{Tk.Email{}, 1n}, Tk.Txt{" from "}, Tk.Tok{Tk.Ip{}, 1n}] : List<&2, Tk.Seg>} & {Tk.restore_tok(Tk.Out.m(Tk.scrub(Tk.Book.empty(), classes_text())), Tk.Ip{}, 1n) == Some{"203.0.113.7"} : Maybe<&2, String>}
