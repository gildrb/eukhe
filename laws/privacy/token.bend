# eukhe: the laws of area privacy, section token: the token map of the
# outbound scrubber, a text scrubbed and restored, and the texts a
# failover sends (bend/privacy/token.bend)

import Base
import ../../bend/privacy/token.bend as Tk
import ../../spec/harness/privacy.bend as S

# (H7) The outbound scrubber gives every byte back
# ------------------------------------------------
# spec/README.md H7. The scrubber once hashed IP addresses one way: the
# model read the token, wrote it back in an edit, and the file kept it.
# And the failover re-dispatch scrubbed the already scrubbed context, so a
# local sibling read tokens. The token map now runs as the compiled core
# (bend/ffi_privacy.bend's stepper, held by eukhe-ai privacy/mod.rs for
# the daemon's life): one step asks the tokens of a text's values
# (Tk.scrub_vals), one the values of a text's tokens (Tk.restore_toks); a
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
