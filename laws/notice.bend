# eukhe: the laws of area notice

import Base
import ../bend/notice.bend as No

# The rank of a version, read by semver.bend's reader (the spec): the text
# before the first '-' read as a version X.Y.Z (Sv.Ver.parse: decimal
# numbers without leading zeros, three of them, nothing else) whose
# numbers have at most 14 digits; [X, Y, 0, Z] with a '-' (a prerelease),
# [X, Y, 1, Z] without; [] for any other text. A number of 15 digits or
# more is past the range of the compiled core's numbers (2^48 - 1): its
# version has no rank, as text that is no version. A text of more than 64
# chars has no rank either (no version is that long): the first 65 chars
# of any text decide its rank, so Rust sends only those.

# LAW notice_shown_once: an attach never shows a kernel restore notice again. After any
# restores, live notices and attaches (reconnects, worker restarts), in
# any order, each stored notice showed at most once (bend/notice.bend;
# the bridge is crates/eukhe-tui/src/restore_notices.rs)
law notice_shown_once:
  for +evs: List<&2, No.Ev>
  {No.once(No.run(evs)) == True{} : Bool}

# LAW notice_per_restore: restore notices do not accumulate. After any events and one more
# attach, the restore rows the view showed equal the restores
law notice_per_restore:
  for +evs: List<&2, No.Ev>
  {No.total(No.run(List.append(&2, No.Ev, evs, [No.Reconnect{}]))) == No.restores(evs) : Nat}
