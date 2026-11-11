# eukhe: the proof of LAW approvals_desk_ask
# PROOF: the session's decision computes for each kind of session (an
# interactive client: show; no client and a parent: relay; a root with no
# client: no one answers, unanswered), and the ask keeps the question, last,
# under the next key.

import Base
import ../../laws/approvals/desk.bend as ApprovalsDesk

def ApprovalsDesk.approvals_desk_ask(n, qs, id, es, p):
  ({==}, {==}, {==})
