# eukhe: the proof of LAW edit_reports_what_landed

import Base
import ../../bend/doc_commit.bend as Cm
import ../../LAWS.bend as Laws

# Edit
# ----

# with no publish, the reply applies no file
def pc.none_applied(fs: List<&2, Cm.Doc>, +n: Nat) -> {Cm.applied(Cm.report(fs, Nil{}), n) == Nil{} : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      pc.none_applied(rest, 1n+n)

def pc.step(-f: Cm.Doc, +rest: List<&2, Cm.Doc>, +n: Nat, o: Cm.Out, ih: {Cm.applied(Cm.report(rest, Cm.run(rest)), 1n+n) == Cm.landed.go(rest, 1n+n) : List<&2, Nat>}) -> {Cm.applied(Cm.report(f <> rest, Cm.run.put(o, Cm.run(rest))), n) == Cm.landed.put(n, Cm.landed.go(rest, 1n+n), o) : List<&2, Nat>}:
  match o:
    case Cm.Landed{w}:
      %ih : {n <> Cm.applied(Cm.report(rest, Cm.run(rest)), 1n+n) == n <> _ : List<&2, Nat>}
      {==}
    case Cm.Failed{}:
      pc.none_applied(rest, 1n+n)

# the reply built from the publishes applies the files that landed
def pc.reported(fs: List<&2, Cm.Doc>, +n: Nat) -> {Cm.applied(Cm.report(fs, Cm.run(fs)), n) == Cm.landed.go(fs, n) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      pc.step(f, rest, n, Cm.publish(f), pc.reported(rest, 1n+n))

def pc.go.step(-f: Cm.Doc, +rest: List<&2, Cm.Doc>, o: Cm.Out) -> {Cm.reported(Cm.reply.go(Cm.run.put(o, Cm.run(rest)), f <> rest)) == Cm.landed.put(0n, Cm.landed.go(rest, 1n), o) : List<&2, Nat>}:
  match o:
    case Cm.Landed{+w}:
      pc.step(f, rest, 0n, Cm.Landed{w}, pc.reported(rest, 1n))
    case Cm.Failed{}:
      {==}

def pc.go(fs: List<&2, Cm.Doc>) -> {Cm.reported(Cm.reply.go(Cm.run(fs), fs)) == Cm.landed.go(fs, 0n) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      pc.go.step(f, rest, Cm.publish(f))

def pc.pick(c: Bool, +fs: List<&2, Cm.Doc>) -> {Cm.reported(Cm.reply.pick(c, fs)) == Cm.landed.pick(c, fs) : List<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      pc.go(fs)

# the law edit_reports_what_landed
def pc.reports_what_landed(+fs: List<&2, Cm.Doc>) -> {Cm.reported(Cm.reply(fs)) == Cm.landed(fs) : List<&2, Nat>}:
  pc.pick(Cm.conflict(fs), fs)

# ---- documents_laws ----

# proof_documents_laws: the fills of the laws of LAWS.bend section documents
# (as Laws.<law>). The lemmas are in PROOF.bend section documents (edits,
# writes, moves, temporary files, seen lines, grep, continuations, tags)
# and PROOF.bend section doc_lines (lines and their endings).

# (F1, F9) An edit of many files

def Laws.edit_reports_what_landed(fs):
  pc.reports_what_landed(fs)
