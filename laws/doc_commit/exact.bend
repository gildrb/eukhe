# eukhe: the laws of area doc_commit, section exact: the move and the
# reply of an edit pinned whole to a spec (laws/doc_commit.bend states
# them only through membership premises and the files reported applied)

import Base
import ../../bend/doc_commit.bend as Cm
import ../doc_commit.bend as DocCommit

# (F5) A move, whole
# ------------------
# move_never_overwrites and move_moves take the model's has as given, and
# read the files after a move only through has and get: a has that is
# always False made both vacuous (an MV over an existing file passed), and
# a rename that deleted every other file passed. Every input is free: any
# files with any names and contents, any source and destination names.

# F5: some file is named n
def sp_has(+n: Nat, es: List<&2, Cm.Entry>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Cm.Entry{m, g}:
          Bool.or(Nat.is_eq(m, n), sp_has(n, rest))

def sp_get.of(b: Bool, g: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{g}
    case False{}:
      rest

# F5: the content of the first file named n (none when no file is)
def sp_get(+n: Nat, es: List<&2, Cm.Entry>) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      None{}
    case e <> rest:
      match e:
        case Cm.Entry{m, g}:
          sp_get.of(Nat.is_eq(m, n), g, sp_get(n, rest))

def sp_name(b: Bool, +t: Nat, m: Nat) -> Nat:
  match b:
    case True{}:
      t
    case False{}:
      m

# F5: every file named s takes the name t, in place, with its content;
# every other file is kept as it was
def sp_rename(+s: Nat, +t: Nat, es: List<&2, Cm.Entry>) -> List<&2, Cm.Entry>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Cm.Entry{+m, g}:
          Cm.Entry{sp_name(Nat.is_eq(m, s), t, m), g} <> sp_rename(s, t, rest)

def sp_move.of(taken: Bool, +s: Nat, +t: Nat, es: List<&2, Cm.Entry>) -> Cm.Mv:
  match taken:
    case True{}:
      Cm.Mv{False{}, es}
    case False{}:
      Cm.Mv{True{}, sp_rename(s, t, es)}

# F5: MV s t: refused, the files unchanged, when a file is named t;
# otherwise done, with the files renamed
def sp_move(+s: Nat, +t: Nat, +es: List<&2, Cm.Entry>) -> Cm.Mv:
  sp_move.of(sp_has(t, es), s, t, es)

# LAW move_tests_exact (F5): a file named n is there exactly when some
# file has that name, and the content of n is the content of the first
# file so named (none when no file is)
# EXCLUDES: a has that is always False (move_never_overwrites and
#   move_moves vacuous: an MV over an existing file) or always True; a has
#   or get that reads only one file; a get that answers another file's
#   content, the last match, or a content for a missing name
law move_tests_exact:
  for +n: Nat
  for +es: List<&2, Cm.Entry>
  {Cm.has(n, es) == sp_has(n, es) : Bool} & {Cm.get(n, es) == sp_get(n, es) : Maybe<&2, Nat>}

# LAW move_exact (F5): MV s t over the files es is refused, every file
# kept, when a file is named t; otherwise it is done, every file named s
# now named t with its content in its place, every other file kept as it
# was
# EXCLUDES: a has that is always False (MV over an existing file); a
#   rename that deletes, adds, reorders or changes another file, drops
#   the moved file's content, or renames only one of several files named
#   s; a refused move that changes the files; a done move reported refused
law move_exact:
  for +s: Nat
  for +t: Nat
  for +es: List<&2, Cm.Entry>
  {Cm.move(s, t, es) == sp_move(s, t, es) : Cm.Mv}

# (F1, F9) The reply of an edit, whole
# ------------------------------------
# edit_reports_what_landed and commit_answer_is_reply read the model's
# reply only through the files it reports applied: a reply that dropped a
# landed publish's warning (Applied{False} for Landed{True}) passed. The
# spec reads the reply off the fates of the model's files (sp_fates of
# laws/doc_commit.bend: each published until the first failure, the rest
# untried), as R3 reads the real one off its fates. Every input is free:
# any files, changed or not, each an update or a move, with any fault.

# F1: some file changed since the edit staged it
def sp_changed(fs: List<&2, Cm.Doc>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> rest:
      match f:
        case Cm.Doc{k, c, x}:
          Bool.or(c, sp_changed(rest))

# F9: whether a landed publish carries a warning
def sp_warned(w: Cm.Warn) -> Bool:
  match w:
    case Cm.NoWarn{}:
      False{}
    case Cm.SyncWarn{}:
      True{}
    case Cm.RemoveWarn{}:
      True{}

# F1: what the reply says of a file by its fate: applied, with the
# publish's warning, when its publish landed; not written otherwise (the
# model has no no-op file)
def sp_rep(f: Cm.Fate) -> Cm.Report:
  match f:
    case Cm.Noop{}:
      Cm.NotWritten{}
    case Cm.Wrote{o}:
      match o:
        case Cm.Lands{w}:
          Cm.Applied{sp_warned(w)}
        case Cm.Fails{}:
          Cm.NotWritten{}
    case Cm.Untried{}:
      Cm.NotWritten{}

def sp_reps(fs: List<&2, Cm.Fate>) -> List<&2, Cm.Report>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      sp_rep(f) <> sp_reps(rest)

# no publish among fs landed
def sp_quiet(fs: List<&2, Cm.Fate>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          sp_quiet(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              False{}
            case Cm.Fails{}:
              sp_quiet(rest)
        case Cm.Untried{}:
          sp_quiet(rest)

# R3: a publish failed and none landed
def sp_rejects(fs: List<&2, Cm.Fate>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          sp_rejects(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              False{}
            case Cm.Fails{}:
              sp_quiet(rest)
        case Cm.Untried{}:
          sp_rejects(rest)

def sp_reply.if(b: Bool, fs: List<&2, Cm.Fate>) -> Cm.Reply:
  match b:
    case True{}:
      Cm.Rejected{}
    case False{}:
      Cm.Answered{sp_reps(fs)}

# R3 on the model's reply: an error when a publish failed and none
# landed; otherwise one report a file
def sp_reply.fates(+fs: List<&2, Cm.Fate>) -> Cm.Reply:
  sp_reply.if(sp_rejects(fs), fs)

def sp_reply.pick(c: Bool, +fs: List<&2, Cm.Doc>) -> Cm.Reply:
  match c:
    case True{}:
      Cm.Rejected{}
    case False{}:
      sp_reply.fates(DocCommit.sp_fates(fs))

# F1, F9: the reply of an edit: an error when a file changed since it was
# staged (nothing was written); otherwise R3 on the files' fates
def sp_reply(+fs: List<&2, Cm.Doc>) -> Cm.Reply:
  sp_reply.pick(sp_changed(fs), fs)

# LAW edit_reply_exact (F1, F9): the reply of an edit is an error when a
# file changed since the edit staged it, or when the first publish failed
# so none landed; otherwise it reports each file applied, with its
# publish's warning, when its publish landed, and not written otherwise
# (its publish failed, or one before it did)
# EXCLUDES: a lost warning (Landed{w} reported Applied{False}) or an
#   invented one; an answer after a conflict or after nothing landed; an
#   error after a file landed; a file reported applied that failed or was
#   never tried, or the reverse; a report dropped, added or reordered
law edit_reply_exact:
  for +fs: List<&2, Cm.Doc>
  {Cm.reply(fs) == sp_reply(fs) : Cm.Reply}
