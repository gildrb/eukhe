# eukhe: the proof of LAW commit_answer_spec
#
# PROOF: the spec's counts are three folds (dcw.cl, cx, cu); some publish
# landed (failed, some file is unwritten) exactly when its count is not
# zero; the notes and the first failure are the spec's file by file.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit

def dcw.pos(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      True{}

# how many publishes landed (cl), failed (cx); how many files were not
# written (cu)
def dcw.cl(fs: List<&2, Cm.Fate>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case f <> rest:
      match f:
        case Cm.Noop{}:
          dcw.cl(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              1n+dcw.cl(rest)
            case Cm.Fails{}:
              dcw.cl(rest)
        case Cm.Untried{}:
          dcw.cl(rest)

def dcw.cx(fs: List<&2, Cm.Fate>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case f <> rest:
      match f:
        case Cm.Noop{}:
          dcw.cx(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              dcw.cx(rest)
            case Cm.Fails{}:
              1n+dcw.cx(rest)
        case Cm.Untried{}:
          dcw.cx(rest)

def dcw.cu(fs: List<&2, Cm.Fate>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case f <> rest:
      match f:
        case Cm.Noop{}:
          dcw.cu(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              dcw.cu(rest)
            case Cm.Fails{}:
              1n+dcw.cu(rest)
        case Cm.Untried{}:
          1n+dcw.cu(rest)

def dcw.counts.add(f: Cm.Fate, -rest: List<&2, Cm.Fate>) -> {((dcw.cl(f <> rest), dcw.cx(f <> rest)), dcw.cu(f <> rest)) == DocCommit.sp_counts.add(f, dcw.cl(rest), dcw.cx(rest), dcw.cu(rest)) : (Nat & Nat) & Nat}:
  match f:
    case Cm.Noop{}:
      {==}
    case Cm.Wrote{o}:
      match o:
        case Cm.Lands{w}:
          {==}
        case Cm.Fails{}:
          {==}
    case Cm.Untried{}:
      {==}

# the spec's counts are cl, cx, cu
def dcw.counts(fs: List<&2, Cm.Fate>) -> {((dcw.cl(fs), dcw.cx(fs)), dcw.cu(fs)) == DocCommit.sp_counts(fs) : (Nat & Nat) & Nat}:
  match fs:
    case Nil{}:
      {==}
    case f <> +rest:
      %dcw.counts(rest) : {((dcw.cl(f <> rest), dcw.cx(f <> rest)), dcw.cu(f <> rest)) == DocCommit.sp_counts.of(f, _) : (Nat & Nat) & Nat}
      dcw.counts.add(f, rest)

def dcw.landed(fs: List<&2, Cm.Fate>) -> {dcw.pos(dcw.cl(fs)) == Cm.any.landed(fs) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          dcw.landed(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              {==}
            case Cm.Fails{}:
              dcw.landed(rest)
        case Cm.Untried{}:
          dcw.landed(rest)

def dcw.failed(fs: List<&2, Cm.Fate>) -> {dcw.pos(dcw.cx(fs)) == Cm.any.failed(fs) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          dcw.failed(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              dcw.failed(rest)
            case Cm.Fails{}:
              {==}
        case Cm.Untried{}:
          dcw.failed(rest)

def dcw.unwritten(fs: List<&2, Cm.Fate>) -> {Cm.unwritten(fs) == Nat.is_gt(dcw.cu(fs), 0n) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          dcw.unwritten(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              dcw.unwritten(rest)
            case Cm.Fails{}:
              {==}
        case Cm.Untried{}:
          {==}

def dcw.note(f: Cm.Fate, +k: Nat) -> {Cm.report.of(k, f) == DocCommit.sp_note(f, k) : Cm.Note}:
  match f:
    case Cm.Noop{}:
      {==}
    case Cm.Wrote{o}:
      match o:
        case Cm.Lands{w}:
          {==}
        case Cm.Fails{}:
          {==}
    case Cm.Untried{}:
      {==}

def dcw.notes(fs: List<&2, Cm.Fate>, +k: Nat) -> {Cm.reports(fs, k) == DocCommit.sp_notes(fs, k) : List<&2, Cm.Note>}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      %dcw.notes(rest, k) : {Cm.reports(f <> rest, k) == DocCommit.sp_note(f, k) <> _ : List<&2, Cm.Note>}
      %dcw.note(f, k) : {Cm.reports(f <> rest, k) == _ <> Cm.reports(rest, k) : List<&2, Cm.Note>}
      {==}

def dcw.first(fs: List<&2, Cm.Fate>, +n: Nat) -> {Cm.first.failed(fs, n) == DocCommit.sp_first(fs, n) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          dcw.first(rest, 1n+n)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              dcw.first(rest, 1n+n)
            case Cm.Fails{}:
              {==}
        case Cm.Untried{}:
          dcw.first(rest, 1n+n)

# the code's summary is the spec's
def dcw.summary(+fs: List<&2, Cm.Fate>) -> {Cm.Summary{Cm.reports(fs, Cm.first.failed(fs, 0n)), Cm.unwritten(fs)} == Cm.Summary{DocCommit.sp_notes(fs, DocCommit.sp_first(fs, 0n)), Nat.is_gt(dcw.cu(fs), 0n)} : Cm.Verdict}:
  %dcw.notes(fs, DocCommit.sp_first(fs, 0n)) : {Cm.Summary{Cm.reports(fs, Cm.first.failed(fs, 0n)), Cm.unwritten(fs)} == Cm.Summary{_, Nat.is_gt(dcw.cu(fs), 0n)} : Cm.Verdict}
  %dcw.first(fs, 0n) : {Cm.Summary{Cm.reports(fs, Cm.first.failed(fs, 0n)), Cm.unwritten(fs)} == Cm.Summary{Cm.reports(fs, _), Nat.is_gt(dcw.cu(fs), 0n)} : Cm.Verdict}
  %dcw.unwritten(fs) : {Cm.Summary{Cm.reports(fs, Cm.first.failed(fs, 0n)), Cm.unwritten(fs)} == Cm.Summary{Cm.reports(fs, Cm.first.failed(fs, 0n)), _} : Cm.Verdict}
  {==}

# the verdict on the counts
def dcw.verdict(l: Nat, x: Nat, +fs: List<&2, Cm.Fate>, -u: Nat, es: {Cm.Summary{Cm.reports(fs, Cm.first.failed(fs, 0n)), Cm.unwritten(fs)} == Cm.Summary{DocCommit.sp_notes(fs, DocCommit.sp_first(fs, 0n)), Nat.is_gt(u, 0n)} : Cm.Verdict}) -> {Cm.answer.go(Bool.and(dcw.pos(x), Bool.not(dcw.pos(l))), fs) == DocCommit.sp_answer.of(fs, ((l, x), u)) : Cm.Verdict}:
  match l:
    case 0n:
      match x:
        case 0n:
          es
        case 1n+y:
          {==}
    case 1n+m:
      match x:
        case 0n:
          es
        case 1n+y:
          es

def dcw.answer(+fs: List<&2, Cm.Fate>) -> {Cm.answer(fs) == DocCommit.sp_answer(fs) : Cm.Verdict}:
  %dcw.counts(fs) : {Cm.answer(fs) == DocCommit.sp_answer.of(fs, _) : Cm.Verdict}
  %dcw.failed(fs) : {Cm.answer.go(Bool.and(_, Bool.not(Cm.any.landed(fs))), fs) == DocCommit.sp_answer.of(fs, ((dcw.cl(fs), dcw.cx(fs)), dcw.cu(fs))) : Cm.Verdict}
  %dcw.landed(fs) : {Cm.answer.go(Bool.and(dcw.pos(dcw.cx(fs)), Bool.not(_)), fs) == DocCommit.sp_answer.of(fs, ((dcw.cl(fs), dcw.cx(fs)), dcw.cu(fs))) : Cm.Verdict}
  dcw.verdict(dcw.cl(fs), dcw.cx(fs), fs, dcw.cu(fs), dcw.summary(fs))

def DocCommit.commit_answer_spec(fs):
  dcw.answer(fs)
