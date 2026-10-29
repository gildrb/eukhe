import Mathlib

/-!
# eukhe: the durability port (Pi Durable) — the commit log

This file is the Lean 4 formalization of the durable storage of an eukhe
session: the append-only commit log `main.jsonl`, under power loss at any
point. It is the Lean counterpart of the Bend model in `spec/log.bend` and
the laws in `laws/log.bend` of `gildrb/eukhe`.

The model, in three parts (as `bendtt.lean`):

1. THEORY: the bytes and lines of the log, the parse (open reads the
   complete lines and cuts the torn tail), the disk, and one epoch (an open,
   its commits, and a crash).
2. CLAIMS: the crash-safety laws — open reads exactly the complete lines;
   a crash at any point never loses an acknowledged commit; and the log
   only ever holds a prefix of the commits, in order.
3. PROOF: the lemmas, in order.

A file is a list of bytes; `0` is the newline that ends a line, and a data
byte is `1 + b`. A line holds the bytes `1 + b` of its content `b..`; a
commit is one line. Open reads the complete lines and cuts the torn tail
(the bytes after the last newline).

One epoch is one open of the storage (with fsync on), its commits, and a
crash. The file system does each step in order and the crash comes after the
first `p` of them:

  open:    flush the parent directory (the storage directory's entry)
  commit:  append its line, flush the file, flush the storage directory
           (the first commit of the epoch only: the file's entry), and then
           acknowledge it

A crash keeps the flushed bytes and the first `k` bytes not flushed (any
prefix: a torn tail when `k` ends inside a line). When `drop` is set, a
crash also loses each directory entry not flushed: then the file is gone
unless both entries are durable. After the crash, what is on disk is the
start of the next epoch.
-/

open scoped BigOperators

-- THEORY
-- ======

-- Bytes and lines
-- ---------------

-- the bytes of a content: each b is written as 1 + b
def data (l : List Nat) : List Nat := l.map (· + 1)

-- one line: its data bytes and the newline
def line (l : List Nat) : List Nat := data l ++ [0]

-- the bytes of lines
def render (ls : List (List Nat)) : List Nat :=
  match ls with
  | [] => []
  | l :: rest => line l ++ render rest

-- A parse: the complete lines, and the tail after the last newline
structure P where
  ls : List (List Nat)
  t : List Nat

-- parse a file's bytes into complete lines (oldest first) and a torn tail
def P.go (f : List Nat) (cur : List Nat) (ls : List (List Nat)) : P :=
  match f with
  | [] => ⟨ls, cur⟩
  | b :: rest =>
      if b = 0 then
        P.go rest [] (cur :: ls)
      else
        P.go rest (cur ++ [b - 1]) ls

def parse (f : List Nat) : P :=
  let p := P.go f [] []
  ⟨p.ls.reverse, p.t⟩

-- what open reads: the complete lines; the torn tail is cut
def recover (f : List Nat) : List (List Nat) := (parse f).ls

-- The disk
-- --------

inductive Disk
  | absent
  | present (bytes : List Nat)

-- the log that an open of the disk reads
def Disk.log (d : Disk) : List (List Nat) :=
  match d with
  | .absent => []
  | .present b => recover b

-- One epoch
-- ---------

-- the storage while it runs: the storage directory's entry is durable (de),
-- the file's entry is durable (fe), the flushed lines, the line appended and
-- not flushed, the acknowledged commits
structure St where
  de : Bool
  fe : Bool
  log : List (List Nat)
  pend : Option (List Nat)
  acked : List (List Nat)

-- open: a file that is there has durable entries (the crash before kept
-- them); its torn tail is cut
def openSt (d : Disk) : St :=
  match d with
  | .absent => ⟨false, false, [], none, []⟩
  | .present b => ⟨true, true, recover b, none, []⟩

def parent (s : St) : St := { s with de := true }

def append (c : List Nat) (s : St) : St := { s with pend := some c }

def flush (s : St) : St :=
  { s with
    log := s.log ++ match s.pend with | none => [] | some l => [l]
    pend := none }

def dir (s : St) : St := { s with fe := true }

def ackCommit (c : List Nat) (s : St) : St := { s with acked := s.acked ++ [c] }

-- the commits after the first, with p steps left: append, flush, ack
def more (cs : List (List Nat)) (p : Nat) (s : St) : St :=
  match cs with
  | [] => s
  | c :: rest =>
      match p with
      | 0 => s
      | p1 + 1 =>
          match p1 with
          | 0 => append c s
          | p2 + 1 => more rest p2 (ackCommit c (flush (append c s)))

-- the first commit, with q steps left: append, flush, flush the directory,
-- ack
def first (cs : List (List Nat)) (q : Nat) (s : St) : St :=
  match cs with
  | [] => s
  | c :: rest =>
      match q with
      | 0 => s
      | q1 + 1 =>
          match q1 with
          | 0 => append c s
          | q2 + 1 =>
              match q2 with
              | 0 => flush (append c s)
              | q3 + 1 => more rest q3 (ackCommit c (dir (flush (append c s))))

-- an epoch's run up to the crash, after p steps
def run (d : Disk) (cs : List (List Nat)) (p : Nat) : St :=
  match p with
  | 0 => openSt d
  | q + 1 => first cs q (parent (openSt d))

-- the bytes not flushed that a crash keeps
def cut (k : Nat) (m : Option (List Nat)) : List Nat :=
  match m with
  | none => []
  | some l => (line l).take k

-- whether the file outlives the crash
def keeps (drop : Bool) (de fe : Bool) : Bool :=
  if drop then de && fe else true

def stays (b : Bool) (bytes : List Nat) : Disk :=
  if b then .present bytes else .absent

-- the disk after an epoch
def crash (k : Nat) (drop : Bool) (s : St) : Disk :=
  stays (keeps drop s.de s.fe) (render s.log ++ cut k s.pend)

structure Epoch where
  cs : List (List Nat)
  p : Nat
  k : Nat
  drop : Bool

def after (d : Disk) (e : Epoch) : Disk :=
  crash e.k e.drop (run d e.cs e.p)

-- the commits an epoch acknowledged
def acked (d : Disk) (e : Epoch) : List (List Nat) :=
  (run d e.cs e.p).acked

-- PROOF
-- ======

-- processing data bytes (no newlines) with a starting cursor: the cursor
-- accumulates the content bytes, and no lines are produced
theorem P.go_data_cur (l : List Nat) (cur0 : List Nat) :
    P.go (data l) cur0 [] = ⟨[], cur0 ++ l⟩ := by
  induction l generalizing cur0 with
  | nil => simp [P.go, data]
  | cons b ls' ih =>
    simp [P.go, data]
    simpa [data] using ih (cur0 ++ [b])

-- a newline closes the current line and prepends it to the line list
theorem P.go_newline (x : List Nat) (cur0 : List Nat) (ls0 : List (List Nat)) :
    P.go ([0] ++ x) cur0 ls0 = P.go x [] (cur0 :: ls0) := by
  simp [P.go]

-- processing (a ++ b) is processing a, then b from where a left off
theorem P.go_append (a b : List Nat) (cur0 : List Nat) (ls0 : List (List Nat)) :
    P.go (a ++ b) cur0 ls0 = P.go b (P.go a cur0 ls0).t (P.go a cur0 ls0).ls := by
  induction a generalizing cur0 ls0 with
  | nil => simp [P.go]
  | cons c as ih =>
    rw [List.cons_append]
    by_cases hc : c = 0
    · -- c = 0: a newline
      have h1 : P.go (c :: (as ++ b)) cur0 ls0 = P.go (as ++ b) [] (cur0 :: ls0) := by
        simp [P.go, hc]
      have h2 : P.go (c :: as) cur0 ls0 = P.go as [] (cur0 :: ls0) := by
        simp [P.go, hc]
      have h3 : P.go (as ++ b) [] (cur0 :: ls0) =
          P.go b (P.go as [] (cur0 :: ls0)).t (P.go as [] (cur0 :: ls0)).ls :=
        ih [] (cur0 :: ls0)
      rw [h1, h2, h3]
    · -- c is a data byte
      have h1 : P.go (c :: (as ++ b)) cur0 ls0 = P.go (as ++ b) (cur0 ++ [c - 1]) ls0 := by
        simp [P.go, hc]
      have h2 : P.go (c :: as) cur0 ls0 = P.go as (cur0 ++ [c - 1]) ls0 := by
        simp [P.go, hc]
      have h3 : P.go (as ++ b) (cur0 ++ [c - 1]) ls0 =
          P.go b (P.go as (cur0 ++ [c - 1]) ls0).t (P.go as (cur0 ++ [c - 1]) ls0).ls :=
        ih (cur0 ++ [c - 1]) ls0
      rw [h1, h2, h3]

-- processing x with a starting line-list ls0: the lines of x (in reverse)
-- are prepended to ls0, and the tail is the one from the empty start
theorem P.go_append_ls (x : List Nat) (cur0 : List Nat) (ls0 : List (List Nat)) :
    P.go x cur0 ls0 = ⟨(P.go x cur0 []).ls ++ ls0, (P.go x cur0 []).t⟩ := by
  induction x generalizing cur0 ls0 with
  | nil => simp [P.go]
  | cons b xs ih =>
    by_cases hb : b = 0
    · -- b = 0: a newline closes the current line
      have h1 : P.go (b :: xs) cur0 ls0 = P.go xs [] (cur0 :: ls0) := by
        simp [P.go, hb]
      have h2 : P.go (b :: xs) cur0 [] = P.go xs [] [cur0] := by
        simp [P.go, hb]
      have h3 : P.go xs [] (cur0 :: ls0) =
          ⟨(P.go xs [] []).ls ++ (cur0 :: ls0), (P.go xs [] []).t⟩ := ih [] (cur0 :: ls0)
      have h4 : P.go xs [] [cur0] = ⟨(P.go xs [] []).ls ++ [cur0], (P.go xs [] []).t⟩ :=
        ih [] [cur0]
      rw [h1, h3, h2, h4]
      simp [List.append_assoc]
    · -- b is a data byte
      have h1 : P.go (b :: xs) cur0 ls0 = P.go xs (cur0 ++ [b - 1]) ls0 := by
        simp [P.go, hb]
      have h2 : P.go (b :: xs) cur0 [] = P.go xs (cur0 ++ [b - 1]) [] := by
        simp [P.go, hb]
      have h3 : P.go xs (cur0 ++ [b - 1]) ls0 =
          ⟨(P.go xs (cur0 ++ [b - 1]) []).ls ++ ls0, (P.go xs (cur0 ++ [b - 1]) []).t⟩ :=
        ih (cur0 ++ [b - 1]) ls0
      have h4 : P.go xs (cur0 ++ [b - 1]) [] =
          ⟨(P.go xs (cur0 ++ [b - 1]) []).ls ++ [], (P.go xs (cur0 ++ [b - 1]) []).t⟩ :=
        ih (cur0 ++ [b - 1]) []
      rw [h1, h3, h2, h4]

-- a line l (encoded as data l ++ [0]) followed by x: the line l, then the
-- parse of x. Holds for every l, including the empty line.
theorem parse_line (l : List Nat) (x : List Nat) :
    parse (data l ++ [0] ++ x) = ⟨l :: (parse x).ls, (parse x).t⟩ := by
  have h1 : P.go (data l ++ [0] ++ x) [] [] = P.go x [] [l] := by
    have h2 : P.go (data l ++ [0]) [] [] = ⟨[l], []⟩ := by
      have h3 : P.go (data l) [] [] = ⟨[], l⟩ := by simpa using P.go_data_cur l []
      have h4 : P.go (data l ++ [0]) [] [] = P.go [0] l [] := by
        simpa [h3] using P.go_append (data l) [0] [] []
      have h5 : P.go [0] l [] = ⟨[l], []⟩ := by
        simp [P.go]
      exact (h4.trans h5)
    have h3 : P.go (data l ++ [0] ++ x) [] [] =
        P.go x (P.go (data l ++ [0]) [] []).t (P.go (data l ++ [0]) [] []).ls :=
      P.go_append (data l ++ [0]) x [] []
    rw [h2] at h3
    simpa using h3
  have h2 : P.go x [] [l] = ⟨(P.go x [] []).ls ++ [l], (P.go x [] []).t⟩ := by
    simpa using P.go_append_ls x [] [l]
  have h4 : (P.go x [] []).ls.reverse = (parse x).ls := by simp [parse]
  have h5 : ((P.go x [] []).ls ++ [l]).reverse = l :: (P.go x [] []).ls.reverse := by
    simp [List.reverse_append]
  have hassoc : data l ++ (0 :: x) = (data l ++ [0]) ++ x := by
    calc
      data l ++ (0 :: x) = data l ++ ([0] ++ x) := by rfl
      _ = (data l ++ [0]) ++ x := by rw [← List.append_assoc]
  simp [parse]
  rw [hassoc]
  rw [h1, h2]
  simp

-- data has no newline, so it parses to no lines and the whole (decoded) tail
theorem parse_data (t : List Nat) : parse (data t) = ⟨[], t⟩ := by
  have h : P.go (data t) [] [] = ⟨[], t⟩ := by simpa using P.go_data_cur t []
  simp [parse, h]

-- the parse of rendered lines followed by a data tail: the lines, then the
-- (decoded) tail
theorem parse_render (ls : List (List Nat)) (t : List Nat) :
    parse (render ls ++ data t) = ⟨ls, t⟩ := by
  induction ls with
  | nil =>
    simp [render, parse_data]
  | cons l rest ih =>
    have hrender : render (l :: rest) = line l ++ render rest := by simp [render]
    rw [hrender]
    have hx : line l = data l ++ [0] := by simp [line]
    rw [hx]
    have hline : parse (data l ++ [0] ++ render rest ++ data t) =
        ⟨l :: (parse (render rest ++ data t)).ls, (parse (render rest ++ data t)).t⟩ := by
      simpa using parse_line l (render rest ++ data t)
    have himh : parse (render rest ++ data t) = ⟨rest, t⟩ := ih
    rw [hline, himh]

-- LAW log_reads_lines: open reads exactly the complete lines, in order; a
-- torn tail (the bytes after the last newline) is never read as an entry.
theorem log_reads_lines (ls : List (List Nat)) (t : List Nat) :
    recover (render ls ++ data t) = ls := by
  have h : parse (render ls ++ data t) = ⟨ls, t⟩ := parse_render ls t
  simp [recover, h]

-- open reads exactly the disk's log
theorem openSt_log (d : Disk) : (openSt d).log = Disk.log d := by
  cases d with
  | absent => simp [openSt, Disk.log]
  | present b => simp [openSt, Disk.log]

-- more: the log only grows by a prefix of the commits
theorem more_log (cs : List (List Nat)) (p : Nat) (s : St) :
    ∃ i, (more cs p s).log = s.log ++ (cs).take i := by
  induction cs generalizing p s with
  | nil => exact ⟨0, by simp [more]⟩
  | cons c rest ih =>
    induction p with
    | zero => exact ⟨0, by simp [more]⟩
    | succ p1 =>
      induction p1 with
      | zero => exact ⟨0, by simp [more, append]⟩
      | succ p2 =>
        obtain ⟨i, hi⟩ := ih p2 (ackCommit c (flush (append c s)))
        exact ⟨1 + i, by
          calc
            (more (c :: rest) (p2 + 2) s).log
                = (more rest p2 (ackCommit c (flush (append c s)))).log := by
                  simp [more]
            _ = (ackCommit c (flush (append c s))).log ++ rest.take i := hi
            _ = (s.log ++ [c]) ++ rest.take i := by
                  simp [ackCommit, flush, append]
            _ = s.log ++ ([c] ++ rest.take i) := by
                  rw [List.append_assoc]
            _ = s.log ++ (c :: rest.take i) := rfl
            _ = s.log ++ (c :: rest).take (1 + i) := by
                  congr
                  rw [Nat.add_comm, List.take_cons (Nat.succ_pos i), Nat.succ_sub_one]⟩

-- first: the log only grows by a prefix of the commits
theorem first_log (cs : List (List Nat)) (q : Nat) (s : St) :
    ∃ i, (first cs q s).log = s.log ++ (cs).take i := by
  induction cs generalizing q s with
  | nil => exact ⟨0, by simp [first]⟩
  | cons c rest ih =>
    induction q with
    | zero => exact ⟨0, by simp [first]⟩
    | succ q1 =>
      induction q1 with
      | zero => exact ⟨0, by simp [first, append]⟩
      | succ q2 =>
        induction q2 with
        | zero => exact ⟨1, by simp [first, flush, append, List.take_add_one]⟩
        | succ q3 =>
          obtain ⟨i, hi⟩ := more_log rest q3 (ackCommit c (dir (flush (append c s))))
          exact ⟨1 + i, by
            calc
              (first (c :: rest) (q3 + 3) s).log
                  = (more rest q3 (ackCommit c (dir (flush (append c s))))).log := by
                        simp [first]
              _ = (ackCommit c (dir (flush (append c s)))).log ++ rest.take i := hi
              _ = (s.log ++ [c]) ++ rest.take i := by
                        simp [ackCommit, dir, flush, append]
              _ = s.log ++ ([c] ++ rest.take i) := by
                        rw [List.append_assoc]
              _ = s.log ++ (c :: rest.take i) := rfl
              _ = s.log ++ (c :: rest).take (1 + i) := by
                        congr
                        rw [Nat.add_comm, List.take_cons (Nat.succ_pos i), Nat.succ_sub_one]⟩

-- run: the log is the old log plus a prefix of the commits
theorem run_log (d : Disk) (cs : List (List Nat)) (p : Nat) :
    ∃ i, (run d cs p).log = Disk.log d ++ (cs).take i := by
  induction p with
  | zero =>
    exact ⟨0, by simp [run, openSt_log]⟩
  | succ q =>
    obtain ⟨i, hi⟩ := first_log cs q (parent (openSt d))
    exact ⟨i, by
      have h1 : run d cs (q + 1) = first cs q (parent (openSt d)) := by
        simp [run]
      rw [h1, hi]
      have h2 : (parent (openSt d)).log = Disk.log d := by
        simp [parent, openSt_log]
      rw [h2]⟩

-- rendering lines then one more line is rendering the appended list
theorem render_append_one (ls : List (List Nat)) (l : List Nat) :
    render ls ++ line l = render (ls ++ [l]) := by
  induction ls with
  | nil => simp [render, line]
  | cons l1 rest ih =>
    simp [render, line, List.cons_append]
    simpa [line] using ih

-- recover of rendered lines plus a cut: the lines, plus maybe the pending line
theorem recover_render_cut (ls : List (List Nat)) (k : Nat) (m : Option (List Nat)) :
    recover (render ls ++ cut k m) = ls ∨
    (∃ l, m = some l ∧ recover (render ls ++ cut k m) = ls ++ [l]) := by
  cases m with
  | none =>
    have h : parse (render ls) = ⟨ls, []⟩ := by
      simpa [data] using parse_render ls []
    exact Or.inl (by simp [cut, recover, h])
  | some l =>
    have hline : line l = data l ++ [0] := by simp [line]
    by_cases hk : k ≤ (data l).length
    · -- the cut is a prefix of the data bytes (no newline): no complete line
      have hcut : (line l).take k = (data l).take k := by
        rw [hline]
        simp [List.take_eq_left_iff, hk]
      have htake : (data l).take k = data (l.take k) := by
        simp [data, List.map_take]
      have hparse : parse (render ls ++ (data l).take k) = ⟨ls, l.take k⟩ := by
        simpa [htake] using parse_render ls (l.take k)
      exact Or.inl (by
        simp [cut, recover]
        rw [hcut, hparse])
    · -- the cut includes the newline: the whole line
      have hlt : (data l).length < k := by
        simpa [Nat.not_le] using hk
      have hlen : (line l).length = (data l).length + 1 := by
        simp [line, List.length_append, List.length_cons]
      have h : (line l).length ≤ k := by
        rw [hlen]
        omega
      have hcut : (line l).take k = line l := by
        exact (List.take_of_length_le h)
      have hrender : render ls ++ line l = render (ls ++ [l]) := render_append_one ls l
      have hparse : parse (render ls ++ line l) = ⟨ls ++ [l], []⟩ := by
        rw [hrender]
        simpa [data] using parse_render (ls ++ [l]) []
      exact Or.inr ⟨l, rfl, by
        simp [cut, recover]
        rw [hcut, hparse]⟩

-- more never changes the durable flags
theorem more_de (cs : List (List Nat)) (p : Nat) (s : St) : (more cs p s).de = s.de := by
  induction cs generalizing p s with
  | nil => simp [more]
  | cons c rest ih =>
    induction p with
    | zero => simp [more]
    | succ p1 =>
      induction p1 with
      | zero => simp [more, append]
      | succ p2 =>
        have h1 : more (c :: rest) (p2 + 2) s = more rest p2 (ackCommit c (flush (append c s))) := by
          simp [more]
        rw [h1, ih p2 (ackCommit c (flush (append c s)))]
        simp [ackCommit, flush, append]

theorem more_fe (cs : List (List Nat)) (p : Nat) (s : St) : (more cs p s).fe = s.fe := by
  induction cs generalizing p s with
  | nil => simp [more]
  | cons c rest ih =>
    induction p with
    | zero => simp [more]
    | succ p1 =>
      induction p1 with
      | zero => simp [more, append]
      | succ p2 =>
        have h1 : more (c :: rest) (p2 + 2) s = more rest p2 (ackCommit c (flush (append c s))) := by
          simp [more]
        rw [h1, ih p2 (ackCommit c (flush (append c s)))]
        simp [ackCommit, flush, append]

-- first never changes de, and keeps fe true if it started true
theorem first_de (cs : List (List Nat)) (q : Nat) (s : St) : (first cs q s).de = s.de := by
  induction cs generalizing q s with
  | nil => simp [first]
  | cons c rest ih =>
    induction q with
    | zero => simp [first]
    | succ q1 =>
      induction q1 with
      | zero => simp [first, append]
      | succ q2 =>
        induction q2 with
        | zero => simp [first, flush, append]
        | succ q3 =>
          have h1 : first (c :: rest) (q3 + 3) s =
              more rest q3 (ackCommit c (dir (flush (append c s)))) := by
            simp [first]
          rw [h1, more_de rest q3 (ackCommit c (dir (flush (append c s))))]
          simp [ackCommit, dir, flush, append]

theorem first_fe_true (cs : List (List Nat)) (q : Nat) (s : St) (h : s.fe = true) :
    (first cs q s).fe = true := by
  induction cs generalizing q s h with
  | nil => simp [first, h]
  | cons c rest ih =>
    induction q with
    | zero => simp [first, h]
    | succ q1 =>
      induction q1 with
      | zero => simp [first, append, h]
      | succ q2 =>
        induction q2 with
        | zero => simp [first, flush, append, h]
        | succ q3 =>
          have h1 : first (c :: rest) (q3 + 3) s =
              more rest q3 (ackCommit c (dir (flush (append c s)))) := by
            simp [first]
          rw [h1, more_fe rest q3 (ackCommit c (dir (flush (append c s))))]
          simp [ackCommit, dir, flush, append]

-- a present disk keeps durable flags through the whole run
theorem run_present_de (b : List Nat) (cs : List (List Nat)) (p : Nat) :
    (run (Disk.present b) cs p).de = true := by
  induction p with
  | zero => simp [run, openSt]
  | succ q =>
    have h1 : run (Disk.present b) cs (q + 1) =
        first cs q (parent (openSt (Disk.present b))) := by
      simp [run]
    rw [h1, first_de cs q (parent (openSt (Disk.present b)))]
    simp [parent, openSt]

theorem run_present_fe (b : List Nat) (cs : List (List Nat)) (p : Nat) :
    (run (Disk.present b) cs p).fe = true := by
  induction p with
  | zero => simp [run, openSt]
  | succ q =>
    have h1 : run (Disk.present b) cs (q + 1) =
        first cs q (parent (openSt (Disk.present b))) := by
      simp [run]
    rw [h1]
    exact first_fe_true cs q (parent (openSt (Disk.present b))) (by simp [parent, openSt])

-- if the file does not survive the crash, the disk before was absent
theorem keeps_false_absent (d : Disk) (cs : List (List Nat)) (p : Nat) (drop : Bool) :
    ¬ keeps drop (run d cs p).de (run d cs p).fe → d = Disk.absent := by
  intro h
  cases d with
  | present b =>
    have hde : (run (Disk.present b) cs p).de = true := run_present_de b cs p
    have hfe : (run (Disk.present b) cs p).fe = true := run_present_fe b cs p
    simp [keeps, hde, hfe] at h
  | absent => rfl

-- if the first commit's directory entry was never written (fe stays false),
-- then no commit was acknowledged: the first ack sits behind the dir step,
-- and the later commits sit behind the first ack
theorem first_fe_false_acked_empty (cs : List (List Nat)) (q : Nat) (s0 : St)
    (h0 : s0.acked = []) :
    (first cs q s0).fe = false → (first cs q s0).acked = [] := by
  induction cs generalizing q s0 h0 with
  | nil =>
    intro hfe
    simp [first] at hfe ⊢
    exact h0
  | cons c rest ih =>
    induction q with
    | zero =>
      intro hfe
      simp [first] at hfe ⊢
      exact h0
    | succ q1 =>
      induction q1 with
      | zero =>
        intro hfe
        simp [first, append] at hfe ⊢
        exact h0
      | succ q2 =>
        induction q2 with
        | zero =>
          intro hfe
          simp [first, flush, append] at hfe ⊢
          exact h0
        | succ q3 =>
          intro hfe
          have h : first (c :: rest) (q3 + 3) s0 =
              more rest q3 (ackCommit c (dir (flush (append c s0)))) := by
            simp [first]
          rw [h] at hfe ⊢
          have hfe' : (more rest q3 (ackCommit c (dir (flush (append c s0))))).fe =
              (ackCommit c (dir (flush (append c s0)))).fe :=
            more_fe rest q3 (ackCommit c (dir (flush (append c s0))))
          rw [hfe'] at hfe
          have hdir : (ackCommit c (dir (flush (append c s0)))).fe = true := by
            simp [ackCommit, dir, flush, append]
          rw [hdir] at hfe
          contradiction

-- if the disk was absent and the file does not survive the crash, then no
-- commit was acknowledged: surviving needs the directory entry (de) and the
-- file entry (fe), and the first ack is written only once both are durable
theorem run_absent_keeps_false_acked_empty (cs : List (List Nat)) (p : Nat)
    (drop : Bool) :
    ¬ keeps drop (run Disk.absent cs p).de (run Disk.absent cs p).fe →
      (run Disk.absent cs p).acked = [] := by
  induction p with
  | zero =>
    intro h
    simp [run, openSt]
  | succ q =>
    intro h
    have h1 : run Disk.absent cs (q + 1) =
        first cs q (parent (openSt Disk.absent)) := by
      simp [run]
    rw [h1] at h ⊢
    have hs : parent (openSt Disk.absent) = ⟨true, false, [], none, []⟩ := by
      simp [parent, openSt]
    rw [hs] at h ⊢
    have hde : (first cs q ⟨true, false, [], none, []⟩).de = true := by
      simp [first_de]
    have hfe : (first cs q ⟨true, false, [], none, []⟩).fe = false := by
      cases drop with
      | true => simp [keeps, hde] at h; exact h
      | false => simp [keeps] at h
    exact first_fe_false_acked_empty cs q ⟨true, false, [], none, []⟩ (by simp) hfe

-- the log grows by a prefix of the commits, and the pending line (if any)
-- is exactly the next commit after that prefix

-- if l is the next commit after a prefix of rest of length i, then it is
-- also the next commit after the prefix c :: rest of length i + 1
theorem take_succ_cons (c : List Nat) (rest : List (List Nat)) (i : Nat) (l : List Nat)
    (h : rest.take (i + 1) = rest.take i ++ [l]) :
    (c :: rest).take (1 + i + 1) = (c :: rest).take (1 + i) ++ [l] := by
  have h1 : (c :: rest).take (1 + i + 1) = c :: rest.take (1 + i) := by
    rw [List.take_cons (Nat.succ_pos (1 + i)), Nat.succ_sub_one]
  have h2 : (c :: rest).take (1 + i) = c :: rest.take i := by
    rw [Nat.add_comm, List.take_cons (Nat.succ_pos i), Nat.succ_sub_one]
  rw [h1, h2]
  have h3 : rest.take (1 + i) = rest.take i ++ [l] := by
    rw [Nat.add_comm]
    exact h
  rw [h3]
  simp [List.cons_append]

theorem more_inv (cs : List (List Nat)) (p : Nat) (s0 : St) (h0 : s0.pend = none) :
    ∃ i, (more cs p s0).log = s0.log ++ cs.take i ∧
      ((more cs p s0).pend = none ∨
       ∃ l, (more cs p s0).pend = some l ∧ cs.take (i + 1) = cs.take i ++ [l]) := by
  induction cs generalizing p s0 h0 with
  | nil =>
    exact ⟨0, by
      have h : more [] p s0 = s0 := by simp [more]
      rw [h]
      exact ⟨by simp, by left; exact h0⟩⟩
  | cons c rest ih =>
    induction p with
    | zero =>
      exact ⟨0, by
        have h : more (c :: rest) 0 s0 = s0 := by simp [more]
        rw [h]
        exact ⟨by simp, by left; exact h0⟩⟩
    | succ p1 =>
      induction p1 with
      | zero =>
        have hmore : more (c :: rest) 1 s0 = append c s0 := by simp [more]
        exact ⟨0, by
          rw [hmore]
          constructor
          · simp [append]
          · right
            exact ⟨c, by simp [append]⟩⟩
      | succ p2 =>
        have hmore : more (c :: rest) (p2 + 2) s0 =
            more rest p2 (ackCommit c (flush (append c s0))) := by simp [more]
        have hs1pend : (ackCommit c (flush (append c s0))).pend = none :=
          by simp [ackCommit, flush, append]
        obtain ⟨i, hlog, hpend⟩ :=
          ih p2 (ackCommit c (flush (append c s0))) hs1pend
        have hlog' : (more (c :: rest) (p2 + 2) s0).log =
            s0.log ++ (c :: rest).take (1 + i) := by
          rw [hmore, hlog]
          have hs1log : (ackCommit c (flush (append c s0))).log = s0.log ++ [c] :=
            by simp [ackCommit, flush, append]
          rw [hs1log]
          simp [List.append_assoc]
          rw [Nat.add_comm, List.take_cons (Nat.succ_pos i), Nat.succ_sub_one]
        cases hpend with
        | inl hnone =>
          exact ⟨1 + i, ⟨hlog', by
            rw [hmore]
            simp [hnone]⟩⟩
        | inr h =>
          obtain ⟨l, hrest⟩ := h
          obtain ⟨hpl, htake⟩ := hrest
          exact ⟨1 + i, ⟨hlog', by
            rw [hmore]
            right
            exact ⟨l, by simp [hpl], take_succ_cons c rest i l htake⟩⟩⟩

-- the same invariant for the first commit
theorem first_inv (cs : List (List Nat)) (q : Nat) (s0 : St) (h0 : s0.pend = none) :
    ∃ i, (first cs q s0).log = s0.log ++ cs.take i ∧
      ((first cs q s0).pend = none ∨
       ∃ l, (first cs q s0).pend = some l ∧ cs.take (i + 1) = cs.take i ++ [l]) := by
  induction cs generalizing q s0 h0 with
  | nil =>
    exact ⟨0, by
      have h : first [] q s0 = s0 := by simp [first]
      rw [h]
      exact ⟨by simp, by left; exact h0⟩⟩
  | cons c rest ih =>
    induction q with
    | zero =>
      exact ⟨0, by
        have h : first (c :: rest) 0 s0 = s0 := by simp [first]
        rw [h]
        exact ⟨by simp, by left; exact h0⟩⟩
    | succ q1 =>
      induction q1 with
      | zero =>
        have hfirst : first (c :: rest) 1 s0 = append c s0 := by simp [first]
        exact ⟨0, by
          rw [hfirst]
          constructor
          · simp [append]
          · right
            exact ⟨c, by simp [append]⟩⟩
      | succ q2 =>
        induction q2 with
        | zero =>
          have hfirst : first (c :: rest) 2 s0 = flush (append c s0) := by simp [first]
          exact ⟨1, by
            rw [hfirst]
            constructor
            · simp [flush, append]
            · left
              simp [flush, append]⟩
        | succ q3 =>
          have hfirst : first (c :: rest) (q3 + 3) s0 =
              more rest q3 (ackCommit c (dir (flush (append c s0)))) := by simp [first]
          have hs1pend : (ackCommit c (dir (flush (append c s0)))).pend = none :=
            by simp [ackCommit, dir, flush, append]
          obtain ⟨i, hlog, hpend⟩ :=
            more_inv rest q3 (ackCommit c (dir (flush (append c s0)))) hs1pend
          have hlog' : (first (c :: rest) (q3 + 3) s0).log =
              s0.log ++ (c :: rest).take (1 + i) := by
            rw [hfirst, hlog]
            have hs1log : (ackCommit c (dir (flush (append c s0)))).log = s0.log ++ [c] :=
              by simp [ackCommit, dir, flush, append]
            rw [hs1log]
            simp [List.append_assoc]
            rw [Nat.add_comm, List.take_cons (Nat.succ_pos i), Nat.succ_sub_one]
          cases hpend with
          | inl hnone =>
            exact ⟨1 + i, ⟨hlog', by
              rw [hfirst]
              simp [hnone]⟩⟩
          | inr h =>
            obtain ⟨l, hrest⟩ := h
            obtain ⟨hpl, htake⟩ := hrest
            exact ⟨1 + i, ⟨hlog', by
              rw [hfirst]
              right
              exact ⟨l, by simp [hpl], take_succ_cons c rest i l htake⟩⟩⟩

-- the same invariant for a whole epoch run
theorem run_inv (d : Disk) (cs : List (List Nat)) (p : Nat) :
    ∃ i, (run d cs p).log = Disk.log d ++ cs.take i ∧
      ((run d cs p).pend = none ∨
       ∃ l, (run d cs p).pend = some l ∧ cs.take (i + 1) = cs.take i ++ [l]) := by
  induction p with
  | zero =>
    exact ⟨0, by
      have h : run d cs 0 = openSt d := by simp [run]
      rw [h]
      constructor
      · simp [openSt_log]
      · left
        cases d with
        | absent => simp [openSt]
        | present b => simp [openSt]⟩
  | succ q =>
    have hrun : run d cs (q + 1) = first cs q (parent (openSt d)) := by simp [run]
    have h0 : (parent (openSt d)).pend = none := by
      cases d with
      | absent => simp [parent, openSt]
      | present b => simp [parent, openSt]
    obtain ⟨i, hlog, hpend⟩ := first_inv cs q (parent (openSt d)) h0
    have hlog' : (run d cs (q + 1)).log = Disk.log d ++ cs.take i := by
      rw [hrun, hlog]
      have h : (parent (openSt d)).log = Disk.log d := by simp [parent, openSt_log]
      rw [h]
    cases hpend with
    | inl hnone =>
      exact ⟨i, ⟨hlog', by
        rw [hrun]
        simp [hnone]⟩⟩
    | inr h =>
      obtain ⟨l, hrest⟩ := h
      obtain ⟨hpl, htake⟩ := hrest
      exact ⟨i, ⟨hlog', by
        rw [hrun]
        right
        exact ⟨l, by simp [hpl], htake⟩⟩⟩

-- a prefix of a take is a take, then the rest
theorem take_split (cs : List (List Nat)) (i j : Nat) (h : j ≤ i) :
    cs.take i = cs.take j ++ (cs.take i).drop j := by
  have h1 : (cs.take i).take j ++ (cs.take i).drop j = cs.take i :=
    List.take_append_drop j (cs.take i)
  have h2 : (cs.take i).take j = cs.take j := by
    rw [List.take_take]
    simp [h]
  rw [h2] at h1
  exact h1.symm

-- the full invariant of more: the log grows by a prefix of the commits, the
-- acked is a prefix of that (no longer than the log), and the pending line
-- (if any) is exactly the next commit after the log prefix
theorem more_full (cs : List (List Nat)) (p : Nat) (s0 : St) (h0 : s0.pend = none) :
    ∃ i j, (more cs p s0).log = s0.log ++ cs.take i ∧
      (more cs p s0).acked = s0.acked ++ cs.take j ∧ j ≤ i ∧
      ((more cs p s0).pend = none ∨
       ∃ l, (more cs p s0).pend = some l ∧ cs.take (i + 1) = cs.take i ++ [l]) := by
  induction cs generalizing p s0 h0 with
  | nil =>
    exact ⟨0, 0, by
      have h : more [] p s0 = s0 := by simp [more]
      rw [h]
      exact ⟨by simp, by simp, by norm_num, by left; exact h0⟩⟩
  | cons c rest ih =>
    induction p with
    | zero =>
      exact ⟨0, 0, by
        have h : more (c :: rest) 0 s0 = s0 := by simp [more]
        rw [h]
        exact ⟨by simp, by simp, by norm_num, by left; exact h0⟩⟩
    | succ p1 =>
      induction p1 with
      | zero =>
        exact ⟨0, 0, by
          have h : more (c :: rest) 1 s0 = append c s0 := by simp [more]
          rw [h]
          exact ⟨by simp [append], by simp [append], by norm_num,
            by right; exact ⟨c, by simp [append], by simp⟩⟩⟩
      | succ p2 =>
        obtain ⟨i, j, hlog, hacc, hle, hpend⟩ :=
          ih p2 (ackCommit c (flush (append c s0))) (by simp [ackCommit, flush, append])
        have hmore : more (c :: rest) (p2 + 2) s0 =
            more rest p2 (ackCommit c (flush (append c s0))) := by simp [more]
        have hlog' : (more (c :: rest) (p2 + 2) s0).log =
            s0.log ++ (c :: rest).take (1 + i) := by
          rw [hmore, hlog]
          have hs1log : (ackCommit c (flush (append c s0))).log = s0.log ++ [c] :=
            by simp [ackCommit, flush, append]
          rw [hs1log]
          simp [List.append_assoc]
          rw [Nat.add_comm, List.take_cons (Nat.succ_pos i), Nat.succ_sub_one]
        have hacc' : (more (c :: rest) (p2 + 2) s0).acked =
            s0.acked ++ (c :: rest).take (1 + j) := by
          rw [hmore, hacc]
          have hs1acc : (ackCommit c (flush (append c s0))).acked = s0.acked ++ [c] :=
            by simp [ackCommit, flush, append]
          rw [hs1acc]
          simp [List.append_assoc]
          rw [Nat.add_comm, List.take_cons (Nat.succ_pos j), Nat.succ_sub_one]
        cases hpend with
        | inl hnone =>
          exact ⟨1 + i, 1 + j, hlog', hacc', by omega, by
            rw [hmore]
            simp [hnone]⟩
        | inr h =>
          obtain ⟨l, hpl, htake⟩ := h
          exact ⟨1 + i, 1 + j, hlog', hacc', by omega, by
            rw [hmore]
            right
            exact ⟨l, by simp [hpl], take_succ_cons c rest i l htake⟩⟩

theorem first_full (cs : List (List Nat)) (q : Nat) (s0 : St) (h0 : s0.pend = none) :
    ∃ i j, (first cs q s0).log = s0.log ++ cs.take i ∧
      (first cs q s0).acked = s0.acked ++ cs.take j ∧ j ≤ i ∧
      ((first cs q s0).pend = none ∨
       ∃ l, (first cs q s0).pend = some l ∧ cs.take (i + 1) = cs.take i ++ [l]) := by
  induction cs generalizing q s0 h0 with
  | nil =>
    exact ⟨0, 0, by
      have h : first [] q s0 = s0 := by simp [first]
      rw [h]
      exact ⟨by simp, by simp, by norm_num, by left; exact h0⟩⟩
  | cons c rest ih =>
    induction q with
    | zero =>
      exact ⟨0, 0, by
        have h : first (c :: rest) 0 s0 = s0 := by simp [first]
        rw [h]
        exact ⟨by simp, by simp, by norm_num, by left; exact h0⟩⟩
    | succ q1 =>
      induction q1 with
      | zero =>
        exact ⟨0, 0, by
          have h : first (c :: rest) 1 s0 = append c s0 := by simp [first]
          rw [h]
          exact ⟨by simp [append], by simp [append], by norm_num,
            by right; exact ⟨c, by simp [append], by simp⟩⟩⟩
      | succ q2 =>
        induction q2 with
        | zero =>
          exact ⟨1, 0, by
            have h : first (c :: rest) 2 s0 = flush (append c s0) := by simp [first]
            rw [h]
            exact ⟨by simp [flush, append], by simp [flush, append], by norm_num,
              by left; simp [flush, append]⟩⟩
        | succ q3 =>
          obtain ⟨i, j, hlog, hacc, hle, hpend⟩ :=
            more_full rest q3 (ackCommit c (dir (flush (append c s0))))
              (by simp [ackCommit, dir, flush, append])
          have hfirst : first (c :: rest) (q3 + 3) s0 =
              more rest q3 (ackCommit c (dir (flush (append c s0)))) := by simp [first]
          have hlog' : (first (c :: rest) (q3 + 3) s0).log =
              s0.log ++ (c :: rest).take (1 + i) := by
            rw [hfirst, hlog]
            have hs1log : (ackCommit c (dir (flush (append c s0)))).log = s0.log ++ [c] :=
              by simp [ackCommit, dir, flush, append]
            rw [hs1log]
            simp [List.append_assoc]
            rw [Nat.add_comm, List.take_cons (Nat.succ_pos i), Nat.succ_sub_one]
          have hacc' : (first (c :: rest) (q3 + 3) s0).acked =
              s0.acked ++ (c :: rest).take (1 + j) := by
            rw [hfirst, hacc]
            have hs1acc : (ackCommit c (dir (flush (append c s0)))).acked = s0.acked ++ [c] :=
              by simp [ackCommit, dir, flush, append]
            rw [hs1acc]
            simp [List.append_assoc]
            rw [Nat.add_comm, List.take_cons (Nat.succ_pos j), Nat.succ_sub_one]
          cases hpend with
          | inl hnone =>
            exact ⟨1 + i, 1 + j, hlog', hacc', by omega, by
              rw [hfirst]
              simp [hnone]⟩
          | inr h =>
            obtain ⟨l, hpl, htake⟩ := h
            exact ⟨1 + i, 1 + j, hlog', hacc', by omega, by
              rw [hfirst]
              right
              exact ⟨l, by simp [hpl], take_succ_cons c rest i l htake⟩⟩

-- the full invariant of a whole epoch run
theorem run_full (d : Disk) (cs : List (List Nat)) (p : Nat) :
    ∃ i j, (run d cs p).log = Disk.log d ++ cs.take i ∧
      (run d cs p).acked = cs.take j ∧ j ≤ i ∧
      ((run d cs p).pend = none ∨
       ∃ l, (run d cs p).pend = some l ∧ cs.take (i + 1) = cs.take i ++ [l]) := by
  induction p with
  | zero =>
    exact ⟨0, 0, by
      have h : run d cs 0 = openSt d := by simp [run]
      rw [h]
      exact ⟨by simp [openSt_log], by
        cases d with
        | absent => simp [openSt]
        | present b => simp [openSt], by norm_num, by
        left
        cases d with
        | absent => simp [openSt]
        | present b => simp [openSt]⟩⟩
  | succ q =>
    have hrun : run d cs (q + 1) = first cs q (parent (openSt d)) := by simp [run]
    have h0 : (parent (openSt d)).pend = none := by
      cases d with
      | absent => simp [parent, openSt]
      | present b => simp [parent, openSt]
    obtain ⟨i, j, hlog, hacc, hle, hpend⟩ := first_full cs q (parent (openSt d)) h0
    have hlog' : (run d cs (q + 1)).log = Disk.log d ++ cs.take i := by
      rw [hrun, hlog]
      have h : (parent (openSt d)).log = Disk.log d := by simp [parent, openSt_log]
      rw [h]
    have hacc' : (run d cs (q + 1)).acked = cs.take j := by
      rw [hrun, hacc]
      have h : (parent (openSt d)).acked = [] := by
        cases d with
        | absent => simp [parent, openSt]
        | present b => simp [parent, openSt]
      rw [h]
      simp
    cases hpend with
    | inl hnone =>
      exact ⟨i, j, hlog', hacc', hle, by
        rw [hrun]
        simp [hnone]⟩
    | inr h =>
      obtain ⟨l, hpl, htake⟩ := h
      exact ⟨i, j, hlog', hacc', hle, by
        rw [hrun]
        right
        exact ⟨l, by simp [hpl], htake⟩⟩

-- LAW log_only_commits: after an epoch the log is the log before it, then a
-- prefix of the commits it tried, in order: nothing torn, nothing out of
-- order, nothing twice.
theorem log_only_commits (d : Disk) (e : Epoch) :
    ∃ n, Disk.log (after d e) = Disk.log d ++ (e.cs).take n := by
  obtain ⟨i, j, hlog, hacc, hle, hpend⟩ := run_full d e.cs e.p
  by_cases hkeeps : keeps e.drop (run d e.cs e.p).de (run d e.cs e.p).fe = true
  · -- the file survives the crash
    have hafter : after d e =
        Disk.present (render (run d e.cs e.p).log ++ cut e.k (run d e.cs e.p).pend) := by
      simp [after, crash, stays, hkeeps]
    have hrec : Disk.log (after d e) =
        recover (render (run d e.cs e.p).log ++ cut e.k (run d e.cs e.p).pend) := by
      simp [hafter, Disk.log]
    cases recover_render_cut (run d e.cs e.p).log e.k (run d e.cs e.p).pend with
    | inl h =>
      exact ⟨i, by rw [hrec, h, hlog]⟩
    | inr h =>
      obtain ⟨l, hpl, hrec2⟩ := h
      have htake : (e.cs).take (i + 1) = (e.cs).take i ++ [l] := by
        cases hpend with
        | inl hnone =>
          exfalso
          rw [hnone] at hpl
          cases hpl
        | inr h2 =>
          obtain ⟨l2, hpl2, htake2⟩ := h2
          have heq : l2 = l := by
            have h : some l2 = some l := by rw [← hpl2, ← hpl]
            exact Option.some_inj.mp h
          rw [heq] at htake2
          exact htake2
      exact ⟨i + 1, by
        rw [hrec, hrec2, hlog]
        simp [List.append_assoc, htake]⟩
  · -- the file does not survive the crash
    have hafter : after d e = Disk.absent := by
      simp [after, crash, stays, hkeeps]
    have hd : d = Disk.absent := keeps_false_absent d e.cs e.p e.drop hkeeps
    exact ⟨0, by
      rw [hafter, hd]
      simp [Disk.log]⟩

-- LAW log_ack_durable: a crash at any point never loses a commit: after an
-- epoch the log is the log before it, then every commit it acknowledged,
-- then maybe more.
theorem log_ack_durable (d : Disk) (e : Epoch) :
    ∃ rest, Disk.log (after d e) = Disk.log d ++ acked d e ++ rest := by
  obtain ⟨i, j, hlog, hacc, hle, hpend⟩ := run_full d e.cs e.p
  have hacc' : acked d e = (e.cs).take j := by
    simp [acked]
    exact hacc
  by_cases hkeeps : keeps e.drop (run d e.cs e.p).de (run d e.cs e.p).fe = true
  · -- the file survives the crash
    have hafter : after d e =
        Disk.present (render (run d e.cs e.p).log ++ cut e.k (run d e.cs e.p).pend) := by
      simp [after, crash, stays, hkeeps]
    have hrec : Disk.log (after d e) =
        recover (render (run d e.cs e.p).log ++ cut e.k (run d e.cs e.p).pend) := by
      simp [hafter, Disk.log]
    cases recover_render_cut (run d e.cs e.p).log e.k (run d e.cs e.p).pend with
    | inl h =>
      have hsplit := take_split e.cs i j hle
      exact ⟨(e.cs).take i |>.drop j, by
        rw [hrec, h, hlog, hacc']
        simp [List.append_assoc]
        rw [← hsplit]⟩
    | inr h =>
      obtain ⟨l, hpl, hrec2⟩ := h
      have htake : (e.cs).take (i + 1) = (e.cs).take i ++ [l] := by
        cases hpend with
        | inl hnone =>
          exfalso
          rw [hnone] at hpl
          cases hpl
        | inr h2 =>
          obtain ⟨l2, hpl2, htake2⟩ := h2
          have heq : l2 = l := by
            have h : some l2 = some l := by rw [← hpl2, ← hpl]
            exact Option.some_inj.mp h
          rw [heq] at htake2
          exact htake2
      have hsplit := take_split e.cs (i + 1) j (by omega)
      exact ⟨(e.cs).take (i + 1) |>.drop j, by
        rw [hrec, hrec2, hlog, hacc']
        simp [List.append_assoc]
        rw [← htake]
        rw [← hsplit]⟩
  · -- the file does not survive the crash
    have hafter : after d e = Disk.absent := by
      simp [after, crash, stays, hkeeps]
    have hd : d = Disk.absent := keeps_false_absent d e.cs e.p e.drop hkeeps
    rw [hd] at hkeeps
    have hacc : acked d e = (run Disk.absent e.cs e.p).acked := by
      simp [acked, hd]
    have hempty : (run Disk.absent e.cs e.p).acked = [] :=
      run_absent_keeps_false_acked_empty e.cs e.p e.drop hkeeps
    exact ⟨[], by
      rw [hafter, hacc, hd, hempty]
      simp [Disk.log]⟩
