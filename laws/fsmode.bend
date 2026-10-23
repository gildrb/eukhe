# eukhe: the laws of area fsmode

import Base
import ../bend/fsmode.bend as Fs

# ---- fsmode ----

# LAWS (G1, file modes, the socket dir and the working dir): who
# reaches eukhe's own state. Each law is an open claim about the model in
# bend/fsmode.bend; PROOF.bend proves them (as Fsmode.<law>) with the lemmas
# of proof/fsmode/.

# (G1) Path policy
# ----------------

# File modes, the socket dir and the working dir
# ----------------------------------------------
# docs/runtime.md "Local access", the model in bend/fsmode.bend; the Rust
# bridge test crates/eukhe-daemon/src/fsmode_bridge.rs runs the real
# socket-dir check, the peer rule, the real creation paths and the real
# session cwd check against bridge/bridge_fsmode.bend.

# LAW socket_dir_owned: the daemon binds in a socket dir only when the dir is a real
# directory (not a link), this uid owns it, and no group or other user
# may write in it
law socket_dir_owned:
  for d: Fs.Seen
  for used: {Fs.socket_dir(d) == Fs.Use{} : Fs.Verdict}
  {Fs.Seen.safe(d) == True{} : Bool}

# LAW socket_dir_progress: a safe socket dir is used (the check refuses nothing it must not)
law socket_dir_progress:
  for d: Fs.Seen
  for safe: {Fs.Seen.safe(d) == True{} : Bool}
  {Fs.socket_dir(d) == Fs.Use{} : Fs.Verdict}

# LAW socket_dir_created: a missing socket dir is created with mode 0700
law socket_dir_created:
  for mine: Bool
  for loose: Bool
  {Fs.socket_dir(Fs.Seen{Fs.Missing{}, mine, loose}) == Fs.Create{Fs.dir_mode()} : Fs.Verdict}

# LAW socket_dir_created_used: the dir the daemon creates with mode 0700 is then used
law socket_dir_created_used:
  {Fs.socket_dir(Fs.made(Fs.dir_mode())) == Fs.Use{} : Fs.Verdict}

# LAW peer_same_uid: a socket peer is accepted only when its uid is this process's uid
law peer_same_uid:
  for p: Nat
  for own: Nat
  for ok: {Fs.peer(p, own) == Fs.Accept{} : Fs.Peer}
  {p == own : Nat}

# LAW peer_own_accepted: a peer of this process's uid is accepted
law peer_own_accepted:
  for own: Nat
  {Fs.peer(own, own) == Fs.Accept{} : Fs.Peer}

# LAW private_on_create: every file and dir eukhe creates under its home has no group or
# other permission bit
law private_on_create:
  for k: Fs.Made
  {Fs.Mode.loose(Fs.made_mode(k)) == False{} : Bool}

# LAW cwd_is_explicit: an accepted session create runs in the dir it named, and that dir
# exists
law cwd_is_explicit:
  for c: Fs.Cwd
  for p: Nat
  for ok: {Fs.open(c) == Fs.Opened{p} : Fs.Open}
  {c == Fs.DirCwd{p} : Fs.Cwd}

# LAW cwd_none_refused: a create that names no working dir is refused
law cwd_none_refused:
  {Fs.open(Fs.NoCwd{}) == Fs.NeedsCwd{} : Fs.Open}

# LAW cwd_gone_refused: a create whose working dir is gone is refused, and the refusal
# names that dir
law cwd_gone_refused:
  for p: Nat
  {Fs.open(Fs.GoneCwd{p}) == Fs.Gone{p} : Fs.Open}

# LAW cwd_file_refused: a create whose working dir is a file is refused, and the refusal
# names that path
law cwd_file_refused:
  for p: Nat
  {Fs.open(Fs.FileCwd{p}) == Fs.NotDir{p} : Fs.Open}

# LAW cwd_dir_opens: a create that names an existing dir runs in it
law cwd_dir_opens:
  for p: Nat
  {Fs.open(Fs.DirCwd{p}) == Fs.Opened{p} : Fs.Open}
