# proof_fsmode: the laws of laws/fsmode.bend over the model in
# bend/fsmode.bend. Each decision is a match on its inputs, so each law
# follows by case analysis; a clash of two constructors is refuted with a
# motive that sends the expected constructor to the goal and the others
# to Unit.

import Base
import ./fsmode.bend as Fs

# Clashes
# -------

def pf.VD(v: Fs.Verdict, A: Type) -> Type:
  match v:
    case Fs.Create{m}:
      Unit
    case Fs.Use{}:
      A
    case Fs.Refuse{}:
      Unit

def pf.refuse_use(-A: Type, e: {Fs.Refuse{} == Fs.Use{} : Fs.Verdict}) -> A:
  %e : pf.VD(_, A)
  Unit{}

def pf.create_use(-A: Type, +m: Fs.Mode, e: {Fs.Create{m} == Fs.Use{} : Fs.Verdict}) -> A:
  %e : pf.VD(_, A)
  Unit{}

def pf.PD(v: Fs.Peer, A: Type) -> Type:
  match v:
    case Fs.Accept{}:
      A
    case Fs.Drop{}:
      Unit

def pf.drop_accept(-A: Type, e: {Fs.Drop{} == Fs.Accept{} : Fs.Peer}) -> A:
  %e : pf.PD(_, A)
  Unit{}

def pf.OD(v: Fs.Open, A: Type) -> Type:
  match v:
    case Fs.Opened{p}:
      A
    case Fs.NeedsCwd{}:
      Unit
    case Fs.Gone{p}:
      Unit
    case Fs.NotDir{p}:
      Unit

def pf.needs_opened(-A: Type, +p: Nat, e: {Fs.NeedsCwd{} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def pf.gone_opened(-A: Type, +q: Nat, +p: Nat, e: {Fs.Gone{q} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def pf.notdir_opened(-A: Type, +q: Nat, +p: Nat, e: {Fs.NotDir{q} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def pf.BD(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

def pf.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pf.BD(_, A)
  Unit{}

# Numbers
# -------

def pf.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pf.eq_refl(p)

def pf.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pf.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pf.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pf.eq_true(p, q, h))

# The socket dir
# --------------

def pf.dir_owned(mine: Bool, loose: Bool, used: {Fs.socket_dir.dir(mine, loose) == Fs.Use{} : Fs.Verdict}) -> {Bool.and(mine, Bool.not(loose)) == True{} : Bool}:
  match mine loose:
    case True{} False{}:
      {==}
    case True{} True{}:
      pf.refuse_use({Bool.and(True{}, Bool.not(True{})) == True{} : Bool}, used)
    case False{} l:
      pf.refuse_use({Bool.and(False{}, Bool.not(l)) == True{} : Bool}, used)

def owned(d: Fs.Seen, used: {Fs.socket_dir(d) == Fs.Use{} : Fs.Verdict}) -> {Fs.Seen.safe(d) == True{} : Bool}:
  match d:
    case Fs.Seen{k, mine, loose}:
      match k:
        case Fs.Missing{}:
          pf.create_use({Fs.Seen.safe(Fs.Seen{Fs.Missing{}, mine, loose}) == True{} : Bool}, Fs.dir_mode(), used)
        case Fs.Dir{}:
          pf.dir_owned(mine, loose, used)
        case Fs.Link{}:
          pf.refuse_use({Fs.Seen.safe(Fs.Seen{Fs.Link{}, mine, loose}) == True{} : Bool}, used)
        case Fs.Other{}:
          pf.refuse_use({Fs.Seen.safe(Fs.Seen{Fs.Other{}, mine, loose}) == True{} : Bool}, used)

def pf.dir_progress(mine: Bool, loose: Bool, safe: {Bool.and(mine, Bool.not(loose)) == True{} : Bool}) -> {Fs.socket_dir.dir(mine, loose) == Fs.Use{} : Fs.Verdict}:
  match mine loose:
    case True{} False{}:
      {==}
    case True{} True{}:
      pf.absurdF({Fs.socket_dir.dir(True{}, True{}) == Fs.Use{} : Fs.Verdict}, safe)
    case False{} l:
      pf.absurdF({Fs.socket_dir.dir(False{}, l) == Fs.Use{} : Fs.Verdict}, safe)

def progress(d: Fs.Seen, safe: {Fs.Seen.safe(d) == True{} : Bool}) -> {Fs.socket_dir(d) == Fs.Use{} : Fs.Verdict}:
  match d:
    case Fs.Seen{k, mine, loose}:
      match k:
        case Fs.Missing{}:
          pf.absurdF({Fs.socket_dir(Fs.Seen{Fs.Missing{}, mine, loose}) == Fs.Use{} : Fs.Verdict}, safe)
        case Fs.Dir{}:
          pf.dir_progress(mine, loose, safe)
        case Fs.Link{}:
          pf.absurdF({Fs.socket_dir(Fs.Seen{Fs.Link{}, mine, loose}) == Fs.Use{} : Fs.Verdict}, safe)
        case Fs.Other{}:
          pf.absurdF({Fs.socket_dir(Fs.Seen{Fs.Other{}, mine, loose}) == Fs.Use{} : Fs.Verdict}, safe)

def created(mine: Bool, loose: Bool) -> {Fs.socket_dir(Fs.Seen{Fs.Missing{}, mine, loose}) == Fs.Create{Fs.dir_mode()} : Fs.Verdict}:
  {==}

def created_used() -> {Fs.socket_dir(Fs.made(Fs.dir_mode())) == Fs.Use{} : Fs.Verdict}:
  {==}

# Socket peers
# ------------

def pf.peer_at(b: Bool, +p: Nat, +own: Nat, eb: {Nat.is_eq(p, own) == b : Bool}, ok: {Fs.peer.at(b) == Fs.Accept{} : Fs.Peer}) -> {p == own : Nat}:
  match b:
    case True{}:
      pf.eq_true(p, own, eb)
    case False{}:
      pf.drop_accept({p == own : Nat}, ok)

def peer_same(+p: Nat, +own: Nat, ok: {Fs.peer(p, own) == Fs.Accept{} : Fs.Peer}) -> {p == own : Nat}:
  pf.peer_at(Nat.is_eq(p, own), p, own, {==}, ok)

def peer_own(+own: Nat) -> {Fs.peer(own, own) == Fs.Accept{} : Fs.Peer}:
  %pf.eq_refl(own) : {Fs.peer.at(_) == Fs.Accept{} : Fs.Peer}
  {==}

# What eukhe creates
# ------------------

def private(k: Fs.Made) -> {Fs.Mode.loose(Fs.made_mode(k)) == False{} : Bool}:
  match k:
    case Fs.DirMade{}:
      {==}
    case Fs.FileMade{}:
      {==}

# The working dir of a session
# ----------------------------

def pf.opened_p(o: Fs.Open) -> Nat:
  match o:
    case Fs.Opened{p}:
      p
    case Fs.NeedsCwd{}:
      0n
    case Fs.Gone{p}:
      0n
    case Fs.NotDir{p}:
      0n

def explicit(c: Fs.Cwd, +p: Nat, ok: {Fs.open(c) == Fs.Opened{p} : Fs.Open}) -> {c == Fs.DirCwd{p} : Fs.Cwd}:
  match c:
    case Fs.NoCwd{}:
      pf.needs_opened({Fs.NoCwd{} == Fs.DirCwd{p} : Fs.Cwd}, p, ok)
    case Fs.GoneCwd{q}:
      pf.gone_opened({Fs.GoneCwd{q} == Fs.DirCwd{p} : Fs.Cwd}, q, p, ok)
    case Fs.FileCwd{q}:
      pf.notdir_opened({Fs.FileCwd{q} == Fs.DirCwd{p} : Fs.Cwd}, q, p, ok)
    case Fs.DirCwd{q}:
      Equal.cong(Nat, Fs.Cwd, n => Fs.DirCwd{n}, q, p, Equal.cong(Fs.Open, Nat, pf.opened_p, Fs.Opened{q}, Fs.Opened{p}, ok))
