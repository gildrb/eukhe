# eukhe: the proof of LAW socket_dir_progress

import Base
import ../../bend/fsmode.bend as Fs
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pf.dir_progress(mine: Bool, loose: Bool, safe: {Bool.and(mine, Bool.not(loose)) == True{} : Bool}) -> {Fs.socket_dir.dir(mine, loose) == Fs.Use{} : Fs.Verdict}:
  match mine loose:
    case True{} False{}:
      {==}
    case True{} True{}:
      LA.fsmode.pf.absurdF({Fs.socket_dir.dir(True{}, True{}) == Fs.Use{} : Fs.Verdict}, safe)
    case False{} l:
      LA.fsmode.pf.absurdF({Fs.socket_dir.dir(False{}, l) == Fs.Use{} : Fs.Verdict}, safe)

def progress(d: Fs.Seen, safe: {Fs.Seen.safe(d) == True{} : Bool}) -> {Fs.socket_dir(d) == Fs.Use{} : Fs.Verdict}:
  match d:
    case Fs.Seen{k, mine, loose}:
      match k:
        case Fs.Missing{}:
          LA.fsmode.pf.absurdF({Fs.socket_dir(Fs.Seen{Fs.Missing{}, mine, loose}) == Fs.Use{} : Fs.Verdict}, safe)
        case Fs.Dir{}:
          pf.dir_progress(mine, loose, safe)
        case Fs.Link{}:
          LA.fsmode.pf.absurdF({Fs.socket_dir(Fs.Seen{Fs.Link{}, mine, loose}) == Fs.Use{} : Fs.Verdict}, safe)
        case Fs.Other{}:
          LA.fsmode.pf.absurdF({Fs.socket_dir(Fs.Seen{Fs.Other{}, mine, loose}) == Fs.Use{} : Fs.Verdict}, safe)

def Laws.socket_dir_progress(d, safe):
  progress(d, safe)
