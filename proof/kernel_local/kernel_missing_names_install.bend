# eukhe: the proof of LAW kernel_missing_names_install

import Base
import ../../bend/kernel_local.bend as KL
import ../../LAWS.bend as Laws

# ---- kernel_local ----

# proof_kernel_local: the K1 laws (LAWS.bend section kernel_local) of the kernel
# setup model in bend/kernel_local.bend.
#
# A setup's plan is a fixed list for each venv found and each setup, so
# the setup laws hold by computation in every case. The tool laws read
# the answer: another tool runs whatever the kernel, and a failed setup
# of a venv that is not current is Missing. The sweep laws go by
# induction on the files: each file is kept exactly when it is not a
# leftover of a dead attempt.

# Logic
# -----

def pk.KD(k: KL.Kernel, u: Type, m: Type) -> Type:
  match k:
    case KL.Up{}:
      u
    case KL.Missing{}:
      m

def pk.up_missing(-A: Type, e: {KL.Up{} == KL.Missing{} : KL.Kernel}) -> A:
  %e : pk.KD(_, Unit, A)
  Unit{}

def pk.missing_names_install(f: KL.Found, failed: {KL.start(f, False{}) == KL.Missing{} : KL.Kernel}) -> {KL.answer(KL.Python{}, KL.start(f, False{})) == KL.NamesInstall{} : KL.Answer}:
  match f:
    case KL.Current{}:
      pk.up_missing({KL.answer(KL.Python{}, KL.Up{}) == KL.NamesInstall{} : KL.Answer}, failed)
    case KL.Skills{}:
      {==}
    case KL.Stale{}:
      {==}

def Laws.kernel_missing_names_install(f, failed):
  pk.missing_names_install(f, failed)
