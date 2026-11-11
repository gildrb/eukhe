# eukhe: the proof of LAW kernel_offline_once_fetched

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

# ---- kernel_local ----

# proof_kernel_local: the K1 laws (LAWS.bend section kernel_local) of the kernel
# setup model in bend/kernel_local.bend.
#
# A setup's plan is a fixed list for each of the eight things it can find
# (the pinned uv, the pinned CPython and the kernel env, each there or
# not), so the setup laws hold by computation in every case. The tool laws
# read the answer: another tool runs whatever the kernel, and a failed
# step of a setup that found something not there leaves it Missing. The
# sweep laws go by induction on the files: each file is kept exactly when
# it is not a leftover of a dead attempt.

# (K1) The kernel environment is Eukhe's own

def KernelLocal.kernel_offline_once_fetched(env):
  match env:
    case True{}:
      {==}
    case False{}:
      {==}
