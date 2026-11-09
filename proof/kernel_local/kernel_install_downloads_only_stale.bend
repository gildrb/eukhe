# eukhe: the proof of LAW kernel_install_downloads_only_stale
#
# Each venv found computes: a stale venv's install plan has a fetch, the
# others none.

import Base
import ../../bend/kernel_local.bend as KL
import ../../laws/kernel_local.bend as KernelLocal

def KernelLocal.kernel_install_downloads_only_stale(f):
  match f:
    case KL.Current{}:
      {==}
    case KL.Skills{}:
      {==}
    case KL.Stale{}:
      {==}
