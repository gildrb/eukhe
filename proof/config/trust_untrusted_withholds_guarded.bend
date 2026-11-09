# eukhe: the proof of LAW trust_untrusted_withholds_guarded
# Each guarded path, whatever follows it, meets its rule (a limit, a
# credential or a prompt file) before any other: it computes.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def Config.trust_untrusted_withholds_guarded(r, k, v):
  {==}
