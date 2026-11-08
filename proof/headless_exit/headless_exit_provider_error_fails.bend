# eukhe: the proof of LAW headless_exit_provider_error_fails
#
# PROOF: above the transcript every cause has code 1 (hx.facts_fail, hx.run_fails), and the PProviderError entry is a cause of its own, code 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_provider_error_fails(cf, gu, r, c, a):
  LAHeadlessExit.hx.facts_fail(cf, gu, r, Hx.PProviderError{}, c, a, LAHeadlessExit.hx.run_fails(r, Hx.PProviderError{}, c, a, {==}))
