# eukhe: the proof of LAW package_source_npm_spec_spec
#
# PROOF: the model's functions are the spec helpers, function by function, by induction on what each reads (psb.npm_spec).

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/ffi_package_source.bend as FPs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/package_source/model.bend as PackageSource
import ../../laws/package_source/entry.bend as PackageSourceEntry
import ./base.bend as LA

def PackageSource.package_source_npm_spec_spec(s):
  LA.psb.npm_spec(s)
