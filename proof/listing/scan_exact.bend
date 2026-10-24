# eukhe: the proof of LAW scan_exact

import Base
import ../../laws/listing.bend as Listing
import ./base/scan.bend as LA

def Listing.scan_exact(es):
  LA.ls.scan_go(es, es)
