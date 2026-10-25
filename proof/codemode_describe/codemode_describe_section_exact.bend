# eukhe: the proof of LAW codemode_describe_section_exact

import Base
import ../../bend/codemode_describe.bend as Dsc
import ../../laws/codemode_describe.bend as CodemodeDescribe
import ./base.bend as LACd
import ./base/section.bend as LACdSection

# PROOF of LAW codemode_describe_section_exact: each step of the section is the spec's (cds.section: the tools and namespaces, the groups, their order, the tools shown, the headings, blocks and joint).

def CodemodeDescribe.codemode_describe_section_exact(ts, ss, budget):
  LACdSection.cds.section(ts, ss, budget)
