# eukhe: the proof of LAW progress_type_terms_exact
# Both ways by induction (proof/progress_terms/base.bend).

import Base
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def ProgressTerms.progress_type_terms_exact(x, xs, s, segs, ps):
  ((i => LPT.pg.in_sound(x, xs, i), c => LPT.pg.in_complete(x, xs, c)), ((i => LPT.pg.within_sound(xs, s, i), c => LPT.pg.within_complete(xs, s, c)), ((i => LPT.pg.repeats_sound(segs, s, i), c => LPT.pg.repeats_complete(segs, s, c)), (i => LPT.pg.loops_sound(ps, s, i), c => LPT.pg.loops_complete(ps, s, c)))))
