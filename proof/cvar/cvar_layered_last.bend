# eukhe: the proof of LAW cvar_layered_last
# A layer over a current value is its latest counting set, else that value
# (LR.rs.layer_tag, LS.sv.or); a family chain is its agents' layers in
# turn (LR.rs.chainm); the latest set of a concatenation is the later
# part's, else the earlier part's (LR.rs.latest_app).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base/resolve.bend as LR
import ./base/save.bend as LS

def Cvar.cvar_layered_last(ds, cfg, fam, x):
  +lc = Cv.layer(cfg, ds, Cv.Config{}, x, None{})
  +tc = Cvar.spec_tag(Cv.Config{}, cfg)
  +ff = Cvar.spec_flat_fam(fam)
  +lf = Cvar.spec_latest(ff, ds, x)
  +fin = Cvar.spec_latest(List.append(&2, Cvar.LSet, tc, ff), ds, x)
  Equal.trans(Maybe<&2, Cv.Val>, Cv.chainm(fam, ds, x, lc), LS.sv.orm(lf, lc), fin, LR.rs.chainm(fam, ds, x, lc),
    Equal.trans(Maybe<&2, Cv.Val>, LS.sv.orm(lf, lc), LS.sv.orm(lf, Cvar.spec_latest(tc, ds, x)), fin,
      Equal.cong(Maybe<&2, Cv.Val>, Maybe<&2, Cv.Val>, y => LS.sv.orm(lf, y), lc, Cvar.spec_latest(tc, ds, x), LR.rs.layer_tag(cfg, ds, Cv.Config{}, x)),
      Equal.sym(Maybe<&2, Cv.Val>, fin, LS.sv.orm(lf, Cvar.spec_latest(tc, ds, x)), LR.rs.latest_app(tc, ff, ds, x))))
