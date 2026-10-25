# eukhe: the proof of LAW cron_clear_exact
# A case split on whose the claim is.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

def cx.clear(w: CS.Who) -> {CS.clear(w) == CronStore.clear_spec(w) : Bool}:
  match w:
    case CS.Mine{r}:
      match r:
        case True{}:
          {==}
        case False{}:
          {==}
    case CS.Theirs{d}:
      {==}

def CronStore.cron_clear_exact(w):
  cx.clear(w)
