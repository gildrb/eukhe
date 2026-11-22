# eukhe: the proof of LAW attack_clean_iff
#
# PROOF: by cases: ran, passes, differs and the judge's verdict.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../spec/verified/attack.bend as SA
import ../../laws/attack.bend as Attack
import ../strength/base/model.bend as LS
import ./base/model.bend as LA

def Attack.attack_clean_iff(ran, passes, differs, agrees):
  match ran:
    case True{}:
      match passes:
        case True{}:
          match differs:
            case True{}:
              match agrees:
                case None{}:
                  {==}
                case Some{yes}:
                  match yes:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              {==}
        case False{}:
          {==}
    case False{}:
      {==}
