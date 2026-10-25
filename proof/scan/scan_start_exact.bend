# eukhe: the proof of LAW scan_start_exact

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../base/logic/logic.bend as LLogicLogic
import ../../laws/scan.bend as Scan
import ./base.bend as LAScan

# PROOF of LAW scan_start_exact: case on the query's order, the cursor (its `after` and `order` fields) and the default order: every case computes to the spec's start.

def Scan.scan_start_exact(asked, c, fallback):
  match asked:
    case None{}:
      match c:
        case None{}:
          match fallback:
            case Sc.Asc{}:
              {==}
            case Sc.Desc{}:
              {==}
        case Some{k}:
          match k:
            case Sc.Cursor{a, m}:
              match a:
                case Sc.NoAfter{}:
                  match m:
                    case Sc.NoMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                    case Sc.AscMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                    case Sc.DescMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                    case Sc.BadMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                case Sc.BadAfter{}:
                  match m:
                    case Sc.NoMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                    case Sc.AscMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                    case Sc.DescMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                    case Sc.BadMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                case Sc.SafeAfter{}:
                  match m:
                    case Sc.NoMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                    case Sc.AscMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                    case Sc.DescMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
                    case Sc.BadMark{}:
                      match fallback:
                        case Sc.Asc{}:
                          {==}
                        case Sc.Desc{}:
                          {==}
    case Some{o}:
      match o:
        case Sc.Asc{}:
          match c:
            case None{}:
              match fallback:
                case Sc.Asc{}:
                  {==}
                case Sc.Desc{}:
                  {==}
            case Some{k}:
              match k:
                case Sc.Cursor{a, m}:
                  match a:
                    case Sc.NoAfter{}:
                      match m:
                        case Sc.NoMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.AscMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.DescMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.BadMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                    case Sc.BadAfter{}:
                      match m:
                        case Sc.NoMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.AscMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.DescMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.BadMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                    case Sc.SafeAfter{}:
                      match m:
                        case Sc.NoMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.AscMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.DescMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.BadMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
        case Sc.Desc{}:
          match c:
            case None{}:
              match fallback:
                case Sc.Asc{}:
                  {==}
                case Sc.Desc{}:
                  {==}
            case Some{k}:
              match k:
                case Sc.Cursor{a, m}:
                  match a:
                    case Sc.NoAfter{}:
                      match m:
                        case Sc.NoMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.AscMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.DescMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.BadMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                    case Sc.BadAfter{}:
                      match m:
                        case Sc.NoMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.AscMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.DescMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.BadMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                    case Sc.SafeAfter{}:
                      match m:
                        case Sc.NoMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.AscMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.DescMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.BadMark{}:
                          match fallback:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
