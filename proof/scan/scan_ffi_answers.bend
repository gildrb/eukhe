# eukhe: the proof of LAW scan_ffi_answers

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

# PROOF of LAW scan_ffi_answers: case on every field of the request: no field holds a number past a tag, so each spelled request decodes and answers by computation.

def Scan.scan_ffi_answers(q):
  match q:
    case FSc.QStart{asked, c, f}:
      match asked:
        case None{}:
          match c:
            case None{}:
              match f:
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
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.AscMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.DescMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.BadMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                    case Sc.BadAfter{}:
                      match m:
                        case Sc.NoMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.AscMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.DescMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.BadMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                    case Sc.SafeAfter{}:
                      match m:
                        case Sc.NoMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.AscMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.DescMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
                        case Sc.BadMark{}:
                          match f:
                            case Sc.Asc{}:
                              {==}
                            case Sc.Desc{}:
                              {==}
        case Some{o}:
          match o:
            case Sc.Asc{}:
              match c:
                case None{}:
                  match f:
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
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.AscMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.DescMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.BadMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                        case Sc.BadAfter{}:
                          match m:
                            case Sc.NoMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.AscMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.DescMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.BadMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                        case Sc.SafeAfter{}:
                          match m:
                            case Sc.NoMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.AscMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.DescMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.BadMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
            case Sc.Desc{}:
              match c:
                case None{}:
                  match f:
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
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.AscMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.DescMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.BadMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                        case Sc.BadAfter{}:
                          match m:
                            case Sc.NoMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.AscMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.DescMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.BadMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                        case Sc.SafeAfter{}:
                          match m:
                            case Sc.NoMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.AscMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.DescMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
                            case Sc.BadMark{}:
                              match f:
                                case Sc.Asc{}:
                                  {==}
                                case Sc.Desc{}:
                                  {==}
    case FSc.QId{c}:
      match c:
        case None{}:
          {==}
        case Some{a}:
          match a:
            case Sc.NoAfter{}:
              {==}
            case Sc.BadAfter{}:
              {==}
            case Sc.SafeAfter{}:
              {==}
