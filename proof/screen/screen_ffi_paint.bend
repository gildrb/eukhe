# eukhe: the proof of LAW screen_ffi_paint

import Base
import ../../LAWS.bend as Laws

def Laws.screen_ffi_paint(k, ok1, ok2, ok3):
  match k:
    case 0n:
      match ok1:
        case True{}:
          match ok2:
            case True{}:
              match ok3:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match ok3:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match ok2:
            case True{}:
              match ok3:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match ok3:
                case True{}:
                  {==}
                case False{}:
                  {==}
    case 1n+p:
      match p:
        case 0n:
          match ok1:
            case True{}:
              match ok2:
                case True{}:
                  match ok3:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match ok3:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match ok2:
                case True{}:
                  match ok3:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match ok3:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case 1n+q:
          match q:
            case 0n:
              match ok1:
                case True{}:
                  match ok2:
                    case True{}:
                      match ok3:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match ok3:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case False{}:
                  match ok2:
                    case True{}:
                      match ok3:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match ok3:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
            case 1n+r:
              match ok1:
                case True{}:
                  match ok2:
                    case True{}:
                      match ok3:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match ok3:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                case False{}:
                  match ok2:
                    case True{}:
                      match ok3:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
                    case False{}:
                      match ok3:
                        case True{}:
                          {==}
                        case False{}:
                          {==}
