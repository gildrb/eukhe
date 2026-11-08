# eukhe: the proof of LAW tool_call_gate_is_spec
# Every question, case by case: the entry spells the spec's answer.

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../spec/harness/effect.bend as Sp
import ./base.bend as LA

def ToolCall.tool_call_gate_is_spec(q):
  match q:
    case Tc.Enter{f, t}:
      match f:
        case True{}:
          match t:
            case Tc.Gone{}:
              {==}
            case Tc.Offered{tr}:
              match tr:
                case Tc.Safe{}:
                  {==}
                case Tc.Unsafe{}:
                  {==}
        case False{}:
          match t:
            case Tc.Gone{}:
              {==}
            case Tc.Offered{tr}:
              match tr:
                case Tc.Safe{}:
                  {==}
                case Tc.Unsafe{}:
                  {==}
    case Tc.Recover{f, p, t}:
      match f:
        case True{}:
          match p:
            case Tc.Safe{}:
              match t:
                case Tc.Gone{}:
                  {==}
                case Tc.Offered{tr}:
                  match tr:
                    case Tc.Safe{}:
                      {==}
                    case Tc.Unsafe{}:
                      {==}
            case Tc.Unsafe{}:
              match t:
                case Tc.Gone{}:
                  {==}
                case Tc.Offered{tr}:
                  match tr:
                    case Tc.Safe{}:
                      {==}
                    case Tc.Unsafe{}:
                      {==}
        case False{}:
          match p:
            case Tc.Safe{}:
              match t:
                case Tc.Gone{}:
                  {==}
                case Tc.Offered{tr}:
                  match tr:
                    case Tc.Safe{}:
                      {==}
                    case Tc.Unsafe{}:
                      {==}
            case Tc.Unsafe{}:
              match t:
                case Tc.Gone{}:
                  {==}
                case Tc.Offered{tr}:
                  match tr:
                    case Tc.Safe{}:
                      {==}
                    case Tc.Unsafe{}:
                      {==}
    case Tc.Stop{f, x, i}:
      match f:
        case True{}:
          match x:
            case True{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match x:
            case True{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match i:
                case True{}:
                  {==}
                case False{}:
                  {==}
