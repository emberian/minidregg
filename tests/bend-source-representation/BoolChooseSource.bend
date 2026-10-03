import Base

def SourceBool.choose(c: Bool, a: Bool, b: Bool) -> Bool:
  match c:
    case False{}:
      b
    case True{}:
      a
