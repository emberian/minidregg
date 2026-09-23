import Host.Main

open Minidregg.Host

def zeros (count : Nat) : String := String.ofList (List.replicate count '0')

def validLine : String :=
  "fn-portable-v1 " ++ zeros 64 ++ " " ++ zeros 96 ++ " " ++ zeros 64 ++
  " " ++ zeros 3904 ++ " 41\n"

def refused (line : String) : Bool :=
  match parseFnPortableLine line with
  | .error _ => true
  | .ok _ => false

#guard !(refused validLine)
#guard refused (validLine ++ "junk")
#guard refused (validLine.replace "fn-portable-v1" "fn-portable-v2")
#guard refused (validLine.replace " 41\n" " 41 extra\n")
#guard refused (validLine.replace " 41\n" " 41")
#guard refused (validLine.replace " 41\n" " 4A\n")
#guard refused (validLine.replace (zeros 3904) (zeros 3902))
