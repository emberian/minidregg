::  counter: a NockApp kernel written to NockApp's own kernel interface — the
::  arms load / peek / poke / wish, which are the arms of hoon/common/wrapper's
::  outer door and so sit at NockApp's axes (load 4, peek 22, poke 23) — over a
::  door sample at axis 6 (NockApp's STATE_AXIS). Unlike +keep it normalizes the
::  poke input with ;; rather than +soft (+soft virtualizes through +mink).
::  Poke: state +1 and the effect ~[['count' n]]; cause %exit: the effect
::  ~[[%exit 0]] (not a write). Peek: ``n.
=>
|%
+$  state  [%0 n=@]
+$  input  [eny=@ our=@ux now=@da cause=*]
--
|_  k=state
++  load
  |=  old=state
  ..load(k old)
::
++  peek
  |=  arg=path
  ^-  (unit (unit *))
  ``n.k
::
++  wish
  |=  txt=@
  ^-  *
  q:(slap !>(~) (ream txt))
::
++  poke
  |=  [num=@ ovum=*]
  ^-  [(list *) _..poke]
  =/  in  ;;(input +.ovum)
  ?:  =(cause.in %exit)  [~[[%exit 0]] ..poke]
  =/  m  +(n.k)
  [~[['count' m]] ..poke(n.k m)]
--
