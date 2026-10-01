::  counter: a NockApp kernel (the pinned hoon/common/wrapper.hoon +keep,
::  inlined because the pipeline compiles one file). Poke: state +1, effect
::  ~[['count' n]]; cause %exit: effect ~[[%exit 0]] (not a write). Peek: ``n.
=>
|%
+$  goof    [mote=term =tang]
+$  wire    path
+$  ovum    [=wire =input]
+$  crud    [=goof =input]
+$  input   [eny=@ our=@ux now=@da cause=*]
::
++  keep
  |*  inner=mold
  =>
  |%
  +$  inner-state  inner
  +$  outer-state
    $%  [%0 desk-hash=(unit @uvI) internal=inner]
    ==
  +$  outer-fort
    $_  ^|
    |_  outer-state
    ++  load
      |~  arg=outer-state
      **
    ++  peek
      |~  arg=path
      *(unit (unit *))
    ++  poke
      |~  [num=@ ovum=*]
      *[(list *) *]
    ++  wish
      |~  txt=@
      **
    --
  ::
  +$  fort
    $_  ^|
    |_  state=inner-state
    ++  load
      |~  arg=inner-state
      *inner-state
    ++  peek
      |~  arg=path
      *(unit (unit *))
    ++  poke
      |~  arg=ovum
      [*(list *) *inner-state]
    --
  --
  ::
  |=  crash=?
  |=  inner=fort
  |=  hash=@uvI
  =<  .(desk-hash.outer `hash)
  |_  outer=outer-state
  +*  inner-fort  ~(. inner internal.outer)
  ++  load
    |=  old=outer-state
    ?+    -.old  !!
        %0
      =/  new-internal  (load:inner-fort internal.old)
      ..load(internal.outer new-internal)
    ==
  ::
  ++  peek
    |=  arg=path
    ^-  (unit (unit *))
    =/  pax  ((soft path) arg)
    ?~  pax  ~
    (peek:inner-fort u.pax)
  ::
  ++  wish
    |=  txt=@
    ^-  *
    q:(slap !>(~) (ream txt))
  ::
  ++  poke
    |=  [num=@ ovum=*]
    ^-  [(list *) _..poke]
    =/  effects=(list *)  ?:(crash ~[exit/0] ~)
    ?+   ovum  effects^..poke
        [[%$ %arvo ~] *]
      =/  g  ((soft crud) +.ovum)
      ?~  g  effects^..poke
      ?:  ?=(%intr mote.goof.u.g)
        [effects ..poke]
      =-  [effects ..poke]
      (slog tang.goof.u.g)
    ::
        [[%poke *] *]
      =/  ovum  ((soft ^ovum) ovum)
      ?~  ovum  ~^..poke
      =/  o  ((soft input) input.u.ovum)
      ?~  o
        ~^..poke
      =^  effects  internal.outer
        (poke:inner-fort u.ovum)
      [effects ..poke(internal.outer internal.outer)]
    ==
  --
::
+$  state  [%0 n=@]
++  moat  (keep state)
--
=/  inner
  ^-  fort:moat
  |_  k=state
  ++  load  |=(old=state old)
  ++  peek
    |=  =path
    ^-  (unit (unit *))
    ``n.k
  ++  poke
    |=  =ovum:moat
    ^-  [(list *) state]
    ?:  =(cause.input.ovum %exit)  [~[[%exit 0]] k]
    =/  m  +(n.k)
    [~[['count' m]] k(n m)]
  --
(((moat |) inner) `@uvI`0)
