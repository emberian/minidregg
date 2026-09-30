::  rat.hoon: a mob's behaviour, MUD §2.5 (wander / strike / flee / respawn)
::  TEXT, NOT COMPILED: pseudocode for the NOCK lanes. Sample layout and key convention: programs/README.md.
::
::  A mob is a sheet {REALM}-mob-{M} whose subject M is the mob's own enrolled key, held by the referee
::  process. So the mob's moves and strikes are OWNER turns under law.sheet, the same law a player's are:
::  it cannot walk through the locked door without the key, cannot re-enter the dark cellar without a
::  lantern (it spawns there, and the revive's `at := HOME` is the referee's clause 20, not a move), and
::  cannot hit harder than MAXHIT. Death and respawn are the referee's writes (resolver.hoon and the revive).
::
::  sample   [ctx=[height=@ caller=@ room=@ now=@] inv=(list [key=@t val=@s])]
::           '0/N'  the rat's own sheet (sheet/fields.json)
::           '1/N'  its current room (room/fields.json: 0 id, 2 dark, 8+3k exit-DIR_k, 9+3k locked-DIR_k)
::           'p/I'  I = 0..7: the subjects whose sheets are observed to be in the rat's room (the runner reads
::                  `at` over the area's sheets, MUD §2.0, and passes their ids; ASSUMED key form 'p/I')
::           'h/I'  1 if subject p/I is hostile to rats (a player who struck a rat; the referee's journal)
::  product  ONE of
::           - strike:  ~[['0/7' --1] ['0/8' target] ['0/14' --3]]       intent strike, skill gnaw
::           - flee:    ~[['0/1' next] ['0/7' --4]]                        a go that pays balance
::           - wander:  ~[['0/1' next]]                                    a go along the wander list
::           - pray:    ~[['0/7' --9]]                                     when dead: the referee revives it
::                                                                         once now >= respawn (clause 23)
::           - ~        nothing to do this tick
::  output law (grammar), the owner clauses of law.sheet with {S} = M:
::    owner-alive   alive before = 1, or the write is exactly intent := 9
::    bal           intent in {1,3,4} => leSlots field bal before clock now          (K-CLOCK)
::    paralysis     aff-paralysis before = 1 => no physical intent, no move
::    move-from / move-to / exits / door / dark                                       (K-JOINT-INDEX)
::      the go command's targets are [rat sheet, room now, next room]
::
|=  [ctx=[height=@ caller=@ room=@ now=@] inv=(list [key=@t val=@s])]
^-  (list [key=@t val=@s])
|^
=/  alive   (get '0/5')
=/  hp      (get '0/2')
=/  bal     (get '0/3')
=/  here    (get '0/1')
?.  =(alive --1)
  ~[['0/7' --9]]                                       ::  dead: pray; the revive waits for respawn
=/  ready=?  !=(--1 (cmp:si bal (new:si & now.ctx)))   ::  bal <= now
=/  foe=(unit @s)  (first-hostile 0)
::  flee at hp < FLEE_AT, if balanced and an open, lit exit exists
?:  &(ready =(-1 (cmp:si hp {FLEE_AT})))
  =/  n  (next here)
  ?~  n  ~
  ~[['0/1' u.n] ['0/7' --4]]
::  strike the first hostile player here, if balanced
?:  &(ready ?=(^ foe))
  ~[['0/7' --1] ['0/8' u.foe] ['0/14' --3]]
::  otherwise wander, every WANDER_EVERY ticks (deterministic: the tick number decides, no dice)
?.  =(0 (mod now.ctx {WANDER_EVERY}))  ~
=/  n  (next here)
?~  n  ~
~[['0/1' u.n]]
::
++  wander  ~[--201 --203 --205 --203]                ::  area.json spawns[0].wander, bound at load;
                                                       ::  201 -> 203, then 203 <-> 205 (201 is dark)
++  next                                               ::  the wander-list successor of `here`, if the
  |=  here=@s                                          ::  current room has an unlocked exit to it and
  ^-  (unit @s)                                        ::  it is not dark (the rat has no lantern)
  =/  i  (find ~[here] wander)
  ?~  i  ~
  =/  to  (snag (mod +(u.i) (lent wander)) wander)
  ?.  (exit-to to)  ~
  ?:  =(to --201)  ~                                   ::  the cellar is dark: law.sheet clause 18
  `to
++  exit-to                                            ::  some DIR_k with exit = to and locked = 0
  |=  to=@s
  ^-  ?
  =/  k  0
  |-  ?:  =(k 12)  |
  ?:  &(=((get (key 1 (add 8 (mul 3 k)))) to) =((get (key 1 (add 9 (mul 3 k)))) --0))  &
  $(k +(k))
++  first-hostile
  |=  i=@
  ^-  (unit @s)
  ?:  =(i 8)  ~
  =/  p  (get (cat 3 'p/' (scot %ud i)))
  ?:  &(!=(p --0) =((get (cat 3 'h/' (scot %ud i))) --1))  `p
  $(i +(i))
++  key  |=([t=@ n=@] (rap 3 ~[(scot %ud t) '/' (scot %ud n)]))
++  get                                                ::  linear lookup, --0 if absent
  |=  k=@t
  ^-  @s
  =/  l  inv
  |-  ?~  l  --0
  ?:  =(k key.i.l)  val.i.l
  $(l t.l)
--
