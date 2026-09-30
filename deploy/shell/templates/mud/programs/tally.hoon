::  tally.hoon: plurality tally of a closed ballot, MUD §2.7
::  TEXT, NOT COMPILED: pseudocode for the NOCK lanes. Sample layout and key convention: programs/README.md.
::
::  sample   [ctx=[height=@ caller=@ room=@ now=@] inv=(list [key=@t val=@s])]
::           '0/N'  the ballot cell (org/fields.json kinds.ballot: 3 open, 4 result, 5 ncand, 16..23 vote-0..7)
::  product  ~[['0/4' winner]]  or  ~  (still open, or already has a result)
::  regime   plurality; a tie goes to the lowest candidate number (deterministic, stated in the charter:
::           charter.md {REGIME}). Another regime (approval, ranked) is another program with another id,
::           and so another {TALLY} runner or another `witnessed` identifier. DreggSolve helps a guild CHOOSE a
::           regime; it is not a kernel object (MUD §2.7).
::  output law (grammar), law.ballot:
::    6 result       field result delta == 0, or (subject == {TALLY} and field open before == 0)
::    7 result-once  field result writeOnce
::  level 3: the tally's run witnessed ('nock:' ++ H(this jam)) -- a lying returning officer is refused,
::  not caught. Until then the law guarantees only WHO wrote the result and WHEN, not that it is the count.
::
|=  [ctx=[height=@ caller=@ room=@ now=@] inv=(list [key=@t val=@s])]
^-  (list [key=@t val=@s])
|^
?.  =((get '0/3') --0)  ~                              ::  still open
?.  =((get '0/4') --0)  ~                              ::  already tallied (writeOnce would pass a same
                                                       ::  value, but there is nothing to say)
=/  ncand  (abs:si (get '0/5'))
=/  counts=(list @)                                    ::  counts.i = votes for candidate i+1
  %+  turn  (gulf 1 ncand)
  |=  c=@
  %-  lent
  %+  skim  (gulf 16 23)
  |=(f=@ =((get (cat 3 '0/' (scot %ud f))) (new:si & c)))
=/  best  (roll counts max)
?:  =(0 best)  ~                                       ::  no votes: no result
=/  w  +((need (find ~[best] counts)))                 ::  first (lowest-numbered) candidate with the max
~[['0/4' (new:si & w)]]
::
++  get
  |=  k=@t
  ^-  @s
  =/  l  inv
  |-  ?~  l  --0
  ?:  =(k key.i.l)  val.i.l
  $(l t.l)
--
