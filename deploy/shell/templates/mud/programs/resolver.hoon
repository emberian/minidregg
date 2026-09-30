::  resolver.hoon: combat resolution, MUD §2.3 / affliction-table.json
::  TEXT, NOT COMPILED: pseudocode for the NOCK lanes. Sample layout and key convention: programs/README.md.
::
::  sample   [ctx=[height=@ caller=@ room=@ now=@] inv=(list [key=@t val=@s])]
::           inv holds every field of joint 0 (attacker sheet) and joint 1 (defender sheet),
::           keys '0/N' and '1/N' with N from sheet/fields.json:
::             0 id  1 at  2 hp  3 bal  4 eq  5 alive  6 deaths  7 intent  8 target  9 respawn
::             10 aff-asthma  11 aff-paralysis  12 aff-clumsiness  13 def-ward  14 skill
::           the skill is the attacker's own signed choice, field 14 (sheet/fields.json skillCodes)
::  product  (list [key=@t val=@s])  the writes; the referee submits them as ONE command whose targets are
::           [attacker, defender] (+ a separate K-WELL burn of essence when the defender dies)
::  output law (grammar; installed on BOTH sheets as law.management ; law.sheet):
::    on joint 1  maxhit      not (field hp delta <= {MAXHIT_LT})
::                attacker    hp down or aff up  =>  j0 intent before in {1,2}, j0 target before = my id,
::                            j0 alive, same room, me alive before
::                attacker-paid  j0 bal before <= now, j0 bal after >= now + COST       (leSlotsOff)
::                dead-at-zero / deaths-count / death-timer  (hp <= 0 => alive 0, deaths +1, respawn >= now+RESPAWN)
::                ward        def-ward before = 1 => aff-paralysis does not rise
::    on joint 0  bal-paid    bal after >= now + COST, never lowered;  intent-clear  intent, target := 0
::  level 3: + witnessed {VK_RESOLVER} on both (law.sheet-witnessed), H(this jam) = VK_RESOLVER
::
|=  [ctx=[height=@ caller=@ room=@ now=@] inv=(list [key=@t val=@s])]
^-  (list [key=@t val=@s])
|^
=/  a-intent   (get '0/7')
=/  a-target   (get '0/8')
=/  a-at       (get '0/1')
=/  a-alive    (get '0/5')
=/  a-clumsy   (get '0/12')
=/  d-id       (get '1/0')
=/  d-at       (get '1/1')
=/  d-hp       (get '1/2')
=/  d-alive    (get '1/5')
=/  d-deaths   (get '1/6')
=/  d-ward     (get '1/13')
=/  sk         (skill (abs:si (get '0/14')))
::  1. nothing to resolve, or an intent that can no longer land: clear it, write nothing else
?.  ?&  |(=(a-intent --1) =(a-intent --2))
        =(a-target d-id)  =(a-alive --1)  =(d-alive --1)  =(a-at d-at)
    ==
  :~  ['0/7' --0]  ['0/8' --0]  ['0/14' --0]  ==
::  2. damage: the table's, minus one if the attacker is clumsy, floored at 0 (never above MAXHIT: the table
::     is validated against MAXHIT, and the law refuses the write anyway if it were)
=/  dmg=@s   (max:si --0 (dif:si dmg.sk ?:(=(a-clumsy --1) --1 --0)))
=/  hp2=@s   (dif:si d-hp dmg)
::  3. the affliction, unless the ward blocks it
=/  aff=(unit @t)
  ?~  aff.sk  ~
  ?:  &(=(u.aff.sk '1/11') =(d-ward --1))  ~          ::  ward blocks paralysis
  `u.aff.sk
::  4. the attacker pays: bal (strike) or eq (cast) := now + cost
=/  pay=[key=@t val=@s]
  ?:  =(a-intent --1)  ['0/3' (sum:si (new:si & now.ctx) cost.sk)]
  ['0/4' (sum:si (new:si & now.ctx) cost.sk)]
=/  attacker=(list [key=@t val=@s])  :~(pay ['0/7' --0] ['0/8' --0] ['0/14' --0])
::  5. the defender: hp, the affliction, and death if hp <= 0 (death is a write, never a refusal)
=/  defender=(list [key=@t val=@s])
  %+  weld
    ?~(aff ~ [[u.aff --1] ~])
  ?:  =(--1 (cmp:si hp2 --0))                          ::  hp2 > 0: alive
    :~  ['1/2' hp2]  ==
  :~  ['1/2' hp2]
      ['1/5' --0]
      ['1/6' (sum:si d-deaths --1)]
      ['1/9' (sum:si (new:si & now.ctx) (respawn d-id))]  ::  must meet the sheet's {RESPAWN_M1} (death-timer)
  ==
(weld attacker defender)
::
++  respawn                                            ::  per-sheet RESPAWN: area.json spawns, bound when
  |=  id=@s                                            ::  the areas load (mob subjects are known then);
  ^-  @s                                               ::  players get realm.json constants.RESPAWN (0)
  ?:  =(id {RAT})      --20
  ?:  =(id {RATKING})  --200
  --0
++  skill                                              ::  affliction-table.json skills, compiled in
  |=  n=@
  ^-  [dmg=@s aff=(unit @t) cost=@s]
  ?+  n  [--0 ~ --3]
    %1  [--3 `'1/10' --3]                             ::  bite:    strike, 3, asthma,    bal 3
    %2  [--2 `'1/11' --3]                             ::  envenom: strike, 2, paralysis, bal 3
    %3  [--4 `'1/10' --3]                             ::  gnaw:    strike, 4, asthma,    bal 3 (mob)
    %4  [--1 `'1/12' --4]                             ::  gust:    cast,   1, clumsiness, eq 4
  ==
++  get                                                ::  linear lookup, --0 if absent (NOCK.md §5's get)
  |=  k=@t
  ^-  @s
  =/  l  inv
  |-  ?~  l  --0
  ?:  =(k key.i.l)  val.i.l
  $(l t.l)
--
