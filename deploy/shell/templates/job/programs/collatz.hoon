::  collatz: a job program (COMPUTE, the J-JOB floor). A bare gate over the
::  kernel sample; the job input is the sample key input (the job field 2),
::  and the one write it names is truth: the number of Collatz steps from the
::  input down to 1 (0 for an input of 0). The job law compares it with the
::  provider output field.
|=  [ctx=[height=@ caller=@ room=@] inv=(list [key=@t val=@])]
^-  (list [key=@t val=@])
|^  =/  n  (get %input)
    ?:  =(0 n)  ~[[%truth 0]]
    =/  steps  0
    |-  ^-  (list [key=@t val=@])
    ?:  =(1 n)  ~[[%truth steps]]
    %=  $
      steps  +(steps)
      n      ?:(=(0 (mod n 2)) (div n 2) +((mul 3 n)))
    ==
++  get
  |=  key=@t
  ^-  @
  =/  l  inv
  |-  ?~  l  0
  ?:  =(key key.i.l)  val.i.l
  $(l t.l)
--
