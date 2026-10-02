::  liar: a program that names the job truth field but ignores the input and
::  always answers 9. A caller who runs it instead of the job program gets the
::  run slot of THIS program, not the job program, and the job law refuses.
|=  [ctx=[height=@ caller=@ room=@] inv=(list [key=@t val=@])]
^-  (list [key=@t val=@])
~[[%truth 9]]
