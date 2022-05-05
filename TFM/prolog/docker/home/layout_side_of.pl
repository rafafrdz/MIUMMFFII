left_of(sandclock, pencil).
left_of(buttlefly, sandclock).
left_of(fish, buttlefly).
above(pencil, byke).
above(buttlefly, camera).

right_of(O1, O2) :- left_of(O2, O1).
left_of(O2, O1) :- left_of(O2, O3), left_of(O3, O1).
below(O1, O2) :- above(O2, O1).