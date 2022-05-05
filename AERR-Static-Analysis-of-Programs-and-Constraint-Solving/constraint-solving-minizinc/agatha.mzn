include "globals.mzn";

int: n = 3;
set of int: r = 1..3;

% Persons
r: agatha  = 1;
r: butler  = 2;
r: charles = 3;

var r: the_killer;
var r: the_victim;

array[r,r] of var 0..1: hates;
array[r,r] of var 0..1: richer;

solve satisfy;

constraint
    hates[the_killer, the_victim] = 1  /\
    richer[the_killer, the_victim] = 0 /\
    forall(i in r) ( richer[i,i] = 0 )  /\
    forall(i, j in r where i != j) ( richer[i,j] = 1 <-> richer[j,i] = 0 ) /\ 
    forall(i in r) (hates[charles, i] = 0 <- hates[agatha, i] = 1) /\ 
    hates[agatha, charles] = 1 /\ 
    hates[agatha, agatha] = 1 /\
    hates[agatha, butler] = 0 /\ 
    forall(i in r) ( hates[butler, i] = 1 <- richer[i, agatha] = 0 ) /\ 
    forall(i in r) ( hates[butler, i] = 1 <- hates[agatha, i] = 1) /\
    forall(i in r) ( sum(j in r) (hates[i,j]) <= 2) /\
    the_victim = agatha
    ;


%% Solution:
%% There is not enough information about certain relations
%% in the hates and richer matrices to yield a unique solution.

output [
  "Killer: ", show(the_killer), "\n",
  "Victim: ", show(the_victim),
] ++ 
["\nHates:"] ++
[
  if j = 1 then "\n" else " " endif ++
    show(hates[i,j])
  | i, j in r
] ++ ["\nRicher:"] ++
[
  if j = 1 then "\n" else " " endif ++
    show(richer[i,j])
  | i, j in r
] ++
[ "\n" ]
++
[
  "Hates: ", show(hates), "\n",
  "Richer: ", show(richer), "\n"
]
;