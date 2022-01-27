int: h = 4;
var int: a; var int: b;
set of int: N = 1..h;
array[N] of var N: n1;
array[N] of var N: n2;

%% no entendia el problema..
constraint forall(i,j in N)(abs(i-j) >= max(i,j) - 1);

solve satisfy;