natural(0).
natural(s(X)) :- natural(X).

lq(0,X) :- natural(X).
lq(s(X),s(Y)) :- lq(X,Y).

plus(0,X,X) :- natural(X).
plus(s(X),Y,s(Z)) :- plus(X,Y,Z).

times(0, X ,0) :- natural(X).
times(s(X),Y,Z) :- times(X,Y,C),plus(C,Y,Z).

factorial(0,s(0)).
factorial(s(X),Y) :- factorial(X,C), times(s(X),C,Y).