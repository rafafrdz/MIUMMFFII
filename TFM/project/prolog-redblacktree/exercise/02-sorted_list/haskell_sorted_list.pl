:- use_module(library(clpfd)).

%% Implementation of lists Haskell' style
list([]).
list(_:Xs) :- list(Xs).

%% Implementation of sorted lists Haskell' style
sordlist([]).
sordlist(_:[]).
sordlist(X:Y:Xs) :- X #=< Y, sordlist(Y:Xs).