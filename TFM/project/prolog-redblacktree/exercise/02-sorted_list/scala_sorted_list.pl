:- use_module(library(clpfd)).

%% Implementation of lists Scala' style
list(nil).
list(cons(_, Xs)) :- list(Xs).

%% Implementation of sorted lists Scala' style
sordlist(nil).
sordlist(cons(_,nil)).
sordlist(cons(X, cons(Y, Xs))) :- X #=< Y, sordlist(cons(Y,Xs)).