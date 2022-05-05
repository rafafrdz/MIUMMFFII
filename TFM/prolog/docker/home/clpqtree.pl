%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Option 3: Red Black Trees with Constraint Logic Programming over Rationals CLP(Q)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Red Black Nodes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(clpq)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Red Black Nodes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Is either red node or black node
isblackorred(X) :- red(X).
isblackorred(X) :- black(X).

%% Definition of red node
red(r(_,L,R)) :- black(L), black(R).

%% Definition of black node
black(nil).
black(b(_,L,R)) :- isblackorred(L), isblackorred(R).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Implementation of Binary Search Tree for Red and Black Nodes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% - Nil - %%
bstree(nil).
less(X, nil, X).
greater(X, nil, X).

%% - Red node - %%
bstree(r(X, L, R)) :- greater(X,L,X), less(X, R, X), bstree(L), bstree(R).
less(X, r(Y,_,_), X) :- clpq:{X < Y}.
greater(X, r(Y,_,_), X) :- clpq:{Y < X}.

%% - Black node - %%
bstree(b(X, L, R)) :- greater(X,L,X), less(X, R, X), bstree(L), bstree(R).
less(X, b(Y,_,_), X) :- clpq:{X < Y}.
greater(X, b(Y,_,_), X) :- clpq:{Y < X}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Balance of Black Nodes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% To control the balance (number of black node in every path)
countblack(nil, 0).
countblack(b(_,L,R), Z) :- clpq:{0 =< N},  clpq:{Z = N + 1}, countblack(L, N), countblack(R,N).
countblack(r(_,L,R), N) :- clpq:{0 =< N}, countblack(L, N), countblack(R,N).

balance(b(_,L,R), N) :- countblack(L,N), countblack(R, N).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Depth of Trees
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% To control the depth of a tree
depth(nil, 0).
depth(b(_,L,R), Z) :- clpq:{0 =< N, N + 1 =< Z, 0 =< M, M + 1 =< Z}, depth(L, N), depth(R, M).
depth(r(_,L,R), Z) :- clpq:{0 =< N, N + 1 =< Z, 0 =< M, M + 1 =< Z}, depth(L, N), depth(R, M).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Red-Black Tree
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
redblack(X, N) :- depth(X, N), balance(X, _), bstree(X).
redblack(X) :- depth(X, _), balance(X, _), bstree(X).


%% Examples.
%% X = b(13, r(8, b(1, nil, r(6, nil, nil)), b(11, nil,nil)), r(17, b(15, nil, nil), b(25, r(22, nil,nil), r(27, nil,nil)))) -- true
%% Y = b(13, r(8, nil, nil), r(6, nil, nil)) -- true

%% Google Images
%% X1 = b(12, b(5, b(3, nil, r(4, nil, nil)), r(10, b(7, r(6, nil, nil), r(8, nil, nil)), b(11, nil, nil))), b(15, b(13, nil, r(14, nil, nil)), b(17, nil, nil))) -- true
%% X2 = b(61, b(52, b(20, r(16, nil, nil), nil), b(55, nil, nil)), b(85, r(76, b(71, r(65, nil, nil), nil), b(81, nil, nil)), r(93, b(90, nil, nil), b(101, nil, nil)))) -- true


%% b(_A, r(_B, nil, nil), r(_C, nil, nil)),
%% {_D>0, _C=_A+_D, _B=_A-_E, _E>0}
%% b(9, r(8, nil, nil), r(11, nil, nil)).

%% b(_A, r(_B, nil, nil), r(_C, nil, b(_D, r(_E, nil, nil), r(_F, nil, nil))))
%% b(_A, r(_B, nil, nil), r(_C, nil, b(_D, r(_E, nil, nil), r(_F, nil, b(_G, r(_H, nil, nil), r(_I, nil, nil))))))