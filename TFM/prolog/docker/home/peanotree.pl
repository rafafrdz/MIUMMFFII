
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Option 1: Red Black Trees with Peano Arithmetic
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Definition of Peano Natural
nat(z).
nat(s(X)) :- nat(X).

eq(X,X).

% Definition of sum operation in Peano Arithemtic
sum(z, Y, Y) :- nat(Y).
sum(s(X), Y, s(Z)) :- sum(X, Y, Z).

% Definition of order relationship in Peano Arithemtic

%% (>)
ngt(z, _) :- false. %% revisar
ngt(_, z).
ngt(s(X), s(Y)) :- ngt(X,Y).

%% (>=)
ngte(X,X).
ngte(X,Y) :- ngt(X,Y).

%% (<)
nlt(_, z) :- false. %% - revisar
nlt(z, X).
nlt(s(X), s(Y)) :- nlt(X,Y).

%% (=<)
nlte(X,X).
nlte(X,Y) :- nlt(X,Y).

btwn(X, N, Y) :- nlte(X, N), nlt(N, Y).

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
less(X, r(Y,_,_), X) :- nlt(X,Y).
greater(X, r(Y,_,_), X) :- nlt(Y,X).

%% - Black node - %%
bstree(b(X, L, R)) :- greater(X,L,X), less(X, R, X), bstree(L), bstree(R).
less(X, b(Y,_,_), X) :- nlt(X,Y).
greater(X, b(Y,_,_), X) :- nlt(Y,X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Balance of Black Nodes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% To control the balance (number of black node in every path)
countblack(nil, z).
countblack(b(_,L,R), Z) :- eq(Z, s(N)), countblack(L, N), countblack(R,N).
countblack(r(_,L,R), N) :- countblack(L, N), countblack(R,N).

balance(b(_,L,R),N) :- countblack(L,N), countblack(R, N).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Depth of Trees
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% To control the depth of a tree

%% Duda para Julio
%% Debugg nlte(z,X), nlte(s(X), s(s(z))).
depth(nil, z).
depth(b(_,L,R), Z) :- nlte(z, N), nlte(s(N), Z), nlte(z, M), nlte(s(M), Z), depth(L, N), depth(R, M).
depth(r(_,L,R), Z) :- nlte(z, N), nlte(s(N), Z), nlte(z, M), nlte(s(M), Z), depth(L, N), depth(R, M).

%% Problemas para construir con depth porque no se limita en la profundidad (como se deberia esperar)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Red-Black Tree
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
redblack(X) :- balance(X, _), bstree(X).
% redblack(X, N) :- depth(X, N), balance(X, _), bstree(X).


%% Examples.
%% X = b(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))), r(s(s(s(s(s(s(s(s(z)))))))), b(s(z), nil, r(s(s(s(s(s(s(z)))))), nil, nil)), b(s(s(s(s(s(s(s(s(s(s(s(z))))))))))), nil,nil)), r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))), nil, nil), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))), r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))))))), nil,nil), r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))), nil,nil))))
%% Y = b(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))), r(s(s(s(s(s(s(s(s(z)))))))), nil, nil), r(s(s(s(s(s(s(z)))))), nil, nil))

%% X = b(13, r(8, b(1, nil, r(6, nil, nil)), b(11, nil,nil)), r(17, b(15, nil, nil), b(25, r(22, nil,nil), r(27, nil,nil)))) -- true
%% Y = b(13, r(8, nil, nil), r(6, nil, nil)) -- true