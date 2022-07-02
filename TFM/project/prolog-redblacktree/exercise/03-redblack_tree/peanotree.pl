
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Option 1: Red Black Trees with Peano Arithmetic
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- discontiguous bstree/1.
:- discontiguous less/3.
:- discontiguous greater/3.


% Definition of Peano Natural
nat(z).
nat(s(X)) :- nat(X).

eq(X,X).

% Definition of sum operation in Peano Arithemtic
sum(z, Y, Y) :- nat(Y).
sum(s(X), Y, s(Z)) :- sum(X, Y, Z).

% Definition of order relationship in Peano Arithemtic

%% (<)
lt(s(X), X) :- 3 < 2.
lt(z, s(_)).
lt(s(X), s(Y)) :- lt(X, Y).

%% (=<)
lte(X, X).
lte(X, Y) :- lt(X, Y).

%% (>)
gt(X, Y) :- lt(Y, X).

%% (>=)
gte(X, Y) :- lte(Y, X).

btwn(X, N, Y) :- lte(X, N), lt(N, Y).
%% lte(z, N), lt(N, s(s(s(s(z))))).

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
less(X, r(Y,_,_), X) :- lt(X,Y).
greater(X, r(Y,_,_), X) :- lt(Y,X).

%% - Black node - %%
bstree(b(X, L, R)) :- greater(X,L,X), less(X, R, X), bstree(L), bstree(R).
less(X, b(Y,_,_), X) :- lt(X,Y).
greater(X, b(Y,_,_), X) :- lt(Y,X).

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
depth(nil, z).
depth(b(_,L,R), Z) :- btwn(z, N, Z), btwn(z, M, Z), depth(L, N), depth(R, M).
depth(r(_,L,R), Z) :- btwn(z, N, Z), btwn(z, M, Z), depth(L, N), depth(R, M).

% ?- depth(X, s(s(z))).
% X = b(_, nil, nil) ;
% X = b(_, nil, b(_, nil, nil)) ;
% X = b(_, nil, r(_, nil, nil)) ;
% X = b(_, b(_, nil, nil), nil) ;
% X = b(_, r(_, nil, nil), nil) ;
% X = b(_, b(_, nil, nil), b(_, nil, nil)) ;
% X = b(_, b(_, nil, nil), r(_, nil, nil)) ;
% X = b(_, r(_, nil, nil), b(_, nil, nil)) ;
% X = b(_, r(_, nil, nil), r(_, nil, nil)) ;
% X = r(_, nil, nil) ;
% X = r(_, nil, b(_, nil, nil)) ;
% X = r(_, nil, r(_, nil, nil)) ;
% X = r(_, b(_, nil, nil), nil) ;
% X = r(_, r(_, nil, nil), nil) ;
% X = r(_, b(_, nil, nil), b(_, nil, nil)) ;
% X = r(_, b(_, nil, nil), r(_, nil, nil)) ;
% X = r(_, r(_, nil, nil), b(_, nil, nil)) ;
% X = r(_, r(_, nil, nil), r(_, nil, nil)) ;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Red-Black Tree
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
redblack(X) :- balance(X, _), bstree(X).
redblack(X, N) :- depth(X, N), balance(X, _), bstree(X).


%% Examples.
%% X = b(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))), r(s(s(s(s(s(s(s(s(z)))))))), b(s(z), nil, r(s(s(s(s(s(s(z)))))), nil, nil)), b(s(s(s(s(s(s(s(s(s(s(s(z))))))))))), nil,nil)), r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))), nil, nil), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))), r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))))))), nil,nil), r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))), nil,nil))))
%% Y = b(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))), r(s(s(s(s(s(s(s(s(z)))))))), nil, nil), r(s(s(s(s(s(s(z)))))), nil, nil))

%% Google Examples
%% X1 = b(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))), b(s(s(s(s(s(z))))), b(s(s(s(z))), nil, r(s(s(s(s(z)))), nil, nil)), r(s(s(s(s(s(s(s(s(s(s(z)))))))))), b(s(s(s(s(s(s(s(z))))))), r(s(s(s(s(s(s(z)))))), nil, nil), r(s(s(s(s(s(s(s(s(z)))))))), nil, nil)), b(s(s(s(s(s(s(s(s(s(s(s(z))))))))))), nil, nil))), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))), b(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))), nil, r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))), nil, nil)), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))), nil, nil)))
%% X2 = b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))))))))))))))))))))))))))))))))))))), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))))), r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))), nil, nil), nil), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))))))))))))))))))))))), nil, nil)), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), nil, nil), nil), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), nil, nil)), r(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), nil, nil), b(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), nil, nil))))


%% Examples above in natural numbers terms
%% X = b(13, r(8, b(1, nil, r(6, nil, nil)), b(11, nil,nil)), r(17, b(15, nil, nil), b(25, r(22, nil,nil), r(27, nil,nil)))) -- true
%% Y = b(13, r(8, nil, nil), r(6, nil, nil)) -- true
%% X1 = b(12, b(5, b(3, nil, r(4, nil, nil)), r(10, b(7, r(6, nil, nil), r(8, nil, nil)), b(11, nil, nil))), b(15, b(13, nil, r(14, nil, nil)), b(17, nil, nil))) -- true
%% X2 = b(61, b(52, b(20, r(16, nil, nil), nil), b(55, nil, nil)), b(85, r(76, b(71, r(65, nil, nil), nil), b(81, nil, nil)), r(93, b(90, nil, nil), b(101, nil, nil)))) -- true