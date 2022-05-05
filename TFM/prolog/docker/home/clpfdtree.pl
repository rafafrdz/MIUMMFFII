%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Option 4: Red Black Trees with Constraint Logic Programming over Finite Domain CLP(FD)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Red Black Nodes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(clpfd)).

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
less(X, r(Y,_,_), X) :- X #< Y.
greater(X, r(Y,_,_), X) :- Y #< X.

%% - Black node - %%
bstree(b(X, L, R)) :- greater(X,L,X), less(X, R, X), bstree(L), bstree(R).
less(X, b(Y,_,_), X) :- X #< Y.
greater(X, b(Y,_,_), X) :- Y #< X.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Balance of Black Nodes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% To control the balance (number of black node in every path)
countblack(nil, 0).
countblack(b(_,L,R), Z) :- 0 #=< N, Z #= N + 1, countblack(L, N), countblack(R,N).
countblack(r(_,L,R), N) :- 0 #=< N, countblack(L, N), countblack(R,N).

balance(b(_,L,R), N) :- countblack(L,N), countblack(R, N).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Depth of Trees
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% To control the depth of a tree
depth(nil, 0).
depth(b(_,L,R), Z) :- 0 #=< N, N #< Z, 0 #=< M, M #< Z, depth(L, N), depth(R, M).
depth(r(_,L,R), Z) :- 0 #=< N, N #< Z, 0 #=< M, M #< Z, depth(L, N), depth(R, M).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Red-Black Tree
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
redblack(X, N) :- depth(X, N), balance(X, _), bstree(X).
redblack(X) :- depth(X, _), balance(X, _), bstree(X). %% This one have sense just for to know if a given tree is a red black tree, not for generate test cases.


%% Examples.
%% X = b(13, r(8, b(1, nil, r(6, nil, nil)), b(11, nil,nil)), r(17, b(15, nil, nil), b(25, r(22, nil,nil), r(27, nil,nil)))) -- true
%% Y = b(13, r(8, nil, nil), r(6, nil, nil)) -- true

%% Google Images
%% X1 = b(12, b(5, b(3, nil, r(4, nil, nil)), r(10, b(7, r(6, nil, nil), r(8, nil, nil)), b(11, nil, nil))), b(15, b(13, nil, r(14, nil, nil)), b(17, nil, nil))) -- true
%% X2 = b(61, b(52, b(20, r(16, nil, nil), nil), b(55, nil, nil)), b(85, r(76, b(71, r(65, nil, nil), nil), b(81, nil, nil)), r(93, b(90, nil, nil), b(101, nil, nil)))) -- true

%% X = b(_A, r(_B, nil, nil), r(_C, nil, b(_D, r(_E, nil, nil), r(_F, nil, b(_G, r(_H, nil, nil), r(_I, nil, b(_J, r(_K, nil, nil), r(_L, nil, nil)))))))),
% _B#=<_A+ -1,  -> _B = 2 , _A = 3
% _A#=<_C+ -1,  -> _C = 4
% _C#=<_D+ -1,  -> _D = 5
% _D#=<_F+ -1,  -> _F = 6
% _E#=<_D+ -1,  -> _E = 4
% _F#=<_G+ -1,  -> _G = 7
% _G#=<_I+ -1,  -> _I = 8
% _H#=<_G+ -1,  -> 
% _I#=<_J+ -1,
% _J#=<_L+ -1,
% _K#=<_J+ -1 .

% _B#=<_A+ -1,
% _A#=<_C+ -1,
% _C#=<_D+ -1,
% _D#=<_F+ -1,
% _E#=<_D+ -1,
% _F#=<_G+ -1,
% _G#=<_I+ -1,
% _H#=<_G+ -1,
% _I#=<_J+ -1,
% _J#=<_L+ -1,
% _K#=<_J+ -1, _B = 2.

% res:
% _B = 2,
% _A in 3..sup,
% _A#=<_C+ -1,
% _C in 4..sup,
% _C#=<_D+ -1,
% _D in 5..sup,
% _E#=<_D+ -1,
% _D#=<_F+ -1,
% _F in 6..sup,
% _F#=<_G+ -1,
% _G in 7..sup,
% _H#=<_G+ -1,
% _G#=<_I+ -1,
% _I in 8..sup,
% _I#=<_J+ -1,
% _J in 9..sup,
% _K#=<_J+ -1,
% _J#=<_L+ -1,
% _L in 10..sup.

%% =>

% _B = 2 , _A = 3
% _C = 4
% _D = 5
% _F = 6
% _E = 4
% _G = 7
% _H = 6
% _I = 8
% _J = 9
% _K = 8
% _L = 10

%% black(X), bstree(X). -> holds
%% redblack(X). -> no holds

%% X = b(3, r(2, nil, nil), r(4, nil, b(5, r(4, nil, nil), r(6, nil, b(7, r(6, nil, nil), r(8, nil, b(9, r(8, nil, nil), r(10, nil, nil)))))))).