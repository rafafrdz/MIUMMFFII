%%////////////////////////////////////////////////////////////////////////////////////////////%

%% -- Comentarios.
%% -- Estos son solo unas implementaciones para tenerlas como idea base para la implementacion
%% -- del los red-black trees

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Binary Tree
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%
%% tree(nil).
%% tree(t(_,L,R)) :- tree(L), tree(R).
%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Binary Search Tree
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%
%% binarytree(nil).
%% binarytree(br(X, L, R)) :- greater(X,L,X), less(X, R, X), binarytree(L), binarytree(R).
%%
%% greater(X,nil,X).
%% greater(X, br(Y,_,_), X) :- Y =< X.
%%
%% less(X,nil,X).
%% less(X, br(Y,_,_), X) :- X =< Y.
%%

%%////////////////////////////////////////////////////////////////////////////////////////////%


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
binarytree(nil).
less(X, nil, X).
greater(X, nil, X).

%% - Red node - %%
binarytree(r(X, L, R)) :- greater(X,L,X), less(X, R, X), binarytree(L), binarytree(R).
less(X, r(Y,_,_), X) :- X < Y.
greater(X, r(Y,_,_), X) :- Y < X.

%% - Black node - %%
binarytree(b(X, L, R)) :- greater(X,L,X), less(X, R, X), binarytree(L), binarytree(R).
less(X, b(Y,_,_), X) :- X < Y.
greater(X, b(Y,_,_), X) :- Y < X.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Balance of Black Nodes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

countblack(nil, 0).
countblack(b(_,L,R), N) :- countblack(L, Nl), countblack(R,Nr), N is Nl + Nr + 1.
countblack(r(_,L,R), N) :- countblack(L, Nl), countblack(R,Nr), N is Nl + Nr.

balanceblack(b(_,L,R)) :- countblack(L,N), countblack(R, N). %% -- Aqui tengo mis dudas.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Red-Black Tree
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
redblack(X) :- black(X), binarytree(X), balanceblack(X).


%% Examples.
%% X = b(13, r(8, b(1, nil, r(6, nil, nil)), b(11, nil,nil)), r(17, b(15, nil, nil), b(25, r(22, nil,nil), r(27, nil,nil)))) -- true
%% Y = b(13, r(8, nil, nil), r(6, nil, nil)) -- true