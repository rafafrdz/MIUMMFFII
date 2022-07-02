list([]).
list(X|Xs) :- list(Xs).


replace(A, B, A, B).
replace(A, B, X, X).

select(X, X|Xs, Xs).
select(Z, X|Xs, X|Ys) :- Z=\=X, select(X, Xs, Ys).
insert(X, Xs, X|Xs).

member(X,X|Xs).
member(X,Y|Ys) :- member(X, Ys).

% 3.3.1 Exercise for section 3.3
% i.
substitute(_, _, [], []).
substitute(X, Y, X|Xs, Y|Ys) :- substitute(X, Y, Xs, Ys).
substitute(X, Y, Z|Zs, Z|Ys) :- Z \= X, substitute(X, Y, Zs, Ys).

%% 1.(v2)
substitute2(_, _, [], []).
substitute2(X, Y, Z|Zs, P|Ps) :- replace(X,Y,Z,P), substitute2(X, Y, Zs, Ps).

% iii.
no_doubles(_, []).
no_doubles(X|Xs, Y|Ys) :- member(X, Y|Ys), no_doubles(Xs,Ys).
