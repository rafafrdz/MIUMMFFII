%% Author: Rafael Fernandez Ortiz
%% Language: Erlang

-module(ex1).
-compile(nowarn_export_all).
-compile(export_all). 

% Exercise 0
fib(0) -> 0;
fib(1) -> 1;
fib(N) when N > 1 -> fib(N-1) + fib(N-2).

% Exercise 1
sum([]) -> 0;
sum([H|T]) when is_integer(H) -> H + sum(T);
sum([_|T]) -> sum(T).

% Exercise 2
member(_, []) -> false;
member(E, [E |_]) -> true;
member(E, [_ | LS])-> member(E, LS).

% Exercise 2.5
insert(N, []) -> [N];
insert(N, [T | LS]) when N < T -> [N, T | LS];
insert(N, [T | LS]) -> [T | insert(N, LS)].

% Exercise 3
sort([]) -> [];
sort([H|L]=XS) ->
    sort([X || X <- L, X < H]) ++
    [X || X <- XS, X == H] ++
    sort([X || X <- L, X > H]).

% Exercise 4
% fibonnaci with index
fibix(N) -> {N, fib(N)}.

% Exercise 5
keyfind(_,[]) -> false;
keyfind(K, [{K, V} | _]) -> {K,V};
keyfind(K, [{_, _} | T]) -> keyfind(K, T).

% Auxiliar function to try keyfind
createfibindx(-1) -> [];
createfibindx(N) -> [fibix(N)] ++ createfibindx(N-1).

%% res:
%% ex1:keyfind(4, ex1:createfibindx(4)). -> {4,3}
%% ex1:keyfind(2, ex1:createfibindx(4)). -> {2,1}
%% ex1:keyfind(8, ex1:createfibindx(4)). -> false

% Exercise 6
merge([], []) -> [];
merge([], X) -> X;
merge(X, []) -> X;
merge([X | XS], [Y | _] = L) when X < Y -> [X | merge(XS, L)];
merge(L, [Y | YS]) -> [Y | merge(L,YS)].