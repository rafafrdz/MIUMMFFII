%% Author: Rafael Fernandez Ortiz
%% Language: Erlang

-module(hor).
-compile(nowarn_export_all).
-compile(export_all).


% Exercise 1 - implement all(F,L)
all(F,[L]) -> F(L);
all(F,[L|Ls]) -> F(L) and all(F,Ls).

% Example:
%   all(fun (X) -> X > 5 end, [1,8,9])
%   returns false since 1 is less than 5.


% Exercise 2 - implement foldl and foldr
foldl(_, Ac, []) -> Ac;
foldl(F, B, [L|Ls]) -> foldl(F, F(B,L), Ls).

foldr(F, Ac, [L]) -> F(Ac,L);
foldr(F, B, [L|Ls]) -> F(foldr(F,B,Ls),L).

% Example:
%   identity(Xs) -> hor:foldl(fun (X,Y) -> X++[Y] end, [], Xs).
%   reverse(Xs) -> hor:foldr(fun (X,Y) -> X++[Y] end, [], Xs).

identity(Xs) -> hor:foldl(fun (X,Y) -> X++[Y] end, [], Xs).
reverse(Xs) -> hor:foldr(fun (X,Y) -> X++[Y] end, [], Xs).


% Exercise 3 - implement filter and map
map(F, Ls) ->  [F(L) || L <- Ls].
filter(P, Ls) ->  [L || L <- Ls, P(L)].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% - Another filter implementation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
filter2(P, [H|T]) ->
  case P(H) of
    true -> [H|filter2(P, T)];
    false -> filter2(P, T)
  end;
filter2(_, []) -> [].

incrementList(Ls) -> map(fun(X) -> X+1 end, Ls).


% Exercise 4 - Work with binary trees
% btree := {node, Node, LeftChild, RightChild}
% Ej: {node, 2, {node, 5, void, void}, {node, 6, {node, 8, void, void}, void}}

tree(_, void) -> void;
tree(F, {node, N, Lt, Rt}) -> {node, F(N), tree(F,Lt), tree(F,Rt)}.

%% Example.
%% hor:find(fun(X) -> X*2 end, {node, 2, {node, 5, void, void}, {node, 6, {node, 8, void, void}, void}}).


% Exercise 5 - fold for trees
foldt(_, Acc, void) -> Acc;
foldt(F, Acc, {node, N, Lt, Rt}) -> F(foldt(F, Acc, Lt), N, foldt(F, Acc, Rt)).


% Exercise 6 - Implmement find(Pred, L) which returns {ok, Value} if there is a node with value Value in the tree
% such that Pred(Value) == true.

find(_, void) -> false;
find(P, {node, N, Lt, Rt}) -> 
  case P(N) of
    true -> {ok, N};
    false ->
      PLt = find(P, Lt),
      if PLt == false -> find(P, Rt)
  end
end.

%% Example.
%% hor:find(fun(X) -> X==2 end, {node, 2, {node, 5, void, void}, {node, 6, {node, 8, void, void}, void}}).


%% Exercise 7 - Redo tree, fold and find with Records or Maps
-record(node, {value, left, right}).

%% Tree for records
rec_tree(_, void) -> void;
rec_tree(F, T) -> T#node{ value = F(T#node.value), left  = rec_tree(F, T#node.left), right = rec_tree(F, T#node.right)}.

%% Fold tree for records
rec_foldt(_, Init, void) -> Init;
rec_foldt(F, Init, T)    -> F(foldt(F, Init, T#node.left), T#node.value, foldt(F, Init, T#node.right)).

%% Find for records
rec_find(_, void) -> false;
rec_find(P, T) -> 
  case P(T#node.value) of
    true -> {ok, T#node.value};
    false ->
      PLt = rec_find(P, T#node.left),
      if PLt == false -> rec_find(P, T#node.right)
  end
end.