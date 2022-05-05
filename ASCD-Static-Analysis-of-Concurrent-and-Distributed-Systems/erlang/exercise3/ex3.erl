%% Author: Rafael Fernandez Ortiz
%% Language: Erlang

-module(ex3).
-compile(nowarn_export_all).
-compile(export_all).
-include_lib("eqc/include/eqc.hrl").


%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Auxiliar Generators
%%%%%%%%%%%%%%%%%%%%%%%%%

list_sized(0, _)  -> [];
list_sized(N, G) -> [G | list_sized(N-1, G)].
gen_sorted_list() -> ?SUCHTHAT(Ls, list(int()), is_sorted(Ls)).
gen_elem_no_member(Ls) -> ?SUCHTHAT(K, int(), not(member(K, Ls))).

%% Is sorted property
is_sorted([]) -> true;
is_sorted([_]) -> true;
is_sorted([X,Y|Ls]) when X =< Y -> is_sorted([Y|Ls]);
is_sorted(_) -> false.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Exercise 2 - member and insert
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

member(_, []) -> false;
member(E, [E |_]) -> true;
member(E, [_ | LS])-> member(E, LS).

insert(N, []) -> [N];
insert(N, [T | LS]) when N < T -> [N, T | LS];
insert(N, [T | LS]) -> [T | insert(N, LS)].

%% Testing all properties of insert
test_prop_insert() ->
    eqc:quickcheck(prop_insert_length()),
    eqc:quickcheck(prop_insert_member()),
    eqc:quickcheck(prop_insert_still_sort()).

%% Insert - Prop 1 - Length
prop_insert_length() ->
    ?FORALL(K, int(),
        ?FORALL(Ls, list(int()),
            length(insert(K, Ls)) == length(Ls) + 1)).

%% Insert - Prop 2 - Element inserted is in the new list
prop_insert_member() ->
    ?FORALL(K, int(),
        ?FORALL(Ls, list(int()),
            member(K, insert(K, Ls)))).

%% Insert - Prop 3 - New list is still a sorted list
prop_insert_still_sort() ->
    ?FORALL (Ls, gen_sorted_list(),
        ?FORALL(K, gen_elem_no_member(Ls),
            is_sorted(insert(K, Ls)))).


%%%%%%%%%%%%%%%%%%%%%%
%% Exercise 3 - sort
%%%%%%%%%%%%%%%%%%%%%%

sort([]) -> [];
sort([H|L]=XS) ->
    sort([X || X <- L, X < H]) ++
    [X || X <- XS, X == H] ++
    sort([X || X <- L, X > H]).

%% Testing all properties of insert
test_prop_sort() ->
    eqc:quickcheck(prop_sorted()),
    eqc:quickcheck(prop_sort_length()).

%% Insert - Prop 1 - Sort a list is a sorted list
prop_sorted() ->
        ?FORALL (Ls, list(int()),
            is_sorted(sort(Ls))).

%% Insert - Prop 2 - Length
prop_sort_length() ->
        ?FORALL(Ls, list(int()),
            length(sort(Ls)) == length(Ls)).


%%%%%%%%%%%%%%%%%%%%%%
%% Exercise 6 - merge
%%%%%%%%%%%%%%%%%%%%%%

merge([], []) -> [];
merge([], X) -> X;
merge(X, []) -> X;
merge([X | XS], [Y | _] = L) when X < Y -> [X | merge(XS, L)];
merge(L, [Y | YS]) -> [Y | merge(L,YS)].

%% Testing properties
test_prop_merge() ->
    eqc:quickcheck(prop_merge_length()),
    eqc:quickcheck(prop_merge_associative()),
    eqc:quickcheck(prop_merge_commutative_if_sorted()),
    eqc:quickcheck(prop_merge_commutative_if_sorted_list()).

%% Merge - Prop 1 - Length
prop_merge_length() ->
    ?FORALL(Ks, list(int()),
        ?FORALL(Ls, list(int()),
            length(merge(Ks, Ls)) == length(Ls) + length(Ks))).

%% Merge - Prop 2 - Merge is associative
prop_merge_associative() ->
    ?FORALL(Zs, list(int()),
        ?FORALL(Ks, list(int()),
            ?FORALL(Ls, list(int()),
                merge(Zs, merge(Ks, Ls)) == merge(merge(Zs, Ks), Ls)))).

%% Merge is not commutative

% prop_merge_commutative() ->
%     ?FORALL(Ks, list(choose(-5,5)),
%         ?FORALL(Ls, list(choose(-5,5)),
%             merge(Ks, Ls) == merge(Ls, Ks))).

%% No passed -> merge([1,0],[1]) != merge([1],[1,0])

%% Merge - Prop 2.1 - But, If a list is a sorted list, then Merge is commutative
prop_merge_commutative_if_sorted() ->
    ?FORALL(Ks, list(int()),
        ?FORALL(Ls, list(int()),
            merge(sort(Ks), sort(Ls)) == merge(sort(Ks), sort(Ls)) )).

%% Merge - Prop 2.2 - Alternative form
prop_merge_commutative_if_sorted_list() ->
    ?FORALL(Ks, gen_sorted_list(),
        ?FORALL(Ls, gen_sorted_list(),
            merge(Ks, Ls) == merge(Ls, Ks) )).