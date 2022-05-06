-module(ktc).
-compile(nowarn_export_all).
-compile(export_all).

post(To , Cmmd) -> To ! {self(), Cmmd} .

%% API
show(Fridge) -> post(Fridge, show).
store(Fridge, Food) -> post(Fridge, {store, Food}).
take(Fridge, Food) -> post(Fridge, {take, Food}).

% Init
start() -> spawn(?MODULE, fridge, [[]]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Otra forma de instanciar
%% start() -> spawn(fun() -> ?MODULE:fridge([]) end).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Fridge Server
fridge(FoodList) ->
    receive
        {From, {store, _Food}} ->
            post(From, ok),
            fridge([_Food|FoodList]);
        {From, {take, _Food}} ->
            case lists:member(_Food, FoodList) of
                true ->
                    post(From, {ok, _Food}),
                    _FList = lists:delete(_Food, FoodList),
                    fridge(_FList);
                false ->
                    post(From, not_found),
                    fridge(FoodList)
            end;
        {From, show} ->
            post(From, FoodList),
            fridge(FoodList);
        terminate -> ok
    end.

