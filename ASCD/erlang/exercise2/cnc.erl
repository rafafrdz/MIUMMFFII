%% Author: Rafael Fernandez Ortiz
%% Language: Erlang

-module(cnc).
-compile(nowarn_export_all).
-compile(export_all).

%%%%%%%%%%%%%%%%%%
%% Exercise 1
%%%%%%%%%%%%%%%%%%

%% Example:
%% S = cnc:stping(). % Init
%% S ! {req, holaMundo, self()}. % Send a request
%% flush(). //res: Shell got {ack,holaMundo} % See response

%% Init
stping() -> spawn(?MODULE, ping, []).

ping() ->
    receive
        {req, Msg, Pid} when is_pid(Pid) ->
            Pid ! {ack, Msg},
            ping();
        NotValid ->
            io:format("This is not a valid process ~p~n", [NotValid]),
            ping()    
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Auxiliar Actors Functions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

post(To, Cmmd) when is_pid(To) -> To ! {self(), Cmmd}.

getRefByWorkerPid(Wpid, [{Wpid,Ref}|_]) -> Ref;
getRefByWorkerPid(Wpid, [_|Refs]) -> getRefByWorkerPid(Wpid, Refs).

%% ---

%% General API
queque(Server) -> post(Server, show).
show(Server) -> queque(Server). % alias of queque
stop(Server) -> post(Server, stop).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Exercise 2 - Fib Server
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Example:
%% S = cnc:sfibs(). % Init

%% % You can check non-blocking request with two following request:
%% cnc:fib(S, 45). % Send a request 
%% cnc:fib(S, 10). % Send a request

%% cnc:queque(S). % To see if there is any worker pending
%% //res0: Queque [{<0.96.0>,<0.80.0>}] % This worker correspond to fib(45) request

%% flush(). % To see all response
%% //res1: Shell got {<0.87.0>,{fib,10,is,55}} 
%% //res2: Shell got {<0.87.0>,{fib,45,is,1134903170}}


%% Fibonacci Function
fib(0) -> 0;
fib(1) -> 1;
fib(N) when N > 1 -> fib(N-1) + fib(N-2).

%% Fib API
fib(Server, N) -> post(Server, {fib, N}).

%% Init
sfibs() -> spawn(?MODULE, fibserver, [[]]).

%% Server
fibserver(Refs) ->
    process_flag(trap_exit, true),
    receive
        {From, {fib, N}} ->
            WorkerPid = spawn(fun() -> fibworker() end),
            post(WorkerPid, {fib, N}),
            fibserver([{WorkerPid,From}|Refs]);

        %% Worker Mssg %%%%%%%%%%%%%
        {WorkerPid, {fibOk, N, FibN}} ->
            Ref = getRefByWorkerPid(WorkerPid, Refs),
            post(Ref, {fib,N,is, FibN}),
            _Refs = lists:delete({WorkerPid, Ref}, Refs),
            fibserver(_Refs);            

        {WorkerPid, {errorWorker, NotValid}} ->
            Ref = getRefByWorkerPid(WorkerPid, Refs),
            post(Ref, {error, NotValid}),
            _Refs = lists:delete({WorkerPid, Ref}, Refs),
            fibserver(_Refs);
        %% %%%%%%%%%%%%%%%%%%%%%%

        {From, show} ->
            io:format("Queque ~p~n",[Refs]),
            post(From, {queque, Refs}),
            fibserver(Refs);

        {From, stop} ->
            post(From, {stop, ok});      
          
        NotValid ->
            io:format("Not valid command ~p~n",[NotValid]),
            fibserver(Refs)
    end.

%% Worker
fibworker() ->
    receive
        {From, {fib, N}} -> post(From, {fibOk, N, fib(N)});
        {From, NotValid} -> post(From, {errorWorker, NotValid})
    end.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Exercise 3 - Records
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Example:
%% R = cnc:srec(). % Init

%% % Use the Rec API
%% cnc:put(R, 10). % Put a number
%% cnc:put(R, 100).
%% cnc:put(R, 1000).
%% cnc:put(R, -310000).
%% cnc:put(R, -345310000).
%% cnc:put(R, 78345310000).
%% cnc:query(R). % Do a query
%% cnc:query(R).
%% cnc:query(R).
%% cnc:query(R).
%% cnc:statc(R). % Get the statistics
% //res0: Shell got {<0.101.0>,{largest,7834531000}}
% //res1: Shell got {<0.101.0>,{6,4}}


%%%%% Custom Auxiliar Max
max(none, Y) -> Y;
max(X, none) -> X;
max(X,Y) -> erlang:max(X,Y).

%% Init
srec() -> spawn(?MODULE, recserver, [none, 0, 0]).

%% Rec API
put(Server, N) -> post(Server, {put, N}).
query(Server) -> post(Server, {query, self()}).
statc(Server) -> post(Server, {statistics, self()}).

%% Server
recserver(Gt, PutAcc, QueryAcc) ->
    process_flag(trap_exit, true),
    receive

        %% Orders %%%%%%%%%%%%%%%
        {_, {put, N}} when is_integer(N) ->
            _PutAcc = PutAcc + 1,
            _Gt = cnc:max(Gt, N),
            recserver(_Gt, _PutAcc, QueryAcc);
        
        {_, {query, Pid}} ->
            _QueryAcc = QueryAcc + 1,
            post(Pid, {largest, Gt}),
            recserver(Gt, PutAcc, _QueryAcc);

        {_, {statistics, Pid}} ->
            post(Pid, {PutAcc, QueryAcc}),
            recserver(Gt, PutAcc, QueryAcc);
        %% %%%%%%%%%%%%%%%%%%%%%%

        {From, show} ->
            io:format("Queque ~p~n",[{Gt, PutAcc, QueryAcc}]),
            post(From, {queque, {Gt, PutAcc, QueryAcc}}),
            recserver(Gt, PutAcc, QueryAcc);

        {From, stop} ->
            post(From, {stop, ok});      
          
        NotValid ->
            io:format("Not valid command ~p~n",[NotValid]),
            recserver(Gt, PutAcc, QueryAcc)
    end.




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Exercise 4 - Linear Network
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

n_connected_cells(N) -> n_connected_cells(N, self()).
n_connected_cells(N, Pid) -> spawn_link(fun() -> cells_func(N,Pid) end).

cells_func(N,Pid) -> 
    receive
        AnyMssg when N == 1 ->
            Pid ! AnyMssg;
            
        AnyMssg ->
            Wpid = n_connected_cells(N-1, Pid),
            Wpid ! AnyMssg
        end.

