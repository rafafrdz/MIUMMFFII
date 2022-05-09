%% Author: Rafael Fernandez Ortiz
%% Language: Erlang

-module(bank).
-compile(nowarn_export_all).
-compile(export_all).
 %% accounts = [{acc1, 200}, {acc2, 23}]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Exercise 5 - Bank Application
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Bank API
%%%%%%%%%%%%%%%%%%%%%

receiveMssg() ->
    receive 
        {_, {_, ok}} -> ok;
        {_, {_, ko}} -> ko;
        {_, {balance, Balance}} -> Balance;
        {_, Mssg} -> Mssg
    end.

%% Create an instance of a bank
create_bank() -> spawn(?MODULE, bankserver, [[],[]]).

%% Create a new account with number 'AccountNumber'
new_account(Bank, AccountNumber) ->
    post(Bank, {new_account, AccountNumber}),
    receiveMssg().

%% Withdraw 'Quantity' from 'AccountNumber' account
withdraw_money(Bank, AccountNumber, Quantity) ->
    post(Bank, {withdraw_money, AccountNumber, Quantity}),
    receiveMssg().

%% Deposit 'Quantity' to 'AccountNumber' account
deposit_money(Bank, AccountNumber, Quantity) ->
    post(Bank, {deposit_money, AccountNumber, Quantity}),
    receiveMssg().

%% Transfer 'Quantity' from 'FromAccount' account to 'ToAccount' account
transfer(Bank, FromAccount, ToAccount, Quantity) ->
    post(Bank, {transfer, FromAccount, ToAccount, Quantity}),
    receiveMssg().

%% Get the balance of 'AccountNumber' account
balance(Bank, AccountNumber)  ->
    post(Bank, {balance, AccountNumber}),
    receiveMssg().

%% Debug Bank Server
show(Bank) ->
    post(Bank, show),
    receiveMssg().

%%%%%%%%%%%%%%%%%%%%%
%% Bank Server
%%%%%%%%%%%%%%%%%%%%%

bankserver(Accounts, Ref) ->
    process_flag(trap_exit, true),
    receive
        %% Create a new account if no exists
        {From, {new_account, AccountNumber}} ->
            case existAccount(AccountNumber, Accounts) of
                true ->
                    post(From, ko),
                    bankserver(Accounts, Ref);
                false ->
                    WorkerPid = spawn(fun() -> account(0) end),
                    post(From, ok),
                    bankserver([{AccountNumber, WorkerPid}|Accounts], [{WorkerPid, From}| Ref])
            end;

        %% Withdraw 'Quantity' money
        {_, {withdraw_money, AccountNumber, Quantity}} ->
            AccPid = getAccountPidByAccountNumber(AccountNumber, Accounts),
            post(AccPid, {withdraw_money, Quantity}),
            bankserver(Accounts, Ref);
        
        %% Deposit 'Quantity' money
        {_, {deposit_money, AccountNumber, Quantity}} ->
            AccPid = getAccountPidByAccountNumber(AccountNumber, Accounts),
            post(AccPid, {deposit_money, Quantity}),
            bankserver(Accounts, Ref);

        %% Transfer 'Quantity' money from 'FromAccount' to 'ToAccount'
        {_, {transfer, FromAccount, ToAccount, Quantity}} ->
            FromAccPid = getAccountPidByAccountNumber(FromAccount, Accounts),
            ToAccPid = getAccountPidByAccountNumber(ToAccount, Accounts),
            post(FromAccPid, {transfer, ToAccPid, Quantity}),
            bankserver(Accounts, Ref);

        %% Get the balance of the account with account number 'AccountNumber'
        {_, {balance, AccountNumber}} ->
            AccPid = getAccountPidByAccountNumber(AccountNumber, Accounts),
            post(AccPid, balance),
            bankserver(Accounts, Ref);

        %% Account Response %%%%%%%%%%%%%
        {AccountPid, {ack, Mssg}} ->
            Client = getRefByWorkerPid(AccountPid, Ref),
            post(Client, Mssg),
            bankserver(Accounts, Ref);

        {AccountPid, {notValid, NotValid}} ->
            Client = getRefByWorkerPid(AccountPid, Ref),
            post(Client, {error, notValid, NotValid}),
            bankserver(Accounts, Ref);

        %% %%%%%%%%%%%%%%%%%%%%%%
        %% To debug
        {From, show} ->
            io:format("Accounts: ~p~n", [Accounts]),
            io:format("References: ~p~n", [Ref]),
            post(From, {show, ok}),
            bankserver(Accounts, Ref); 

        {From, stop} ->
            post(From, {stop, ok});      
          
        NotValid ->
            io:format("Not valid command ~p~n",[NotValid]),
            bankserver(Accounts, Ref)
    end.


%%%%%%%%%%%%%%%%%%%%%
%% Account Actor
%%%%%%%%%%%%%%%%%%%%%

account(Balance) ->
    receive
        {BankPid, {withdraw_money, Quantity}} -> withdraw_money_ac(BankPid, Quantity, Balance);
        {BankPid, {deposit_money, Quantity}} -> deposit_money_ac(BankPid, Quantity, Balance);
        {BankPid, {transfer, ToAccPid, Quantity}} -> transfer_ac(BankPid, ToAccPid, Quantity, Balance);
        {BankPid, balance} -> balance_ac(BankPid, Balance);
        {_, {ack, _}} -> account(Balance);
        {BankPid, NotValid} -> post(BankPid, {notValid, NotValid})
    end.

%% Account Functions
%%%%%%%%%%%%%%%%%%%%%

balance_ac(BankPid, Balance) ->
        post(BankPid, {ack, {balance, Balance}}),
        account(Balance).

withdraw_money_ac(BankPid, Quantity, Balance) ->
        case Balance >= Quantity of
            true ->
                _Balance = Balance - Quantity,
                post(BankPid, {ack, {withdraw, ok}}),
                account(_Balance);
            false ->
                post(BankPid, {ack, {withdraw, ko}}),
                account(Balance)
        end.

deposit_money_ac(BankPid, Quantity, Balance) ->
        _Balance = Balance + Quantity,
        post(BankPid, {ack, {deposit, ok}}),
        account(_Balance).

transfer_ac(BankPid, ToPid, Quantity, Balance) ->
        case Balance >= Quantity of
            true ->
                _Balance = Balance - Quantity,
                post(ToPid, {deposit_money, Quantity}),
                post(BankPid, {ack, {transfer, ok}}),
                account(_Balance);
            false ->
                post(BankPid, {ack, {transfer, ko}}),
                account(Balance)
        end.


%% Auxiliar Functions
%%%%%%%%%%%%%%%%%%%%%%

post(To, Cmmd) when is_pid(To) -> To ! {self(), Cmmd}.

getAccountPidByAccountNumber(AccountNumber, [{AccountNumber, AccPid}|_]) -> AccPid;
getAccountPidByAccountNumber(AccountNumber, [_ | AccountsRef]) -> getAccountPidByAccountNumber(AccountNumber, AccountsRef).

existAccount(_, []) -> false;
existAccount(AccNumber, [{AccNumber, _}|_]) -> true;
existAccount(AccNumber, [_|Accounts]) -> existAccount(AccNumber, Accounts).

getRefByWorkerPid(Wpid, [{Wpid,Ref}|_]) -> Ref;
getRefByWorkerPid(Wpid, [_|Refs]) -> getRefByWorkerPid(Wpid, Refs).