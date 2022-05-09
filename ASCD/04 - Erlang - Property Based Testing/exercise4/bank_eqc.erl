%% Author: Rafael Fernandez Ortiz
%% Language: Erlang

-module(bank_eqc).
-compile(nowarn_export_all).
-compile(export_all).
-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Exercise 6 - Property Base Testing on Bank Application
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-record(state, {bank = none, accounts = []}). %% accounts = [{acc1, 200}, {acc2, 23}]
initial_state() -> #state{}.

%% Generators
-define(LowF, 1). %% Low frecuency
-define(HiF, 9). %% High frecuency
-define(ACC_ID, [{?LowF, acc1}, {?LowF, acc2}, {?LowF, acc3}]).


%%%%%%%%%%%%%%%%%%%
%% Property
%%%%%%%%%%%%%%%%%%%

prop_bank() ->
    ?FORALL(Cmds, eqc_statem:commands(bank_eqc),
            begin
                {_H,_S,Result} = eqc_statem:run_commands(bank_eqc,Cmds),
                Result == ok
            end).

sample() -> eqc_gen:sample(eqc_statem:commands(bank_eqc)).
%%  EJ. eqc_statem:run_commands(bank_eqc,[{model,bank_eqc},{set,{var,1},{call,bank_eqc,create_bank,[]}}]).

check() -> eqc:quickcheck(prop_bank()).


%%%%%%%%%%%%%%%%%%%
%% Helpers
%%%%%%%%%%%%%%%%%%%

%% gettets
bank(State) -> State#state.bank.
accounts(State) -> State#state.accounts.

%% Generator of accounts
account() -> eqc_gen:frequency(?ACC_ID).
account(State) ->
    AccInState = [{?HiF, Acc} || Acc <- accounts(State)],
    eqc_gen:frequency(AccInState ++ ?ACC_ID).

%% Get Account from State
getAcc(State, Account) ->
    case list:filter(fun({ACC, _B}) -> ACC == Account end, accounts(State)) of
        [OldAcc] -> OldAcc;
        _ -> false
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%




%% 1 - Create Bank
create_bank_pre(State) -> bank(State) == none.

create_bank_args(_State) -> [].

create_bank() -> bank:create_bank().

create_bank_next(State, Bank, _Args) -> State#state{bank = Bank}.

% create_bank_post(State, Args, Result) -> true.


%% 2 - Create Account
new_account_pre(State) -> is_pid(bank(State)).

new_account_args(State) -> [bank(State), account()].

new_account(Bank, AccountNumber) -> bank:new_account(Bank, AccountNumber).

new_account_next(State, _Result, [_Bank, Acc]) ->
    case getAcc(State, Acc) of
        {Acc, _} -> State;
        _ -> State#state{accounts = accounts(State) ++ [{Acc, 0}]}
    end.

new_account_post(State, [_Bank, Acc], Result) ->
    case getAcc(State, Acc) of
        {Acc, 0} -> Result == ok;
        _ -> Result == ko
    end.

%% 3 - Deposit Money
deposit_money_pre(State) -> (is_pid(bank(State))) and (accounts(State) =/= []).

deposit_money_args(State) ->
    [bank(State), account(State), choose(5, 25)].

deposit_money(Bank, AccountNumber, Quantity) ->
    bank:deposit_money(Bank, AccountNumber, Quantity).

deposit_money_next(State, _Result, [_Bank, Account, Quantity]) ->
    case getAcc(State, Account) of
        OldAcc = {Acc, B} ->
            Bal = B + Quantity,
            State#state{accounts = (accounts(State)--[OldAcc])++[{Acc, Bal}]};
        false -> State
    end.

deposit_money_post(_State, [_Bank, _Account, _Quantity], Result) ->
    case Result == ok of
        true -> Result == ok;
        false -> Result == ko
    end.


%% 4 - Withdraw Money
withdraw_money_pre(State) -> (is_pid(bank(State))) and (accounts(State) =/= []).

withdraw_money_args(State) ->
    [bank(State), account(State), choose(5, 25)].

withdraw_money(Bank, Account, Quantity) ->
    bank:withdraw_money(Bank, Account, Quantity).

withdraw_money_next(State, _Result, [_Bank, Account, Quantity]) ->
    case getAcc(State, Account) of
        OldAcc = {Acc, B} ->
            Bal = B - Quantity,
            State#state{accounts = (accounts(State)--[OldAcc])++[{Acc, Bal}]};
        false -> State
    end.

withdraw_money_post(_State, [_Bank, _Account, _Quantity], Result) ->
    case Result == ok of
        true -> Result == ok;
        false -> Result == ko
    end.


%% 5 - Balance
balance_pre(State) -> (is_pid(bank(State))) and (accounts(State) =/= []).

balance_args(State) -> [bank(State), account(State)].

balance(Bank, Account) -> bank:balance(Bank, Account).

balance_next(State, _Result, [_Bank, _Account]) -> State.

balance_post(State, [_Bank, Account], Result) ->
    case getAcc(State, Account) of
        {_Acc, B} -> Result == B;
    _ -> false
    end.


%% 6 - Transfer
transfer_pre(State) -> (is_pid(bank(State))) and (length(accounts(State)) > 1).

transfer_args(State) -> [bank(State), account(State), account(State), choose(5, 25)].

transfer(Bank, FromAccount, ToAccount, Quantity) -> bank:transfer(Bank, FromAccount, ToAccount, Quantity).

transfer_next(State, _Result, [_Bank, FromAccount, ToAccount, Quantity]) ->
        case {getAcc(State, FromAccount), getAcc(State, ToAccount)} of
        {OldAcc1, OldAcc2}  = {{Acc1, B1}, {Acc2, B2}} ->
            Bal1 = B1 - Quantity,
            Bal2 = B2 + Quantity,
            State#state{accounts = (accounts(State)--[OldAcc1, OldAcc2])++[{Acc1, Bal1}, {Acc2, Bal2}]};
        _ -> State
    end.

transfer_post(_State, [_Bank, _FromAccount, _ToAccount, _Quantity], Result) ->
    case Result == ok of
        true -> Result == ok;
        false -> Result == ko
    end.