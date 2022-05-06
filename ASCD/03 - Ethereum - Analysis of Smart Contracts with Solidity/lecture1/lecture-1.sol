// SPDX-License-Identifier: MIT
// Author: Rafael Fernandez Ortiz

pragma solidity >=0.7.0 <0.9.0;
contract Exercise1 {

    function run(uint x3, uint x2, uint x1, uint x0) pure public returns (uint) {
        uint base; uint exp;
        base = x3 + x2;
        exp = x1 + x0;
        return base ** exp; 
    }
}


contract Exercise2 {

    uint state; // contract state

    event Event(string, uint); //event

    function run(uint x) public {
        state += x;
        emit Event("State incremented", x);
    }
}

contract Exercise3 {

    address[] members;

    event NewMember(string, address);

    function request() public {
        members.push(msg.sender);
        emit NewMember("New member was included", msg.sender);
    }
}

contract Sample {

    mapping(address => uint) balances;

    event LogDeposit(address sender, uint amount);
    event LogRefund(address receiver, uint amount);

    function deposit() public payable{

        // esto crea o incrementa el valor de msg.sender con msg.value
        balances[msg.sender] += msg.value;
        
        emit LogDeposit(msg.sender, msg.value);
    }

    function refund(uint amountRequested) public {
        require(amountRequested > 0);
        require(balances[msg.sender] >= amountRequested);

        payable(msg.sender).transfer(amountRequested);
        balances[msg.sender] -= amountRequested;

        emit LogRefund(msg.sender, amountRequested);
    }
}

