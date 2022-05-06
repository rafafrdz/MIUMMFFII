// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.4.0;
contract exercise {
  uint[] arr;
  uint sum;
  function generate(uint n) external {
    for (uint i = 0; i < n; i++) {
        arr.push(i*i);
    }      
  }

  // Executions cost --> [1]: 99013, [2]: 79113
  function computeSum() external {
    sum = 0;
    for (uint i = 0; i < arr.length; i++) {
      sum = sum + arr[i];
    } 
  }

  // 1. Safe Version of computeSum
  // Executions cost --> [1]: 92925, [2]: 92925
  function sComputeSum() external {
    sum = 0;
    for (uint i = 0; i < arr.length; i++) {
    require (arr.length > 0); // non empty
    require (i < arr.length); // out of range
    require (sum + arr[i] < (2**256 - 1)); // overflow
      sum = sum + arr[i];
    } 
  }
  

  // 2. Safe and Optimized version of computeSum
  // Executions cost --> [1]: 72921, [2]: 72921
  function computeSumOpt() external {
    uint arrLength = arr.length;
    if(arrLength > 1) {
        uint acc;
        for (uint i = 0; i < arrLength; i++) {
            acc = acc + arr[i];
        }
        sum = acc;
    }
  }

  // 2.opt (Safe and) Optimized version of computeSum
  // Executions cost --> [1]: 76932, [2]: 76932
  function sComputeSumOpt() external {
    uint arrLength = arr.length;
    require (arrLength > 0); // non empty
    if(arrLength > 1) {
        uint acc;
        for (uint i = 0; i < arrLength; i++) {
            require (i < arrLength); // out of range
            acc = acc + arr[i];
            require (acc < (2**256 - 1)); // overflow
        }
        sum = acc;
    }
  }

  // Executions cost --> [1]: 153853, [2]: 136753
  function increment() external {
    for (uint i = 0; i < arr.length-1; i++) {
      arr[i] = arr[i] + arr[i+1];
    } 
  }

  // 1. Safe Version of increment
  // Executions cost --> [1]: 153566, [2]: 153566
  function sIncrement() external {
    for (uint i = 0; i < arr.length-1; i++) {
    require (arr.length > 0); // non empty
    require (i < arr.length - 1); // out of range
    require (arr[i] + arr[i+1] < (2 ** 256 - 1)); // overflow
      arr[i] = arr[i] + arr[i+1];
    } 
  }

  // 3. Optimized version of increment
  // Executions cost --> [1]: 130027, [2]: 130027
  function incrementOpt() external {
    uint arrLength = arr.length;
    if(arrLength > 1) {
        uint acc; uint crr; uint next = arr[0];
        for (uint i = 0; i < arrLength-1; i++) {
            crr = next; next = arr[i+1];
            acc = crr + next;
            arr[i] = acc;
        }
    } 
  }

  // 3.opt (Safe and) Optimized version of increment
  // Executions cost --> [1]: 131228, [2]: 131228
  function sIncrementOpt() external {
    uint arrLength = arr.length;
    require (arrLength > 0); // non empty
    if(arrLength > 1) {
        uint acc; uint crr; uint next = arr[0];
        for (uint i = 0; i < arrLength-1; i++) {
            require (i < arrLength - 1); // out of range
            crr = next; next = arr[i+1];
            acc = crr + next;
            require (acc < (2 ** 256 - 1)); // overflow
            arr[i] = acc;
        }
    } 
  }

  // 4. Optimized Plus (with memory store) version of increment
  // Executions cost --> [1]: 128850, [2]: 128850
  function incrementOptPlus() external {
    uint arrLength = arr.length;
    if(arrLength > 1) {
        uint[] memory arrM = arr;
        uint acc; uint crr; uint next = arrM[0];
        for (uint i = 0; i < arrLength-1; i++) {
            crr = next;
            next = arrM[i+1];
            acc = crr + next;
            arr[i] = acc;
        }
    } 
  }

  // 4.opt (Safe and) Optimized Plus (with memory store) version of increment
  // Executions cost --> [1]: 130139, [2]: 130139
  function sIncrementOptPlus() external {
    uint arrLength = arr.length;
    require (arrLength > 0); // non empty
    if(arrLength > 1) {
        uint[] memory arrM = arr;
        uint acc; uint crr; uint next = arrM[0];
        for (uint i = 0; i < arrLength-1; i++) {
            require (i < arrLength - 1); // out of range
            crr = next;
            next = arrM[i+1];
            acc = crr + next;
            require (acc < (2 ** 256 - 1)); // overflow
            arr[i] = acc;
        }
    } 
  }
}