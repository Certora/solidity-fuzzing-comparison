/***


to run:
from folder solidity-fuzzing-comparison: 

certoraRun test/02-unstoppable/UnstoppableCertora.conf


***/

using UnstoppableLender as lender;
using TestToken as token;

methods{
    function _.receiveTokens(address tokenAddress, uint256 amount) external => DISPATCHER(true);
    function _.transfer(address, uint256) external => DISPATCHER(true);
    function token.totalSupply() external returns (uint256) envfree;
}


/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ totalSupplyIsSumOfBalances                                                                                          │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/ 

persistent ghost mathint sum_of_balances {
    init_state axiom sum_of_balances == 0;
}

hook Sstore token._balances[KEY address a] uint new_value (uint old_value) {
    // when balance changes, update ghost
    sum_of_balances = sum_of_balances + new_value - old_value;
}

// This `sload` makes `sum_of_balances >= to_mathint(balance)` hold at the beginning of each rule.
hook Sload uint256 balance token._balances[KEY address a] {
  require sum_of_balances >= to_mathint(balance);
}

//// ## Part 4: Invariants

/** `totalSupply()` returns the sum of `balanceOf(u)` over all users `u`. */
invariant totalSupplyIsSumOfBalances()
    to_mathint(token.totalSupply()) == sum_of_balances;


/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ lender allowance always 0                                                                                           │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/ 

persistent ghost mapping(address => mapping(address => uint256)) allowancesMirror;

hook Sstore token._allowances[KEY address owner][KEY address spender] uint256 newValue (uint256 oldValue) {
    require allowancesMirror[owner][spender] == oldValue;
    allowancesMirror[owner][spender] = newValue;
}

hook Sload uint256 value token._allowances[KEY address owner][KEY address spender] {
    require allowancesMirror[owner][spender] == value;
}

rule lenderAllowanceAlwaysZero(){
    env e;
    method f;
    calldataarg args;
    
    require e.msg.sender != lender; 
    require forall address a. allowancesMirror[lender][a] == 0;

    f(e, args);

    assert forall address a. allowancesMirror[lender][a] == 0;
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ FlashLoan Denial of service                                                                                         │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

/// @title If a user can take a flash loan he can also take it after some operation by another user
rule flashLoadDenialOfService()
{
    requireInvariant totalSupplyIsSumOfBalances();
    require forall address a. allowancesMirror[lender][a] == 0;
    
    // Show it's possible for someUser to take out a flash loan
    env e1;
    require e1.msg.sender != currentContract && e1.msg.sender != lender && e1.msg.sender != token;

    uint256 amount;

    storage init = lastStorage;

    executeFlashLoan(e1, amount);

    // simulate other user operation
    env e2;
    require e1.msg.sender != e2.msg.sender && e2.msg.sender != currentContract && e2.msg.sender != lender && e2.msg.sender != token;

    method f;
    calldataarg args;

    f(e2, args) at init;

    // make sure one can still perform the same flashloan
    executeFlashLoan@withrevert(e1, amount);
    assert !lastReverted;
}