
/***


to run:
from folder solidity-fuzzing-comparison: 

certoraRun test/01-naive-receiver/NaiveReceiverCertora.conf


***/

using FlashLoanReceiver as receiver;

methods {
    function _.receiveEther(uint256) external => DISPATCHER(true);
}


/* Property 1: receiver.balance != 0 
This does not hold as the prover just starts with balance 0 
*/
invariant receiverHasAssets_invariant() 
    nativeBalances[receiver] != 0 ;


/* Property 1: receiver.balance does not become 0 
This finds the issue with the code but fails also on a fixed version 
*/
rule receiverHasAssets_rule(method f) {
    uint256 before = nativeBalances[receiver];
    // call arbitrary all functions 
    env e;
    calldataarg args;
    f(e,args);

    assert before != 0 =>  nativeBalances[receiver] != 0 ;
}

/* Good property : only the system or the msg.sender
*/
rule noChangeToOtherUser {
    method f;
    calldataarg args;
    env e;
    address someUser;

    uint256 someUserBalanceBefore = nativeBalances[someUser];
    
    f(e, args);
    
    assert someUserBalanceBefore != nativeBalances[someUser] => 
           someUser == e.msg.sender || someUser == f.contract;
}
