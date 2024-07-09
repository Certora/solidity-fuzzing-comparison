methods {
    function isActive() external returns bool envfree;
    // on unresolved calls, assume callbacks 
    function _._ external => DISPATCH [
        currentContract._
    ] default NONDET;

}

use builtin rule sanity; 

invariant  proposal_complete_all_rewards_distributed()
    // either proposal is active and contract balance > 0 
    // or proposal is not active and contract balance == 0

    //use implication - it's fun and elegant 
    isActive() <=> nativeBalances[currentContract] > 0;

