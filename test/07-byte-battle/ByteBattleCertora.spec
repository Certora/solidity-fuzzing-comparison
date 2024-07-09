methods {

    function _convertIt(bytes32 b) external returns (uint96)  envfree;
}


rule check_ByteBattle(bytes32 a, bytes32 b) {
    require (a != b);
    assert _convertIt(a) != _convertIt(b);
}