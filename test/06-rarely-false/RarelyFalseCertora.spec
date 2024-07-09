
/

methods {
    function _rarelyFalse(uint256 n, uint256 e) external returns(bool) envfree;
}



rule rarelyFalse(uint256 n,) {
    require n >= 1 && n <= max_uint256 - 1234;
    assert _rarelyFalse(require_uint256(n + 1234) ,80);
}