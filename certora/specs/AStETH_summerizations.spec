methods {
    // Summerizations:
    // getPooledEthByShares(uint256 _sharesAmount) returns (uint256) => NONDET
    _toInternalAmount(uint256 amount, uint256 stEthRebasingIndex, uint256 aaveLiquidityIndex) returns (uint256) => returnAmount(amount, stEthRebasingIndex, aaveLiquidityIndex)
    _stEthRebasingIndex() returns (uint256) => rebasingRatio()
    
    // Simplifications:
    rayMul(uint256 x, uint256 y ) returns (uint256) => identity(x, y);
    rayDiv(uint256 x, uint256 y ) returns (uint256) => identity(x, y);
}

function identity (uint256 x, uint256 y) returns uint256{
	return x;
}

function returnAmount(uint256 amount, uint256 stEthRebasingIndex, uint256 aaveLiquidityIndex) returns uint256 {
    return amount;
}

function rebasingRatio() returns uint256 {
    return 1000000000000000000000000000; // = one RAY
}
