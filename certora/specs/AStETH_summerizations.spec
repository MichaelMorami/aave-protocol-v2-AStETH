methods {
    // Always returns amount to avoid arithmetics
    _toInternalAmount(uint256 amount, uint256 stEthRebasingIndex, uint256 aaveLiquidityIndex) returns (uint256) => returnAmount(amount, stEthRebasingIndex, aaveLiquidityIndex)
    // Always returns 1 RAY to simplify arithmetic calculations
    _stEthRebasingIndex() returns (uint256) => ALWAYS(1000000000000000000000000000) // = one RAY
    
    // The operators rayMul and rayDiv are simplified to implenent the identity operator.
    rayMul(uint256 x, uint256 y ) => identity(x, y);
    rayDiv(uint256 x, uint256 y ) => identity(x, y);
}

// Defining an error bar for y. x must be within the declared deviation.
definition bounded_error_eq(uint x, uint y, uint epsilon) returns bool =
    x <= y + epsilon && x + epsilon >= y;

// An identity operator - takes 2 vars and always returns the first.
// Used to simplify computations.
function identity (uint256 x, uint256 y) returns uint256{
	return x;
}

// simplification function for `_toInternalAmount()` - retrns the input amount to reduce computational complexity
function returnAmount(uint256 amount, uint256 stEthRebasingIndex, uint256 aaveLiquidityIndex) returns uint256 {
    return amount;
}

function rebasingRatio() returns uint256 {
    return 1000000000000000000000000000; // = one RAY
}
