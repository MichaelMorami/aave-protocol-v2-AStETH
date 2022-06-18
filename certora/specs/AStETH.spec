import "./AStETH_summerizations.spec"

using SymbolicLendingPool as LENDING_POOL
using IncentivesControllerMock as _incentivesController
using DummyERC20A as UNDERLYING_ASSET_ADDRESS
using DummyERC20B as RESERVE_TREASURY_ADDRESS

methods {     
    setInitializing(bool) envfree
    initialize(uint8, string, string) envfree
    balanceOf(address) returns (uint256) envfree
    scaledBalanceOf(address) returns (uint256) envfree
    internalBalanceOf(address) returns (uint256) envfree
    getScaledUserBalanceAndSupply(address) returns (uint256, uint256) envfree
    totalSupply() returns (uint256) envfree
    scaledTotalSupply() returns (uint256) envfree
    burn(address, address,uint256, uint256)
    mint(address, uint256, uint256)
    mintToTreasury(uint256, uint256)
    transferOnLiquidation(address, address, uint256)
    transferUnderlyingTo(address, uint256) returns (uint256)
    permit(address, address, uint256, uint256, uint8, bytes32, bytes32)

    UNDERLYING_ASSET_ADDRESS.balanceOf(address user) returns(uint256) envfree;
    RESERVE_TREASURY_ADDRESS.balanceOf(address user) returns(uint256) envfree;

    // IncentivizedERC20 methods:
    // handleAction(address user, uint256 userBalance, uint256 totalSupply) => DISPATCHER(true)
}

/**************************************************
 *               CVL FUNCS & DEFS                 *
 **************************************************/


 /**************************************************
 *                GHOSTS AND HOOKS                *
 **************************************************/


 /**************************************************
 *                  VALID STATES                  *
 **************************************************/


 /**************************************************
 *                STATE TRANSITION                *
 **************************************************/


 /**************************************************
 *                METHOD INTEGRITY                *
 **************************************************/

rule canOnlyInitializedOnce(uint8 underlyingAssetDecimals,
    string tokenName,
    string tokenSymbol)
description "contract can only be initialized once"
{
    // setInitializing(false);
    initialize(underlyingAssetDecimals, tokenName, tokenSymbol);

    initialize@withrevert(underlyingAssetDecimals, tokenName, tokenSymbol);
    bool secondSucceeded = !lastReverted;

    assert secondSucceeded==false;
}


rule burnIntegrity(address user, address receiverOfUnderlying,
    uint256 amount, uint256 index, uint256 stEthRebasingIndex,
    uint256 aaveLiquidityIndex)
{
    env e;
    // for onlyLendingPool modifier
    require e.msg.sender == LENDING_POOL;
    // uint256 amountScaled = _toInternalAmount(e, amount, stEthRebasingIndex, aaveLiquidityIndex);
    uint256 amountScaled = amount;
    require amount!=0 && amountScaled!=0;
    mathint _totalSupply = totalSupply();
    uint256 _balance = balanceOf(user);
    uint256 _underlyingBalance = UNDERLYING_ASSET_ADDRESS.balanceOf(receiverOfUnderlying);
    burn(e, user, receiverOfUnderlying, amount, index);
    mathint totalSupply_ = totalSupply();
    uint256 balance_ = balanceOf(user);
    uint256 underlyingBalance_ = UNDERLYING_ASSET_ADDRESS.balanceOf(receiverOfUnderlying);

    assert _totalSupply-amountScaled == totalSupply_;
    assert _balance-amountScaled == balance_;
    assert _underlyingBalance+amount == underlyingBalance_;
}

//  deposit X stETH to mint X astETH * Total astETH supply increases by X.

rule integrityOfMint(address user, uint256 amount, uint256 index) {
	env e;
    // for onlyLendingPool modifier
    require e.msg.sender == LENDING_POOL;

    mathint totalSupplyBefore = totalSupply();
    mint(e, user, amount, index);
    mathint totalSupplyAfter = totalSupply();

    assert amount != 0 => totalSupplyBefore < totalSupplyAfter;
}


// rule depositAdditivity(address recipient, uint256 amount1, uint256 amount2, uint16 referralCode, bool fromUnderlying) {
// 	env e;
// 	setup(e, recipient);
	
// 	storage init = lastStorage;
// 	uint amount = amount1 + amount2;
// 	require amount1 > 0 && amount2 > 0 && (amount <= MAX_UINT256());
// 	deposit(e, recipient, amount1, referralCode, fromUnderlying);
// 	deposit(e, recipient, amount2, referralCode, fromUnderlying);
	
// 	uint256 _assetBySender = ASSET.balanceOf(e.msg.sender);
// 	uint256 _assetByRecipient = ASSET.balanceOf(recipient);
// 	uint256 _assetByStaticAToken = ASSET.balanceOf(currentContract);
// 	uint256 _assetByAToken = ASSET.balanceOf(ATOKEN);
	
// 	uint256 _staticATokenBySender = balanceOf(e.msg.sender);
// 	uint256 _staticATokenByRecipient = balanceOf(recipient);
	
// 	uint256 _aTokenBySender = ATOKEN.balanceOf(e.msg.sender);
// 	uint256 _aTokenByRecipient = ATOKEN.balanceOf(recipient);
// 	uint256 _aTokenByStaticAToken = ATOKEN.balanceOf(currentContract);

// 	deposit(e, recipient, amount, referralCode, fromUnderlying) at init;

// 	uint256 assetBySender_ = ASSET.balanceOf(e.msg.sender);
// 	uint256 assetByRecipient_ = ASSET.balanceOf(recipient);
// 	uint256 assetByStaticAToken_ = ASSET.balanceOf(currentContract);
// 	uint256 assetByAToken_ = ASSET.balanceOf(ATOKEN);
	
// 	uint256 staticATokenBySender_ = balanceOf(e.msg.sender);
// 	uint256 staticATokenByRecipient_ = balanceOf(recipient);
	
// 	uint256 aTokenBySender_ = ATOKEN.balanceOf(e.msg.sender);
// 	uint256 aTokenByRecipient_ = ATOKEN.balanceOf(recipient);
// 	uint256 aTokenByStaticAToken_ = ATOKEN.balanceOf(currentContract);
	
// 	assert assetBySender_ == _assetBySender && assetByAToken_ == _assetByAToken && aTokenBySender_ == _aTokenBySender;
// 	assert assetByStaticAToken_ == _assetByStaticAToken && aTokenByStaticAToken_ == _aTokenByStaticAToken;
// 	assert staticATokenByRecipient_ == _staticATokenByRecipient;
// 	assert assetByRecipient_ == _assetByRecipient;
// 	assert staticATokenBySender_ == _staticATokenBySender && aTokenByRecipient_ == _aTokenByRecipient;
// }


// rule depositNoInterfernece(address recipient, address other, uint256 amount, uint16 referralCode, bool fromUnderlying) {
// 	env e;
// 	setup(e, recipient);
// 	setup(e, other);
// 	require recipient != other;
	
// 	uint256 _assetByOther = ASSET.balanceOf(other);
// 	uint256 _staticATokenByOther = balanceOf(other);
// 	uint256 _aTokenByOther = ATOKEN.balanceOf(other);
	
// 	deposit(e, recipient, amount, referralCode, fromUnderlying);

// 	uint256 assetByOther_ = ASSET.balanceOf(other);
// 	uint256 staticATokenByOther_ = balanceOf(other);
// 	uint256 aTokenByOther_ = ATOKEN.balanceOf(other);

// 	assert _assetByOther == assetByOther_ && _staticATokenByOther == staticATokenByOther_ && 	_aTokenByOther == aTokenByOther_;
// }

// rule withdrawIntegrity(address owner, address recipient, uint256 staticAmount, uint256 dynamicAmount, bool toUnderlying, uint256 deadline, uint8 v, bytes32 r, bytes32 s, method f) filtered {
// 	f -> f.selector == withdraw(address, uint256, bool).selector ||
// 		f.selector == withdrawDynamicAmount(address, uint256, bool).selector 
// 		|| f.selector == metaWithdraw(address, address, uint256, uint256, bool, uint256, uint8, bytes32, bytes32).selector 
// 	}
// {
// 	env e;
// 	setup(e, recipient);
// 	require e.msg.sender == owner;
// 	uint amount = staticAmount + dynamicAmount;
// 	require (staticAmount==0 && dynamicAmount>0) || (staticAmount>0 && dynamicAmount==0);

// 	uint256 _assetBySender = ASSET.balanceOf(e.msg.sender);
// 	uint256 _assetByRecipient = ASSET.balanceOf(recipient);
// 	uint256 _assetByStaticAToken = ASSET.balanceOf(currentContract);
// 	uint256 _assetByAToken = ASSET.balanceOf(ATOKEN);
	
// 	uint256 _staticATokenBySender = balanceOf(e.msg.sender);
// 	uint256 _staticATokenByRecipient = balanceOf(recipient);
	
// 	uint256 _aTokenBySender = ATOKEN.balanceOf(e.msg.sender);
// 	uint256 _aTokenByRecipient = ATOKEN.balanceOf(recipient);
// 	uint256 _aTokenByStaticAToken = ATOKEN.balanceOf(currentContract);
	
// 	uint256 _nonce = nonces(owner);

// 	require amount > 0;
// 	if (f.selector == withdraw(address, uint256, bool).selector) {
// 		withdraw(e, recipient, amount, toUnderlying);
// 	} else if (f.selector == withdrawDynamicAmount(address, uint256, bool).selector) {
// 		withdrawDynamicAmount(e, recipient, amount, toUnderlying);
// 	} else {
// 		metaWithdraw(e, owner, recipient,  staticAmount, dynamicAmount, toUnderlying, deadline, v, r, s);
// 	}
// 	uint256 assetBySender_ = ASSET.balanceOf(e.msg.sender);
// 	uint256 assetByRecipient_ = ASSET.balanceOf(recipient);
// 	uint256 assetByStaticAToken_ = ASSET.balanceOf(currentContract);
// 	uint256 assetByAToken_ = ASSET.balanceOf(ATOKEN);
	
// 	uint256 staticATokenBySender_ = balanceOf(e.msg.sender);
// 	uint256 staticATokenByRecipient_ = balanceOf(recipient);
	
// 	uint256 aTokenBySender_ = ATOKEN.balanceOf(e.msg.sender);
// 	uint256 aTokenByRecipient_ = ATOKEN.balanceOf(recipient);
// 	uint256 aTokenByStaticAToken_ = ATOKEN.balanceOf(currentContract);
	
// 	assert _staticATokenBySender > 0 && toUnderlying => assetByRecipient_ > _assetByRecipient && assetByAToken_ < _assetByAToken;
// 	assert _staticATokenBySender > 0 && !toUnderlying => aTokenByRecipient_ > _aTokenByRecipient;
// 	assert _staticATokenBySender > 0 => aTokenByStaticAToken_ < _aTokenByStaticAToken && staticATokenBySender_ < _staticATokenBySender;
// 	assert assetByStaticAToken_ == _assetByStaticAToken;
// 	assert e.msg.sender != recipient => aTokenBySender_ == _aTokenBySender && assetBySender_ == _assetBySender && staticATokenByRecipient_ == _staticATokenByRecipient;

// 	if (f.selector == withdraw(address, uint256, bool).selector || f.selector == withdrawDynamicAmount(address, uint256, bool).selector) {
// 		assert nonces(owner) == _nonce;
// 	} else {
// 		assert nonces(owner) == _nonce + 1;
// 	}
// }

// rule withdrawAdditivity(address recipient, uint256 amount1, uint256 amount2, bool toUnderlying, method f) filtered {
// 	f -> f.selector == withdraw(address, uint256, bool).selector ||
// 		f.selector == withdrawDynamicAmount(address, uint256, bool).selector
// 	}
// {
// 	env e;
// 	setup(e, recipient);
// 	require amount1 > 0 && amount2 > 0 && (amount1 + amount2 <= MAX_UINT256());
	
// 	storage init = lastStorage;
// 	if (f.selector == withdraw(address, uint256, bool).selector) {
// 		withdraw(e, recipient, amount1, toUnderlying);
// 		withdraw(e, recipient, amount2, toUnderlying);
// 	}
// 	else {
// 		withdrawDynamicAmount(e, recipient, amount1, toUnderlying);
// 		withdrawDynamicAmount(e, recipient, amount2, toUnderlying);
// 	}

// 	uint256 _assetBySender = ASSET.balanceOf(e.msg.sender);
// 	uint256 _assetByRecipient = ASSET.balanceOf(recipient);
// 	uint256 _assetByStaticAToken = ASSET.balanceOf(currentContract);
// 	uint256 _assetByAToken = ASSET.balanceOf(ATOKEN);
	
// 	uint256 _staticATokenBySender = balanceOf(e.msg.sender);
// 	uint256 _staticATokenByRecipient = balanceOf(recipient);
	
// 	uint256 _aTokenBySender = ATOKEN.balanceOf(e.msg.sender);
// 	uint256 _aTokenByRecipient = ATOKEN.balanceOf(recipient);
// 	uint256 _aTokenByStaticAToken = ATOKEN.balanceOf(currentContract);
	
// 	require amount1 > 0 && amount2 > 0;
// 	if (f.selector == withdraw(address, uint256, bool).selector) {
// 		withdraw(e, recipient, amount1 + amount2, toUnderlying);
// 	}
// 	else {
// 		withdrawDynamicAmount(e, recipient, amount1 + amount2, toUnderlying);
// 	}
// 	uint256 assetBySender_ = ASSET.balanceOf(e.msg.sender);
// 	uint256 assetByRecipient_ = ASSET.balanceOf(recipient);
// 	uint256 assetByStaticAToken_ = ASSET.balanceOf(currentContract);
// 	uint256 assetByAToken_ = ASSET.balanceOf(ATOKEN);
	
// 	uint256 staticATokenBySender_ = balanceOf(e.msg.sender);
// 	uint256 staticATokenByRecipient_ = balanceOf(recipient);
	
// 	uint256 aTokenBySender_ = ATOKEN.balanceOf(e.msg.sender);
// 	uint256 aTokenByRecipient_ = ATOKEN.balanceOf(recipient);
// 	uint256 aTokenByStaticAToken_ = ATOKEN.balanceOf(currentContract);
	
// 	assert _staticATokenBySender > 0 && toUnderlying => assetByRecipient_ > _assetByRecipient && assetByAToken_ < _assetByAToken;
// 	assert _staticATokenBySender > 0 && !toUnderlying => aTokenByRecipient_ > _aTokenByRecipient;
// 	assert _staticATokenBySender > 0 => aTokenByStaticAToken_ < _aTokenByStaticAToken && staticATokenBySender_ < _staticATokenBySender;
// 	assert assetByStaticAToken_ == _assetByStaticAToken;
// 	assert e.msg.sender != recipient => aTokenBySender_ == _aTokenBySender && assetBySender_ == _assetBySender && staticATokenByRecipient_ == _staticATokenByRecipient;
// }
