import "./AStETH_summerizations.spec"

using SymbolicLendingPool as LENDING_POOL
using IncentivesControllerMock as _incentivesController
using DummyERC20A as UNDERLYING_ASSET_ADDRESS
using DummyERC20B as RESERVE_TREASURY_ADDRESS

methods {     
    initializing() envfree
    initialize(uint8, string, string) envfree
    nonces(address) returns(uint256) envfree
    allowance(address, address) returns(uint256) envfree
    balanceOf(address) returns (uint256) envfree
    scaledBalanceOf(address) returns (uint256) envfree
    internalBalanceOf(address) returns (uint256) envfree
    getScaledUserBalanceAndSupply(address) returns (uint256, uint256) envfree
    totalSupply() returns (uint256) envfree
    scaledTotalSupply() returns (uint256) envfree
    internalTotalSupply() returns (uint256) envfree
    burn(address, address,uint256, uint256)
    mint(address, uint256, uint256)
    mintToTreasury(uint256, uint256)
    transferOnLiquidation(address, address, uint256)
    transferUnderlyingTo(address, uint256) returns (uint256)
    permit(address, address, uint256, uint256, uint8, bytes32, bytes32)

    UNDERLYING_ASSET_ADDRESS.balanceOf(address user) returns(uint256) envfree
    RESERVE_TREASURY_ADDRESS.balanceOf(address user) returns(uint256) envfree

    LENDING_POOL.getReserveNormalizedIncome(address asset) returns(uint256) envfree
    // IncentivizedERC20 methods:
    // handleAction(address user, uint256 userBalance, uint256 totalSupply) => DISPATCHER(true)
}

/**************************************************
 *               CVL FUNCS & DEFS                 *
 **************************************************/

function ray() returns uint256 {
    return 1000000000000000000000000000; // = one RAY
}

function halfray() returns uint256 {
    return 500000000000000000000000000; // = half RAY
}

 /**************************************************
 *                GHOSTS AND HOOKS                *
 **************************************************/
ghost balanceSum() returns uint256 {    
    init_state axiom balanceSum() == 0;
}

hook Sstore _balances[KEY address user] uint balance (uint oldBalance) STORAGE {
	havoc balanceSum assuming balanceSum@new() == balanceSum@old() + balance - oldBalance;
}

// Invariants
invariant integrityOfTotalSupply() 
 	totalSupply() == balanceSum()


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
    require initializing() == false;
    initialize(underlyingAssetDecimals, tokenName, tokenSymbol);

    initialize@withrevert(underlyingAssetDecimals, tokenName, tokenSymbol);
    bool secondSucceeded = !lastReverted;

    assert secondSucceeded==false;
}

rule balanceOfChange(address user1, address user2, method f)
{
	env e;
	require user1!=user2;
	uint256 _balanceA = balanceOf(user1);
	uint256 _balanceB = balanceOf(user2);
	 
	calldataarg arg;
	f(e, arg); 

	uint256 balanceA_ = balanceOf(user1);
	uint256 balanceB_ = balanceOf(user2);
	
	assert (_balanceA == balanceA_ || _balanceB == balanceB_ || 
        (_balanceA != balanceA_ && _balanceB != balanceB_ && _balanceA+_balanceB == balanceA_+balanceB_)
    );
}

rule integirtyBalanceOfTotalSupply(address user, method f ) filtered {
	f -> f.selector != transferFrom(address,address,uint256).selector
        && f.selector != transfer(address,uint256).selector
        && f.selector != transferOnLiquidation(address,address,uint256).selector 
	}
{
	env e;
	uint256 _balanceA = balanceOf(user);
	uint256 _totalSupply = totalSupply();
	 
	calldataarg arg;
	f(e, arg); 
	uint256 balanceA_ = balanceOf(user);
	uint256 totalSupply_ = totalSupply();

	assert  (balanceA_ != _balanceA  => (balanceA_ - _balanceA  == totalSupply_ - _totalSupply));
}

rule integrityOfBurn(address user, address receiverOfUnderlying,
    uint256 amount, uint256 index, uint256 stEthRebasingIndex,
    uint256 aaveLiquidityIndex)
{
    env e;
    uint256 amountScaled = returnAmount(amount, stEthRebasingIndex, aaveLiquidityIndex);
    mathint _totalSupply = totalSupply();
    uint256 _balance = balanceOf(user);
    uint256 _underlyingBalance = UNDERLYING_ASSET_ADDRESS.balanceOf(receiverOfUnderlying);
    burn(e, user, receiverOfUnderlying, amount, index);
    mathint totalSupply_ = totalSupply();
    uint256 balance_ = balanceOf(user);
    uint256 underlyingBalance_ = UNDERLYING_ASSET_ADDRESS.balanceOf(receiverOfUnderlying);

    assert e.msg.sender == LENDING_POOL;
    assert _totalSupply-amountScaled == totalSupply_;
    assert _balance-amountScaled == balance_;
    assert receiverOfUnderlying!=currentContract => _underlyingBalance+amount == underlyingBalance_;
}

rule burnAdditive(address user, address receiverOfUnderlying, uint256 amount1,  uint256 amount2, uint256 index) {
	env e;
	storage initialStorage = lastStorage;
	burn(e, user, receiverOfUnderlying, amount1, index);
	burn(e, user, receiverOfUnderlying, amount2, index);
	uint256 balanceScenario1 = balanceOf(user);
    mathint totalSupplyScenario1 = totalSupply();
	uint256 amount = amount1 + amount2;
	burn(e, user, receiverOfUnderlying, amount, index) at initialStorage;
	uint256 balanceScenario2 = balanceOf(user);
    mathint totalSupplyScenario2 = totalSupply();

	assert balanceScenario1 == balanceScenario2, "burn is not additive";
    assert totalSupplyScenario1 == totalSupplyScenario2;
}

rule burnNoInterfernece(address user, address user2, address receiverOfUnderlying, address receiverOfUnderlying2,
    uint256 amount, uint256 index, uint256 stEthRebasingIndex, uint256 aaveLiquidityIndex)
{
    env e;
    // for onlyLendingPool modifier
    require e.msg.sender == LENDING_POOL;
    uint256 _balance = balanceOf(user2);
    uint256 _underlyingBalance = UNDERLYING_ASSET_ADDRESS.balanceOf(receiverOfUnderlying2);
    burn(e, user, receiverOfUnderlying, amount, index);
    uint256 balance_ = balanceOf(user2);
    uint256 underlyingBalance_ = UNDERLYING_ASSET_ADDRESS.balanceOf(receiverOfUnderlying2);

    assert user!=user2 => _balance==balance_;
    assert receiverOfUnderlying!=receiverOfUnderlying2 && receiverOfUnderlying2!=currentContract =>  _underlyingBalance==underlyingBalance_;
}

rule integrityOfMint(address user, uint256 amount, uint256 index) {
	env e;
    mathint _totalSupply = totalSupply();
    uint256 _balance = balanceOf(user);
    mint(e, user, amount, index);
    mathint totalSupply_ = totalSupply();
    uint256 balance_ = balanceOf(user);
    assert e.msg.sender == LENDING_POOL;
    assert amount != 0 => _totalSupply < totalSupply_;
    assert amount != 0 => _balance < balance_;
}


rule mintAdditive(address user, uint256 amount1, uint256 amount2, uint256 index) {
    env e;
	storage initialStorage = lastStorage;
	mint(e, user, amount1, index);
	mint(e, user, amount2, index);
	uint256 balanceScenario1 = balanceOf(user);
    mathint totalSupplyScenario1 = totalSupply();
	uint256 amount = amount1 + amount2;
	mint(e, user, amount, index) at initialStorage;
	uint256 balanceScenario2 = balanceOf(user);
    mathint totalSupplyScenario2 = totalSupply();
	assert balanceScenario1 == balanceScenario2, "burn is not additive";
    assert totalSupplyScenario1 == totalSupplyScenario2;
}

rule mintNoInterfernece(address user, address user2,
    uint256 amount, uint256 index) {
    env e;
    // for onlyLendingPool modifier
    require e.msg.sender == LENDING_POOL;
    uint256 _balance = balanceOf(user2);
    mint(e, user, amount, index);
    uint256 balance_ = balanceOf(user2);

    assert user!=user2 => _balance==balance_;
}

rule mintToTreasuryEquivalence(uint256 amount, uint256 index) {
    env e;
    storage initialStorage = lastStorage;
    address user = RESERVE_TREASURY_ADDRESS;
    mint(e, user, amount, index);
    mathint _totalSupply = totalSupply();
    uint256 _balance = balanceOf(user);

    mintToTreasury(e, amount, index) at initialStorage;
    mathint totalSupply_ = totalSupply();
    uint256 balance_ = balanceOf(user);

    assert e.msg.sender == LENDING_POOL;
    assert _totalSupply == totalSupply_;
    assert _balance == balance_;
}

rule inverseMintBurn(address user, address receiverOfUnderlying, uint256 amount, uint256 index) {
	env e;
	uint256 _balance = balanceOf(user);
	mint(e, user, amount, index);
	burn(e, user, receiverOfUnderlying, amount, index);
	uint256 balance_ = balanceOf(user);
	assert _balance == balance_, "burn is not the inverse of mint";
}

rule transferOnLiquidation(address from, address to, uint256 value) {
    env e;
    uint256 _balanceByFrom = balanceOf(from);
    uint256 _balanceByTo = balanceOf(to);
    mathint _totalSupply = totalSupply();

	transferOnLiquidation(e, from, to, value);

    uint256 balanceByFrom_ = balanceOf(from);
    uint256 balanceByTo_ = balanceOf(to);
    mathint totalSupply_ = totalSupply();

    assert e.msg.sender == LENDING_POOL;
    assert from != to && value!=0 => _balanceByFrom > balanceByFrom_;
    assert from != to && value!=0 => _balanceByTo < balanceByTo_;
    assert _balanceByFrom+_balanceByTo == balanceByFrom_+balanceByTo_;
    assert _totalSupply == totalSupply_;
}

rule permitIntegrity(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s)
{
	env e;
	uint256 nonceBefore = nonces(owner);
	permit(e, owner, spender, value, deadline, v, r, s);
	assert allowance(owner, spender) == value;
	assert nonces(owner) == nonceBefore + 1;
}

rule permitNoInterfernece(address owner, address owner2, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s)
{
	env e;
    require owner != owner2;
	uint256 _allowance = allowance(owner2, spender);
    uint256 _nonce = nonces(owner2);
	permit(e, owner, spender, value, deadline, v, r, s);
    uint256 allowance_ = allowance(owner2, spender);
    uint256 nonce_ = nonces(owner2);
	assert _allowance == allowance_;
	assert _nonce == nonce_;
}

rule scaledTotalSupplyEquivalance(address user) {
    env e;
    uint256 sts = scaledTotalSupply();
    uint256 scaledBalanceOf;
    uint256 scaledTotalSupply;
    scaledBalanceOf, scaledTotalSupply = getScaledUserBalanceAndSupply(user);
    uint256 its = internalTotalSupply();
    uint256 ts = totalSupply();
    assert sts == scaledTotalSupply;
    // how to use rayMul directly?
    assert ts == identity(sts, LENDING_POOL.getReserveNormalizedIncome(UNDERLYING_ASSET_ADDRESS)); 
    assert sts == its * rebasingRatio() / ray();
}

rule scaledBalanceEquivalance(address user) {
    env e;
    uint256 sbc = scaledBalanceOf(user);
    uint256 scaledBalanceOf;
    uint256 scaledTotalSupply;
    scaledBalanceOf, scaledTotalSupply = getScaledUserBalanceAndSupply(user);
    uint256 ibc = internalBalanceOf(user);
    uint256 bc = balanceOf(user);
    assert sbc == scaledBalanceOf;
    // how to use rayMul directly?
    assert bc == identity(ibc, LENDING_POOL.getReserveNormalizedIncome(UNDERLYING_ASSET_ADDRESS)); 
    assert sbc == ibc * rebasingRatio() / ray();
}

rule transferUnderlyingTo(address target, uint256 amount) {
    env e;
    uint256 _balance = UNDERLYING_ASSET_ADDRESS.balanceOf(target);
    transferUnderlyingTo(e, target, amount);
    uint256 balance_ = UNDERLYING_ASSET_ADDRESS.balanceOf(target);
    assert e.msg.sender == LENDING_POOL;
    if (target!=currentContract)
        assert _balance + amount == balance_;
    else
        assert _balance == balance_;
}

rule transferUnderlyingToAdditivity(address target, uint256 amount1, uint256 amount2) {
    env e;
    storage init = lastStorage;
    uint amount = amount1 + amount2;
    transferUnderlyingTo(e, target, amount1);
    transferUnderlyingTo(e, target, amount2);

    uint256 _balance = UNDERLYING_ASSET_ADDRESS.balanceOf(target);

    transferUnderlyingTo(e, target, amount) at init;
    uint256 balance_ = UNDERLYING_ASSET_ADDRESS.balanceOf(target);
    assert _balance == balance_;
}


rule transferUnderlyingToNoInterfernece(address target, address target2, uint256 amount) {
    env e;
    uint256 _balance = UNDERLYING_ASSET_ADDRESS.balanceOf(target2);
    transferUnderlyingTo(e, target, amount);
    uint256 balance_ = UNDERLYING_ASSET_ADDRESS.balanceOf(target2);
    assert target!=target2 && target2!=currentContract => _balance == balance_;
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
