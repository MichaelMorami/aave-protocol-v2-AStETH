import "./AStETH_summerizations.spec"

using SymbolicLendingPool as LENDING_POOL
using IncentivesControllerMock as _incentivesController
using DummyERC20A as UNDERLYING_ASSET
using DummyERC20B as RESERVE_TREASURY

methods {     
    getRevision() returns (uint256)
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
    isContractIsTrue(address) returns (bool) envfree

    UNDERLYING_ASSET.balanceOf(address user) returns(uint256) envfree
    UNDERLYING_ASSET.totalSupply() returns(uint256) envfree
    RESERVE_TREASURY.balanceOf(address user) returns(uint256) envfree

    LENDING_POOL.aToken() envfree
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

rule integrityBalanceOfAndTotalSupply(address user, method f ) filtered {
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
    uint256 _underlyingBalance = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying);
    burn(e, user, receiverOfUnderlying, amount, index);
    mathint totalSupply_ = totalSupply();
    uint256 balance_ = balanceOf(user);
    uint256 underlyingBalance_ = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying);

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
    uint256 _underlyingBalance = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying2);
    burn(e, user, receiverOfUnderlying, amount, index);
    uint256 balance_ = balanceOf(user2);
    uint256 underlyingBalance_ = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying2);

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
    address user = RESERVE_TREASURY;
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
    assert ts == identity(sts, LENDING_POOL.getReserveNormalizedIncome(UNDERLYING_ASSET)); 
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
    assert bc == identity(ibc, LENDING_POOL.getReserveNormalizedIncome(UNDERLYING_ASSET)); 
    assert sbc == ibc * rebasingRatio() / ray();
}

rule transferUnderlyingTo(address target, uint256 amount) {
    env e;
    uint256 _balance = UNDERLYING_ASSET.balanceOf(target);
    transferUnderlyingTo(e, target, amount);
    uint256 balance_ = UNDERLYING_ASSET.balanceOf(target);
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

    uint256 _balance = UNDERLYING_ASSET.balanceOf(target);

    transferUnderlyingTo(e, target, amount) at init;
    uint256 balance_ = UNDERLYING_ASSET.balanceOf(target);
    assert _balance == balance_;
}


rule transferUnderlyingToNoInterfernece(address target, address target2, uint256 amount) {
    env e;
    uint256 _balance = UNDERLYING_ASSET.balanceOf(target2);
    transferUnderlyingTo(e, target, amount);
    uint256 balance_ = UNDERLYING_ASSET.balanceOf(target2);
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


/*
    @Rule

    @Description:
        The balance of a reciver in TransferUnderlyingTo() should increase by amount
        The balance of a sender in TransferUnderlyingTo() should decrease by amount

    @Formula:
        {
            user != currentContract;
        }

        transferUnderlyingTo(user, amount)
        
        {
            userBalanceAfter == userBalanceBefore + amountTransfered;
            totalSupplyAfter == totalSupplyBefore - amountTransfered;
        }

    @Note:

    @Link:
*/
rule integrityOfTransferUnderlyingTo(address user, uint256 amount) {
    env e;
    require user != currentContract;
    mathint totalSupplyBefore = UNDERLYING_ASSET.balanceOf(currentContract);
    mathint userBalanceBefore = UNDERLYING_ASSET.balanceOf(user);
    uint256 amountTransfered = transferUnderlyingTo(e, user, amount);
    mathint totalSupplyAfter = UNDERLYING_ASSET.balanceOf(currentContract);
    mathint userBalanceAfter = UNDERLYING_ASSET.balanceOf(user);
    assert userBalanceAfter == userBalanceBefore + amountTransfered;
    assert totalSupplyAfter == totalSupplyBefore - amountTransfered;
}
/*
    @Rule

    @Description:
        Minting AStETH must increase the AStETH totalSupply and user's balance
    @Formula:
        {
        }
        mint()
        
        {
            _ATokenInternalBalance < ATokenInternalBalance_ &&
            _ATokenScaledBalance < ATokenScaledBalance_ &&
            _ATokenBalance < ATokenBalance_ &&
            _ATokenInternalTotalSupply < ATokenInternalTotalSupply_ &&
            _ATokenScaledTotalSupply < ATokenScaledTotalSupply_ &&
            _ATokenTotalSupply < ATokenTotalSupply_
        }
    @Note:
    @Link:
*/
rule monotonicityOfMint(address user, uint256 amount, uint256 index) {
	env e;
    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    
    mint(e, user, amount, index);
    
    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    
    assert _ATokenInternalBalance < ATokenInternalBalance_;
    assert _ATokenScaledBalance < ATokenScaledBalance_;
    assert _ATokenBalance < ATokenBalance_;
    assert _ATokenInternalTotalSupply < ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply < ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply < ATokenTotalSupply_;
}
/*
    @Rule
    @Description:
        Burning AStETH must decrease the AStETH totalSupply and user's balance.
        It should also not decrease reciver's underlying asset.

    @Formula:
        {

        }

        burn()
        
        {
            _ATokenInternalBalance > ATokenInternalBalance_ &&
            _ATokenScaledBalance > ATokenScaledBalance_ &&
            _ATokenBalance > ATokenBalance_ &&
            _ATokenInternalTotalSupply > ATokenInternalTotalSupply_ &&
            _ATokenScaledTotalSupply > ATokenScaledTotalSupply_ &&
            _ATokenTotalSupply > ATokenTotalSupply_ &&
            _underlyingReciverBalance <= underlyingReciverBalance_ &&
            _underlyingTotalSupply == underlyingTotalSupply_
        }

    @Note:

    @Link:
*/

rule monotonicityOfBurn(address user, address reciver, uint256 amount, uint256 index) {
	env e;

    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    mathint _underlyingReciverBalance = UNDERLYING_ASSET.balanceOf(reciver);
    
    burn(e, user, reciver, amount, index);
    
    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    mathint underlyingReciverBalance_ = UNDERLYING_ASSET.balanceOf(reciver);
    
    
    assert _ATokenInternalBalance > ATokenInternalBalance_;
    assert _ATokenScaledBalance > ATokenScaledBalance_;
    assert _ATokenBalance > ATokenBalance_;
    assert _ATokenInternalTotalSupply > ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply > ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply > ATokenTotalSupply_;
    
    assert _underlyingReciverBalance <= underlyingReciverBalance_;
}

/*
    @Rule

    @Description:
        Minting and burning are invert operations within the AStETH context

    @Formula:
        {

        }

        mint()
        burn()
        
        {
            _ATokenInternalBalance == ATokenInternalBalance_ &&
            _ATokenScaledBalance == ATokenScaledBalance_ &&
            _ATokenBalance == ATokenBalance_ &&
            _ATokenInternalTotalSupply == ATokenInternalTotalSupply_ &&
            _ATokenScaledTotalSupply == ATokenScaledTotalSupply_ &&
            _ATokenTotalSupply == ATokenTotalSupply_
        }

    @Note:

    @Link:
*/
rule mintBurnInvertability(address user, uint256 amount, uint256 index, address reciver){
    env e;
    
    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    
    mint(e, user, amount, index);
    burn(e, user, reciver, amount, index);
    
    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    
    assert _ATokenInternalBalance == ATokenInternalBalance_;
    assert _ATokenScaledBalance == ATokenScaledBalance_;
    assert _ATokenBalance == ATokenBalance_;
    assert _ATokenInternalTotalSupply == ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply == ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply == ATokenTotalSupply_;
}
/*
    @Rule

    @Description:
        AStETH cannot change the totalSupply of the underlying asset

    @Formula:
        {

        }

        < call any function >
        
        {
            _underlyingTotalSupply == underlyingTotalSupply_
        }

    @Note:

    @Link:
*/
rule aTokenCantAffectUnderlying(){
    env e; calldataarg args; method f;
    mathint _underlyingTotalSupply = UNDERLYING_ASSET.totalSupply();
    f(e, args);
    mathint underlyingTotalSupply_ = UNDERLYING_ASSET.totalSupply();
    assert _underlyingTotalSupply == underlyingTotalSupply_;
}
/*
    @Rule

    @Description:
        Check that each possible operation changes the balance of at most two users

    @Formula:
        {

        }

        < call any function >
        
        {
            _ATokenInternalBalance1 == ATokenInternalBalance1_ || _ATokenInternalBalance2 == ATokenInternalBalance2_ || _ATokenInternalBalance3 == ATokenInternalBalance3_
            _ATokenScaledBalance1 == ATokenScaledBalance1_ || _ATokenScaledBalance2 == ATokenScaledBalance2_ || _ATokenScaledBalance3 == ATokenScaledBalance3_
            _ATokenBalance1 == ATokenBalance1_ || _ATokenBalance2 == ATokenBalance2_ || _ATokenBalance3 == ATokenBalance3_
        }

    @Note:

    @Link:
*/
rule operationAffectMaxTwo(address user1, address user2, address user3)
{
	env e; calldataarg arg; method f;
	require user1!=user2 && user1!=user3 && user2!=user3;
    mathint _ATokenInternalBalance1 = internalBalanceOf(user1);
    mathint _ATokenInternalBalance2 = internalBalanceOf(user2);
    mathint _ATokenInternalBalance3 = internalBalanceOf(user3);
    mathint _ATokenScaledBalance1 = scaledBalanceOf(user1);
    mathint _ATokenScaledBalance2 = scaledBalanceOf(user2);
    mathint _ATokenScaledBalance3 = scaledBalanceOf(user3);
    mathint _ATokenBalance1 = balanceOf(user1);
    mathint _ATokenBalance2 = balanceOf(user2);
    mathint _ATokenBalance3 = balanceOf(user3);
	
    f(e, arg);
    mathint ATokenInternalBalance1_ = internalBalanceOf(user1);
    mathint ATokenInternalBalance2_ = internalBalanceOf(user2);
    mathint ATokenInternalBalance3_ = internalBalanceOf(user3);
    mathint ATokenScaledBalance1_ = scaledBalanceOf(user1);
    mathint ATokenScaledBalance2_ = scaledBalanceOf(user2);
    mathint ATokenScaledBalance3_ = scaledBalanceOf(user3);
    mathint ATokenBalance1_ = balanceOf(user1);
    mathint ATokenBalance2_ = balanceOf(user2);
    mathint ATokenBalance3_ = balanceOf(user3);
	assert (_ATokenInternalBalance1 == ATokenInternalBalance1_ || _ATokenInternalBalance2 == ATokenInternalBalance2_ || _ATokenInternalBalance3 == ATokenInternalBalance3_);
	assert (_ATokenScaledBalance1 == ATokenScaledBalance1_ || _ATokenScaledBalance2 == ATokenScaledBalance2_ || _ATokenScaledBalance3 == ATokenScaledBalance3_);
	assert (_ATokenBalance1 == ATokenBalance1_ || _ATokenBalance2 == ATokenBalance2_ || _ATokenBalance3 == ATokenBalance3_);
}
/*
    @Rule

    @Description:
        The totalSupply of AStETH must be backed by underlying asset in the contract

    @Formula:
        UNDERLYING_ASSET.balanceOf(LENDING_POOL) == totalSupply()

    @Note:
        Not including the minting functions since mint can only be called through LENDING_POOL after a user deposits UNDERLYING_ASSET.
        Calling mint from within the contract, without the greater contex will break this invariant.

    @Link:

*/

invariant atokenPeggedToUnderlying(env e)
    UNDERLYING_ASSET.balanceOf(currentContract) >= totalSupply()
    filtered { f -> f.selector != mint(address ,uint256 ,uint256).selector &&
                    f.selector != mintToTreasury(uint256, uint256).selector }
    {
        preserved with (env e2) {
            require currentContract != LENDING_POOL;
        }
    }

/*
    @Rule
    @Description:
        Checks that the totalSupply of AStETH must be backed by underlying asset in the contract when deposit is called (and hence mint)
    @Formula:
        {
            _underlyingBalance >= _aTokenTotalSupply
        }
        LENDING_POOL.deposit(UNDERLYING_ASSET, amount, user, referralCode);
        {
            underlyingBalance_ >= aTokenTotalSupply_
        }
    @Note:
    @Link:
    
*/

rule atokenPeggedToUnderlyingMint(env e, uint256 amount, address user, uint16 referralCode){
    mathint _underlyingBalance = UNDERLYING_ASSET.balanceOf(currentContract);
    mathint _aTokenTotalSupply = totalSupply();

    require _underlyingBalance >= _aTokenTotalSupply;
    require LENDING_POOL.aToken() == currentContract;
    
    LENDING_POOL.deposit(e, UNDERLYING_ASSET, amount, user, referralCode);
    
    mathint underlyingBalance_ = UNDERLYING_ASSET.balanceOf(currentContract);
    mathint aTokenTotalSupply_ = totalSupply();

    assert underlyingBalance_ >= aTokenTotalSupply_;
}

/*****************************
 *         UNFINISHED        *
 *****************************/
/*
    @Rule

    @Description:
        Verify conditions in which burn should revert

    @Formula:
        {
            user != 0 &&
		    e.msg.value == 0 &&
		    e.msg.sender == LENDING_POOL && LENDING_POOL != 0 &&
		    totalSupply() >= amount &&
		    to != 0 && 
		    (UNDERLYING_ASSET.balanceOf(currentContract) > amount  ) &&
		    UNDERLYING_ASSET.balanceOf(to) + amount < max_uint &&
		    balanceOf(user) < amount
        }

        burn@withrevert(e, user, to, amount, index)
        
        {
            !lastReverted
        }

    @Note:

    @Link:
*/
rule nonrevertOfBurn(address user, address to, uint256 amount) {
	env e;
	uint256 index;
    uint256 totalSupply = totalSupply();
    uint256 underlyingAStETHBalance = UNDERLYING_ASSET.balanceOf(currentContract);
    uint256 underlyingReciverBalance = UNDERLYING_ASSET.balanceOf(to);
    uint256 AStETHBalance = balanceOf(currentContract);
    uint256 reciverBalance = balanceOf(to);
    uint256 senderBalance = balanceOf(user);
    bool isContract = isContractIsTrue(UNDERLYING_ASSET);
	require (
		user != 0 && //user is not zero
		e.msg.value == 0 && //sends assets
		e.msg.sender == LENDING_POOL && LENDING_POOL != 0 && //sender is Lending pool
        amount != 0 && //amount is non-zero (for line 109 in AStETH.sol )
		totalSupply >= amount && //enough total supply is system (for line 214 in IncentivizedERC20.sol )
		to != 0 && //valid reciever
		(underlyingAStETHBalance >= amount)  && //enough balance in the underlying asset
		(AStETHBalance >= amount)  && //enough balance in the underlying asset
		underlyingReciverBalance + amount <= max_uint && //balance of reviever will not overflow, why not <
		reciverBalance + amount <= max_uint && //balance of reviever will not overflow, why not <
		senderBalance >= amount && //user have enough balance (for line 217 in IncentivizedERC20.sol )
        isContract //underlying asset is a contract
	 );
	burn@withrevert(e, user, to, amount, index);
	assert !lastReverted; 
}
/*
    @Rule

    @Description:
        Check that the changes to total supply are coherent with the changes to balance

    @Formula:
        {

        }

        < call any function >
        
        {

        }

    @Note:

    @Link:
*/

rule integrityBalanceOfTotalSupply(address user1, address user2){
	env e; calldataarg arg; method f;
    require user1 != user2;
	
    mathint _ATokenInternalBalance1 = internalBalanceOf(user1);
    mathint _ATokenInternalBalance2 = internalBalanceOf(user2);
    mathint _ATokenScaledBalance1 = scaledBalanceOf(user1);
    mathint _ATokenScaledBalance2 = scaledBalanceOf(user2);
    mathint _ATokenBalance1 = balanceOf(user1);
    mathint _ATokenBalance2 = balanceOf(user2);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
	 
	f(e, arg); 

    mathint ATokenInternalBalance1_ = internalBalanceOf(user1);
    mathint ATokenInternalBalance2_ = internalBalanceOf(user2);
    mathint ATokenScaledBalance1_ = scaledBalanceOf(user1);
    mathint ATokenScaledBalance2_ = scaledBalanceOf(user2);
    mathint ATokenBalance1_ = balanceOf(user1);
    mathint ATokenBalance2_ = balanceOf(user2);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
	
    assert (ATokenInternalBalance1_ - _ATokenInternalBalance1) + (ATokenInternalBalance2_ - _ATokenInternalBalance2)  == (ATokenInternalTotalSupply_ - _ATokenInternalTotalSupply);
    assert (ATokenScaledBalance1_ - _ATokenScaledBalance1) + (ATokenScaledBalance2_ - _ATokenScaledBalance2)  == (ATokenScaledTotalSupply_ - _ATokenScaledTotalSupply);
    assert (ATokenBalance1_ - _ATokenBalance1) + (ATokenBalance2_ - _ATokenBalance2)  == (ATokenTotalSupply_ - ATokenTotalSupply_);
}