import "./AStETH_summerizations.spec"

using SymbolicLendingPool as LENDING_POOL
using DummyERC20A as UNDERLYING_ASSET
using DummyERC20B as RESERVE_TREASURY

methods {    

    getRevision() returns (uint256)
    initialize(uint8, string, string) envfree
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
    allowance(address, address) returns (uint256) envfree

    isContractIsTrue(address) returns (bool) envfree

    UNDERLYING_ASSET.balanceOf(address) returns (uint256) envfree
    UNDERLYING_ASSET.totalSupply() returns (uint256) envfree

    LENDING_POOL.aToken() returns (address) envfree

}

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
        Check that the changes to total supply are coherent with the changes to balance

    @Formula:
        {

        }

        < call any function >
        
        {
            ((ATokenInternalBalance1_ != _ATokenInternalBalance1) && (ATokenInternalBalance2_ != _ATokenInternalBalance2)) =>
            (ATokenInternalBalance1_ - _ATokenInternalBalance1) + (ATokenInternalBalance2_ - _ATokenInternalBalance2)  == (ATokenInternalTotalSupply_ - _ATokenInternalTotalSupply);
            
            ((ATokenScaledBalance1_ != _ATokenScaledBalance1) && (ATokenScaledBalance2_ != _ATokenScaledBalance2)) =>
            (ATokenScaledBalance1_ - _ATokenScaledBalance1) + (ATokenScaledBalance2_ - _ATokenScaledBalance2)  == (ATokenScaledTotalSupply_ - _ATokenScaledTotalSupply);
            
            ((ATokenBalance1_ != _ATokenBalance1) && (ATokenBalance2_ != _ATokenBalance2)) =>
            (ATokenBalance1_ - _ATokenBalance1) + (ATokenBalance2_ - _ATokenBalance2)  == (ATokenTotalSupply_ - ATokenTotalSupply_);
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

    assert ((ATokenInternalBalance1_ != _ATokenInternalBalance1) && (ATokenInternalBalance2_ != _ATokenInternalBalance2)) =>
            (ATokenInternalBalance1_ - _ATokenInternalBalance1) + (ATokenInternalBalance2_ - _ATokenInternalBalance2)  == (ATokenInternalTotalSupply_ - _ATokenInternalTotalSupply);
    assert ((ATokenScaledBalance1_ != _ATokenScaledBalance1) && (ATokenScaledBalance2_ != _ATokenScaledBalance2)) =>
            (ATokenScaledBalance1_ - _ATokenScaledBalance1) + (ATokenScaledBalance2_ - _ATokenScaledBalance2)  == (ATokenScaledTotalSupply_ - _ATokenScaledTotalSupply);
    assert ((ATokenBalance1_ != _ATokenBalance1) && (ATokenBalance2_ != _ATokenBalance2)) =>
            (ATokenBalance1_ - _ATokenBalance1) + (ATokenBalance2_ - _ATokenBalance2)  == (ATokenTotalSupply_ - ATokenTotalSupply_);
}

/*
    @Rule

    @Description:
        Checks that the totalSupply of AStETH must be backed by underlying asset in the contract when deposit is called (and hence mint)
        Checks that the totalSupply of AStETH must be backed by underlying asset in the contract when withdraw is called (and hence burn)

    @Formula:
        {
            _underlyingBalance >= _aTokenTotalSupply
        }

        LENDING_POOL.deposit(UNDERLYING_ASSET, amount, user, referralCode);
                                    OR
        LENDING_POOL.withdraw(e, UNDERLYING_ASSET, amount, user);

        {
            msg.sender != currentContract => underlyingBalance_ >= aTokenTotalSupply_
        }

    @Note:

    @Link:
    
*/

rule atokenPeggedToUnderlying(env e, uint256 amount, address user, uint16 referralCode){
    uint8 case;
    mathint _underlyingBalance = UNDERLYING_ASSET.balanceOf(currentContract);
    mathint _aTokenTotalSupply = totalSupply();

    require _underlyingBalance >= _aTokenTotalSupply;
    require LENDING_POOL.aToken() == currentContract;
    
    if (case == 0){
        LENDING_POOL.deposit(e, UNDERLYING_ASSET, amount, user, referralCode);
    }
    else if (case == 1){
        LENDING_POOL.withdraw(e, UNDERLYING_ASSET, amount, user);
    }
    // else if (case == 2){
    //     LENDING_POOL.borrow(e, UNDERLYING_ASSET, amount, user);
    // }
    // else if (case == 3){
    //     LENDING_POOL.flashLoan(e, UNDERLYING_ASSET, amount, user);
    // }
    
    mathint underlyingBalance_ = UNDERLYING_ASSET.balanceOf(currentContract);
    mathint aTokenTotalSupply_ = totalSupply();

    // Here the LHS of the implication is vital since a case where AStETH calls deposit will cause the backing token to be unchanged while Atokens will be minted.
    // This LHS demand is fine since AStETH cannot actively call deposit from lending pool, nor there is an `execute` method that allows calling methods externally from other contracts.
    assert e.msg.sender != currentContract => underlyingBalance_ >= aTokenTotalSupply_;
}

/*
    @Rule

    @Description:ֿ
        The AStETH totalSupply, tracked by the contract, is the sum of AStETH balances across all users.

    @Formula:
        totalsGhost() == internalTotalSupply()

    @Note:

    @Link:
    
*/

invariant totalSupplyIsSumOfBalances()
    totalsGhost() == internalTotalSupply()

/*
    @Rule

    @Description:ֿ
        The AStETH balance of a single user is less or equal to the total supply

    @Formula:
        totalsGhost() >= internalBalanceOf(user)

    @Note: 
        For every function that implements a transfer between 2 users within the system, we required that the sum of balances of the 2 users start as less than the totalSupply.
        

    @Link:
    
*/

invariant totalSupplyGESingleUserBalance(address user, env e)
    totalsGhost() >= internalBalanceOf(user)
    {
        preserved transferFrom(address spender, address reciever, uint256 amount) with (env e2) {
            require internalBalanceOf(user) + internalBalanceOf(spender) <= totalsGhost();
        }
        preserved transfer(address reciever, uint256 amount) with (env e3) {
            require e3.msg.sender == e.msg.sender;
            require internalBalanceOf(user) + internalBalanceOf(e3.msg.sender) <= totalsGhost();
        }
        preserved transferOnLiquidation(address from, address to, uint256 amount) with (env e4) {
            require internalBalanceOf(user) + internalBalanceOf(from) <= totalsGhost(); 
        }
        preserved burn(address owner, address recieverUnderlying, uint256 amount, uint256 index)  with (env e5) {
            require internalBalanceOf(user) + internalBalanceOf(owner) <= totalsGhost(); 
        }
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


/*****************************
 *    IKHLAS - i01001        *
 *****************************/


 rule checkingGetRevisionFunction(){
	env e; method f; calldataarg args;
	f(e, args);
	
    mathint _RevisionStored = _getRevision(e);

    assert _RevisionStored <= max_uint, "Checking if GetRevision is within limits";
}


// rule MethodsVacuityCheck(method f) {
// 	env e; calldataarg args;
// 	f(e, args);
// 	assert false, "this method should have a non reverting path";
// }


rule AssetandTreasuryDifferentAddress(){
    env e; calldataarg args; method f;
    require UNDERLYING_ASSET != RESERVE_TREASURY;
    f(e, args);
    assert UNDERLYING_ASSET != RESERVE_TREASURY, "this is to ensure that they are different addresses; needs to be verified on Deployed Contract";
}

//
// checkingcorrectChainID TO BE RUN WITH DEPLOYED CONTRACT !
//

//  rule checkingcorrectChainID(){
// 	env e; method f; calldataarg args;
// 	f(e, args);
	
//     mathint _chainId = getChainID(e);

//     assert _chainId == 1, "Checking if chainId is the correct one as Mainnet for Ethereum";
// }

//
// checkingsetDecimalsIsCorrect TO BE RUN WITH DEPLOYED CONTRACT !
//

//  rule checkingsetDecimalsIsCorrect(){
// 	env e; method f; calldataarg args;
// 	f(e, args);
	
//     mathint _SetDecimals = _getDecimals(e);

//     assert _SetDecimals == 18, "Checking if number of decimals is correct";
// }


rule BurningbyLendingPoolOnly(address user, address receiver, uint256 amount, uint256 index, method f) {
	env e;

    burn@withrevert(e, user, receiver, amount, index);
    assert e.msg.sender != LENDING_POOL => lastReverted, "Burn function can only be called by LendingPool";
}

rule MintbyLendingPoolOnly(address user, uint256 amount, uint256 index, method f) {
	env e;

    mint@withrevert(e, user, amount, index);
    assert e.msg.sender != LENDING_POOL => lastReverted, "Mint function can only be called by LendingPool";

}

rule MinttoTreasurybyLendingPoolOnly(uint256 amount, uint256 index, method f) {
	env e;

    mintToTreasury@withrevert(e, amount, index);
    assert e.msg.sender != LENDING_POOL => lastReverted, "mintToTreasury function can only be called by LendingPool";

}

rule transferOnLiquidationbyLendingPoolOnly(address from, address to, uint256 value, method f) {
	env e;

    transferOnLiquidation@withrevert(e, from, to, value);
    assert e.msg.sender != LENDING_POOL => lastReverted, "transferOnLiquidation function can only be called by LendingPool";

}

rule transferUnderlyingTobyLendingPoolOnly(address target, uint256 amount, method f) {
	env e;

    transferUnderlyingTo@withrevert(e, target, amount);
    assert e.msg.sender != LENDING_POOL => lastReverted, "transferUnderlyingTo function can only be called by LendingPool";

}

rule checkingInternalAmountandBurnFunction(address user, address receiver, uint256 index, uint256 _amount, uint256 _stEthRebasingIndex, uint256 _aaveLiquidityIndex){
	env e; method f; calldataarg args;
	f(e, args);
    
    require _amount != 0;

    
    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
	
    burn(e, user, receiver, _amount, index);

    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint _InternalAmount = _gettoInternalAmount(e, _amount, _stEthRebasingIndex, _aaveLiquidityIndex);
    
    assert  _InternalAmount != 0, "Ensuring amount scaled is not giving an invalid number";
    assert _InternalAmount <=  max_uint, "Ensuring Internal Amount is within the max_uint limit";
    assert (_ATokenScaledBalance - ATokenScaledBalance_ ) == _InternalAmount, "Ensuring actual burn amount matches the Internal Amount";
}

 rule checkingInternalAmountandMintFunction(address user, uint256 index, uint256 _amount, uint256 _stEthRebasingIndex, uint256 _aaveLiquidityIndex){
	env e; method f; calldataarg args;
	f(e, args);
    
    require _amount != 0;

    
    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
	
    mint(e, user, _amount, index);

    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint _InternalAmount = _gettoInternalAmount(e, _amount, _stEthRebasingIndex, _aaveLiquidityIndex);
    
    assert  _InternalAmount != 0, "Ensuring amount scaled is not giving an invalid number";
    assert _InternalAmount <=  max_uint, "Ensuring Internal Amount is within the max_uint limit";
    assert (ATokenScaledBalance_ - _ATokenScaledBalance) == _InternalAmount, "Ensuring actual mint amount matches the Internal Amount";
}

rule MinttoTreasuryAmountZeroOrNot(uint256 amount, uint256 index, uint256 _stEthRebasingIndex, uint256 _aaveLiquidityIndex, method f) {
	env e;

    require e.msg.sender == LENDING_POOL;
    mathint _ATokenBalance = balanceOf(RESERVE_TREASURY);


    mintToTreasury(e, amount, index);

    mathint _InternalAmount = _gettoInternalAmount(e, amount, _stEthRebasingIndex, _aaveLiquidityIndex);
    mathint ATokenBalance_ = balanceOf(RESERVE_TREASURY);

    if(amount == 0){
    assert _ATokenBalance == ATokenBalance_, "No mint if amount is equal to zero";
    }

    else{
    assert _ATokenBalance + _InternalAmount == ATokenBalance_, "Mint amount is equivalent to the calculated Internal Amount";

    }

}

rule CheckingFunctiontransferOnLiquidation(address from, address to, uint256 value) {
	env e;

    require from != to;

    mathint _ATokenInternalBalanceFROM = internalBalanceOf(from);
    mathint _ATokenScaledBalanceFROM = scaledBalanceOf(from);
    mathint _ATokenBalanceFROM = balanceOf(from);
    mathint _ATokenInternalBalanceTO = internalBalanceOf(to);
    mathint _ATokenScaledBalanceTO = scaledBalanceOf(to);
    mathint _ATokenBalanceTO = balanceOf(to);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    
    transferOnLiquidation(e, from, to, value);
    
    mathint ATokenInternalBalanceFROM_ = internalBalanceOf(from);
    mathint ATokenScaledBalanceFROM_ = scaledBalanceOf(from);
    mathint ATokenBalanceFROM_ = balanceOf(from);
    mathint ATokenInternalBalanceTO_ = internalBalanceOf(to);
    mathint ATokenScaledBalanceTO_ = scaledBalanceOf(to);
    mathint ATokenBalanceTO_ = balanceOf(to);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    
    assert _ATokenInternalBalanceFROM == value + ATokenInternalBalanceFROM_;
    assert _ATokenScaledBalanceFROM == value + ATokenScaledBalanceFROM_;
    assert _ATokenBalanceFROM == value + ATokenBalanceFROM_;

    assert _ATokenInternalBalanceTO + value == ATokenInternalBalanceTO_;
    assert _ATokenScaledBalanceTO + value == ATokenScaledBalanceTO_;
    assert _ATokenBalanceTO + value == ATokenBalanceTO_;

    assert _ATokenInternalTotalSupply == ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply == ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply == ATokenTotalSupply_;
}


rule transferOnLiquidationExceedingBalance(address from, address to, uint256 value, method f) {
	env e;

    mathint _ATokenInternalBalanceFROM = internalBalanceOf(from);
    mathint _ATokenScaledBalanceFROM = scaledBalanceOf(from);
    mathint _ATokenBalanceFROM = balanceOf(from);
    mathint _ATokenInternalBalanceTO = internalBalanceOf(to);
    mathint _ATokenScaledBalanceTO = scaledBalanceOf(to);
    mathint _ATokenBalanceTO = balanceOf(to);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();

    require value > _ATokenBalanceFROM;
    
    transferOnLiquidation@withrevert(e, from, to, value);

    mathint ATokenInternalBalanceFROM_ = internalBalanceOf(from);
    mathint ATokenScaledBalanceFROM_ = scaledBalanceOf(from);
    mathint ATokenBalanceFROM_ = balanceOf(from);
    mathint ATokenInternalBalanceTO_ = internalBalanceOf(to);
    mathint ATokenScaledBalanceTO_ = scaledBalanceOf(to);
    mathint ATokenBalanceTO_ = balanceOf(to);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    

    assert _ATokenInternalBalanceFROM == ATokenInternalBalanceFROM_;
    assert _ATokenScaledBalanceFROM == ATokenScaledBalanceFROM_;
    assert _ATokenBalanceFROM == ATokenBalanceFROM_;

    assert _ATokenInternalBalanceTO == ATokenInternalBalanceTO_;
    assert _ATokenScaledBalanceTO == ATokenScaledBalanceTO_;
    assert _ATokenBalanceTO == ATokenBalanceTO_;

    assert _ATokenInternalTotalSupply == ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply == ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply == ATokenTotalSupply_;
}

rule BurnExceedingBalance(address user, address receiver, uint256 amount, uint256 index) {
	env e;

    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    mathint _underlyingReciverBalance = UNDERLYING_ASSET.balanceOf(receiver);
    
    require amount > _ATokenBalance;
    burn@withrevert(e, user, receiver, amount, index);
    
    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    mathint underlyingReciverBalance_ = UNDERLYING_ASSET.balanceOf(receiver);
    
    
    assert _ATokenInternalBalance == ATokenInternalBalance_;
    assert _ATokenScaledBalance == ATokenScaledBalance_;
    assert _ATokenBalance == ATokenBalance_;
    assert _ATokenInternalTotalSupply == ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply == ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply == ATokenTotalSupply_;
    
    assert _underlyingReciverBalance == underlyingReciverBalance_;
}

 rule checkingBalanceOfFunctionLimits(address user){
	env e; method f; calldataarg args;
	// f(e, args);
	
    mathint _Balance = balanceOf(user);
    mathint _ScaledBalance = scaledBalanceOf(user);
    mathint _InternalBalance = internalBalanceOf(user);
    mathint _Supply = totalSupply();

    assert _Balance <= max_uint, "Checking if Balanceof is within limits";
    assert _Balance <= _Supply, "Checking if Balanceof is less than supply";
    assert _ScaledBalance <= _Balance, "Checking if Balanceof is greater than scaled balance";
    assert _InternalBalance <= _Balance, "Checking if Balanceof is greater than internal balance";

}


 rule checkingscaledBalanceOfFunctionLimits(address user){
	env e; method f; calldataarg args;
	f(e, args);
	
    mathint _Balance = scaledBalanceOf(user);
    mathint _scaledTotalSupply = scaledTotalSupply();

    assert _Balance <= max_uint, "Checking if scaledBalanceOf is within limits";
    // assert _Balance <= _scaledTotalSupply, "Checking if scaledBalanceOf is less than scaledTotalSupply";  ASSERT BEING VIOLATED 

}


 rule checkinginternalBalanceOfFunctionLimits(address user){
	env e; method f; calldataarg args;
	f(e, args);
	
    mathint _Balance = internalBalanceOf(user);
    mathint _InternalTotalSupply = internalTotalSupply();

    assert _Balance <= max_uint, "Checking if internalBalanceOf is within limits";
    assert _Balance <= _InternalTotalSupply, "Checking if internalBalanceOf is less than internalTotalSupply";

}


 rule checkinggetScaledUserBalanceAndSupplyFunctionLimits(address user){
	env e; method f; calldataarg args;
	// f(e, args);
	mathint _Balance;
    mathint _Supply;
    _Balance, _Supply = getScaledUserBalanceAndSupply(user);

    assert _Balance <= max_uint, "Checking if ScaledUserBalance is within limits";
    assert _Supply <= max_uint, "Checking if ScaledSupply is within limits";
    assert _Balance <= _Supply, "Checking if ScaledUserBalance is less than or equal to supply";

}

 rule checkingtotalSupplyFunctionLimits(address user, uint256 _rebasingIndex){
	env e; method f; calldataarg args;
	f(e, args);
	
    mathint _scaledTotalSupply = scaledTotalSupply();
    mathint _Supply = totalSupply();

    if(_scaledTotalSupply == 0){
        assert _Supply == 0, "Checking if the correct Total Supply is provided";
    }
    else{
    assert _Supply <= max_uint, "Checking if Total Supply Function is within limits";
    }
}

 rule checkingscaledTotalSupplyFunctionLimits(address user){
	env e; method f; calldataarg args;
	f(e, args);
	
    mathint _scaledTotalSupply = scaledTotalSupply();

    assert _scaledTotalSupply <= max_uint, "Checking if scaledTotalSupply is within limits";
}

 rule checkinginternalTotalSupplyFunctionLimits(address user){
	env e; method f; calldataarg args;
	f(e, args);
	
    mathint _InternalTotalSupply = internalTotalSupply();

    assert _InternalTotalSupply <= max_uint, "Checking if internalTotalSupply is within limits";
}

rule PermitFunctionOwnerNotAddress0(	address owner,
    address spender,
    uint256 value,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s, method f) {

    env e;

    permit@withrevert(e, owner, spender, value, deadline, v, r, s);
    assert owner == 0x0000000000000000000000000000000000000000 => lastReverted, "Permit function cannot have owner as Address(0)";
}


rule CheckPermitFunction(	address owner,
    address spender,
    uint256 value,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s) {

    env e;
    require value != 0;

    mathint _BeforeNonce = _getNonces(e, owner);
    mathint _allowance = allowance(owner, spender);
    
    permit(e, owner, spender, value, deadline, v, r, s);

    mathint _NonceAfter = _getNonces(e, owner);
    mathint allowance_ = allowance(owner, spender);

    assert _NonceAfter >  _BeforeNonce, "Nonce changes after Permit";
    assert allowance_ >= _allowance, "Allowance increases";
}


rule checktransferFunction(address from, address to, uint256 amount, bool validate, method f) {

    env e;

    require amount != 0;

    mathint _ATokenInternalBalanceFROM = internalBalanceOf(from);
    mathint _ATokenScaledBalanceFROM = scaledBalanceOf(from);
    mathint _ATokenBalanceFROM = balanceOf(from);
    mathint _ATokenInternalBalanceTO = internalBalanceOf(to);
    mathint _ATokenScaledBalanceTO = scaledBalanceOf(to);
    mathint _ATokenBalanceTO = balanceOf(to);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    
    _gettransfer(e, from, to, amount, validate);

    mathint ATokenInternalBalanceFROM_ = internalBalanceOf(from);
    mathint ATokenScaledBalanceFROM_ = scaledBalanceOf(from);
    mathint ATokenBalanceFROM_ = balanceOf(from);
    mathint ATokenInternalBalanceTO_ = internalBalanceOf(to);
    mathint ATokenScaledBalanceTO_ = scaledBalanceOf(to);
    mathint ATokenBalanceTO_ = balanceOf(to);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    

    assert _ATokenInternalBalanceFROM >= ATokenInternalBalanceFROM_;
    assert _ATokenScaledBalanceFROM >= ATokenScaledBalanceFROM_;
    assert _ATokenBalanceFROM >= ATokenBalanceFROM_;

    assert _ATokenInternalBalanceTO <= ATokenInternalBalanceTO_;
    assert _ATokenScaledBalanceTO <= ATokenScaledBalanceTO_;
    assert _ATokenBalanceTO <= ATokenBalanceTO_;

    assert _ATokenInternalTotalSupply == ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply == ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply == ATokenTotalSupply_;

}

rule checktransferFunction2(address from, address to, uint256 amount, method f) {

    env e;

    require amount != 0;

    mathint _ATokenInternalBalanceFROM = internalBalanceOf(from);
    mathint _ATokenScaledBalanceFROM = scaledBalanceOf(from);
    mathint _ATokenBalanceFROM = balanceOf(from);
    mathint _ATokenInternalBalanceTO = internalBalanceOf(to);
    mathint _ATokenScaledBalanceTO = scaledBalanceOf(to);
    mathint _ATokenBalanceTO = balanceOf(to);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    
    _gettransfer2(e, from, to, amount);

    mathint ATokenInternalBalanceFROM_ = internalBalanceOf(from);
    mathint ATokenScaledBalanceFROM_ = scaledBalanceOf(from);
    mathint ATokenBalanceFROM_ = balanceOf(from);
    mathint ATokenInternalBalanceTO_ = internalBalanceOf(to);
    mathint ATokenScaledBalanceTO_ = scaledBalanceOf(to);
    mathint ATokenBalanceTO_ = balanceOf(to);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    

    assert _ATokenInternalBalanceFROM >= ATokenInternalBalanceFROM_;
    assert _ATokenScaledBalanceFROM >= ATokenScaledBalanceFROM_;
    assert _ATokenBalanceFROM >= ATokenBalanceFROM_;

    assert _ATokenInternalBalanceTO <= ATokenInternalBalanceTO_;
    assert _ATokenScaledBalanceTO <= ATokenScaledBalanceTO_;
    assert _ATokenBalanceTO <= ATokenBalanceTO_;

    assert _ATokenInternalTotalSupply == ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply == ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply == ATokenTotalSupply_;

}

 rule checkingscaledBalanceOfFunctionLimits2(address user, uint256 rebasingIndex){
	env e; method f; calldataarg args;
	f(e, args);
	
    mathint _Balance = _getscaledBalanceOf(e, user, rebasingIndex);
    mathint _ScaledTotalSupply = _getscaledTotalSupply(e, rebasingIndex);

    assert _Balance <= max_uint, "Checking if scaledBalanceOf is within limits";
    assert _Balance <= _ScaledTotalSupply, "Checking if _scaledBalanceOf is less than scaledTotalSupply";
}


 rule checkingstEthRebasingIndexFunctionLimits(){
	env e; method f; calldataarg args;
	f(e, args);
	
    mathint _Index = _getstEthRebasingIndex(e);

    assert _Index <= max_uint, "Checking if stEthRebasingIndex is within limits";
}