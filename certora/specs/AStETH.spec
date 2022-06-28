import "./AStETH_summerizations.spec"

using SymbolicLendingPool as LENDING_POOL
using DummyERC20A as UNDERLYING_ASSET
using DummyERC20B as RESERVE_TREASURY

methods {    

    getRevision() returns (uint256)
    initialize(uint8, string, string) envfree
    initializing() returns(bool) envfree
    balanceOf(address) returns (uint256) envfree
    scaledBalanceOf(address) returns (uint256) envfree
    internalBalanceOf(address) returns (uint256) envfree
    getScaledUserBalanceAndSupply(address) returns (uint256, uint256) envfree
    totalSupply() returns (uint256) envfree
    scaledTotalSupply() returns (uint256) envfree
    internalTotalSupply() returns (uint256) envfree
    getNonceOf(address) returns (uint256) envfree
    allowance(address, address) returns(uint256) envfree
    burn(address, address,uint256, uint256)
    mint(address, uint256, uint256)
    mintToTreasury(uint256, uint256)
    transferOnLiquidation(address, address, uint256) 
    transferUnderlyingTo(address, uint256) returns (uint256) 
    permit(address, address, uint256, uint256, uint8, bytes32, bytes32) 

    isContractIsTrue(address) returns (bool) envfree

    UNDERLYING_ASSET.balanceOf(address) returns (uint256) envfree
    UNDERLYING_ASSET.totalSupply() returns (uint256) envfree

    LENDING_POOL.aToken() returns (address) envfree

}

// aToken is reserve token

ghost sum_of_all_balances() returns uint256{
    // for the constructor - assuming that on the constructor the value of the ghost is 0
    init_state axiom sum_of_all_balances() == 0;
}

hook Sstore _balances[KEY address user] uint balance (uint oldBalance) STORAGE {
	havoc sum_of_all_balances assuming sum_of_all_balances@new() == sum_of_all_balances@old() + balance - oldBalance;
}

invariant totalSupply_equals_sumOfAllBalances() 
 	totalSupply() == sum_of_all_balances()



rule burnReducesTotalSupplyOfATokens(
    address user, 
    address receiverOfUnderlying, 
    uint256 amount,
    uint256 index,
    uint256 stEthRebasingIndex,
    uint256 aaveLiquidityIndex
    ) {
        env e;
        mathint amountScaled = returnAmount(amount, stEthRebasingIndex, aaveLiquidityIndex);
        mathint totalSupplyBefore = totalSupply();
        burn(e, user, receiverOfUnderlying, amount, index);
        mathint totalSupplyAfter = totalSupply();
        assert amount > 0 => totalSupplyBefore > totalSupplyAfter;
        assert amount == 0 => totalSupplyBefore == totalSupplyAfter;
        assert totalSupplyAfter == totalSupplyBefore - amountScaled;
    }



rule burnReducesBalanceOfATokensOfUser(
    address user, 
    address receiverOfUnderlying, 
    uint256 amount,
    uint256 index,
    uint256 stEthRebasingIndex,
    uint256 aaveLiquidityIndex
    ) {
        env e;
        mathint amountScaled = returnAmount(amount, stEthRebasingIndex, aaveLiquidityIndex);
        mathint balanceBefore = balanceOf(user);
        burn(e, user, receiverOfUnderlying, amount, index);
        mathint balanceAfter = balanceOf(user);
        assert amount > 0 => balanceBefore > balanceAfter;
        assert amount == 0 => balanceBefore == balanceAfter;
        assert balanceAfter == balanceBefore - amountScaled;
    }


rule burnCanOnlyBeCalledByLendingPool(
    address user, 
    address receiverOfUnderlying, 
    uint256 amount,
    uint256 index
) {
        env e;
        require e.msg.sender != LENDING_POOL;
        burn@withrevert(e, user, receiverOfUnderlying, amount, index);
        assert lastReverted;
}


rule burnIncreasesTheBalanceOfUnderlyingTokenOfUnderlyingAddress(
    address user, 
    address receiverOfUnderlying, 
    uint256 amount,
    uint256 index
) {
        env e;
        mathint underlyingTokenBalanceBefore = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying);
        burn(e, user, receiverOfUnderlying, amount, index);
        mathint underlyingTokenBalanceAfter = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying);
        assert amount > 0 && receiverOfUnderlying!=currentContract => underlyingTokenBalanceBefore < underlyingTokenBalanceAfter;
        assert amount == 0 => underlyingTokenBalanceBefore == underlyingTokenBalanceAfter;
        assert receiverOfUnderlying!=currentContract  => underlyingTokenBalanceAfter == underlyingTokenBalanceBefore + amount;
}

rule burnHoldsAdditivePropertyForDifferentAmountForATokens(
    address user,
    address receiverOfUnderlying,
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    burn(e, user, receiverOfUnderlying, amount1, index);
    burn(e, user, receiverOfUnderlying, amount2, index);
    mathint balanceAfterSeparateBurn = balanceOf(user);
    mathint totalSupplyAfterSeparateBurn = totalSupply();
    burn(e, user, receiverOfUnderlying, amount1 + amount2, index) at initialState;
    mathint balanceAfterCombinedBurn = balanceOf(user);
    mathint totalSupplyAfterCombinedBurn = totalSupply();
    assert balanceAfterSeparateBurn == balanceAfterCombinedBurn;
    assert totalSupplyAfterCombinedBurn == totalSupplyAfterSeparateBurn;

}

rule burnHoldsAdditivePropertyForDifferentAmountForUnderlyingTokens(
    address user,
    address receiverOfUnderlying,
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    burn(e, user, receiverOfUnderlying, amount1, index);
    burn(e, user, receiverOfUnderlying, amount2, index);
    mathint balanceOfUnderlyingTokenAfterSeparateBurn = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying);
    burn(e, user, receiverOfUnderlying, amount1 + amount2, index) at initialState;
    mathint balanceOfUnderlyingTokenAfterCombinedBurn = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying);
   assert balanceOfUnderlyingTokenAfterSeparateBurn == balanceOfUnderlyingTokenAfterCombinedBurn;
}

rule burnSatisfiesCommuntativeProperty(
    address user1,
    address receiverOfUnderlying1,
    address user2,
    address user3,
    address receiverOfUnderlying2,
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    burn(e, user1, receiverOfUnderlying1, amount1, index);
    burn(e, user2, receiverOfUnderlying2, amount2, index);
    mathint totalSupplyBefore = totalSupply();
    mathint aTokenbalanceOfRandomUserBefore = balanceOf(user3);
    mathint underlyingTokenBalanceOfRandomUserBefore = UNDERLYING_ASSET.balanceOf(user3);
    burn(e, user2, receiverOfUnderlying2, amount2, index) at initialState;
    burn(e, user1, receiverOfUnderlying1, amount1, index);
    mathint totalSupplyAfter = totalSupply();
    mathint aTokenbalanceOfRandomUserAfter = balanceOf(user3);
    mathint underlyingTokenBalanceOfRandomUserAfter = UNDERLYING_ASSET.balanceOf(user3);
    assert totalSupplyBefore == totalSupplyAfter;
    assert aTokenbalanceOfRandomUserBefore == aTokenbalanceOfRandomUserAfter;
    assert underlyingTokenBalanceOfRandomUserBefore == underlyingTokenBalanceOfRandomUserAfter;
}

rule orderOfBurnDoesNotMatter(
    address user1,
    address receiverOfUnderlying1,
    address user2,
    address receiverOfUnderlying2,
    address user3,
    address receiverOfUnderlying3,
    address user4,
    uint256 amount1,
    uint256 amount2,
    uint256 amount3,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    burn(e, user1, receiverOfUnderlying1, amount1, index);
    burn(e, user2, receiverOfUnderlying2, amount2, index);
    burn(e, user3, receiverOfUnderlying3, amount3, index);
    mathint totalSupplyBefore = totalSupply();
    mathint aTokenbalanceOfRandomUserBefore = balanceOf(user4);
    mathint underlyingTokenBalanceOfRandomUserBefore = UNDERLYING_ASSET.balanceOf(user4);
    burn(e, user2, receiverOfUnderlying2, amount2, index) at initialState;
    burn(e, user3, receiverOfUnderlying3, amount3, index);
    burn(e, user1, receiverOfUnderlying1, amount1, index);
    mathint totalSupplyAfter = totalSupply();
    mathint aTokenbalanceOfRandomUserAfter = balanceOf(user4);
    mathint underlyingTokenBalanceOfRandomUserAfter = UNDERLYING_ASSET.balanceOf(user4);
    assert totalSupplyBefore == totalSupplyAfter;
    assert aTokenbalanceOfRandomUserBefore == aTokenbalanceOfRandomUserAfter;
    assert underlyingTokenBalanceOfRandomUserBefore == underlyingTokenBalanceOfRandomUserAfter;
}

rule burnFromOneUserDoesNotAffectOtherUsers(
    address user1,
    address receiverOfUnderlying1,
    address user2,
    address receiverOfUnderlying2,
    uint256 amount,
    uint256 index
) {
    env e;
    mathint balanceOfATokensOfNonInteractingUserBefore = balanceOf(user1);
    mathint balanceOfUnderlyingTokenOfNonInteractingUserBefore = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying1);
    burn(e, user2, receiverOfUnderlying2, amount, index);
    mathint balanceOfATokensOfNonInteractingUserAfter = balanceOf(user1);
    mathint balanceOfUnderlyingTokenOfNonInteractingUserAfter = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying1);
    assert user1 != user2 => balanceOfATokensOfNonInteractingUserBefore == balanceOfATokensOfNonInteractingUserAfter;
    assert receiverOfUnderlying1 != receiverOfUnderlying2 && receiverOfUnderlying1 != currentContract => balanceOfUnderlyingTokenOfNonInteractingUserBefore == balanceOfUnderlyingTokenOfNonInteractingUserAfter;
}



rule mintCanOnlyBeCalledByLendingPool(
    address user,
    uint256 amount,
    uint256 index
) {
        env e;
        require e.msg.sender != LENDING_POOL;
        mint@withrevert(e, user, amount, index);
        assert lastReverted;
}

rule mintIncreasesBalanceOfATokesOfUser(
    address user,
    uint256 amount,
    uint256 index,
    uint256 stEthRebasingIndex,
    uint256 aaveLiquidityIndex
) {
    env e;
    mathint aTokenBalanceBefore = balanceOf(user);
    mint(e, user, amount, index);
    mathint scaledAmount = returnAmount(amount, stEthRebasingIndex, aaveLiquidityIndex);
    mathint aTokenBalanceAfter = balanceOf(user);
    assert aTokenBalanceAfter > aTokenBalanceBefore;
    assert aTokenBalanceAfter == aTokenBalanceBefore + scaledAmount;
}

rule mintIncreasesTotalSupplyOfATokens(
    address user,
    uint256 amount,
    uint256 index
) {
    env e;
    mathint totalSupplyBefore = totalSupply();
    mint(e, user, amount, index);
    mathint totalSupplyAfter = totalSupply();
    assert totalSupplyAfter > totalSupplyBefore;
}

rule mintPreservesTheTotalSupplyOfUnderlyingAsset(
    address user,
    uint256 amount,
    uint256 index
) {
    env e;
    mathint totalSupplyOfUnderlyingAssetBefore = UNDERLYING_ASSET.totalSupply();
    mint(e, user, amount, index);
    mathint totalSupplyOfUnderlyingAssetAfter = UNDERLYING_ASSET.totalSupply();
    assert totalSupplyOfUnderlyingAssetAfter == totalSupplyOfUnderlyingAssetBefore;
}

rule mintPreservesTheBalanceOfUnderlyingAssetOfEachUser(
    address user,
    uint256 amount,
    uint256 index
) {
    env e;
    mathint balanceOfUnderlyingAssetBefore = UNDERLYING_ASSET.balanceOf(user);
    mint(e, user, amount, index);
    mathint balanceOfUnderlyingAssetAfter = UNDERLYING_ASSET.balanceOf(user);
    assert balanceOfUnderlyingAssetBefore == balanceOfUnderlyingAssetAfter;
}

rule mintHoldsAdditivePropertyForSeparateAmountForATokens(
    address user,
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    mint(e, user, amount1, index);
    mint(e, user, amount2, index);
    mathint balanceAfterSeparateMint = balanceOf(user);
    mathint totalSupplyAfterSeparateMint = totalSupply();
    mint(e, user, amount1 + amount2, index) at initialState;
    mathint balanceAfterCombinedMint = balanceOf(user);
    mathint totalSupplyAfterCombinedMint = totalSupply();
    assert balanceAfterSeparateMint == balanceAfterCombinedMint;
    assert totalSupplyAfterSeparateMint == totalSupplyAfterCombinedMint;

}

rule mintHoldsAdditivePropertyForDifferentAmountForUnderlyingTokens(
    address user,
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    mint(e, user, amount1, index);
    mint(e, user, amount2, index);
    mathint balanceOfUnderlyingTokenAfterSeparateMint = UNDERLYING_ASSET.balanceOf(user);
    mint(e, user, amount1 + amount2, index) at initialState;
    mathint balanceOfUnderlyingTokenAfterCombinedMint = UNDERLYING_ASSET.balanceOf(user);
   assert balanceOfUnderlyingTokenAfterSeparateMint == balanceOfUnderlyingTokenAfterCombinedMint;
}

rule mintFromOneUserDoesNotAffectOtherUsers(
    address user1,
    address user2,
    uint256 amount,
    uint256 index
) {
    env e;
    mathint balanceOfATokensOfNonInteractingUserBefore = balanceOf(user1);
    mathint balanceOfUnderlyingTokenOfNonInteractingUserBefore = UNDERLYING_ASSET.balanceOf(user1);
    mint(e, user2, amount, index);
    mathint balanceOfATokensOfNonInteractingUserAfter = balanceOf(user1);
    mathint balanceOfUnderlyingTokenOfNonInteractingUserAfter = UNDERLYING_ASSET.balanceOf(user1);
    assert user1 != user2 => balanceOfATokensOfNonInteractingUserBefore == balanceOfATokensOfNonInteractingUserAfter;
    assert user1 != user2 => balanceOfUnderlyingTokenOfNonInteractingUserBefore == balanceOfUnderlyingTokenOfNonInteractingUserAfter;

}

rule mintSatisfiesCommutativeProperty(
    address user1,
    address user2,
    address user3,
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    mint(e, user1, amount1, index);
    mint(e, user2, amount2, index);
    mathint totalSupplyBefore = totalSupply();
    mathint aTokenbalanceOfRandomUserBefore = balanceOf(user3);
    mathint underlyingTokenBalanceOfRandomUserBefore = UNDERLYING_ASSET.balanceOf(user3);
    mint(e, user2, amount2, index) at initialState;
    mint(e, user1, amount1, index);
    mathint totalSupplyAfter = totalSupply();
    mathint aTokenbalanceOfRandomUserAfter = balanceOf(user3);
    mathint underlyingTokenBalanceOfRandomUserAfter = UNDERLYING_ASSET.balanceOf(user3);
    assert totalSupplyBefore == totalSupplyAfter;
    assert aTokenbalanceOfRandomUserBefore == aTokenbalanceOfRandomUserAfter;
    assert underlyingTokenBalanceOfRandomUserBefore == underlyingTokenBalanceOfRandomUserAfter;
}

rule orderOfMintDoesNotMatter(
    address user1,
    address user2,
    address user3,
    address user4,
    uint256 amount1,
    uint256 amount2,
    uint256 amount3,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    mint(e, user1, amount1, index);
    mint(e, user2, amount2, index);
    mint(e, user3, amount3, index);
    mathint totalSupplyBefore = totalSupply();
    mathint aTokenbalanceOfRandomUserBefore = balanceOf(user4);
    mathint underlyingTokenBalanceOfRandomUserBefore = UNDERLYING_ASSET.balanceOf(user4);
    mint(e, user2, amount2, index) at initialState;
    mint(e, user1, amount1, index);
    mint(e, user3, amount3, index);
    mathint totalSupplyAfter = totalSupply();
    mathint aTokenbalanceOfRandomUserAfter = balanceOf(user4);
    mathint underlyingTokenBalanceOfRandomUserAfter = UNDERLYING_ASSET.balanceOf(user4);
    assert totalSupplyBefore == totalSupplyAfter;
    assert aTokenbalanceOfRandomUserBefore == aTokenbalanceOfRandomUserAfter;
    assert underlyingTokenBalanceOfRandomUserBefore == underlyingTokenBalanceOfRandomUserAfter;
}


rule integrityOfBalanceOfATokenOfUsers(
    method f,
    address userA,
    address userB
) {
    env e;
    mathint balanceOfUserABefore = balanceOf(userA);
    mathint balanceOfUserBBefore = balanceOf(userB);

    calldataarg args;
    f(e, args);

    mathint balanceOfUserAAfter = balanceOf(userA);
    mathint balanceOfUserBAfter = balanceOf(userB);

    assert userA != userB => 
    (balanceOfUserABefore == balanceOfUserAAfter) 
    || (balanceOfUserBBefore == balanceOfUserBAfter) 
    || (balanceOfUserABefore != balanceOfUserAAfter && balanceOfUserBBefore != balanceOfUserBAfter && balanceOfUserABefore + balanceOfUserBBefore == balanceOfUserAAfter + balanceOfUserBAfter);

}

rule balanceOfATokenOfUserChangesInProportionToTotalSupply(
    address user,
    method f
) {
    env e;

     require f.selector == burn(address, address, uint256, uint256).selector 
            || f.selector == mint(address, uint256, uint256).selector;

    mathint balanceBefore = balanceOf(user);
    mathint totalSupplyBefore = totalSupply();
    
    calldataarg args;
    f(e, args);  

    mathint balanceAfter = balanceOf(user);
    mathint totalSupplyAfter = totalSupply();

    //to check that mint and burn is done to balance of user 
    assert balanceBefore != balanceAfter => balanceAfter - balanceBefore == totalSupplyAfter - totalSupplyBefore;
}

rule canOnlyBeInitializedOnce(
    uint8 underlyingAssetDecimals,
    string tokenName,
    string tokenSymbol
) {
    require initializing() == false;
    initialize(underlyingAssetDecimals, tokenName, tokenSymbol);
    storage state = lastStorage;
    initialize@withrevert(underlyingAssetDecimals, tokenName, tokenSymbol) at state;

    assert lastReverted;
}

rule mintToTreasuryCanOnlyBeCalledByLendingPool(
    uint256 amount,
    uint256 index
) {
        env e;
        require e.msg.sender != LENDING_POOL;
        mintToTreasury@withrevert(e, amount, index);
        assert lastReverted;
}

rule mintToTreasuryIsSubsetOfMint(
    uint256 amount,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    address user = RESERVE_TREASURY;
    mintToTreasury(e, amount, index);
    mathint balanceBefore = balanceOf(user);
    mathint totalSupplyBefore = totalSupply();

    mint(e, user, amount, index) at initialState;
    mathint balanceAfter = balanceOf(user);
    mathint totalSupplyAfter = totalSupply();

    assert balanceBefore == balanceAfter;
    assert totalSupplyBefore == totalSupplyAfter;
}

rule mintToTreasuryIncreasesBalanceOfATokesOfReserveTreasuryAddress(
    uint256 amount,
    uint256 index,
    uint256 stEthRebasingIndex,
    uint256 aaveLiquidityIndex
) {
    env e;
    require amount != 0;
    mathint aTokenBalanceOfReserveBefore = balanceOf(RESERVE_TREASURY);
    mintToTreasury(e, amount, index);
    mathint scaledAmount = returnAmount(amount, stEthRebasingIndex, aaveLiquidityIndex);
    mathint aTokenBalanceOfReserveAfter = balanceOf(RESERVE_TREASURY);
    assert aTokenBalanceOfReserveAfter > aTokenBalanceOfReserveBefore;
    assert aTokenBalanceOfReserveAfter == aTokenBalanceOfReserveBefore + scaledAmount;
}

rule mintToTreasuryIncreasesTotalSupplyOfATokens(
    uint256 amount,
    uint256 index
) {
    env e;
    require amount != 0;
    mathint totalSupplyBefore = totalSupply();
    mintToTreasury(e, amount, index);
    mathint totalSupplyAfter = totalSupply();
    assert totalSupplyAfter > totalSupplyBefore;
}

rule mintToTreasuryPreservesTheTotalSupplyOfUnderlyingAsset(
    uint256 amount,
    uint256 index
) {
    env e;
    mathint totalSupplyOfUnderlyingAssetBefore = UNDERLYING_ASSET.totalSupply();
    mintToTreasury(e, amount, index);
    mathint totalSupplyOfUnderlyingAssetAfter = UNDERLYING_ASSET.totalSupply();
    assert totalSupplyOfUnderlyingAssetAfter == totalSupplyOfUnderlyingAssetBefore;
}

rule mintToTreasuryPreservesTheBalanceOfUnderlyingAssetOfEachUser(
    address user,
    uint256 amount,
    uint256 index
) {
    env e;
    mathint balanceOfUnderlyingAssetBefore = UNDERLYING_ASSET.balanceOf(user);
    mintToTreasury(e, amount, index);
    mathint balanceOfUnderlyingAssetAfter = UNDERLYING_ASSET.balanceOf(user);
    assert balanceOfUnderlyingAssetBefore == balanceOfUnderlyingAssetAfter;
}

rule mintToTreasuryHoldsAdditivePropertyForSeparateAmountForATokens(
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    mintToTreasury(e, amount1, index);
    mintToTreasury(e, amount2, index);
    mathint balanceAfterSeparateMint = balanceOf(RESERVE_TREASURY);
    mathint totalSupplyAfterSeparateMint = totalSupply();
    mintToTreasury(e, amount1 + amount2, index) at initialState;
    mathint balanceAfterCombinedMint = balanceOf(RESERVE_TREASURY);
    mathint totalSupplyAfterCombinedMint = totalSupply();
    assert balanceAfterSeparateMint == balanceAfterCombinedMint;
    assert totalSupplyAfterSeparateMint == totalSupplyAfterCombinedMint;
}

rule mintToTreasuryHoldsAdditivePropertyForDifferentAmountForUnderlyingTokens(
    address user,
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    mintToTreasury(e, amount1, index);
    mintToTreasury(e, amount2, index);
    mathint balanceOfUnderlyingTokenAfterSeparateMint = UNDERLYING_ASSET.balanceOf(user);
    mintToTreasury(e, amount1 + amount2, index) at initialState;
    mathint balanceOfUnderlyingTokenAfterCombinedMint = UNDERLYING_ASSET.balanceOf(user);
   assert balanceOfUnderlyingTokenAfterSeparateMint == balanceOfUnderlyingTokenAfterCombinedMint;
}

rule mintToTreasuryDoesNotAffectOtherUsers(
    address user1,
    uint256 amount,
    uint256 index
) {
    env e;
    mathint balanceOfATokensOfNonInteractingUserBefore = balanceOf(user1);
    mathint balanceOfUnderlyingTokenOfNonInteractingUserBefore = UNDERLYING_ASSET.balanceOf(user1);
    mintToTreasury(e, amount, index);
    mathint balanceOfATokensOfNonInteractingUserAfter = balanceOf(user1);
    mathint balanceOfUnderlyingTokenOfNonInteractingUserAfter = UNDERLYING_ASSET.balanceOf(user1);
    assert user1 != RESERVE_TREASURY => balanceOfATokensOfNonInteractingUserBefore == balanceOfATokensOfNonInteractingUserAfter;
    assert user1 != RESERVE_TREASURY => balanceOfUnderlyingTokenOfNonInteractingUserBefore == balanceOfUnderlyingTokenOfNonInteractingUserAfter;

}

rule mintToTreasurySatisfiesCommutativeProperty(
    address user1,
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    mintToTreasury(e, amount1, index);
    mintToTreasury(e, amount2, index);
    mathint totalSupplyBefore = totalSupply();
    mathint aTokenbalanceOfRandomUserBefore = balanceOf(user1);
    mathint underlyingTokenBalanceOfRandomUserBefore = UNDERLYING_ASSET.balanceOf(user1);
    mintToTreasury(e, amount2, index) at initialState;
    mintToTreasury(e, amount1, index);
    mathint totalSupplyAfter = totalSupply();
    mathint aTokenbalanceOfRandomUserAfter = balanceOf(user1);
    mathint underlyingTokenBalanceOfRandomUserAfter = UNDERLYING_ASSET.balanceOf(user1);
    assert totalSupplyBefore == totalSupplyAfter;
    assert aTokenbalanceOfRandomUserBefore == aTokenbalanceOfRandomUserAfter;
    assert underlyingTokenBalanceOfRandomUserBefore == underlyingTokenBalanceOfRandomUserAfter;
}

rule orderOfMintToTreasuryDoesNotMatter(
    address user1,
    uint256 amount1,
    uint256 amount2,
    uint256 amount3,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    mintToTreasury(e, amount1, index);
    mintToTreasury(e, amount2, index);
    mintToTreasury(e, amount3, index);
    mathint totalSupplyBefore = totalSupply();
    mathint aTokenbalanceOfRandomUserBefore = balanceOf(user1);
    mathint underlyingTokenBalanceOfRandomUserBefore = UNDERLYING_ASSET.balanceOf(user1);
    mintToTreasury(e, amount2, index) at initialState;
    mintToTreasury(e, amount1, index);
    mintToTreasury(e, amount3, index);
    mathint totalSupplyAfter = totalSupply();
    mathint aTokenbalanceOfRandomUserAfter = balanceOf(user1);
    mathint underlyingTokenBalanceOfRandomUserAfter = UNDERLYING_ASSET.balanceOf(user1);
    assert totalSupplyBefore == totalSupplyAfter;
    assert aTokenbalanceOfRandomUserBefore == aTokenbalanceOfRandomUserAfter;
    assert underlyingTokenBalanceOfRandomUserBefore == underlyingTokenBalanceOfRandomUserAfter;
}

rule burnAndMintAreInverseOfEachOther(
    address user,
    address receiverOfUnderlying,
    uint256 amount,
    uint256 index
) {
    env e;
    mathint totalSupplyBefore = totalSupply();
    mathint userBalanceBefore = balanceOf(user);
    burn(e, user, receiverOfUnderlying, amount, index);
    mint(e, user, amount, index);
    mathint totalSupplyAfter = totalSupply();
    mathint userBalanceAfter = balanceOf(user);
    assert totalSupplyBefore == totalSupplyAfter;
    assert userBalanceBefore == userBalanceAfter;
}

rule transferOnLiquidationCanOnlyBeCalledByLendingPool(
    address from, 
    address to, 
    uint256 amount
) {
        env e;
        require e.msg.sender != LENDING_POOL;
        transferOnLiquidation@withrevert(e, from, to, amount);
        assert lastReverted;
}

rule transferOnLiquidationPreservesTotalSupplyOfATokens(
    address from,
    address to,
    uint256 amount
) {
    env e;
    mathint totalSupplyBefore = totalSupply();
    transferOnLiquidation(e, from, to, amount);
    mathint totalSupplyAfter = totalSupply();
    assert totalSupplyBefore == totalSupplyAfter;
}

rule transferOnLiquidationReducesBalanceOfSenderAndIncreasesBalanceOfReceiverForATokens(
    address from,
    address to,
    uint256 amount
) {
    env e;
    require from != to;
    mathint balanceOfUserABefore = balanceOf(from);
    mathint balanceOfUserBBefore = balanceOf(to);
    transferOnLiquidation(e, from, to, amount);
    mathint balanceOfUserAAfter = balanceOf(from);
    mathint balanceOfUserBAfter = balanceOf(to);
    assert amount == 0 => (balanceOfUserABefore == balanceOfUserAAfter) && (balanceOfUserBBefore == balanceOfUserBAfter); 
    assert amount > 0 => balanceOfUserABefore > balanceOfUserAAfter && balanceOfUserBBefore < balanceOfUserBAfter;
    assert amount > 0 => balanceOfUserABefore == balanceOfUserAAfter + amount;
    assert amount > 0 => balanceOfUserBBefore + amount == balanceOfUserBAfter;
}

rule transferOnLiquidationDoesNotTakeFee(
    address from,
    address to,
    uint256 amount
) {
    env e;
    require from != to;
    mathint balanceOfUserABefore = balanceOf(from);
    mathint balanceOfUserBBefore = balanceOf(to);
    transferOnLiquidation(e, from, to, amount);
    mathint balanceOfUserAAfter = balanceOf(from);
    mathint balanceOfUserBAfter = balanceOf(to);
    assert balanceOfUserABefore + balanceOfUserBBefore == balanceOfUserAAfter + balanceOfUserBAfter;
}

rule transferOnLiquidationPreservesTotalSupplyOfUnderlyingToken(
    address from,
    address to,
    uint256 amount
) {
    env e;
    require from != to;
    mathint totalSupplyBefore = UNDERLYING_ASSET.totalSupply();
    transferOnLiquidation(e, from, to, amount);
    mathint totalSupplyAfter = UNDERLYING_ASSET.totalSupply();
    assert totalSupplyBefore == totalSupplyAfter;
}

rule transferOnLiquidationDoesNotAffectOtherUsers(
    address from,
    address to,
    address otherUser,
    uint256 amount
) {
    env e;
    require from != to && from != otherUser && to != otherUser;
    mathint balanceOfOtherUserBefore = balanceOf(otherUser);
    transferOnLiquidation(e, from, to, amount);
    mathint balanceOfOtherUserAfter = balanceOf(otherUser);
    assert balanceOfOtherUserBefore == balanceOfOtherUserAfter;
}

rule transferOnLiquidationIsCommutative(
    address userA,
    address userB,
    address userC,
    address userD,
    uint256 amount1,
    uint256 amount2
) {
    env e;
    storage initialState = lastStorage;
    require userA != userB;
    require userC != userD;
    transferOnLiquidation(e, userA, userB, amount1);
    transferOnLiquidation(e, userC, userD, amount2);
    mathint balanceOfUserAInitial = balanceOf(userA);
    mathint balanceOfUserBInitial = balanceOf(userB);
    mathint balanceOfUserCInitial = balanceOf(userC);
    mathint balanceOfUserDInitial = balanceOf(userD);

    transferOnLiquidation(e, userC, userD, amount2) at initialState;
    transferOnLiquidation(e, userA, userB, amount1);
    mathint balanceOfUserAFinal = balanceOf(userA);
    mathint balanceOfUserBFinal = balanceOf(userB);
    mathint balanceOfUserCFinal = balanceOf(userC);
    mathint balanceOfUserDFinal = balanceOf(userD);

    assert balanceOfUserAInitial == balanceOfUserAFinal 
            && balanceOfUserBInitial == balanceOfUserBFinal 
            && balanceOfUserCInitial == balanceOfUserCFinal 
            && balanceOfUserDInitial == balanceOfUserDFinal;
}

rule transferOnLiquidationIsAdditive(
    address userA,
    address userB,
    uint256 amount1,
    uint256 amount2
) {
    env e;
    storage initialState = lastStorage;
    require userA != userB;
    transferOnLiquidation(e, userA, userB, amount1);
    transferOnLiquidation(e, userA, userB, amount2);
    mathint balanceOfUserAInitial = balanceOf(userA);
    mathint balanceOfUserBInitial = balanceOf(userB);

    transferOnLiquidation(e, userA, userB, amount1 + amount2) at initialState;
    mathint balanceOfUserAFinal = balanceOf(userA);
    mathint balanceOfUserBFinal = balanceOf(userB);

    assert balanceOfUserAInitial == balanceOfUserAFinal 
            && balanceOfUserBInitial == balanceOfUserBFinal;
}

rule permitIncreasesNonceOfOwner(
    address owner,
    address spender,
    uint256 value,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s
) {
    env e;
    uint256 nonceBefore = getNonceOf(owner);
    permit(e, owner, spender, value, deadline, v, r, s);
    uint256 nonceAfter = getNonceOf(owner);
    assert nonceAfter == nonceBefore + 1;
}

rule permitDoesNotChangeNonceOfOtherUser(
    address owner,
    address spender,
    uint256 value,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s,
    address randomUser
) {
    env e;
    require randomUser != owner;
    uint256 nonceBefore = getNonceOf(randomUser);
    permit(e, owner, spender, value, deadline, v, r, s);
    uint256 nonceAfter = getNonceOf(randomUser);
    assert nonceAfter == nonceBefore;
}

rule permitDoesNotChangeAllowanceOfOtherUser(
    address owner,
    address spender,
    uint256 value,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s,
    address randomUser
) {
    env e;
    require randomUser != spender;
    uint256 allowanceBefore = allowance(owner, randomUser);
    permit(e, owner, spender, value, deadline, v, r, s);
    uint256 allowanceAfter = allowance(owner, randomUser);
    assert allowanceBefore == allowanceAfter;
}

rule transferUnderlyingToCanOnlyBeCalledByLendingPool(
    address target, 
    uint256 amount
) {
        env e;
        require e.msg.sender != LENDING_POOL;
        transferUnderlyingTo@withrevert(e, target, amount);
        assert lastReverted;
}

rule transferUnderlyingToTransferUnderlyingAssetToTarget(
    address target,
    uint256 amount
) {
    env e;
    mathint underlyingTokenBalanceBefore = UNDERLYING_ASSET.balanceOf(target);
    transferUnderlyingTo(e, target, amount);
    mathint underlyingTokenBalanceAfter = UNDERLYING_ASSET.balanceOf(target);
    assert target != currentContract => underlyingTokenBalanceAfter == underlyingTokenBalanceBefore + amount;
    assert target == currentContract => underlyingTokenBalanceAfter == underlyingTokenBalanceBefore;
}

rule transferUnderlyingToDoesNotAffectTotalSupplyAndBalanceOfATokens(
    address target,
    uint256 amount,
    address randomUser
) {
    env e;
    mathint aTokensBefore = totalSupply();
    mathint aTokenbalanceOfRandomUserBefore = balanceOf(randomUser);
    transferUnderlyingTo(e, target, amount);
    mathint aTokensAfter = totalSupply();
    mathint aTokenbalanceOfRandomUserAfter = balanceOf(randomUser);
    assert aTokensBefore == aTokensAfter;
    assert aTokenbalanceOfRandomUserBefore == aTokenbalanceOfRandomUserAfter;
}

rule transferUnderlyingToIsCommutative(
    address userA,
    uint256 amountA, 
    address userB,
    uint256 amountB
) {
    env e;
    storage initialState = lastStorage;
    transferUnderlyingTo(e, userA, amountA);
    transferUnderlyingTo(e, userB, amountB);
    mathint initialBalanceOfUserA = UNDERLYING_ASSET.balanceOf(userA);
    mathint initialBalanceOfUserB = UNDERLYING_ASSET.balanceOf(userB);
    mathint totalSupplyBefore = UNDERLYING_ASSET.totalSupply();
    transferUnderlyingTo(e, userB, amountB) at initialState;
    transferUnderlyingTo(e, userA, amountA);
    mathint finalBalanceOfUserA = UNDERLYING_ASSET.balanceOf(userA);
    mathint finalBalanceOfUserB = UNDERLYING_ASSET.balanceOf(userB);
    mathint totalSupplyAfter = UNDERLYING_ASSET.totalSupply();
    assert initialBalanceOfUserA == finalBalanceOfUserA;
    assert initialBalanceOfUserB == finalBalanceOfUserB;
    assert totalSupplyBefore == totalSupplyAfter;

}

rule transferUnderlyingToDoesNotAffectOtherUser(
    address userA,
    uint256 amountA, 
    address randomUser
) {
    env e;
    require userA != randomUser && randomUser != currentContract;
    mathint underlyingBalanceOfRandomUserBefore = UNDERLYING_ASSET.balanceOf(randomUser);
    mathint aTokenbalanceOfRandomUserBefore = balanceOf(randomUser);
    transferUnderlyingTo(e, userA, amountA);
    mathint underlyingBalanceOfRandomUserAfter = UNDERLYING_ASSET.balanceOf(randomUser);
    mathint aTokenbalanceOfRandomUserAfter = balanceOf(randomUser);
    assert underlyingBalanceOfRandomUserBefore == underlyingBalanceOfRandomUserAfter;
    assert aTokenbalanceOfRandomUserBefore == aTokenbalanceOfRandomUserAfter;
}

rule transferUnderlyingToIsAdditive(
    address userA,
    uint256 amountA,
    uint256 amountB
) {
    env e;
    storage initialState = lastStorage;
    transferUnderlyingTo(e, userA, amountA);
    transferUnderlyingTo(e, userA, amountB);
    mathint initialUnderlyingBalanceOfUserA = UNDERLYING_ASSET.balanceOf(userA);
    mathint initialATokenBalanceOfUserA = balanceOf(userA);
    transferUnderlyingTo(e, userA, amountA + amountB) at initialState;
    mathint finalUnderlyingBalanceOfUserA = UNDERLYING_ASSET.balanceOf(userA);
    mathint finalATokenBalanceOfUserA = balanceOf(userA);
    assert initialUnderlyingBalanceOfUserA == finalUnderlyingBalanceOfUserA;
    assert initialATokenBalanceOfUserA == finalATokenBalanceOfUserA;
}

rule methodDoesNotChangeStateOfContract(
    method f,
    address user
) filtered {
    f -> f.selector == balanceOf(address).selector 
        || f.selector == scaledBalanceOf(address).selector
        || f.selector == internalBalanceOf(address).selector
        || f.selector == getScaledUserBalanceAndSupply(address).selector
        || f.selector == totalSupply().selector
        || f.selector == scaledTotalSupply().selector
        || f.selector == internalTotalSupply().selector
} {
    calldataarg args;
    env e;
    storage initialState = lastStorage;
    mathint initialTotalSupplyOfATokens = totalSupply();
    mathint initialTotalSupplyOfUnderlyingTokens = UNDERLYING_ASSET.totalSupply();
    mathint initialBalanceOfATokenOfUser = balanceOf(user);
    mathint initialBalanceOfUnderlyingTokenOfUser = UNDERLYING_ASSET.balanceOf(user);
    mathint initialNonce = getNonceOf(user);

    f(e, args);

    mathint finalTotalSupplyOfATokens = totalSupply();
    mathint finalTotalSupplyOfUnderlyingTokens = UNDERLYING_ASSET.totalSupply();
    mathint finalBalanceOfATokenOfUser = balanceOf(user);
    mathint finalBalanceOfUnderlyingTokenOfUser = UNDERLYING_ASSET.balanceOf(user);
    mathint finalNonce = getNonceOf(user);

    assert initialTotalSupplyOfATokens == finalTotalSupplyOfATokens;
    assert initialTotalSupplyOfUnderlyingTokens == finalTotalSupplyOfUnderlyingTokens;
    assert initialBalanceOfATokenOfUser == finalBalanceOfATokenOfUser;
    assert initialBalanceOfUnderlyingTokenOfUser == finalBalanceOfUnderlyingTokenOfUser;
    assert initialNonce == finalNonce;
}

rule balancesAndTotalSupplyAreProportional(address randomUser) {
    mathint aTokenInternalTotalSupplyBefore = internalTotalSupply();
    mathint aTokenScaledTokenSupplyBefore = scaledTotalSupply();
    mathint aTokenTotalSupplyBefore = totalSupply();

    mathint aTokenInternalBalanceBefore = internalBalanceOf(randomUser);
    mathint aTokenScaledBalanceBefore = scaledBalanceOf(randomUser);
    mathint aTokenBalanceOfUserBefore = balanceOf(randomUser);
    
    assert aTokenInternalBalanceBefore * aTokenScaledTokenSupplyBefore == aTokenScaledBalanceBefore * aTokenInternalTotalSupplyBefore;
    assert aTokenScaledBalanceBefore * aTokenTotalSupplyBefore == aTokenBalanceOfUserBefore * aTokenScaledTokenSupplyBefore;
    assert aTokenInternalBalanceBefore * aTokenTotalSupplyBefore == aTokenBalanceOfUserBefore * aTokenInternalTotalSupplyBefore;
    
    env e; 
    calldataarg args; 
    method f;
    
    f(e, args);

    mathint aTokenInternalBalanceAfter = internalBalanceOf(randomUser);
    mathint aTokenScaledBalanceAfter = scaledBalanceOf(randomUser);
    mathint aTokenBalanceAfter = balanceOf(randomUser);

    mathint aTokenInternalTotalSupplyAfter = internalTotalSupply();
    mathint aTokenScaledTokenSupplyAfter = scaledTotalSupply();
    mathint aTokenTotalSupplyAfter = totalSupply();

    assert aTokenInternalBalanceAfter * aTokenScaledTokenSupplyAfter == aTokenScaledBalanceAfter * aTokenInternalTotalSupplyAfter;
    assert aTokenScaledBalanceAfter * aTokenTotalSupplyAfter == aTokenBalanceAfter * aTokenScaledTokenSupplyAfter;
    assert aTokenInternalBalanceAfter * aTokenTotalSupplyAfter == aTokenBalanceAfter * aTokenInternalTotalSupplyAfter;
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

/*
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

/*
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
*/

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

/*

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
*/

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

/*
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
*/

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

/*
rule aTokenCantAffectUnderlying(){
    env e; calldataarg args; method f;

    mathint _underlyingTotalSupply = UNDERLYING_ASSET.totalSupply();
    f(e, args);
    mathint underlyingTotalSupply_ = UNDERLYING_ASSET.totalSupply();

    assert _underlyingTotalSupply == underlyingTotalSupply_;
}
*/

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

/*
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

/*
invariant atokenPeggedToUnderlying(env e)
    UNDERLYING_ASSET.balanceOf(currentContract) >= totalSupply()
    filtered { f -> f.selector != mint(address ,uint256 ,uint256).selector &&
                    f.selector != mintToTreasury(uint256, uint256).selector }
    {
        preserved with (env e2) {
            require currentContract != LENDING_POOL;
        }
    }
*/

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

/* 
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
