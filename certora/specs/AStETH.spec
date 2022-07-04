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

    isContractIsTrue(address) returns (bool) envfree

    UNDERLYING_ASSET.balanceOf(address) returns (uint256) envfree
    UNDERLYING_ASSET.totalSupply() returns (uint256) envfree

    LENDING_POOL.aToken() returns (address) envfree

}

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