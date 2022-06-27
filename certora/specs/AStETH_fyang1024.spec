import "./AStETH.spec"

methods {
    RESERVE_TREASURY_ADDRESS() returns (address) envfree
}

/*
    @Rule

    @Description:
        scaledBalance / internalBalance should be always equal to scaledTotalSupply / internalTotalSupply,
        that is, 
        internalBalance * scaledTotalSupply should be always equal to scaledBalance * internalTotalSupply,
        similarly, 
        scaledBalance * totalSupply should be always equal to balance * scaledTotalSupply, and
        internalBalance * totalSupply should be always equal to balance * internalTotalSupply

    @Formula:
        {
            _ATokenInternalBalance * _ATokenScaledTotalSupply == _ATokenScaledBalance * _ATokenInternalTotalSupply &&
            _ATokenScaledBalance * _ATokenTotalSupply == _ATokenBalance * _ATokenScaledTotalSupply &&
            _ATokenInternalBalance * _ATokenTotalSupply == _ATokenBalance * _ATokenInternalTotalSupply
        }

        < call any function >
        
        {
            ATokenInternalBalance_ * ATokenScaledTotalSupply_ == ATokenScaledBalance_ * ATokenInternalTotalSupply_ &&
            ATokenScaledBalance_ * ATokenTotalSupply_ == ATokenBalance_ * ATokenScaledTotalSupply_ &&
            ATokenInternalBalance_ * ATokenTotalSupply_ == ATokenBalance_ * ATokenInternalTotalSupply_
        }

    @Note:

    @Link:
*/

rule proportionalBalancesAndTotalSupplies(address user) {

    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();

    require _ATokenInternalBalance * _ATokenScaledTotalSupply == _ATokenScaledBalance * _ATokenInternalTotalSupply;
    require _ATokenScaledBalance * _ATokenTotalSupply == _ATokenBalance * _ATokenScaledTotalSupply;
    require _ATokenInternalBalance * _ATokenTotalSupply == _ATokenBalance * _ATokenInternalTotalSupply;

    env e; calldataarg args; method f;
    f(e, args);

    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();

    assert ATokenInternalBalance_ * ATokenScaledTotalSupply_ == ATokenScaledBalance_ * ATokenInternalTotalSupply_;
    assert ATokenScaledBalance_ * ATokenTotalSupply_ == ATokenBalance_ * ATokenScaledTotalSupply_;
    assert ATokenInternalBalance_ * ATokenTotalSupply_ == ATokenBalance_ * ATokenInternalTotalSupply_;
}

/*
    @Rule

    @Description:
        Burning and minting are invert operations within the AStETH context

    @Formula:
        {

        }

        burn()
        mint()
        
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

rule burnMintInvertability(address user, uint256 amount, uint256 index, address receiver){
    env e;
    
    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    
    burn(e, user, receiver, amount, index);
    mint(e, user, amount, index);
    
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
        the mint function and the mintToTreasury function should be equivalent

    @Formula:
        {
            storage init = lastStorage   
        }

        mintToTreasury(amount, index) 
        mathint _ATokenInternalBalance = internalBalanceOf(RESERVE_TREASURY_ADDRESS());
        mathint _ATokenScaledBalance = scaledBalanceOf(RESERVE_TREASURY_ADDRESS());
        mathint _ATokenBalance = balanceOf(RESERVE_TREASURY_ADDRESS());
        mathint _ATokenInternalTotalSupply = internalTotalSupply();
        mathint _ATokenScaledTotalSupply = scaledTotalSupply();
        mathint _ATokenTotalSupply = totalSupply();

        mint(RESERVE_TREASURY_ADDRESS(), amount, index) at init
        mathint ATokenInternalBalance_ = internalBalanceOf(RESERVE_TREASURY_ADDRESS());
        mathint ATokenScaledBalance_ = scaledBalanceOf(RESERVE_TREASURY_ADDRESS());
        mathint ATokenBalance_ = balanceOf(RESERVE_TREASURY_ADDRESS());
        mathint ATokenInternalTotalSupply_ = internalTotalSupply();
        mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
        mathint ATokenTotalSupply_ = totalSupply();
        
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

rule equivalenceOfMint(uint256 amount, uint256 index) {
    env e;
    storage init = lastStorage;

    mintToTreasury(e, amount, index);
    mathint _ATokenInternalBalance = internalBalanceOf(RESERVE_TREASURY_ADDRESS());
    mathint _ATokenScaledBalance = scaledBalanceOf(RESERVE_TREASURY_ADDRESS());
    mathint _ATokenBalance = balanceOf(RESERVE_TREASURY_ADDRESS());
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();

    mint(e, RESERVE_TREASURY_ADDRESS(), amount, index) at init;
    mathint ATokenInternalBalance_ = internalBalanceOf(RESERVE_TREASURY_ADDRESS());
    mathint ATokenScaledBalance_ = scaledBalanceOf(RESERVE_TREASURY_ADDRESS());
    mathint ATokenBalance_ = balanceOf(RESERVE_TREASURY_ADDRESS());
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();

    assert _ATokenInternalBalance == ATokenInternalBalance_ &&
            _ATokenScaledBalance == ATokenScaledBalance_ &&
            _ATokenBalance == ATokenBalance_ &&
            _ATokenInternalTotalSupply == ATokenInternalTotalSupply_ &&
            _ATokenScaledTotalSupply == ATokenScaledTotalSupply_ &&
            _ATokenTotalSupply == ATokenTotalSupply_;
}

/*
    @Rule

    @Description:
        The balance of a receiver in transferOnLiquidation() should increase by amount
        The balance of a sender in transferOnLiquidation() should decrease by amount

    @Formula:
        {
            sender != receiver;
        }

        transferOnLiquidation(sender, receiver, amount)
        
        {
            balanceOfSenderAfter == balanceOfSenderBefore - amount;
            balanceOfReceiverAfter == balanceOfReceiverBefore + amount;
            totalSupplyAfter == totalSupplyBefore;
        }

    @Note:

    @Link:
*/

rule integrityOfTransferOnLiquidation(address sender, address receiver, uint256 amount) {
    require sender != receiver;

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfSenderBefore = balanceOf(sender);
    mathint balanceOfReceiverBefore = balanceOf(receiver);

    env e;
    transferOnLiquidation(e, sender, receiver, amount);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfSenderAfter = balanceOf(sender);
    mathint balanceOfReceiverAfter = balanceOf(receiver);

    assert balanceOfSenderAfter == balanceOfSenderBefore - amount;
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + amount;
    assert totalSupplyAfter == totalSupplyBefore;
}

/*
    @Rule

    @Description:
        If sender is the same as receiver or the amount is 0, transferOnLiquidation should revert.
        Liquidating astETH to the account itself does not make sense and should fail the transaction.
        Liquidating 0 value does not make sense either and should fail the transaction.
        ** The code violates the rule, which I think should be fixed.

    @Formula:
        {
            sender == receiver || amount == 0;
        }

        transferOnLiquidation(sender, receiver, amount)
        
        {
            lastReverted
        }

    @Note:

    @Link:
*/

rule invalidLiquidationShouldRevert(address sender, address receiver, uint256 amount) {
    require sender == receiver || amount == 0;

    env e;
    transferOnLiquidation@withrevert(e, sender, receiver, amount);

    assert lastReverted;
}