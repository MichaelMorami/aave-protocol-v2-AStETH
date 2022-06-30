// SPDX-License-Identifier: agpl-3.0
pragma solidity 0.6.12;
    
import '/home/i/Desktop/Certora_Forked_AsTETH/aave-protocol-v2-AStETH/certora/harness/autoFinder_DummyERC20Impl.sol';

contract DummyERC20A is DummyERC20Impl {
    function getPooledEthByShares(uint256 _sharesAmount) external view returns (uint256) {
        return 1000000000000000000000000000; // = one RAY
    }
}