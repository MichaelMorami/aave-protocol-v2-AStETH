//todo - inhert ERC20 
//add deposit, withdraw, getReserveNormalizedIncome 
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import { SafeERC20 } from '/home/i/Desktop/Certora_Forked_AsTETH/aave-protocol-v2-AStETH/contracts/dependencies/openzeppelin/contracts/autoFinder_SafeERC20.sol';
import "../../contracts/interfaces/IAToken.sol";
import { Address } from '/home/i/Desktop/Certora_Forked_AsTETH/aave-protocol-v2-AStETH/contracts/dependencies/openzeppelin/contracts/autoFinder_Address.sol';

contract SymbolicLendingPool  {

    using SafeERC20 for IERC20;

    address public aToken; 
    uint256 public liquidityIndex = 1; //TODO 
    uint256 public data;
    address public Asset;

    function deposit(
    address asset,
    uint256 amount,
    address onBehalfOf,
    uint16 referralCode
  ) external {
    Asset = asset;
    IERC20(Asset).safeTransferFrom(msg.sender, aToken, amount);
    IAToken(aToken).mint(onBehalfOf, amount,liquidityIndex );
  }


  function withdraw(
    address asset,
    uint256 amount,
    address to
  ) external  returns (uint256) {
    
    IAToken(aToken).burn(msg.sender, to, amount, liquidityIndex);
    return amount;
  }
  
  function getReserveNormalizedIncome(address asset)
    external
    view
    virtual
    returns (uint256) {
      return liquidityIndex;
    }

    function finalizeTransfer(
    address asset,
    address from,
    address to,
    uint256 amount,
    uint256 balanceFromAfter,
    uint256 balanceToBefore
    ) external {
    }

    function getATokenAddress(address asset) public returns (address) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00530000, 1037618708563) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00530001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00531000, asset) }
      return aToken;
    }
} 