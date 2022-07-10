// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.6.12;

import {AStETH} from "../../contracts/protocol/tokenization/lido/AStETH.sol";
import {ILendingPool} from "../../contracts/interfaces/ILendingPool.sol";
import {WadRayMath} from "../../contracts/protocol/libraries/math/WadRayMath.sol";
import {Address} from "../../contracts/dependencies/openzeppelin/contracts/Address.sol";

contract AStETHHarness is AStETH {
  constructor(
    ILendingPool pool,
    address underlyingAssetAddress,
    address reserveTreasuryAddress,
    string memory tokenName,
    string memory tokenSymbol,
    address incentivesController
  ) public AStETH(pool, underlyingAssetAddress, reserveTreasuryAddress, tokenName, tokenSymbol, incentivesController) {}

  function isContractIsTrue(address account) public view returns (bool){
      require(Address.isContract(account));
      return true;
  }

  function getNonceOf(address owner) public view returns(uint256) {
    return _nonces[owner];
  }

  
}