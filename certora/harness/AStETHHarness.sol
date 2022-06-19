// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.6.12;

import {AStETH} from "../../contracts/protocol/tokenization/lido/AStETH.sol";
import {ILendingPool} from "../../contracts/interfaces/ILendingPool.sol";
import {WadRayMath} from "../../contracts/protocol/libraries/math/WadRayMath.sol";

contract AStETHHarness is AStETH {
  constructor(
    ILendingPool pool,
    address underlyingAssetAddress,
    address reserveTreasuryAddress,
    string memory tokenName,
    string memory tokenSymbol,
    address incentivesController
  ) public AStETH(pool, underlyingAssetAddress, reserveTreasuryAddress, tokenName, tokenSymbol, incentivesController) {}

  function setInitializing(bool _init) public {
    initializing = _init;
  }

  function nonces(address owner) public view returns (uint256) {
    return _nonces[owner];
  }

}