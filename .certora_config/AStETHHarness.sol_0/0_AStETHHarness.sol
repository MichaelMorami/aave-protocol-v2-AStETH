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


/*****************************
 *    IKHLAS - i01001        *
 *****************************/

  function _getRevision() public returns (uint256){
    return getRevision();
  }

  function getChainID() external view returns (uint256) {
    uint256 id;
    assembly {
        id := chainid()
    }
    return id;
}
  
  function _getDecimals() public returns (uint256){
    return decimals();
  }

  function _gettoInternalAmount(    uint256 _amount,
    uint256 _stEthRebasingIndex,
    uint256 _aaveLiquidityIndex) public returns (uint256){
    return _toInternalAmount(_amount, _stEthRebasingIndex, _aaveLiquidityIndex);
  }


    function _getscaledTotalSupply(    uint256 _rebasingIndex) public returns (uint256){
    return _scaledTotalSupply(_rebasingIndex);
  }

    function _getNonces(address _address) public returns (uint256){
    return _nonces[ _address];
  }


    function _gettransfer(address from, address to, uint256 amount, bool validate) public {
    _transfer( from, to, amount, validate);
  }


    function _gettransfer2(address from, address to, uint256 amount) public {
    _transfer( from, to, amount);
  }


   function _getscaledBalanceOf(address user, uint256 rebasingIndex) public returns (uint256){
    return _scaledBalanceOf(user, rebasingIndex);
  }


   function _getstEthRebasingIndex() public returns (uint256){
    return _stEthRebasingIndex();
  }

  
}