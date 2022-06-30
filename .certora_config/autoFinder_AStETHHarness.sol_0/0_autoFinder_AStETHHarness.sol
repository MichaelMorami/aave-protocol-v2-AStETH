// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.6.12;

import { AStETH } from '/home/i/Desktop/Certora_Forked_AsTETH/aave-protocol-v2-AStETH/contracts/protocol/tokenization/lido/autoFinder_AStETH.sol';
import {ILendingPool} from "../../contracts/interfaces/ILendingPool.sol";
import { WadRayMath } from '/home/i/Desktop/Certora_Forked_AsTETH/aave-protocol-v2-AStETH/contracts/protocol/libraries/math/autoFinder_WadRayMath.sol';
import { Address } from '/home/i/Desktop/Certora_Forked_AsTETH/aave-protocol-v2-AStETH/contracts/dependencies/openzeppelin/contracts/autoFinder_Address.sol';

contract AStETHHarness is AStETH {
  constructor(
    ILendingPool pool,
    address underlyingAssetAddress,
    address reserveTreasuryAddress,
    string memory tokenName,
    string memory tokenSymbol,
    address incentivesController
  ) public AStETH(pool, underlyingAssetAddress, reserveTreasuryAddress, tokenName, tokenSymbol, incentivesController) {}

  function isContractIsTrue(address account) public view returns (bool){assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00110000, 1037618708497) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00110001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00111000, account) }
      require(Address.isContract(account));
      return true;
  }


/*****************************
 *    IKHLAS - i01001        *
 *****************************/

  function _getRevision() public returns (uint256){assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00250000, 1037618708517) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00250001, 0) }
    return getRevision();
  }

  function getChainID() external view returns (uint256) {
    uint256 id;
    assembly {
        id := chainid()
    }
    return id;
}
  
  function _getDecimals() public returns (uint256){assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00130000, 1037618708499) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00130001, 0) }
    return decimals();
  }

  function _gettoInternalAmount(    uint256 _amount,
    uint256 _stEthRebasingIndex,
    uint256 _aaveLiquidityIndex) public returns (uint256){assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001d0000, 1037618708509) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001d0001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001d1000, _amount) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001d1001, _stEthRebasingIndex) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001d1002, _aaveLiquidityIndex) }
    return _toInternalAmount(_amount, _stEthRebasingIndex, _aaveLiquidityIndex);
  }


    function _getscaledTotalSupply(    uint256 _rebasingIndex) public returns (uint256){assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001e0000, 1037618708510) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001e0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001e1000, _rebasingIndex) }
    return _scaledTotalSupply(_rebasingIndex);
  }

    function _getNonces(address _address) public returns (uint256){assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00230000, 1037618708515) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00230001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00231000, _address) }
    return _nonces[ _address];
  }


    function _gettransfer(address from, address to, uint256 amount, bool validate) public {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00140000, 1037618708500) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00140001, 4) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00141000, from) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00141001, to) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00141002, amount) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00141003, validate) }
    _transfer( from, to, amount, validate);
  }


    function _gettransfer2(address from, address to, uint256 amount) public {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00170000, 1037618708503) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00170001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00171000, from) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00171001, to) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00171002, amount) }
    _transfer( from, to, amount);
  }


   function _getscaledBalanceOf(address user, uint256 rebasingIndex) public returns (uint256){assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00120000, 1037618708498) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00120001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00121000, user) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00121001, rebasingIndex) }
    return _scaledBalanceOf(user, rebasingIndex);
  }

   function _getstEthRebasingIndex() public returns (uint256){assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00100000, 1037618708496) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00100001, 0) }
    return _stEthRebasingIndex();
  }
  
  
}