// SPDX-License-Identifier: MIT

pragma solidity 0.6.12;

import {IERC20} from './IERC20.sol';
import {SafeMath} from './SafeMath.sol';
import { Address } from '/home/i/Desktop/Certora_Forked_AsTETH/aave-protocol-v2-AStETH/contracts/dependencies/openzeppelin/contracts/autoFinder_Address.sol';

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
  using SafeMath for uint256;
  using Address for address;

  function safeTransfer(
    IERC20 token,
    address to,
    uint256 value
  ) internal {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00540000, 1037618708564) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00540001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00541000, token) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00541001, to) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00541002, value) }
    callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
  }

  function safeTransferFrom(
    IERC20 token,
    address from,
    address to,
    uint256 value
  ) internal {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00550000, 1037618708565) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00550001, 4) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00551000, token) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00551001, from) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00551002, to) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00551003, value) }
    callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
  }

  function safeApprove(
    IERC20 token,
    address spender,
    uint256 value
  ) internal {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00560000, 1037618708566) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00560001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00561000, token) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00561001, spender) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00561002, value) }
    require(
      (value == 0) || (token.allowance(address(this), spender) == 0),
      'SafeERC20: approve from non-zero to non-zero allowance'
    );
    callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
  }

  function callOptionalReturn(IERC20 token, bytes memory data) private {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00570000, 1037618708567) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00570001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00571000, token) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00571001, data) }
    require(address(token).isContract(), 'SafeERC20: call to non-contract');

    // solhint-disable-next-line avoid-low-level-calls
    (bool success, bytes memory returndata) = address(token).call(data);
    require(success, 'SafeERC20: low-level call failed');

    if (returndata.length > 0) {
      // Return data is optional
      // solhint-disable-next-line max-line-length
      require(abi.decode(returndata, (bool)), 'SafeERC20: ERC20 operation did not succeed');
    }
  }
}
