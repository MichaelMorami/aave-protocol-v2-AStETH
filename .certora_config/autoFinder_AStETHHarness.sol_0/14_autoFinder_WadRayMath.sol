// SPDX-License-Identifier: agpl-3.0
pragma solidity 0.6.12;

import {Errors} from '../helpers/Errors.sol';

/**
 * @title WadRayMath library
 * @author Aave
 * @dev Provides mul and div function for wads (decimal numbers with 18 digits precision) and rays (decimals with 27 digits)
 **/

library WadRayMath {
  uint256 internal constant WAD = 1e18;
  uint256 internal constant halfWAD = WAD / 2;

  uint256 internal constant RAY = 1e27;
  uint256 internal constant halfRAY = RAY / 2;

  uint256 internal constant WAD_RAY_RATIO = 1e9;

  /**
   * @return One ray, 1e27
   **/
  function ray() internal pure returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00350000, 1037618708533) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00350001, 0) }
    return RAY;
  }

  /**
   * @return One wad, 1e18
   **/

  function wad() internal pure returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00360000, 1037618708534) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00360001, 0) }
    return WAD;
  }

  /**
   * @return Half ray, 1e27/2
   **/
  function halfRay() internal pure returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00380000, 1037618708536) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00380001, 0) }
    return halfRAY;
  }

  /**
   * @return Half ray, 1e18/2
   **/
  function halfWad() internal pure returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00390000, 1037618708537) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00390001, 0) }
    return halfWAD;
  }

  /**
   * @dev Multiplies two wad, rounding half up to the nearest wad
   * @param a Wad
   * @param b Wad
   * @return The result of a*b, in wad
   **/
  function wadMul(uint256 a, uint256 b) internal pure returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00370000, 1037618708535) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00370001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00371000, a) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00371001, b) }
    if (a == 0 || b == 0) {
      return 0;
    }

    require(a <= (type(uint256).max - halfWAD) / b, Errors.MATH_MULTIPLICATION_OVERFLOW);

    return (a * b + halfWAD) / WAD;
  }

  /**
   * @dev Divides two wad, rounding half up to the nearest wad
   * @param a Wad
   * @param b Wad
   * @return The result of a/b, in wad
   **/
  function wadDiv(uint256 a, uint256 b) internal pure returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003a0000, 1037618708538) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003a0001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003a1000, a) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003a1001, b) }
    require(b != 0, Errors.MATH_DIVISION_BY_ZERO);
    uint256 halfB = b / 2;

    require(a <= (type(uint256).max - halfB) / WAD, Errors.MATH_MULTIPLICATION_OVERFLOW);

    return (a * WAD + halfB) / b;
  }

  /**
   * @dev Multiplies two ray, rounding half up to the nearest ray
   * @param a Ray
   * @param b Ray
   * @return The result of a*b, in ray
   **/
  function rayMul(uint256 a, uint256 b) internal pure returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003b0000, 1037618708539) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003b0001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003b1000, a) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003b1001, b) }
    if (a == 0 || b == 0) {
      return 0;
    }

    require(a <= (type(uint256).max - halfRAY) / b, Errors.MATH_MULTIPLICATION_OVERFLOW);

    return (a * b + halfRAY) / RAY;
  }

  /**
   * @dev Divides two ray, rounding half up to the nearest ray
   * @param a Ray
   * @param b Ray
   * @return The result of a/b, in ray
   **/
  function rayDiv(uint256 a, uint256 b) internal pure returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003c0000, 1037618708540) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003c0001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003c1000, a) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003c1001, b) }
    require(b != 0, Errors.MATH_DIVISION_BY_ZERO);
    uint256 halfB = b / 2;

    require(a <= (type(uint256).max - halfB) / RAY, Errors.MATH_MULTIPLICATION_OVERFLOW);

    return (a * RAY + halfB) / b;
  }

  /**
   * @dev Casts ray down to wad
   * @param a Ray
   * @return a casted to wad, rounded half up to the nearest wad
   **/
  function rayToWad(uint256 a) internal pure returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003d0000, 1037618708541) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003d0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003d1000, a) }
    uint256 halfRatio = WAD_RAY_RATIO / 2;
    uint256 result = halfRatio + a;
    require(result >= halfRatio, Errors.MATH_ADDITION_OVERFLOW);

    return result / WAD_RAY_RATIO;
  }

  /**
   * @dev Converts wad up to ray
   * @param a Wad
   * @return a converted in ray
   **/
  function wadToRay(uint256 a) internal pure returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003e0000, 1037618708542) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003e0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003e1000, a) }
    uint256 result = a * WAD_RAY_RATIO;
    require(result / WAD_RAY_RATIO == a, Errors.MATH_MULTIPLICATION_OVERFLOW);
    return result;
  }
}
