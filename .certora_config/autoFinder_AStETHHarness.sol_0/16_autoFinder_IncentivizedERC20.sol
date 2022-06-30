// SPDX-License-Identifier: agpl-3.0
pragma solidity 0.6.12;

import { Context } from '/home/i/Desktop/Certora_Forked_AsTETH/aave-protocol-v2-AStETH/contracts/dependencies/openzeppelin/contracts/autoFinder_Context.sol';
import {IERC20} from '../../dependencies/openzeppelin/contracts/IERC20.sol';
import {IERC20Detailed} from '../../dependencies/openzeppelin/contracts/IERC20Detailed.sol';
import { SafeMath } from '/home/i/Desktop/Certora_Forked_AsTETH/aave-protocol-v2-AStETH/contracts/dependencies/openzeppelin/contracts/autoFinder_SafeMath.sol';
import {IAaveIncentivesController} from '../../interfaces/IAaveIncentivesController.sol';

/**
 * @title ERC20
 * @notice Basic ERC20 implementation
 * @author Aave, inspired by the Openzeppelin ERC20 implementation
 **/
contract IncentivizedERC20 is Context, IERC20, IERC20Detailed {
  using SafeMath for uint256;

  IAaveIncentivesController internal immutable _incentivesController;

  mapping(address => uint256) internal _balances;

  mapping(address => mapping(address => uint256)) private _allowances;
  uint256 internal _totalSupply;
  string private _name;
  string private _symbol;
  uint8 private _decimals;

  constructor(
    string memory name,
    string memory symbol,
    uint8 decimals,
    address incentivesController
  ) public {
    _name = name;
    _symbol = symbol;
    _decimals = decimals;
    _incentivesController = IAaveIncentivesController(incentivesController);
  }

  /**
   * @return The name of the token
   **/
  function name() public view override returns (string memory) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00260000, 1037618708518) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00260001, 0) }
    return _name;
  }

  /**
   * @return The symbol of the token
   **/
  function symbol() public view override returns (string memory) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001c0000, 1037618708508) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001c0001, 0) }
    return _symbol;
  }

  /**
   * @return The decimals of the token
   **/
  function decimals() public view override returns (uint8) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00240000, 1037618708516) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00240001, 0) }
    return _decimals;
  }

  /**
   * @return The total supply of the token
   **/
  function totalSupply() public view virtual override returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002a0000, 1037618708522) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002a0001, 0) }
    return _totalSupply;
  }

  /**
   * @return The balance of the token
   **/
  function balanceOf(address account) public view virtual override returns (uint256) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002b0000, 1037618708523) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002b0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002b1000, account) }
    return _balances[account];
  }

  /**
   * @dev Executes a transfer of tokens from _msgSender() to recipient
   * @param recipient The recipient of the tokens
   * @param amount The amount of tokens being transferred
   * @return `true` if the transfer succeeds, `false` otherwise
   **/
  function transfer(address recipient, uint256 amount) public virtual override returns (bool) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00190000, 1037618708505) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00190001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00191000, recipient) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00191001, amount) }
    _transfer(_msgSender(), recipient, amount);
    emit Transfer(_msgSender(), recipient, amount);
    return true;
  }

  /**
   * @dev Returns the allowance of spender on the tokens owned by owner
   * @param owner The owner of the tokens
   * @param spender The user allowed to spend the owner's tokens
   * @return The amount of owner's tokens spender is allowed to spend
   **/
  function allowance(address owner, address spender)
    public
    view
    virtual
    override
    returns (uint256)
  {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001b0000, 1037618708507) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001b0001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001b1000, owner) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001b1001, spender) }
    return _allowances[owner][spender];
  }

  /**
   * @dev Allows `spender` to spend the tokens owned by _msgSender()
   * @param spender The user allowed to spend _msgSender() tokens
   * @return `true`
   **/
  function approve(address spender, uint256 amount) public virtual override returns (bool) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00180000, 1037618708504) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00180001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00181000, spender) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00181001, amount) }
    _approve(_msgSender(), spender, amount);
    return true;
  }

  /**
   * @dev Executes a transfer of token from sender to recipient, if _msgSender() is allowed to do so
   * @param sender The owner of the tokens
   * @param recipient The recipient of the tokens
   * @param amount The amount of tokens being transferred
   * @return `true` if the transfer succeeds, `false` otherwise
   **/
  function transferFrom(
    address sender,
    address recipient,
    uint256 amount
  ) public virtual override returns (bool) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00220000, 1037618708514) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00220001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00221000, sender) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00221001, recipient) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00221002, amount) }
    _transfer(sender, recipient, amount);
    _approve(
      sender,
      _msgSender(),
      _allowances[sender][_msgSender()].sub(amount, 'ERC20: transfer amount exceeds allowance')
    );
    emit Transfer(sender, recipient, amount);
    return true;
  }

  /**
   * @dev Increases the allowance of spender to spend _msgSender() tokens
   * @param spender The user allowed to spend on behalf of _msgSender()
   * @param addedValue The amount being added to the allowance
   * @return `true`
   **/
  function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001f0000, 1037618708511) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001f0001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001f1000, spender) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff001f1001, addedValue) }
    _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
    return true;
  }

  /**
   * @dev Decreases the allowance of spender to spend _msgSender() tokens
   * @param spender The user allowed to spend on behalf of _msgSender()
   * @param subtractedValue The amount being subtracted to the allowance
   * @return `true`
   **/
  function decreaseAllowance(address spender, uint256 subtractedValue)
    public
    virtual
    returns (bool)
  {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00200000, 1037618708512) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00200001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00201000, spender) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00201001, subtractedValue) }
    _approve(
      _msgSender(),
      spender,
      _allowances[_msgSender()][spender].sub(
        subtractedValue,
        'ERC20: decreased allowance below zero'
      )
    );
    return true;
  }

  function _transfer(
    address sender,
    address recipient,
    uint256 amount
  ) internal virtual {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00290000, 1037618708521) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00290001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00291000, sender) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00291001, recipient) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00291002, amount) }
    require(sender != address(0), 'ERC20: transfer from the zero address');
    require(recipient != address(0), 'ERC20: transfer to the zero address');

    _beforeTokenTransfer(sender, recipient, amount);

    uint256 oldSenderBalance = _balances[sender];
    _balances[sender] = oldSenderBalance.sub(amount, 'ERC20: transfer amount exceeds balance');
    uint256 oldRecipientBalance = _balances[recipient];
    _balances[recipient] = _balances[recipient].add(amount);

    if (address(_incentivesController) != address(0)) {
      uint256 currentTotalSupply = _totalSupply;
      _incentivesController.handleAction(sender, currentTotalSupply, oldSenderBalance);
      if (sender != recipient) {
        _incentivesController.handleAction(recipient, currentTotalSupply, oldRecipientBalance);
      }
    }
  }

  function _mint(address account, uint256 amount) internal virtual {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00070000, 1037618708487) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00070001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00071000, account) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00071001, amount) }
    require(account != address(0), 'ERC20: mint to the zero address');

    _beforeTokenTransfer(address(0), account, amount);

    uint256 oldTotalSupply = _totalSupply;
    _totalSupply = oldTotalSupply.add(amount);

    uint256 oldAccountBalance = _balances[account];
    _balances[account] = oldAccountBalance.add(amount);

    if (address(_incentivesController) != address(0)) {
      _incentivesController.handleAction(account, oldTotalSupply, oldAccountBalance);
    }
  }

  function _burn(address account, uint256 amount) internal virtual {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00080000, 1037618708488) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00080001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00081000, account) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00081001, amount) }
    require(account != address(0), 'ERC20: burn from the zero address');

    _beforeTokenTransfer(account, address(0), amount);

    uint256 oldTotalSupply = _totalSupply;
    _totalSupply = oldTotalSupply.sub(amount);

    uint256 oldAccountBalance = _balances[account];
    _balances[account] = oldAccountBalance.sub(amount, 'ERC20: burn amount exceeds balance');

    if (address(_incentivesController) != address(0)) {
      _incentivesController.handleAction(account, oldTotalSupply, oldAccountBalance);
    }
  }

  function _approve(
    address owner,
    address spender,
    uint256 amount
  ) internal virtual {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00090000, 1037618708489) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00090001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00091000, owner) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00091001, spender) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00091002, amount) }
    require(owner != address(0), 'ERC20: approve from the zero address');
    require(spender != address(0), 'ERC20: approve to the zero address');

    _allowances[owner][spender] = amount;
    emit Approval(owner, spender, amount);
  }

  function _setName(string memory newName) internal {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000a0000, 1037618708490) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000a0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000a1000, newName) }
    _name = newName;
  }

  function _setSymbol(string memory newSymbol) internal {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000b0000, 1037618708491) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000b0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000b1000, newSymbol) }
    _symbol = newSymbol;
  }

  function _setDecimals(uint8 newDecimals) internal {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000c0000, 1037618708492) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000c0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000c1000, newDecimals) }
    _decimals = newDecimals;
  }

  function _beforeTokenTransfer(
    address from,
    address to,
    uint256 amount
  ) internal virtual {assembly { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000d0000, 1037618708493) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000d0001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000d1000, from) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000d1001, to) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff000d1002, amount) }}
}
