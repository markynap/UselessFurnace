pragma solidity ^0.8.5;

/**
 * Created June 21 2021
 * Developed by SafemoonMark
 * USELESS Furnace Contract to Buy / Burn USELESS
 */
// SPDX-License-Identifier: Unlicensed

/*
 * Context Contract
 */
contract Context {
  // Empty internal constructor, to prevent people from mistakenly deploying
  // an instance of this contract, which should be used via inheritance.
  constructor () { }

  function _msgSender() internal view returns (address) {
    return msg.sender;
  }

  function _msgData() internal view returns (bytes memory) {
    this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
    return msg.data;
  }
}

interface IERC20 {

    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != accountHash && codehash != 0x0);
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract Ownable is Context {
  address private _owner;

  event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

  /**
   * @dev Initializes the contract setting the deployer as the initial owner.
   */
  constructor () {
    address msgSender = _msgSender();
    _owner = msgSender;
    emit OwnershipTransferred(address(0), msgSender);
  }

  /**
   * @dev Returns the address of the current owner.
   */
  function owner() public view returns (address) {
    return _owner;
  }

  /**
   * @dev Throws if called by any account other than the owner.
   */
  modifier onlyOwner() {
    require(_owner == _msgSender(), "Ownable: caller is not the owner");
    _;
  }

  /**
   * @dev Leaves the contract without owner. It will not be possible to call
   * `onlyOwner` functions anymore. Can only be called by the current owner.
   *
   * NOTE: Renouncing ownership will leave the contract without an owner,
   * thereby removing any functionality that is only available to the owner.
   */
  function renounceOwnership() public onlyOwner {
    emit OwnershipTransferred(_owner, address(0));
    _owner = address(0);
  }

  /**
   * @dev Transfers ownership of the contract to a new account (`newOwner`).
   * Can only be called by the current owner.
   */
  function transferOwnership(address newOwner) public onlyOwner {
    _transferOwnership(newOwner);
  }

  /**
   * @dev Transfers ownership of the contract to a new account (`newOwner`).
   */
  function _transferOwnership(address newOwner) internal {
    require(newOwner != address(0), "Ownable: new owner is the zero address");
    emit OwnershipTransferred(_owner, newOwner);
    _owner = newOwner;
  }
}

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
  /**
   * @dev Returns the addition of two unsigned integers, reverting on
   * overflow.
   *
   * Counterpart to Solidity's `+` operator.
   *
   * Requirements:
   * - Addition cannot overflow.
   */
  function add(uint256 a, uint256 b) internal pure returns (uint256) {
    uint256 c = a + b;
    require(c >= a, "SafeMath: addition overflow");

    return c;
  }

  /**
   * @dev Returns the subtraction of two unsigned integers, reverting on
   * overflow (when the result is negative).
   *
   * Counterpart to Solidity's `-` operator.
   *
   * Requirements:
   * - Subtraction cannot overflow.
   */
  function sub(uint256 a, uint256 b) internal pure returns (uint256) {
    return sub(a, b, "SafeMath: subtraction overflow");
  }

  /**
   * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
   * overflow (when the result is negative).
   *
   * Counterpart to Solidity's `-` operator.
   *
   * Requirements:
   * - Subtraction cannot overflow.
   */
  function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
    require(b <= a, errorMessage);
    uint256 c = a - b;

    return c;
  }

  /**
   * @dev Returns the multiplication of two unsigned integers, reverting on
   * overflow.
   *
   * Counterpart to Solidity's `*` operator.
   *
   * Requirements:
   * - Multiplication cannot overflow.
   */
  function mul(uint256 a, uint256 b) internal pure returns (uint256) {
    // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
    // benefit is lost if 'b' is also tested.
    // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
    if (a == 0) {
      return 0;
    }

    uint256 c = a * b;
    require(c / a == b, "SafeMath: multiplication overflow");

    return c;
  }

  /**
   * @dev Returns the integer division of two unsigned integers. Reverts on
   * division by zero. The result is rounded towards zero.
   *
   * Counterpart to Solidity's `/` operator. Note: this function uses a
   * `revert` opcode (which leaves remaining gas untouched) while Solidity
   * uses an invalid opcode to revert (consuming all remaining gas).
   *
   * Requirements:
   * - The divisor cannot be zero.
   */
  function div(uint256 a, uint256 b) internal pure returns (uint256) {
    return div(a, b, "SafeMath: division by zero");
  }

  /**
   * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
   * division by zero. The result is rounded towards zero.
   *
   * Counterpart to Solidity's `/` operator. Note: this function uses a
   * `revert` opcode (which leaves remaining gas untouched) while Solidity
   * uses an invalid opcode to revert (consuming all remaining gas).
   *
   * Requirements:
   * - The divisor cannot be zero.
   */
  function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
    // Solidity only automatically asserts when dividing by 0
    require(b > 0, errorMessage);
    uint256 c = a / b;
    // assert(a == b * c + a % b); // There is no case in which this doesn't hold

    return c;
  }

  /**
   * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
   * Reverts when dividing by zero.
   *
   * Counterpart to Solidity's `%` operator. This function uses a `revert`
   * opcode (which leaves remaining gas untouched) while Solidity uses an
   * invalid opcode to revert (consuming all remaining gas).
   *
   * Requirements:
   * - The divisor cannot be zero.
   */
  function mod(uint256 a, uint256 b) internal pure returns (uint256) {
    return mod(a, b, "SafeMath: modulo by zero");
  }

  /**
   * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
   * Reverts with custom message when dividing by zero.
   *
   * Counterpart to Solidity's `%` operator. This function uses a `revert`
   * opcode (which leaves remaining gas untouched) while Solidity uses an
   * invalid opcode to revert (consuming all remaining gas).
   *
   * Requirements:
   * - The divisor cannot be zero.
   */
  function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
    require(b != 0, errorMessage);
    return a % b;
  }
}


interface IUniswapV2Factory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB) external view returns (address pair);
    function allPairs(uint) external view returns (address pair);
    function allPairsLength() external view returns (uint);

    function createPair(address tokenA, address tokenB) external returns (address pair);

    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
}

interface IUniswapV2Pair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}

interface IUniswapV2Router02 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountETH);
    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountETH);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable;
    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB, uint liquidity);
    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountETH, uint liquidity);
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETH(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountToken, uint amountETH);
    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETHWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountToken, uint amountETH);
        function swapExactTokensForTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapExactETHForTokens(uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);
    function swapTokensForExactETH(uint amountOut, uint amountInMax, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapExactTokensForETH(uint amountIn, uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapETHForExactTokens(uint amountOut, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);

    function quote(uint amountA, uint reserveA, uint reserveB) external pure returns (uint amountB);
    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) external pure returns (uint amountOut);
    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) external pure returns (uint amountIn);
    function getAmountsOut(uint amountIn, address[] calldata path) external view returns (uint[] memory amounts);
    function getAmountsIn(uint amountOut, address[] calldata path) external view returns (uint[] memory amounts);
    function WETH() external pure returns (address);
    function factory() external pure returns (address);
}
/**
 * 
 * BNB Sent to this contract will be used to automatically buy/burn USELESS
 * And Emits and Event to the blockchain with how much BNB was used
 * Liquidity between 10-15% - reverse SAL
 * Liquidity over 15% - buy/burn or LP extraction
 * Liquidity under 10% - inject LP from sidetokenomics or trigger SAL from previous LP Extractions
 *
 */
contract UselessFurnace is Context, Ownable {
    
  using Address for address;
  using SafeMath for uint8;
  using SafeMath for uint256;
  
  // address of USELESS Smart Contract
  address payable private _uselessAddr = payable(0x2cd2664Ce5639e46c6a3125257361e01d0213657);
 
  // burn wallet address
  address payable private _burnWallet = payable(0x000000000000000000000000000000000000dEaD);
  
  // multisig wallet
  address payable private _multisig = payable(0x405dCC72BF70292Cc23B80F3f01939113cF36A0c);
  
  // useless liquidity pool address
  address private _uselessLP = 0x08A6cD8a2E49E3411d13f9364647E1f2ee2C6380; 
  
  // Total Amount of BNB that has been used to Buy/Sell USELESS
  uint256 public _totalBNBUsedToBuyAndBurnUSELESS = 0;

  // Initialize Pancakeswap Router
  IUniswapV2Router02 private uniswapV2Router = IUniswapV2Router02(0x10ED43C718714eb63d5aA57B78B54704E256024E);
  
  uint256 maxPercent = 100;
  
  // Tells the blockchain how much BNB was used on every Buy/Burn
  event BuyAndBurn(
    uint256 amountBurned
  );
  
  event BuyBack(
    uint256 amountBought
  );
  
  event AddUSELESSLiquidity(
    uint256 uselessAmount,
    uint256 bnbAmount
  );
  
  /**
   * Automates the Buy/Burn, SAL, or reverseSAL operations based on the state of the LP
   */ 
  function automate() public onlyOwner {
    
    // calculate the current Circulating Supply of USELESS    
    uint256 totalSupply = 1000000000 * 10**6 * 10**9;
    // size of burn wallet
    uint256 burnWalletSize = IERC20(_uselessAddr).balanceOf(_burnWallet);
    // Circulating supply is total supply - burned supply
    uint256 circSupply = totalSupply.sub(burnWalletSize);    

    // Find the balance of USELESS in the liquidity pool
    uint256 lpBalance = IERC20(_uselessAddr).balanceOf(_uselessLP);
    // ratio of supply to LP
    uint256 dif = circSupply.div(lpBalance);
    
    if (dif < 1) {
        dif = 1;
    }
    
    if (dif <= 6) {
        // if LP is over 15% of Supply we buy burn useless or pull liquidity
        uint8 ratio = uint8(maxPercent.div(dif));
        
        buyAndBurn(ratio);
    } else if (dif <= 10) {
        // if LP is between 10-15% of Supply we call reverseSAL
        reverseSwapAndLiquify();
    } else {
        // if LP is under 10% of Supply we call SAL or provide a pairing if one exists
        swapAndLiquify(uint8(dif));
    }
  }

  /**
   * Buys USELESS Tokens and sends them to the burn wallet
   * @param percentOfBNB - Percentage of BNB Inside the contract to buy/burn with
   */ 
  function buyAndBurn(uint8 percentOfBNB) private {
      
     uint256 buyBurnBalance = calculateTransferAmount(address(this).balance, percentOfBNB);
     
     buyAndBurnUseless(buyBurnBalance);
     
     _totalBNBUsedToBuyAndBurnUSELESS = _totalBNBUsedToBuyAndBurnUSELESS.add(buyBurnBalance);
     
     emit BuyAndBurn(buyBurnBalance);
  }
  
  /**
   * Sells half of percent of USELESS in the contract address for BNB, pairs it and adds to Liquidity Pool
   * Similar to swapAndLiquify
   * @param percent - Percentage out of 100 for how much USELESS to be used in swapAndLiquify
   */
   function swapAndLiquify(uint8 percent) private {
       
    uint256 oldContractBalance = IERC20(_uselessAddr).balanceOf(address(this));
    
    uint256 contractBalance = calculateTransferAmount(oldContractBalance, percent);
    
    if (contractBalance > oldContractBalance) {
        contractBalance = oldContractBalance;
    }
    
    // split the contract balance in half
    uint256 half = contractBalance.div(2);
    uint256 otherHalf = contractBalance.sub(half);

    // balance of BNB before we swap
    uint256 initialBalance = address(this).balance;

    // swap tokens for BNB
    swapTokensForBNB(half);

    // how many tokens were received from swap
    uint256 newBalance = address(this).balance.sub(initialBalance);

    // add liquidity to Pancakeswap
    addLiquidity(otherHalf, newBalance);
        
    emit AddUSELESSLiquidity(otherHalf, newBalance);
   }
   
   /**
   * Uses BNB in Contract to Purchase Useless, pairs with remaining BNB and adds to Liquidity Pool
   * Similar to swapAndLiquify
   */
   function reverseSwapAndLiquify() private {
      
    // BNB Balance before the swap
    uint256 initialBalance = address(this).balance;
    
    // USELESS Balance before the Swap
    uint256 contractBalance = IERC20(_uselessAddr).balanceOf(address(this));

    // Swap 50% of the BNB in Contract for USELESS Tokens
    justBuyBack(50);

    // how much bnb was spent on the swap
    uint256 bnbInSwap = initialBalance.sub(address(this).balance);
    
    // how many USELESS Tokens do we have now?
    uint256 currentBalance = IERC20(_uselessAddr).balanceOf(address(this));

    // Get Exact Number of USELESS We Swapped For
    uint256 diff = currentBalance.sub(contractBalance);
    
    if (bnbInSwap > address(this).balance) {
        bnbInSwap = address(this).balance;
    }
    
    // add liquidity to Pancakeswap
    addLiquidity(diff, bnbInSwap);
        
    emit AddUSELESSLiquidity(diff, bnbInSwap);
   }
  
    
  /**
   * Internal Function which calls UniswapRouter function 
   */ 
  function buyAndBurnUseless(uint256 tokenAmount) private {
    
    // Uniswap pair path for BNB -> USELESS
    address[] memory path = new address[](2);
    path[0] = uniswapV2Router.WETH();
    path[1] = _uselessAddr;
    
    // Swap BNB for USELESS
    uniswapV2Router.swapExactETHForTokensSupportingFeeOnTransferTokens{value: tokenAmount}(
        0, // accept any amount of USELESS
        path,
        _burnWallet, // Burn Address
        block.timestamp.add(300)
    );  
      
  }
  
   /**
   * Buys USELESS with BNB Stored in the contract, and stores the USELESS in the contract
   * @param ratioOfBNB - Percentage of contract's BNB to Buy
   */ 
  function justBuyBack(uint8 ratioOfBNB) private {
      
    require(ratioOfBNB <= 100, 'Cannot have a ratio over 100%');
    // calculate the amount being transfered 
    uint256 transferAMT = calculateTransferAmount(address(this).balance, ratioOfBNB);
    
    // Uniswap pair path for BNB -> USELESS
    address[] memory path = new address[](2);
    path[0] = uniswapV2Router.WETH();
    path[1] = _uselessAddr;
    
    // Swap BNB for USELESS
    uniswapV2Router.swapExactETHForTokensSupportingFeeOnTransferTokens{value: transferAMT}(
        0, // accept any amount of USELESS
        path,
        address(this), // Store in Contract
        block.timestamp.add(300)
    );  
      
    emit BuyBack(transferAMT);
  }
  
  /**
   * Swaps USELESS for BNB using the USELESS/BNB Pool
   */ 
  function swapTokensForBNB(uint256 tokenAmount) private {
    // generate the uniswap pair path for token -> weth
    address[] memory path = new address[](2);
    path[0] = _uselessAddr;
    path[1] = uniswapV2Router.WETH();

    IERC20(_uselessAddr).approve(address(uniswapV2Router), tokenAmount);

    // make the swap
    uniswapV2Router.swapExactTokensForETHSupportingFeeOnTransferTokens(
        tokenAmount,
        0, // accept any amount of ETH
        path,
        address(this),
        block.timestamp
    );
    }
    
  /**
   * Adds USELESS and BNB to the USELESS/BNB Liquidity Pool
   */ 
  function addLiquidity(uint256 uselessAmount, uint256 bnbAmount) private {
       
    IERC20(_uselessAddr).approve(address(uniswapV2Router), uselessAmount);

    // add the liquidity
    uniswapV2Router.addLiquidityETH{value: bnbAmount}(
        _uselessAddr,
        uselessAmount,
        0,
        0,
        _multisig,
        block.timestamp.add(300)
    );
    }
  
  function calculateTransferAmount(uint256 amount, uint8 fee) private pure returns (uint256){
     return amount.sub((amount.mul(fee)).div(100));
  }
    
  /**
   * @dev Returns the owner of the contract
   */
  function getOwner() external view returns (address) {
    return owner();
  }
  /**
   * Amount of BNB in this contract
   */ 
  function getContractBNBBallance() external view returns (uint256) {
    return address(this).balance;
  }
  
   /**
   * 
   * Updates the Uniswap Router and Uniswap pairing for ETH In Case of migration
   */
  function setUniswapV2Router(address _uniswapV2Router) public onlyOwner {
    uniswapV2Router = IUniswapV2Router02(_uniswapV2Router);
  }
  
  /**
   * Updates the Uniswap Router and Uniswap pairing for ETH In Case of migration
   */
  function setMultiSig(address payable _nMultiSig) public onlyOwner {
    _multisig = _nMultiSig;
  }
  
  /**
   * Updates the Uniswap Router and Uniswap pairing for ETH In Case of migration
   */
  function setUselessLPAddress(address nUselessLP) public onlyOwner {
    _uselessLP = nUselessLP;
  }

  /**
   * 
   * Updates the Contract Address for USELESS
   */
  function setUSELESSContractAddress(address payable newUselessAddress) public onlyOwner {
    _uselessAddr = newUselessAddress;
  }
  
  /**
   * 
   * Updates the Burn Wallet Address for USELESS
   */
  function setUSELESSBurnAddress(address payable newBurnAddress) public onlyOwner {
    _burnWallet = newBurnAddress;
  }
  

    //to recieve ETH from uniswapV2Router when swaping
    receive() external payable {}
    
}