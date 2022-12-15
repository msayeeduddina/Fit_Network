// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;


// File: contracts\open-zeppelin-contracts\AddressUpgradeable.sol

/**
 * @dev Collection of functions related to the address type
 */
library AddressUpgradeable {

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
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns(bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.
        return account.code.length > 0;
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
        (bool success, ) = recipient.call {
            value: amount
        }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
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
    function functionCall(address target, bytes memory data) internal returns(bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns(bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
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
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns(bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns(bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");
        (bool success, bytes memory returndata) = target.call {
            value: value
        }(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns(bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data, string memory errorMessage) internal view returns(bytes memory) {
        require(isContract(target), "Address: static call to non-contract");
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verifies that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(bool success, bytes memory returndata, string memory errorMessage) internal pure returns(bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly
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


// File: contracts\open-zeppelin-contracts\SafeERC20.sol

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

    using AddressUpgradeable for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require((value == 0) || (token.allowance(address(this), spender) == 0), "SafeERC20: approve from non-zero to non-zero allowance");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.
        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }

}


// File: contracts\open-zeppelin-contracts\IERC20.sol

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {

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

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns(uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns(uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns(bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns(uint256);

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
    function approve(address spender, uint256 amount) external returns(bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 amount) external returns(bool);

}


// File: contracts\open-zeppelin-contracts\ILiquidityProvider.sol

interface ILiquidityProvider {

    function apis(uint256) external view returns(address, address, address);

    function addExchange(IPancakeRouter02) external;

    function addLiquidityETH(address, address, uint256, uint256, uint256, uint256, uint256) external payable returns(uint256);

    function addLiquidityETHByPair(IPancakeswapPair, address, uint256, uint256, uint256, uint256, uint256) external payable returns(uint256);

    function addLiquidity(address, address, uint256, uint256, uint256, uint256, address, uint256, uint256) external payable returns(uint256);

    function addLiquidityByPair(IPancakeswapPair, uint256, uint256, uint256, uint256, address, uint256, uint256) external payable returns(uint256);

    function removeLiquidityETH(address, uint256, uint256, uint256, uint256, address, uint256, uint256, uint8) external returns(uint256[3] memory);

    function removeLiquidityETHByPair(IPancakeswapPair, uint256, uint256, uint256, uint256, address, uint256, uint256, uint8) external returns(uint256[3] memory);

    function removeLiquidityETHWithPermit(address, uint256, uint256, uint256, uint256, address, uint256, uint256, uint8, uint8, bytes32, bytes32) external returns(uint256[3] memory);

    function removeLiquidity(address, address, uint256, uint256[2] memory, uint256[2] memory, address, uint256, uint256, uint8) external returns(uint256[3] memory);

    function removeLiquidityByPair(IPancakeswapPair, uint256, uint256[2] memory, uint256[2] memory, address, uint256, uint256, uint8) external returns(uint256[3] memory);

    function removeLiquidityWithPermit(address, address, uint256, uint256[2] memory, uint256[2] memory, address, uint256, uint256, uint8, uint8, bytes32, bytes32) external returns(uint256[3] memory);

}


// File: contracts\open-zeppelin-contracts\IBuyBack.sol

interface IBuyBack {

    function buyAndBurnToken(address, uint256, address, uint256, uint256) external returns(uint256);

}


// File: contracts\open-zeppelin-contracts\IFitMLM.sol

interface IFitMLM {

    function isOnFitMLM(address) external view returns(bool);

    function addFitMLM(address, uint256) external;

    function distributeRewards(uint256, address, address) external;

    function updateInvestment(address _user, uint256 _newInvestment) external;

    function investment(address _user) external returns(uint256);

}


// File: contracts\open-zeppelin-contracts\IWETH.sol

interface IWETH {

    event Deposit(address indexed dst, uint256 wad);
    event Withdrawal(address indexed src, uint256 wad);

    function deposit() external payable;

    function withdraw(uint256 wad) external;

    function transfer(address dst, uint256 wad) external;

    function balanceOf(address dst) external view returns(uint256);

}


// File: contracts\open-zeppelin-contracts\IStrategy.sol

interface IStrategy {

    // Total want tokens managed by strategy
    function wantLockedTotal() external view returns(uint256);

    // Sum of all shares of users to wantLockedTotal
    function sharesTotal() external view returns(uint256);

    function wantAddress() external view returns(address);

    function token0Address() external view returns(address);

    function token1Address() external view returns(address);

    function earnedAddress() external view returns(address);

    function ratio0() external view returns(uint256);

    function ratio1() external view returns(uint256);

    function getPricePerFullShare() external view returns(uint256);

    // Main want token compounding function
    function earn(uint256 _amountOutAmt, uint256 _deadline) external;

    // Transfer want tokens autoFarm -> strategy
    function deposit(address _userAddress, uint256 _wantAmt) external returns(uint256);

    // Transfer want tokens strategy -> autoFarm
    function withdraw(address _userAddress, uint256 _wantAmt) external returns(uint256);

    function migrateFrom(address _oldStrategy, uint256 _oldWantLockedTotal, uint256 _oldSharesTotal) external;

    function inCaseTokensGetStuck(address _token, uint256 _amount, address _to) external;

}


// File: contracts\open-zeppelin-contracts\IPancakeswapPair.sol

interface IPancakeswapPair {

    function balanceOf(address owner) external view returns(uint256);

    function token0() external view returns(address);

    function token1() external view returns(address);

}


// File: contracts\open-zeppelin-contracts\IPancakeRouter01.sol

interface IPancakeRouter01 {

    function factory() external pure returns(address);

    function WETH() external pure returns(address);

    function addLiquidity(address tokenA, address tokenB, uint256 amountADesired, uint256 amountBDesired, uint256 amountAMin, uint256 amountBMin, address to, uint256 deadline) external returns(uint256 amountA, uint256 amountB, uint256 liquidity);

    function addLiquidityETH(address token, uint256 amountTokenDesired, uint256 amountTokenMin, uint256 amountETHMin, address to, uint256 deadline) external payable returns(uint256 amountToken, uint256 amountETH, uint256 liquidity);

    function removeLiquidity(address tokenA, address tokenB, uint256 liquidity, uint256 amountAMin, uint256 amountBMin, address to, uint256 deadline) external returns(uint256 amountA, uint256 amountB);

    function removeLiquidityETH(address token, uint256 liquidity, uint256 amountTokenMin, uint256 amountETHMin, address to, uint256 deadline) external returns(uint256 amountToken, uint256 amountETH);

    function removeLiquidityWithPermit(address tokenA, address tokenB, uint256 liquidity, uint256 amountAMin, uint256 amountBMin, address to, uint256 deadline, bool approveMax, uint8 v, bytes32 r, bytes32 s) external returns(uint256 amountA, uint256 amountB);

    function removeLiquidityETHWithPermit(address token, uint256 liquidity, uint256 amountTokenMin, uint256 amountETHMin, address to, uint256 deadline, bool approveMax, uint8 v, bytes32 r, bytes32 s) external returns(uint256 amountToken, uint256 amountETH);

    function swapExactTokensForTokens(uint256 amountIn, uint256 amountOutMin, address[] calldata path, address to, uint256 deadline) external returns(uint256[] memory amounts);

    function swapTokensForExactTokens(uint256 amountOut, uint256 amountInMax, address[] calldata path, address to, uint256 deadline) external returns(uint256[] memory amounts);

    function swapExactETHForTokens(uint256 amountOutMin, address[] calldata path, address to, uint256 deadline) external payable returns(uint256[] memory amounts);

    function swapTokensForExactETH(uint256 amountOut, uint256 amountInMax, address[] calldata path, address to, uint256 deadline) external returns(uint256[] memory amounts);

    function swapExactTokensForETH(uint256 amountIn, uint256 amountOutMin, address[] calldata path, address to, uint256 deadline) external returns(uint256[] memory amounts);

    function swapETHForExactTokens(uint256 amountOut, address[] calldata path, address to, uint256 deadline) external payable returns(uint256[] memory amounts);

    function quote(uint256 amountA, uint256 reserveA, uint256 reserveB) external pure returns(uint256 amountB);

    function getAmountOut(uint256 amountIn, uint256 reserveIn, uint256 reserveOut) external pure returns(uint256 amountOut);

    function getAmountIn(uint256 amountOut, uint256 reserveIn, uint256 reserveOut) external pure returns(uint256 amountIn);

    function getAmountsOut(uint256 amountIn, address[] calldata path) external view returns(uint256[] memory amounts);

    function getAmountsIn(uint256 amountOut, address[] calldata path) external view returns(uint256[] memory amounts);

}


// File: contracts\open-zeppelin-contracts\IPancakeRouter02.sol

interface IPancakeRouter02 is IPancakeRouter01 {

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(uint256 amountIn, uint256 amountOutMin, address[] calldata path, address to, uint256 deadline) external;

    function swapExactETHForTokensSupportingFeeOnTransferTokens(uint256 amountOutMin, address[] calldata path, address to, uint256 deadline) external payable;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(uint256 amountIn, uint256 amountOutMin, address[] calldata path, address to, uint256 deadline) external;

}


// File: contracts\open-zeppelin-contracts\Initializable.sol

/**
 * @dev This is a base contract to aid in writing upgradeable contracts, or any kind of contract that will be deployed
 * behind a proxy. Since proxied contracts do not make use of a constructor, it's common to move constructor logic to an
 * external initializer function, usually called `initialize`. It then becomes necessary to protect this initializer
 * function so it can only be called once. The {initializer} modifier provided by this contract will have this effect.
 *
 * TIP: To avoid leaving the proxy in an uninitialized state, the initializer function should be called as early as
 * possible by providing the encoded function call as the `_data` argument to {ERC1967Proxy-constructor}.
 *
 * CAUTION: When used with inheritance, manual care must be taken to not invoke a parent initializer twice, or to ensure
 * that all initializers are idempotent. This is not verified automatically as constructors are by Solidity.
 *
 * [CAUTION]
 * ====
 * Avoid leaving a contract uninitialized.
 *
 * An uninitialized contract can be taken over by an attacker. This applies to both a proxy and its implementation
 * contract, which may impact the proxy. To initialize the implementation contract, you can either invoke the
 * initializer manually, or you can include a constructor to automatically mark it as initialized when it is deployed:
 *
 * [.hljs-theme-light.nopadding]
 * ```
 * /// @custom:oz-upgrades-unsafe-allow constructor
 * constructor() initializer {}
 * ```
 * ====
 */
abstract contract Initializable {

    /**
     * @dev Indicates that the contract has been initialized.
     */
    bool private _initialized;
    /**
     * @dev Indicates that the contract is in the process of being initialized.
     */
    bool private _initializing;

    /**
     * @dev Modifier to protect an initializer function from being invoked twice.
     */
    modifier initializer() {
        // If the contract is initializing we ignore whether _initialized is set in order to support multiple
        // inheritance patterns, but we only do this in the context of a constructor, because in other contexts the
        // contract may have been reentered.
        require(_initializing ? _isConstructor() : !_initialized, "Initializable: contract is already initialized");
        bool isTopLevelCall = !_initializing;
        if (isTopLevelCall) {
            _initializing = true;
            _initialized = true;
        }
        _;
        if (isTopLevelCall) {
            _initializing = false;
        }
    }
    /**
     * @dev Modifier to protect an initialization function so that it can only be invoked by functions with the
     * {initializer} modifier, directly or indirectly.
     */
    modifier onlyInitializing() {
        require(_initializing, "Initializable: contract is not initializing");
        _;
    }

    function _isConstructor() private view returns(bool) {
        return !AddressUpgradeable.isContract(address(this));
    }

}


// File: contracts\open-zeppelin-contracts\ContextUpgradeable.sol

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract ContextUpgradeable is Initializable {

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;

    function __Context_init() internal onlyInitializing {}

    function __Context_init_unchained() internal onlyInitializing {}

    function _msgSender() internal view virtual returns(address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns(bytes calldata) {
        return msg.data;
    }

}


// File: contracts\open-zeppelin-contracts\OwnableUpgradeable.sol

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
abstract contract OwnableUpgradeable is Initializable, ContextUpgradeable {

    address private _owner;

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[49] private __gap;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    function __Ownable_init() internal onlyInitializing {
        __Ownable_init_unchained();
    }

    function __Ownable_init_unchained() internal onlyInitializing {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns(address) {
        return _owner;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }

}


// File: contracts\open-zeppelin-contracts\ReentrancyGuardUpgradeable.sol

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuardUpgradeable is Initializable {

    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.
    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;
    uint256 private _status;
    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[49] private __gap;
    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */

    modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");
        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;
        _;
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }

    function __ReentrancyGuard_init() internal onlyInitializing {
        __ReentrancyGuard_init_unchained();
    }

    function __ReentrancyGuard_init_unchained() internal onlyInitializing {
        _status = _NOT_ENTERED;
    }

}


// File: contracts\open-zeppelin-contracts\NetFitFarming.sol

contract NetFitFarming is OwnableUpgradeable, ReentrancyGuardUpgradeable {

    using SafeERC20 for IERC20;

    /**
     * @notice Info of each user
     * @param amount: How many LP tokens the user has provided
     * @param rewardDebt: Reward debt. See explanation below
     */
    struct UserInfo {
        uint256 amount;
        uint256 rewardDebt;
    }
    /**
     * @notice Info of each pool
     * @param lpToken: Address of LP token contract
     * @param allocPoint: How many allocation points assigned to this pool. rewards to distribute per block
     * @param lastRewardBlock: Last block number that rewards distribution occurs
     * @param accRewardPerShare: Accumulated rewards per share, times 1e18. See below
     */
    struct PoolInfo {
        IERC20 lpToken; // Address of LP token contract.
        uint256 allocPoint; // How many allocation points assigned to this pool. rewards to distribute per block.
        uint256 lastRewardBlock; // Last block number that rewards distribution occurs.
        uint256 accRewardPerShare; // Accumulated rewards per share, times 1e18. See below.
    }

    uint256 public rewardPerBlock;
    /// Total allocation poitns. Must be the sum of all allocation points in all pools.
    uint256 public totalAllocPoint;
    /// The block number when reward mining starts.
    uint256 public startBlock;
    uint256 public liquidityProviderApiId;
    uint256 private rewardPerBlockChangesCount;
    uint256 private lastChangeBlock;
    uint256 public buyBackComission;
    uint256 public affilateComission;
    uint256 public poolComission;

    /// The reward token
    IERC20 public rewardToken;
    /// Info of each pool.
    PoolInfo[] public poolInfo;
    /// The Liquidity Provider
    ILiquidityProvider public liquidityProvider;

    address public bankAddress;
    address public ROUTER_ADDRESS;
    address public wbnbAddress;
    address public treasury;
    address public buyBack;
    address[] public rewardTokenToWBNB;
    address public relationship;

    /// Info of each user that stakes LP tokens.
    mapping(uint256 => mapping(address => UserInfo)) public userInfo;
    mapping(address => bool) public isPoolExist;

    event Deposit(address indexed user, uint256 indexed pid, uint256 amount);
    event Harvest(address indexed user, uint256 indexed pid, uint256 amount);
    event Withdraw(address indexed user, uint256 indexed pid, uint256 amount);
    event Provider(address oldProvider, uint256 oldApi, address newProvider, uint256 newApi);

    modifier poolExists(uint256 _pid) {
        require(_pid < poolInfo.length, "FitFarming::UNKNOWN_POOL");
        _;
    }
    modifier onlyBank() {
        require(msg.sender == bankAddress, "FitFarming:: Only bank");
        _;
    }

    function initialize(address _bankAddress, address _rewardToken, uint256 _rewardPerBlock, uint256 _startBlock) public initializer {
        __Ownable_init();
        __ReentrancyGuard_init();
        require(address(_rewardToken) != address(0x0), "FitFarming::SET_ZERO_ADDRESS");
        bankAddress = _bankAddress;
        rewardToken = IERC20(_rewardToken);
        rewardPerBlock = _rewardPerBlock;
        startBlock = _startBlock;
        rewardPerBlockChangesCount = 3;
        lastChangeBlock = _startBlock;
        buyBackComission = 4;
        buyBack = 0xB353eAAf9D16b7F482087816f281415fe292dE5c;  // BuyBack-contract_addr
        ROUTER_ADDRESS = 0x10ED43C718714eb63d5aA57B78B54704E256024E;  // PancakeRouter-contract_addr
        wbnbAddress = address(0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c);  // WBNB-contract_addr
        liquidityProvider = ILiquidityProvider(0x2B1C93fFfF55E2620D6fb5DaD7D69A6a468C9731);  // AdminUpgradeabilityProxy-contract_addr
        liquidityProviderApiId = 1;
        rewardTokenToWBNB = [_rewardToken, wbnbAddress];
    }

    receive() external payable {}

    fallback() external payable {}

    /// @return All pools amount
    function poolLength() external view returns(uint256) {
        return poolInfo.length;
    }

    /**
     * @notice View function to see total pending rewards on frontend
     * @param _user: user address for which reward must be calculated
     * @return total Return reward for user
     */
    function pendingRewardTotal(address _user) external view returns(uint256 total) {
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            total += pendingReward(pid, _user);
        }
    }

    /**
     * @notice Function to set reward token
     * @param _rewardToken: address of reward token
     */
    function setRewardToken(address _rewardToken) external onlyOwner {
        rewardToken = IERC20(_rewardToken);
        rewardTokenToWBNB = [_rewardToken, wbnbAddress];
    }

    /**
     * @notice Function to set comission on claim
     * @param _comission: value between 0 and 80
     */
    function setAffilateComission(uint256 _comission) external onlyOwner {
        require(_comission < 80, "Max comission 80%");
        affilateComission = _comission;
    }

    /**
     * @notice Function to set comission on claim
     * @param _comission: value between 0 and 80
     */
    function setPoolComission(uint256 _comission) external onlyOwner {
        require(_comission < 80, "Max comission 80%");
        poolComission = _comission;
    }

    function setMLMAddress(address _address) external onlyOwner {
        relationship = _address;
    }

    /**
     * @notice Function to set treasury
     * @param _newTreasury: new treasury address
     */
    function setTreasuryAddress(address _newTreasury) external onlyOwner {
        treasury = _newTreasury;
    }

    /**
     * @notice Function to set amount of reward per block
     */
    function setRewardPerBlock() external nonReentrant {
        massUpdatePools();
        if (block.number - lastChangeBlock > 20 && rewardPerBlockChangesCount > 0) {
            rewardPerBlock = (rewardPerBlock * 967742000000) / 1e12;
            rewardPerBlockChangesCount -= 1;
            lastChangeBlock = block.number;
        }
    }

    /**
     * @param _from: block block from which the reward is calculated
     * @param _to: block block before which the reward is calculated
     * @return Return reward multiplier over the given _from to _to block
     */
    function getMultiplier(uint256 _from, uint256 _to) public view returns(uint256) {
        return (rewardPerBlock * (_to - _from));
    }

    /**
     * @notice View function to see pending rewards on frontend
     * @param _pid: pool ID for which reward must be calculated
     * @param _user: user address for which reward must be calculated
     * @return Return reward for user
     */
    function pendingReward(uint256 _pid, address _user) public view poolExists(_pid) returns(uint256) {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][_user];
        uint256 accRewardPerShare = pool.accRewardPerShare;
        uint256 lpSupply = pool.lpToken.balanceOf(address(this));
        if (block.number > pool.lastRewardBlock && lpSupply != 0) {
            uint256 multiplier = getMultiplier(pool.lastRewardBlock, block.number);
            uint256 reward = (multiplier * pool.allocPoint) / totalAllocPoint;
            accRewardPerShare = accRewardPerShare + ((reward * 1e18) / lpSupply);
        }
        return (user.amount * accRewardPerShare) / 1e18 - user.rewardDebt;
    }

    /**
     * @notice Add a new lp to the pool. Can only be called by the owner
     * @param _allocPoint: allocPoint for new pool
     * @param _lpToken: address of lpToken for new pool
     * @param _withUpdate: if true, update all pools
     */
    function add(uint256 _allocPoint, IERC20 _lpToken, bool _withUpdate) public onlyOwner {
        require(!isPoolExist[address(_lpToken)], "FitFarming::DUPLICATE_POOL");
        if (_withUpdate) {
            massUpdatePools();
        }
        uint256 lastRewardBlock = block.number > startBlock ? block.number : startBlock;
        totalAllocPoint += _allocPoint;
        poolInfo.push(
            PoolInfo({
                lpToken: _lpToken,
                allocPoint: _allocPoint,
                lastRewardBlock: lastRewardBlock,
                accRewardPerShare: 0
            })
        );
        isPoolExist[address(_lpToken)] = true;
    }

    /**
     * @notice Update the given pool's reward allocation point. Can only be called by the owner
     */
    function set(uint256 _pid, uint256 _allocPoint, bool _withUpdate) public onlyOwner poolExists(_pid) {
        if (_withUpdate) {
            massUpdatePools();
        }
        totalAllocPoint = totalAllocPoint - poolInfo[_pid].allocPoint + _allocPoint;
        poolInfo[_pid].allocPoint = _allocPoint;
    }

    /**
     * @notice Function which take ETH and tokens, add liquidity with provider and deposit given LP's
     * @param _pid: pool ID where we want deposit
     * @param _tokenAmount: amount of tokens for staking
     * @param _amountAMin: bounds the extent to which the B/A price can go up before the transaction reverts.
        Must be <= amountADesired.
     * @param _amountBMin: bounds the extent to which the A/B price can go up before the transaction reverts.
        Must be <= amountBDesired
     * @param _minAmountOutA: the minimum amount of output A tokens that must be received
        for the transaction not to revert
     */
    function speedStake(uint256 _pid, uint256 _tokenAmount, uint256 _amountAMin, uint256 _amountBMin, uint256 _minAmountOutA, uint256 _deadline, uint256 _minBurnAmt) public payable poolExists(_pid) {
        IPancakeRouter02 router = IPancakeRouter02(ROUTER_ADDRESS);
        updatePool(_pid);
        IPancakeswapPair lpToken = IPancakeswapPair(address(poolInfo[_pid].lpToken));
        require((lpToken.token0() == router.WETH()) || (lpToken.token1() == router.WETH()), "Wrong poolID");
        uint256 bnbAmount = msg.value;
        if (_tokenAmount > 0) {
            IERC20 token = IERC20(lpToken.token0());
            if (lpToken.token0() == router.WETH()) {
                token = IERC20(lpToken.token1());
            }
            address[] memory path = new address[](2);
            path[0] = address(token);
            path[1] = wbnbAddress;
            token.safeTransferFrom(msg.sender, address(this), _tokenAmount);
            token.approve(ROUTER_ADDRESS, _tokenAmount);
            uint256[] memory swapResult = router.swapExactTokensForETH(_tokenAmount, 0, path, address(this), _deadline);
            bnbAmount += swapResult[1];
        }
        IWETH(wbnbAddress).deposit {
            value: (bnbAmount * buyBackComission) / 100
        }();
        IERC20(wbnbAddress).safeTransfer(buyBack, (bnbAmount * buyBackComission) / 100);
        IBuyBack(buyBack).buyAndBurnToken(wbnbAddress, bnbAmount * buyBackComission / 100, address(rewardToken), _minBurnAmt, _deadline);
        bnbAmount = address(this).balance;
        uint256 lp = liquidityProvider.addLiquidityETHByPair {
            value: bnbAmount
        }(lpToken, address(this), _amountAMin, _amountBMin, _minAmountOutA, _deadline, liquidityProviderApiId);
        _deposit(_pid, lp, msg.sender);
    }

    /**
     * @notice Update reward vairables for all pools
     */
    function massUpdatePools() public {
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            updatePool(pid);
        }
    }

    /**
     * @notice Update reward variables of the given pool to be up-to-date
     * @param _pid: pool ID for which the reward variables should be updated
     */
    function updatePool(uint256 _pid) public {
        PoolInfo storage pool = poolInfo[_pid];
        if (block.number <= pool.lastRewardBlock) {
            return;
        }
        uint256 lpSupply = pool.lpToken.balanceOf(address(this));
        if (lpSupply == 0) {
            pool.lastRewardBlock = block.number;
            return;
        }
        uint256 multiplier = getMultiplier(pool.lastRewardBlock, block.number);
        uint256 reward = (multiplier * pool.allocPoint) / totalAllocPoint;
        pool.accRewardPerShare = pool.accRewardPerShare + ((reward * 1e18) / lpSupply);
        pool.lastRewardBlock = block.number;
    }

    /**
     * @notice Deposit LP tokens to FitFarming for reward allocation
     * @param _pid: pool ID on which LP tokens should be deposited
     * @param _amount: the amount of LP tokens that should be deposited
     */
    function deposit(uint256 _pid, uint256 _amount) public poolExists(_pid) {
        updatePool(_pid);
        poolInfo[_pid].lpToken.safeTransferFrom(msg.sender, address(this), _amount);
        _deposit(_pid, _amount, msg.sender);
    }

    function claimAndDeposit(uint256 _pid, uint256 _amountAMin, uint256 _amountBMin, uint256 _minAmountOutA, uint256 _deadline, uint256 _minBurnAmt) external payable poolExists(_pid) {
        UserInfo storage user = userInfo[_pid][msg.sender];
        IPancakeRouter02 router = IPancakeRouter02(ROUTER_ADDRESS);
        uint256 bnbAmount = msg.value;
        IWETH(wbnbAddress).deposit {
            value: (bnbAmount * buyBackComission) / 100
        }();
        IERC20(wbnbAddress).safeTransfer(buyBack, (bnbAmount * buyBackComission) / 100);
        IBuyBack(buyBack).buyAndBurnToken(wbnbAddress, bnbAmount * buyBackComission / 100, address(rewardToken), _minBurnAmt, _deadline);
        bnbAmount = address(this).balance;
        if (user.amount > 0) {
            updatePool(_pid);
            uint256 accRewardPerShare = poolInfo[_pid].accRewardPerShare;
            uint256 pending = (user.amount * accRewardPerShare) / 1e18 - user.rewardDebt;
            user.rewardDebt = (user.amount * accRewardPerShare) / 1e18;
            rewardToken.approve(ROUTER_ADDRESS, pending);
            uint256[] memory swapResult = router.swapExactTokensForETH(pending, 0, rewardTokenToWBNB, address(this), _deadline);
            bnbAmount += swapResult[1];
        }
        uint256 lp = liquidityProvider.addLiquidityETHByPair {
            value: bnbAmount
        }(
            IPancakeswapPair(address(poolInfo[_pid].lpToken)), address(this), _amountAMin, _amountBMin, _minAmountOutA, _deadline, liquidityProviderApiId);
        _deposit(_pid, lp, msg.sender);
    }

    /**
     * @notice Deposit LP tokens to FitFarming from FitVaultsBank
     * @param _pid: pool ID on which LP tokens should be deposited
     * @param _amount: the amount of reward tokens that should be converted to LP tokens and deposits to FitFarming contract
     * @param _from: Address of user that called function from FitVaultsBank
     */
    function autoDeposit(uint256 _pid, uint256 _amount, uint256 _amountTokenMin, uint256 _amountETHMin, uint256 _minAmountOut, address _from, uint256 _deadline) public payable poolExists(_pid) onlyBank {
        updatePool(_pid);
        rewardToken.transferFrom(msg.sender, address(this), _amount);
        uint256 contractbalance = address(this).balance - msg.value;
        rewardToken.approve(ROUTER_ADDRESS, _amount);
        IPancakeRouter02(ROUTER_ADDRESS).swapExactTokensForETHSupportingFeeOnTransferTokens(_amount, _amountETHMin, rewardTokenToWBNB, address(this), _deadline);
        uint256 balanceDifference = address(this).balance - contractbalance;
        uint256 lp = liquidityProvider.addLiquidityETH {
            value: balanceDifference
        }(address(rewardToken), address(this), _amountTokenMin, _amountETHMin, _minAmountOut, _deadline, liquidityProviderApiId);
        _deposit(_pid, lp, _from);
    }

    /**
     * @notice Function which send accumulated reward tokens to messege sender
     * @param _pid: pool ID from which the accumulated reward tokens should be received
     */
    function harvest(uint256 _pid) public poolExists(_pid) {
        _harvest(_pid, msg.sender);
    }

    /**
     * @notice Function which send accumulated reward tokens to messege sender from all pools
     */
    function harvestAll() public {
        uint256 length = poolInfo.length;
        for (uint256 i = 0; i < length; i++) {
            if (poolInfo[i].allocPoint > 0) {
                harvest(i);
            }
        }
    }

    /**
     * @notice Function which withdraw LP tokens to messege sender with the given amount
     * @param _pid: pool ID from which the LP tokens should be withdrawn
     * @param _amount: the amount of LP tokens that should be withdrawn
     */
    function withdraw(uint256 _pid, uint256 _amount) public poolExists(_pid) {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][msg.sender];
        require(user.amount >= _amount, "withdraw: not good");
        updatePool(_pid);
        uint256 pending = (user.amount * pool.accRewardPerShare) / 1e18 - user.rewardDebt;
        safeRewardTransfer(msg.sender, pending);
        emit Harvest(msg.sender, _pid, pending);
        user.amount -= _amount;
        user.rewardDebt = (user.amount * pool.accRewardPerShare) / 1e18;
        pool.lpToken.safeTransfer(address(msg.sender), _amount);
        emit Withdraw(msg.sender, _pid, _amount);
    }

    /**
     * @notice Function which transfer reward tokens to _to with the given amount
     * @param _to: transfer reciver address
     * @param _amount: amount of reward token which should be transfer
     */
    function safeRewardTransfer(address _to, uint256 _amount) internal {
        if (_amount > 0) {
            uint256 rewardTokenBal = rewardToken.balanceOf(address(this));
            if (_amount > rewardTokenBal) {
                uint256 comission = rewardTokenBal * affilateComission / 100;
                rewardToken.transfer(relationship, comission);
                IFitMLM(relationship).distributeRewards(rewardTokenBal, address(rewardToken), msg.sender);
                uint256 poolComissionAmount = rewardTokenBal * poolComission / 100;
                rewardToken.transfer(treasury, poolComissionAmount);
                rewardToken.transfer(_to, (rewardTokenBal - comission));
            } else {
                uint256 comission = _amount * affilateComission / 100;
                rewardToken.transfer(relationship, comission);
                IFitMLM(relationship).distributeRewards(_amount, address(rewardToken), msg.sender);
                uint256 poolComissionAmount = _amount * poolComission / 100;
                rewardToken.transfer(treasury, poolComissionAmount);
                rewardToken.transfer(_to, (_amount - comission));
            }
        }
    }

    /**
     * @notice Function for updating user info
     */
    function _deposit(uint256 _pid, uint256 _amount, address _from) private {
        UserInfo storage user = userInfo[_pid][_from];
        _harvest(_pid, _from);
        user.amount += _amount;
        user.rewardDebt = (user.amount * poolInfo[_pid].accRewardPerShare) / 1e18;
        emit Deposit(_from, _pid, _amount);
    }

    /**
     * @notice Private function which send accumulated reward tokens to givn address
     * @param _pid: pool ID from which the accumulated reward tokens should be received
     * @param _from: Recievers address
     */
    function _harvest(uint256 _pid, address _from) private poolExists(_pid) {
        UserInfo storage user = userInfo[_pid][_from];
        if (user.amount > 0) {
            updatePool(_pid);
            uint256 accRewardPerShare = poolInfo[_pid].accRewardPerShare;
            uint256 pending = (user.amount * accRewardPerShare) / 1e18 - user.rewardDebt;
            safeRewardTransfer(_from, pending);
            user.rewardDebt = (user.amount * accRewardPerShare) / 1e18;
            emit Harvest(_from, _pid, pending);
        }
    }

}
