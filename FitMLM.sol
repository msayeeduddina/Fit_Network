// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

import "hardhat/console.sol";


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


// File: contracts\open-zeppelin-contracts\IWETH.sol

interface IWETH {

    event Deposit(address indexed dst, uint256 wad);
    event Withdrawal(address indexed src, uint256 wad);

    function deposit() external payable;

    function withdraw(uint256 wad) external;

    function transfer(address dst, uint256 wad) external;

    function balanceOf(address dst) external view returns(uint256);

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


// File: contracts\open-zeppelin-contracts\FitMLM.sol

contract FitMLM is OwnableUpgradeable {

    uint256 public currentId;
    uint256 public oldUserTransferTimestampLimit;
    uint256[16] public directReferralBonuses;
    uint256[16] public levels;
    uint256[16] public oldUserLevels;

    address public bankAddress;
    address public farming;

    mapping(address => uint256) public addressToId;
    mapping(uint256 => address) public idToAddress;
    mapping(address => uint256) public investment;
    mapping(address => address) public userToReferrer;
    mapping(address => uint256) public scoring;
    mapping(address => uint256) public firstDepositTimestamp;

    event NewReferral(address indexed user, address indexed referral);
    event ReferralRewardReceived(address indexed user, address indexed referral, uint256 level, uint256 amount, address wantAddress);

    modifier onlyBank() {
        require(msg.sender == bankAddress || msg.sender == farming, "FitMLM:: Only bank");
        _;
    }

    function initialize() external initializer {
        directReferralBonuses = [1000, 700, 500, 400, 400, 300, 100, 100, 100, 50, 50, 50, 50, 50, 25, 25];
        addressToId[0x49A6DaD36768c23eeb75BD253aBBf26AB38BE4EB] = 1;
        idToAddress[1] = 0x49A6DaD36768c23eeb75BD253aBBf26AB38BE4EB;
        userToReferrer[0x49A6DaD36768c23eeb75BD253aBBf26AB38BE4EB] = 0x49A6DaD36768c23eeb75BD253aBBf26AB38BE4EB;
        currentId = 2;
        levels = [0.05 ether, 0.1 ether, 0.25 ether, 0.5 ether, 1 ether, 3 ether, 5 ether, 10 ether, 15 ether, 25 ether, 30 ether, 35 ether, 40 ether, 70 ether, 100 ether, 200 ether];
        oldUserLevels = [0 ether, 0.045 ether, 0.045 ether, 0.045 ether, 0.045 ether, 0.045 ether, 1.35 ether, 4.5 ether, 9 ether, 13.5 ether, 22.5 ether, 27 ether, 31.5 ether, 36 ether, 45 ether, 90 ether];
        __Ownable_init();
    }

    receive() external payable {}

    fallback() external payable {}

    function updateScoring(address _token, uint256 _score) external onlyOwner {
        scoring[_token] = _score;
    }

    function _addUser(address _user, address _referrer) private {
        addressToId[_user] = currentId;
        idToAddress[currentId] = _user;
        userToReferrer[_user] = _referrer;
        currentId++;
        emit NewReferral(_referrer, _user);
    }

    /**
     * @notice  Function to add FitMLM
     * @param _user Address of user
     * @param _referrerId Address of referrer
     */
    function addFitMLM(address _user, uint256 _referrerId) external onlyBank {
        address _referrer = userToReferrer[_user];
        if (_referrer == address(0)) {
            _referrer = idToAddress[_referrerId];
        }
        require(_user != address(0), "FitMLM::user is zero address");
        require(_referrer != address(0), "FitMLM::referrer is zero address");
        require(userToReferrer[_user] == address(0) || userToReferrer[_user] == _referrer, "FitMLM::referrer is zero address");
        // If user didn't exsist before
        if (addressToId[_user] == 0) {
            _addUser(_user, _referrer);
        }
    }

    /**
     * @notice  Function to distribute rewards to referrers
     * @param _wantAmt Amount of assets that will be distributed
     * @param _wantAddr Address of want token contract
     * @param _user Address of user
     */
    function distributeRewards(uint256 _wantAmt, address _wantAddr, address _user) public onlyBank {
        uint256 index;
        uint256 length = directReferralBonuses.length;
        IERC20 token = IERC20(_wantAddr);
        while (index < length && addressToId[userToReferrer[_user]] != 1) {
            address referrer = userToReferrer[_user];
            uint256 levellimit = firstDepositTimestamp[referrer] != 0 && firstDepositTimestamp[referrer] < oldUserTransferTimestampLimit ? oldUserLevels[index] : levels[index];
            if (investment[referrer] >= levellimit) {
                uint256 reward = (_wantAmt * directReferralBonuses[index]) / 10000;
                token.transfer(referrer, reward);
                emit ReferralRewardReceived(referrer, _user, index, reward, _wantAddr);
            }
            _user = userToReferrer[_user];
            index++;
        }
        if (token.balanceOf(address(this)) > 0) {
            token.transfer(bankAddress, token.balanceOf(address(this)));
        }
        return;
    }

    function setBankAddress(address _bank) external onlyOwner {
        bankAddress = _bank;
    }

    function setOldUserTransferTimestampLimit(uint256 _limit) external onlyOwner {
        oldUserTransferTimestampLimit = _limit;
    }

    function setFarmingAddress(address _address) external onlyOwner {
        farming = _address;
    }

    function seedUsers(address[] memory _users, address[] memory _referrers) external onlyOwner {
        require(_users.length == _referrers.length, "Length mismatch");
        for (uint256 i; i < _users.length; i++) {
            addressToId[_users[i]] = currentId;
            idToAddress[currentId] = _users[i];
            userToReferrer[_users[i]] = _referrers[i];
            currentId++;
            emit NewReferral(_referrers[i], _users[i]);
        }
    }

    function updateInvestment(address _user, uint256 _newInvestment) external onlyBank {
        if (firstDepositTimestamp[_user] == 0) firstDepositTimestamp[_user] = block.timestamp;
        investment[_user] = _newInvestment;
    }

}
