// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;


/////**{FitNet.sol}**/////

// File: contracts\open-zeppelin-contracts\Context.sol

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
abstract contract Context {

    function _msgSender() internal view virtual returns(address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns(bytes calldata) {
        return msg.data;
    }

}


// File: contracts\open-zeppelin-contracts\Ownable.sol

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
abstract contract Ownable is Context {

    address private _owner;

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
    constructor() {
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

//{FitNet.sol}
// File: contracts\open-zeppelin-contracts\FitNetwork.sol

contract FitNetwork is Ownable {

    /// @notice EIP-20 token name for this token
    string public constant name = "FIT NETWORK";
    /// @notice EIP-20 token symbol for this token
    string public constant symbol = "FITNET";

    /// @notice EIP-20 token decimals for this token
    uint8 public constant decimals = 18;
    /// @notice Percent amount of tax for the token trade on dex
    uint8 public devFundTax = 6;
    /// @notice Percent amount of tax for the token sell on dex
    uint8 public taxOnSell = 15; //org = 4
    /// @notice Percent amount of tax for the token purchase on dex
    uint8 public taxOnPurchase = 10; // org = 1
    /// @notice Total number of tokens in circulation
    uint96 public constant MAX_SUPPLY = 1000000000 ether;
    uint96 public totalSupply;
    uint96 public minted;
    /// @notice Percent of how much out of supply can be held by one address
    uint96 public constant MAX_PER_HOLDER_PERCENT = 3;
    /// @notice Max gas price allowed for FIT transaction
    uint256 public gasPriceLimit = 20000000000;
    /// @notice Period of 50% sell of limit (by default 24 hours)
    uint256 public limitPeriod = 86400;

    /// @notice Address of FIT Treasury
    address public managementAddress;
    address public sellTaxAddress;
    address public purchaseTaxAddress;
    address public routerAddress;

    /// @dev Allowance amounts on behalf of others
    mapping(address => mapping(address => uint96)) internal allowances;
    /// @dev Official record of token balances for each account
    mapping(address => uint96) internal balances;
    /// @notice A record of each accounts delegate
    mapping(address => address) public delegates;
    /// @notice A record of each DEX account
    mapping(address => bool) public isDex;
    /// @notice A record of whitelisted addresses allowed to hold more than maxPerHolder
    mapping(address => bool) private _isLimitExcempt;
    /// @notice A record of addresses disallowed to withdraw more than 50% within period
    mapping(address => bool) private _isSellLimited;
    /// @notice A record of addresses that are not taxed during trades
    mapping(address => bool) private _dexTaxExcempt;
    /// @notice A record of blacklisted addresses
    mapping(address => bool) private _isBlackListed;
    /// @notice A record of account withdrawals
    mapping(address => User) private _withdrawals;
    /// @notice A record of votes checkpoints for each account, by index
    mapping(address => mapping(uint32 => Checkpoint)) public checkpoints;
    /// @notice The number of checkpoints for each account
    mapping(address => uint32) public numCheckpoints;
    /// @notice A record of states for signing / validating signatures
    mapping(address => uint256) public nonces;

    /// @notice A switch which activates or deactivates sellLimit
    bool public sellLimitActive;
    bool public isTradingPaused;

    /// @notice A checkpoint for marking number of votes from a given block
    struct Checkpoint {
        uint32 fromBlock;
        uint96 votes;
    }
    /// @notice A checkpoint for outgoing transaction
    struct User {
        uint96[] withdrawalAmounts;
        uint256[] withdrawalTimestamps;
    }

    /// @notice The EIP-712 typehash for the contract's domain
    bytes32 public constant DOMAIN_TYPEHASH = keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)");
    /// @notice The EIP-712 typehash for the delegation struct used by the contract
    bytes32 public constant DELEGATION_TYPEHASH = keccak256("Delegation(address delegatee,uint256 nonce,uint256 expiry)");

    /// @notice An event thats emitted when an account changes its delegate
    event DelegateChanged(address indexed delegator, address indexed fromDelegate, address indexed toDelegate);
    /// @notice An event thats emitted when a delegate account's vote balance changes
    event DelegateVotesChanged(address indexed delegate, uint256 previousBalance, uint256 newBalance);
    /// @notice The standard EIP-20 transfer event
    event Transfer(address indexed from, address indexed to, uint256 amount);
    /// @notice The standard EIP-20 approval event
    event Approval(address indexed owner, address indexed spender, uint256 amount);

    /**
     * @notice Construct a new Fit token
     */
    constructor() {
        sellLimitActive = true;
        isTradingPaused = true;
        managementAddress = 0x5B38Da6a701c568545dCfcB03FcB875f56beddC4; // 0x7E8413065775E50b0B0717c46118b2E6C87E960A;
        sellTaxAddress = 0xAb8483F64d9C6d1EcF9b849Ae677dD3315835cb2; // 0xeF6afbb3e43A1289Bd6B96252D372058106042f6;
        purchaseTaxAddress = 0x4B20993Bc481177ec7E8f571ceCaE8A9e22C02db; // 0x9fAb63Fc64E7A6D7792Bcd995C734dc762DDB5b4;
        routerAddress = 0x78731D3Ca6b7E34aC0F824c42a7cC18A495cabaB; // 0x10ED43C718714eb63d5aA57B78B54704E256024E;
        _dexTaxExcempt[address(this)] = true;
        _dexTaxExcempt[routerAddress] = true;
        _isLimitExcempt[owner()] = true;
        _isSellLimited[owner()] = false;
    }

    /**
     * @notice Get the number of tokens `spender` is approved to spend on behalf of `account`
     * @param account The address of the account holding the funds
     * @param spender The address of the account spending the funds
     * @return The number of tokens approved
     */
    function allowance(address account, address spender) external view returns(uint256) {
        return allowances[account][spender];
    }

    /**
     * @notice Approve `spender` to transfer up to `amount` from `src`
     * @dev This will overwrite the approval amount for `spender`
     *  and is subject to issues noted [here](https://eips.ethereum.org/EIPS/eip-20#approve)
     * @param spender The address of the account which may transfer tokens
     * @param rawAmount The number of tokens that are approved (2^256-1 means infinite)
     * @return Whether or not the approval succeeded
     */
    function approve(address spender, uint256 rawAmount) public returns(bool) {
        uint96 amount;
        if (rawAmount == type(uint256).max) {
            amount = type(uint96).max;
        } else {
            amount = safe96(rawAmount, "FitToken::approve: amount exceeds 96 bits");
        }
        allowances[msg.sender][spender] = amount;
        emit Approval(msg.sender, spender, amount);
        return true;
    }

    /**
     * @notice Get the number of tokens held by the `account`
     * @param account The address of the account to get the balance of
     * @return The number of tokens held
     */
    function balanceOf(address account) public view returns(uint256) {
        return balances[account];
    }

    /**
     * @notice Transfer `amount` tokens from `msg.sender` to `dst`
     * @param dst The address of the destination account
     * @param rawAmount The number of tokens to transfer
     * @return Whether or not the transfer succeeded
     */
    function transfer(address dst, uint256 rawAmount) external returns(bool) {
        uint96 amount = safe96(rawAmount, "FitToken::transfer: amount exceeds 96 bits");
        _transferTokens(msg.sender, dst, amount);
        return true;
    }

    /**
     * @notice Transfer `amount` tokens from `src` to `dst`
     * @param src The address of the source account
     * @param dst The address of the destination account
     * @param rawAmount The number of tokens to transfer
     * @return Whether or not the transfer succeeded
     */
    function transferFrom(address src, address dst, uint256 rawAmount) external returns(bool) {
        address spender = msg.sender;
        uint96 spenderAllowance = allowances[src][spender];
        uint96 amount = safe96(rawAmount, "FitToken::approve: amount exceeds 96 bits");
        if (spender != src && spenderAllowance != type(uint96).max) {
            uint96 newAllowance = sub96(spenderAllowance, amount, "FitToken::transferFrom: transfer amount exceeds spender allowance");
            allowances[src][spender] = newAllowance;
            emit Approval(src, spender, newAllowance);
        }
        _transferTokens(src, dst, amount);
        return true;
    }

    /**
     * @notice Gets the current votes balance for `account`
     * @param account The address to get votes balance
     * @return The number of current votes for `account`
     */
    function getCurrentVotes(address account) external view returns(uint96) {
        uint32 nCheckpoints = numCheckpoints[account];
        return nCheckpoints > 0 ? checkpoints[account][nCheckpoints - 1].votes : 0;
    }

    /**
     * @notice Determine the prior number of votes for an account as of a block number
     * @dev Block number must be a finalized block or else this function will revert to prevent misinformation.
     * @param account The address of the account to check
     * @param blockNumber The block number to get the vote balance at
     * @return The number of votes the account had as of the given block
     */
    function getPriorVotes(address account, uint256 blockNumber) public view returns(uint96) {
        require(blockNumber < block.number, "FitToken::getPriorVotes: not yet determined");
        uint32 nCheckpoints = numCheckpoints[account];
        if (nCheckpoints == 0) {
            return 0;
        }
        // First check most recent balance
        if (checkpoints[account][nCheckpoints - 1].fromBlock <= blockNumber) {
            return checkpoints[account][nCheckpoints - 1].votes;
        }
        // Next check implicit zero balance
        if (checkpoints[account][0].fromBlock > blockNumber) {
            return 0;
        }
        uint32 lower = 0;
        uint32 upper = nCheckpoints - 1;
        while (upper > lower) {
            uint32 center = upper - (upper - lower) / 2; // ceil, avoiding overflow
            Checkpoint memory cp = checkpoints[account][center];
            if (cp.fromBlock == blockNumber) {
                return cp.votes;
            } else if (cp.fromBlock < blockNumber) {
                lower = center;
            } else {
                upper = center - 1;
            }
        }
        return checkpoints[account][lower].votes;
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the total supply.
     */
    function burn(uint256 rawAmount) public {
        uint96 amount = safe96(rawAmount, "FitToken::approve: amount exceeds 96 bits");
        _burn(msg.sender, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, deducting from the caller's
     * allowance.
     */
    function burnFrom(address account, uint256 rawAmount) public {
        uint96 amount = safe96(rawAmount, "FitToken::approve: amount exceeds 96 bits");
        uint96 currentAllowance = allowances[account][msg.sender];
        require(currentAllowance >= amount, "FitToken: burn amount exceeds allowance");
        allowances[account][msg.sender] = currentAllowance - amount;
        _burn(account, amount);
    }

    /**
     * @notice Delegate votes from `msg.sender` to `delegatee`
     * @param delegatee The address to delegate votes to
     */
    function delegate(address delegatee) public {
        return _delegate(msg.sender, delegatee);
    }

    /**
     * @notice Delegates votes from signatory to `delegatee`
     * @param delegatee The address to delegate votes to
     * @param nonce The contract state required to match the signature
     * @param expiry The time at which to expire the signature
     * @param v The recovery byte of the signature
     * @param r Half of the ECDSA signature pair
     * @param s Half of the ECDSA signature pair
     */
    function delegateBySig(address delegatee, uint256 nonce, uint256 expiry, uint8 v, bytes32 r, bytes32 s) public {
        bytes32 domainSeparator = keccak256(abi.encode(DOMAIN_TYPEHASH, keccak256(bytes(name)), getChainId(), address(this)));
        bytes32 structHash = keccak256(abi.encode(DELEGATION_TYPEHASH, delegatee, nonce, expiry));
        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));
        address signatory = ecrecover(digest, v, r, s);
        require(signatory != address(0), "FitToken::delegateBySig: invalid signature");
        require(nonce == nonces[signatory]++, "FitToken::delegateBySig: invalid nonce");
        require(block.timestamp <= expiry, "FitToken::delegateBySig: signature expired");
        return _delegate(signatory, delegatee);
    }

    function _delegate(address delegator, address delegatee) internal {
        address currentDelegate = delegates[delegator];
        uint96 delegatorBalance = balances[delegator];
        delegates[delegator] = delegatee;
        emit DelegateChanged(delegator, currentDelegate, delegatee);
        _moveDelegates(currentDelegate, delegatee, delegatorBalance);
    }

    function _burn(address account, uint96 amount) internal {
        require(account != address(0), "FitToken: burn from the zero address");
        balances[account] -= amount;
        totalSupply -= amount;
        emit Transfer(account, address(0), amount);
    }

    function _transferTokens(address src, address dst, uint96 amount) internal {
        require(src != address(0), "FitToken::_transferTokens: cannot transfer from the zero address");
        require(dst != address(0), "FitToken::_transferTokens: cannot transfer to the zero address");
        require(!_isBlackListed[src] && !_isBlackListed[dst], "FitToken::_transferTokens: cannot transfer to/from blacklisted account");
        require(tx.gasprice < gasPriceLimit, "FitToken::_transferTokens: gasprice limit");
        if (sellLimitActive && _isSellLimited[src]) {
            uint96 withdrawnAmount = _withdrawnLastPeriod(src);
            uint96 totalBalance = add96(balances[src], withdrawnAmount, "FitToken::_transferTokens: error with total balance");
            uint96 totalAmountToWithdraw = add96(amount, withdrawnAmount, "FitToken::_transferTokens: error with total balance");
            require(totalAmountToWithdraw < totalBalance / 2, "FitToken::_transferTokens: withdraw more than 50% of balance");
            _withdrawals[src].withdrawalTimestamps.push(block.timestamp);
            _withdrawals[src].withdrawalAmounts.push(amount);
        }
        uint96 maxPerHolder = (totalSupply * MAX_PER_HOLDER_PERCENT) / 100;
        if ((!isDex[dst] && !isDex[src]) || (_dexTaxExcempt[dst] || _dexTaxExcempt[src])) {
            if (!_isLimitExcempt[dst]) {
                require(add96(balances[dst], amount, "FitToken::_transferTokens: exceds max per holder amount") <= maxPerHolder, "FitToken::_transferTokens: final balance exceeds balance limit");
            }
            balances[src] = sub96(balances[src], amount, "FitToken::_transferTokens: transfer amount exceeds balance");
            balances[dst] = add96(balances[dst], amount, "FitToken::_transferTokens: transfer amount overflows");
            emit Transfer(src, dst, amount);
            _moveDelegates(delegates[src], delegates[dst], amount);
        } else {
            require(!isTradingPaused, "FitToken::_transferTokens: only liq transfer allowed");
            uint8 taxValue = isDex[src] ? taxOnPurchase : taxOnSell;
            address taxTarget = isDex[src] ? purchaseTaxAddress : sellTaxAddress;
            uint96 tax = (amount * taxValue) / 100;
            uint96 teamTax = (amount * devFundTax) / 100;
            if (!_isLimitExcempt[dst]) {
                require(add96(balances[dst], (amount - tax - teamTax), "FitToken::_transferTokens: final balance exceeds balance limit") <= maxPerHolder, "FitToken::_transferTokens: final balance exceeds balance limit");
            }
            balances[src] = sub96(balances[src], amount, "FitToken::_transferTokens: transfer amount exceeds balance");
            balances[taxTarget] = add96(balances[taxTarget], tax, "FitToken::_transferTokens: transfer amount overflows");
            balances[managementAddress] = add96(balances[managementAddress], teamTax, "FitToken::_transferTokens: transfer amount overflows");
            balances[dst] = add96(balances[dst], (amount - tax - teamTax), "FitToken::_transferTokens: transfer amount overflows");
            emit Transfer(src, taxTarget, tax);
            emit Transfer(src, managementAddress, teamTax);
            emit Transfer(src, dst, (amount - tax - teamTax));
            _moveDelegates(delegates[src], delegates[taxTarget], tax);
            _moveDelegates(delegates[src], delegates[managementAddress], teamTax);
            _moveDelegates(delegates[src], delegates[dst], (amount - tax - teamTax));
            // _swapReceivedFIT();
        }
    }

    function _moveDelegates(address srcRep, address dstRep, uint96 amount) internal {
        if (srcRep != dstRep && amount > 0) {
            if (srcRep != address(0)) {
                uint32 srcRepNum = numCheckpoints[srcRep];
                uint96 srcRepOld = srcRepNum > 0 ? checkpoints[srcRep][srcRepNum - 1].votes : 0;
                uint96 srcRepNew = sub96(srcRepOld, amount, "FitToken::_moveVotes: vote amount underflows");
                _writeCheckpoint(srcRep, srcRepNum, srcRepOld, srcRepNew);
            }
            if (dstRep != address(0)) {
                uint32 dstRepNum = numCheckpoints[dstRep];
                uint96 dstRepOld = dstRepNum > 0 ? checkpoints[dstRep][dstRepNum - 1].votes : 0;
                uint96 dstRepNew = add96(dstRepOld, amount, "FitToken::_moveVotes: vote amount overflows");
                _writeCheckpoint(dstRep, dstRepNum, dstRepOld, dstRepNew);
            }
        }
    }

    function _writeCheckpoint(address delegatee, uint32 nCheckpoints, uint96 oldVotes, uint96 newVotes) internal {
        uint32 blockNumber = safe32(block.number, "FitToken::_writeCheckpoint: block number exceeds 32 bits");
        if (nCheckpoints > 0 && checkpoints[delegatee][nCheckpoints - 1].fromBlock == blockNumber) {
            checkpoints[delegatee][nCheckpoints - 1].votes = newVotes;
        } else {
            checkpoints[delegatee][nCheckpoints] = Checkpoint(blockNumber, newVotes);
            numCheckpoints[delegatee] = nCheckpoints + 1;
        }
        emit DelegateVotesChanged(delegatee, oldVotes, newVotes);
    }

    /**
     * @dev Internal function which returns amount user withdrawn within last period.
     */
    function _withdrawnLastPeriod(address user) internal view returns(uint96) {
        uint256 numberOfWithdrawals = _withdrawals[user].withdrawalTimestamps.length;
        uint96 withdrawnAmount;
        if (numberOfWithdrawals == 0) return withdrawnAmount;
        while (true) {
            if (numberOfWithdrawals == 0) break;
            numberOfWithdrawals--;
            uint256 withdrawalTimestamp = _withdrawals[user].withdrawalTimestamps[numberOfWithdrawals];
            if (block.timestamp - withdrawalTimestamp < limitPeriod) {
                withdrawnAmount += _withdrawals[user].withdrawalAmounts[numberOfWithdrawals];
                continue;
            }
            break;
        }
        return withdrawnAmount;
    }

    function safe32(uint256 n, string memory errorMessage) internal pure returns(uint32) {
        require(n < 2 ** 32, errorMessage);
        return uint32(n);
    }

    function safe96(uint256 n, string memory errorMessage) internal pure returns(uint96) {
        require(n < 2 ** 96, errorMessage);
        return uint96(n);
    }

    function add96(uint96 a, uint96 b, string memory errorMessage) internal pure returns(uint96) {
        uint96 c = a + b;
        require(c >= a, errorMessage);
        return c;
    }

    function sub96(uint96 a, uint96 b, string memory errorMessage) internal pure returns(uint96) {
        require(b <= a, errorMessage);
        return a - b;
    }

    function getChainId() internal view returns(uint256) {
        uint256 chainId;
        assembly {
            chainId := chainid()
        }
        return chainId;
    }

    function updateTaxOnSell(uint8 _newTaxValue) public onlyOwner {
        require(_newTaxValue <= 80, "FitToken::_adminFunctions: Tax cannot be greater than 80");
        taxOnSell = _newTaxValue;
    }

    function updateTaxOnPurchase(uint8 _newTaxValue) public onlyOwner {
        require(_newTaxValue <= 80, "FitToken::_adminFunctions: Tax cannot be greater than 80");
        taxOnPurchase = _newTaxValue;
    }

    function updateDevTax(uint8 _newTaxValue) public onlyOwner {
        require(_newTaxValue <= 80, "FitToken::_adminFunctions: Tax cannot be greater than 80");
        devFundTax = _newTaxValue;
    }

    function updateLimitPeriod(uint256 _newlimit) public onlyOwner {
        limitPeriod = _newlimit;
    }

    function updateDexAddress(address _dex, bool _isDex) public onlyOwner {
        isDex[_dex] = _isDex;
        _isLimitExcempt[_dex] = true;
    }

    function updateTaxExcemptAddress(address _addr, bool _isExcempt) public onlyOwner {
        _dexTaxExcempt[_addr] = _isExcempt;
    }

    function manageLimitExcempt(address[] memory users, bool[] memory _isUnlimited) public onlyOwner {
        require(users.length == _isUnlimited.length, "FitToken::_adminFunctions: Array mismatch");
        for (uint256 i; i < users.length; i++) {
            _isLimitExcempt[users[i]] = _isUnlimited[i];
        }
    }

    function manageBlacklist(address[] memory users, bool[] memory _toBlackList) public onlyOwner {
        require(users.length == _toBlackList.length, "FitToken::_adminFunctions: Array mismatch");
        for (uint256 i; i < users.length; i++) {
            _isBlackListed[users[i]] = _toBlackList[i];
        }
    }

    function manageSellLimitExcempt(address[] memory users, bool[] memory _toLimit) public onlyOwner {
        require(users.length == _toLimit.length, "FitToken::_adminFunctions: Array mismatch");
        for (uint256 i; i < users.length; i++) {
            _isSellLimited[users[i]] = _toLimit[i];
        }
    }

    function mintFor(address account, uint96 amount) public onlyOwner {
        require(minted + amount <= MAX_SUPPLY, "FitToken::_adminFunctions: Mint more tokens than allowed");
        totalSupply += amount;
        minted += amount;
        balances[account] = uint96(amount);
        emit Transfer(address(0), account, amount);
    }

    function setSellLimitActive(bool _isActive) public onlyOwner {
        sellLimitActive = _isActive;
    }

    function updateGasPriceLimit(uint256 _gasPrice) public onlyOwner {
        gasPriceLimit = _gasPrice;
    }

    function pauseTrading(bool _isPaused) public onlyOwner {
        isTradingPaused = _isPaused;
    }

    function updateRouterAddress(address _router) public onlyOwner {
        routerAddress = _router;
    }

    function updateManagementAddress(address _address) public onlyOwner {
        managementAddress = _address;
    }

    function updatePurchaseTaxAddress(address _address) public onlyOwner {
        purchaseTaxAddress = _address;
    }

    function updateSellTaxAddress(address _address) public onlyOwner {
        sellTaxAddress = _address;
    }

}



/////**{BuyBack.sol}**/////

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


// File: contracts\open-zeppelin-contracts\IERC20Upgradeable.sol

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20Upgradeable {

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


// File: contracts\open-zeppelin-contracts\IERC20Burnable.sol

interface IERC20Burnable is IERC20Upgradeable {

    function burn(uint256 _amount) external;

    function burnFrom(address _account, uint256 _amount) external;

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

//{BuyBack.sol}
// File: contracts\open-zeppelin-contracts\BuyBack.sol

/**
 * @notice BuyBack contract:
 *   Swaps want token to reward token and burns them.
 */
contract BuyBack {

    using SafeERC20 for IERC20;

    address[] private _path;

    /**
     * @notice Function to buy and burn Fit reward token
     * @param _wantAdd: Want token address
     * @param _wantAmt: Amount of want token for swap
     * @param _rewardToken: Address of reward token
     */
    function buyAndBurnToken(address _wantAdd, uint256 _wantAmt, address _rewardToken, uint256 _minBurnAmt, uint256 _deadline) public returns(uint256) {
        if (_wantAdd != _rewardToken) {
            uint256 burnAmt = IERC20(_rewardToken).balanceOf(address(this));
            IERC20(_wantAdd).safeIncreaseAllowance(0x78731D3Ca6b7E34aC0F824c42a7cC18A495cabaB, _wantAmt); //  0x10ED43C718714eb63d5aA57B78B54704E256024E
            _path = [_wantAdd, _rewardToken];
            IPancakeRouter02(0x78731D3Ca6b7E34aC0F824c42a7cC18A495cabaB).swapExactTokensForTokensSupportingFeeOnTransferTokens(_wantAmt, _minBurnAmt, _path, address(this), _deadline); //  0x10ED43C718714eb63d5aA57B78B54704E256024E
            burnAmt = IERC20(_rewardToken).balanceOf(address(this)) - burnAmt;
            IERC20Burnable(_rewardToken).burn(burnAmt);
            return burnAmt;
        }
        IERC20Burnable(_rewardToken).burn(_wantAmt);
        return _wantAmt;
    }

}



/////**{FitNetV2.sol}**/////

// File: contracts\open-zeppelin-contracts\Proxy.sol

/**
 * @dev This abstract contract provides a fallback function that delegates all calls to another contract using the EVM
 * instruction `delegatecall`. We refer to the second contract as the _implementation_ behind the proxy, and it has to
 * be specified by overriding the virtual {_implementation} function.
 *
 * Additionally, delegation to the implementation can be triggered manually through the {_fallback} function, or to a
 * different contract through the {_delegate} function.
 *
 * The success and return data of the delegated call will be returned back to the caller of the proxy.
 */
abstract contract Proxy {

    /**
     * @dev Delegates the current call to `implementation`.
     *
     * This function does not return to its internall call site, it will return directly to the external caller.
     */
    function _delegate(address implementation) internal virtual {
        // solhint-disable-next-line no-inline-assembly
        assembly {
            // Copy msg.data. We take full control of memory in this inline assembly
            // block because it will not return to Solidity code. We overwrite the
            // Solidity scratch pad at memory position 0.
            calldatacopy(0, 0, calldatasize())
            // Call the implementation.
            // out and outsize are 0 because we don't know the size yet.
            let result := delegatecall(gas(), implementation, 0, calldatasize(), 0, 0)
            // Copy the returned data.
            returndatacopy(0, 0, returndatasize())
            switch result
            // delegatecall returns 0 on error.
            case 0 {
                revert(0, returndatasize())
            }
            default {
                return (0, returndatasize())
            }
        }
    }

    /**
     * @dev This is a virtual function that should be overriden so it returns the address to which the fallback function
     * and {_fallback} should delegate.
     */
    function _implementation() internal view virtual returns(address);

    /**
     * @dev Delegates the current call to the address returned by `_implementation()`.
     *
     * This function does not return to its internall call site, it will return directly to the external caller.
     */
    function _fallback() internal virtual {
        _beforeFallback();
        _delegate(_implementation());
    }

    /**
     * @dev Fallback function that delegates calls to the address returned by `_implementation()`. Will run if no other
     * function in the contract matches the call data.
     */
    fallback() external payable virtual {
        _fallback();
    }

    /**
     * @dev Fallback function that delegates calls to the address returned by `_implementation()`. Will run if call data
     * is empty.
     */
    receive() external payable virtual {
        _fallback();
    }

    /**
     * @dev Hook that is called before falling back to the implementation. Can happen as part of a manual `_fallback`
     * call, or as part of the Solidity `fallback` or `receive` functions.
     *
     * If overriden should call `super._beforeFallback()`.
     */
    function _beforeFallback() internal virtual {}

}


// File: contracts\open-zeppelin-contracts\IBeacon.sol

/**
 * @dev This is the interface that {BeaconProxy} expects of its beacon.
 */
interface IBeacon {

    /**
     * @dev Must return an address that can be used as a delegate call target.
     *
     * {BeaconProxy} will check that this address is a contract.
     */
    function implementation() external view returns(address);

}


// File: contracts\open-zeppelin-contracts\Address.sol

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
    function isContract(address account) internal view returns(bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.
        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly {
            size := extcodesize(account)
        }
        return size > 0;
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
        (bool success, ) = recipient.call {
            value: amount
        }("");
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
        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call {
            value: value
        }(data);
        return _verifyCallResult(success, returndata, errorMessage);
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
        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns(bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data, string memory errorMessage) internal returns(bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");
        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(bool success, bytes memory returndata, string memory errorMessage) private pure returns(bytes memory) {
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


// File: contracts\open-zeppelin-contracts\StorageSlot.sol

/**
 * @dev Library for reading and writing primitive types to specific storage slots.
 *
 * Storage slots are often used to avoid storage conflict when dealing with upgradeable contracts.
 * This library helps with reading and writing to such slots without the need for inline assembly.
 *
 * The functions in this library return Slot structs that contain a `value` member that can be used to read or write.
 *
 * Example usage to set ERC1967 implementation slot:
 * ```
 * contract ERC1967 {
 *     bytes32 internal constant _IMPLEMENTATION_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;
 *
 *     function _getImplementation() internal view returns (address) {
 *         return StorageSlot.getAddressSlot(_IMPLEMENTATION_SLOT).value;
 *     }
 *
 *     function _setImplementation(address newImplementation) internal {
 *         require(Address.isContract(newImplementation), "ERC1967: new implementation is not a contract");
 *         StorageSlot.getAddressSlot(_IMPLEMENTATION_SLOT).value = newImplementation;
 *     }
 * }
 * ```
 *
 * _Available since v4.1 for `address`, `bool`, `bytes32`, and `uint256`._
 */
library StorageSlot {

    struct AddressSlot {
        address value;
    }
    struct BooleanSlot {
        bool value;
    }
    struct Bytes32Slot {
        bytes32 value;
    }
    struct Uint256Slot {
        uint256 value;
    }

    /**
     * @dev Returns an `AddressSlot` with member `value` located at `slot`.
     */
    function getAddressSlot(bytes32 slot) internal pure returns(AddressSlot storage r) {
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `BooleanSlot` with member `value` located at `slot`.
     */
    function getBooleanSlot(bytes32 slot) internal pure returns(BooleanSlot storage r) {
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `Bytes32Slot` with member `value` located at `slot`.
     */
    function getBytes32Slot(bytes32 slot) internal pure returns(Bytes32Slot storage r) {
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `Uint256Slot` with member `value` located at `slot`.
     */
    function getUint256Slot(bytes32 slot) internal pure returns(Uint256Slot storage r) {
        assembly {
            r.slot := slot
        }
    }
    
}


// File: contracts\open-zeppelin-contracts\ERC1967Upgrade.sol

/**
 * @dev This abstract contract provides getters and event emitting update functions for
 * https://eips.ethereum.org/EIPS/eip-1967[EIP1967] slots.
 *
 * _Available since v4.1._
 *
 * @custom:oz-upgrades-unsafe-allow delegatecall
 */
abstract contract ERC1967Upgrade {

    // This is the keccak-256 hash of "eip1967.proxy.rollback" subtracted by 1
    bytes32 private constant _ROLLBACK_SLOT = 0x4910fdfa16fed3260ed0e7147f7cc6da11a60208b5b9406d12a635614ffd9143;
    /**
     * @dev Storage slot with the address of the current implementation.
     * This is the keccak-256 hash of "eip1967.proxy.implementation" subtracted by 1, and is
     * validated in the constructor.
     */
    bytes32 internal constant _IMPLEMENTATION_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;
    /**
     * @dev Storage slot with the admin of the contract.
     * This is the keccak-256 hash of "eip1967.proxy.admin" subtracted by 1, and is
     * validated in the constructor.
     */
    bytes32 internal constant _ADMIN_SLOT = 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103;
    /**
     * @dev The storage slot of the UpgradeableBeacon contract which defines the implementation for this proxy.
     * This is bytes32(uint256(keccak256('eip1967.proxy.beacon')) - 1)) and is validated in the constructor.
     */
    bytes32 internal constant _BEACON_SLOT = 0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50;

    /**
     * @dev Emitted when the beacon is upgraded.
     */
    event BeaconUpgraded(address indexed beacon);
    /**
     * @dev Emitted when the admin account has changed.
     */
    event AdminChanged(address previousAdmin, address newAdmin);
    /**
     * @dev Emitted when the implementation is upgraded.
     */
    event Upgraded(address indexed implementation);

    /**
     * @dev Returns the current implementation address.
     */
    function _getImplementation() internal view returns(address) {
        return StorageSlot.getAddressSlot(_IMPLEMENTATION_SLOT).value;
    }

    /**
     * @dev Stores a new address in the EIP1967 implementation slot.
     */
    function _setImplementation(address newImplementation) private {
        require(Address.isContract(newImplementation), "ERC1967: new implementation is not a contract");
        StorageSlot.getAddressSlot(_IMPLEMENTATION_SLOT).value = newImplementation;
    }

    /**
     * @dev Perform implementation upgrade
     *
     * Emits an {Upgraded} event.
     */
    function _upgradeTo(address newImplementation) internal {
        _setImplementation(newImplementation);
        emit Upgraded(newImplementation);
    }

    /**
     * @dev Perform implementation upgrade with additional setup call.
     *
     * Emits an {Upgraded} event.
     */
    function _upgradeToAndCall(address newImplementation, bytes memory data, bool forceCall) internal {
        _setImplementation(newImplementation);
        emit Upgraded(newImplementation);
        if (data.length > 0 || forceCall) {
            Address.functionDelegateCall(newImplementation, data);
        }
    }

    /**
     * @dev Perform implementation upgrade with security checks for UUPS proxies, and additional setup call.
     *
     * Emits an {Upgraded} event.
     */
    function _upgradeToAndCallSecure(address newImplementation, bytes memory data, bool forceCall) internal {
        address oldImplementation = _getImplementation();
        // Initial upgrade and setup call
        _setImplementation(newImplementation);
        if (data.length > 0 || forceCall) {
            Address.functionDelegateCall(newImplementation, data);
        }
        // Perform rollback test if not already in progress
        StorageSlot.BooleanSlot storage rollbackTesting = StorageSlot.getBooleanSlot(_ROLLBACK_SLOT);
        if (!rollbackTesting.value) {
            // Trigger rollback using upgradeTo from the new implementation
            rollbackTesting.value = true;
            Address.functionDelegateCall(newImplementation, abi.encodeWithSignature("upgradeTo(address)", oldImplementation));
            rollbackTesting.value = false;
            // Check rollback was effective
            require(oldImplementation == _getImplementation(), "ERC1967Upgrade: upgrade breaks further upgrades");
            // Finally reset to the new implementation and log the upgrade
            _setImplementation(newImplementation);
            emit Upgraded(newImplementation);
        }
    }

    /**
     * @dev Perform beacon upgrade with additional setup call. Note: This upgrades the address of the beacon, it does
     * not upgrade the implementation contained in the beacon (see {UpgradeableBeacon-_setImplementation} for that).
     *
     * Emits a {BeaconUpgraded} event.
     */
    function _upgradeBeaconToAndCall(address newBeacon, bytes memory data, bool forceCall) internal {
        _setBeacon(newBeacon);
        emit BeaconUpgraded(newBeacon);
        if (data.length > 0 || forceCall) {
            Address.functionDelegateCall(IBeacon(newBeacon).implementation(), data);
        }
    }

    /**
     * @dev Returns the current admin.
     */
    function _getAdmin() internal view returns(address) {
        return StorageSlot.getAddressSlot(_ADMIN_SLOT).value;
    }

    /**
     * @dev Stores a new address in the EIP1967 admin slot.
     */
    function _setAdmin(address newAdmin) private {
        require(newAdmin != address(0), "ERC1967: new admin is the zero address");
        StorageSlot.getAddressSlot(_ADMIN_SLOT).value = newAdmin;
    }

    /**
     * @dev Changes the admin of the proxy.
     *
     * Emits an {AdminChanged} event.
     */
    function _changeAdmin(address newAdmin) internal {
        emit AdminChanged(_getAdmin(), newAdmin);
        _setAdmin(newAdmin);
    }

    /**
     * @dev Returns the current beacon.
     */
    function _getBeacon() internal view returns(address) {
        return StorageSlot.getAddressSlot(_BEACON_SLOT).value;
    }

    /**
     * @dev Stores a new beacon in the EIP1967 beacon slot.
     */
    function _setBeacon(address newBeacon) private {
        require(Address.isContract(newBeacon), "ERC1967: new beacon is not a contract");
        require(Address.isContract(IBeacon(newBeacon).implementation()), "ERC1967: beacon implementation is not a contract");
        StorageSlot.getAddressSlot(_BEACON_SLOT).value = newBeacon;
    }

}


// File: contracts\open-zeppelin-contracts\ERC1967Proxy.sol

/**
 * @dev This contract implements an upgradeable proxy. It is upgradeable because calls are delegated to an
 * implementation address that can be changed. This address is stored in storage in the location specified by
 * https://eips.ethereum.org/EIPS/eip-1967[EIP1967], so that it doesn't conflict with the storage layout of the
 * implementation behind the proxy.
 */
contract ERC1967Proxy is Proxy, ERC1967Upgrade {

    /**
     * @dev Initializes the upgradeable proxy with an initial implementation specified by `_logic`.
     *
     * If `_data` is nonempty, it's used as data in a delegate call to `_logic`. This will typically be an encoded
     * function call, and allows initializating the storage of the proxy like a Solidity constructor.
     */
    constructor(address _logic, bytes memory _data) payable {
        assert(_IMPLEMENTATION_SLOT == bytes32(uint256(keccak256("eip1967.proxy.implementation")) - 1));
        _upgradeToAndCall(_logic, _data, false);
    }

    /**
     * @dev Returns the current implementation address.
     */
    function _implementation() internal view virtual override returns(address impl) {
        return ERC1967Upgrade._getImplementation();
    }

}


// File: contracts\open-zeppelin-contracts\TransparentUpgradeableProxy.sol

/**
 * @dev This contract implements a proxy that is upgradeable by an admin.
 *
 * To avoid https://medium.com/nomic-labs-blog/malicious-backdoors-in-ethereum-proxies-62629adf3357[proxy selector
 * clashing], which can potentially be used in an attack, this contract uses the
 * https://blog.openzeppelin.com/the-transparent-proxy-pattern/[transparent proxy pattern]. This pattern implies two
 * things that go hand in hand:
 *
 * 1. If any account other than the admin calls the proxy, the call will be forwarded to the implementation, even if
 * that call matches one of the admin functions exposed by the proxy itself.
 * 2. If the admin calls the proxy, it can access the admin functions, but its calls will never be forwarded to the
 * implementation. If the admin tries to call a function on the implementation it will fail with an error that says
 * "admin cannot fallback to proxy target".
 *
 * These properties mean that the admin account can only be used for admin actions like upgrading the proxy or changing
 * the admin, so it's best if it's a dedicated account that is not used for anything else. This will avoid headaches due
 * to sudden errors when trying to call a function from the proxy implementation.
 *
 * Our recommendation is for the dedicated account to be an instance of the {ProxyAdmin} contract. If set up this way,
 * you should think of the `ProxyAdmin` instance as the real administrative interface of your proxy.
 */
contract TransparentUpgradeableProxy is ERC1967Proxy {

    /**
     * @dev Modifier used internally that will delegate the call to the implementation unless the sender is the admin.
     */
    modifier ifAdmin() {
        if (msg.sender == _getAdmin()) {
            _;
        } else {
            _fallback();
        }
    }

    /**
     * @dev Initializes an upgradeable proxy managed by `_admin`, backed by the implementation at `_logic`, and
     * optionally initialized with `_data` as explained in {ERC1967Proxy-constructor}.
     */
    constructor(address _logic, address admin_, bytes memory _data) payable ERC1967Proxy(_logic, _data) {
        assert(_ADMIN_SLOT == bytes32(uint256(keccak256("eip1967.proxy.admin")) - 1));
        _changeAdmin(admin_);
    }

    /**
     * @dev Returns the current admin.
     *
     * NOTE: Only the admin can call this function. See {ProxyAdmin-getProxyAdmin}.
     *
     * TIP: To get this value clients can read directly from the storage slot shown below (specified by EIP1967) using the
     * https://eth.wiki/json-rpc/API#eth_getstorageat[`eth_getStorageAt`] RPC call.
     * `0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103`
     */
    function admin() external ifAdmin returns(address admin_) {
        admin_ = _getAdmin();
    }

    /**
     * @dev Returns the current implementation.
     *
     * NOTE: Only the admin can call this function. See {ProxyAdmin-getProxyImplementation}.
     *
     * TIP: To get this value clients can read directly from the storage slot shown below (specified by EIP1967) using the
     * https://eth.wiki/json-rpc/API#eth_getstorageat[`eth_getStorageAt`] RPC call.
     * `0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc`
     */
    function implementation() external ifAdmin returns(address implementation_) {
        implementation_ = _implementation();
    }

    /**
     * @dev Changes the admin of the proxy.
     *
     * Emits an {AdminChanged} event.
     *
     * NOTE: Only the admin can call this function. See {ProxyAdmin-changeProxyAdmin}.
     */
    function changeAdmin(address newAdmin) external virtual ifAdmin {
        _changeAdmin(newAdmin);
    }

    /**
     * @dev Upgrade the implementation of the proxy.
     *
     * NOTE: Only the admin can call this function. See {ProxyAdmin-upgrade}.
     */
    function upgradeTo(address newImplementation) external ifAdmin {
        _upgradeToAndCall(newImplementation, bytes(""), false);
    }

    /**
     * @dev Upgrade the implementation of the proxy, and then call a function from the new implementation as specified
     * by `data`, which should be an encoded function call. This is useful to initialize new storage variables in the
     * proxied contract.
     *
     * NOTE: Only the admin can call this function. See {ProxyAdmin-upgradeAndCall}.
     */
    function upgradeToAndCall(address newImplementation, bytes calldata data) external payable ifAdmin {
        _upgradeToAndCall(newImplementation, data, true);
    }

    /**
     * @dev Returns the current admin.
     */
    function _admin() internal view virtual returns(address) {
        return _getAdmin();
    }

    /**
     * @dev Makes sure the admin cannot access the fallback function. See {Proxy-_beforeFallback}.
     */
    function _beforeFallback() internal virtual override {
        require(msg.sender != _getAdmin(), "TransparentUpgradeableProxy: admin cannot fallback to proxy target");
        super._beforeFallback();
    }

}



/////**{FitVaultsBank.sol}**/////

// import {AddressUpgradeable.sol && SafeERC20.sol && IERC20.sol}


// File: contracts\open-zeppelin-contracts\IWETH.sol

interface IWETH {

    event Deposit(address indexed dst, uint256 wad);
    event Withdrawal(address indexed src, uint256 wad);

    function deposit() external payable;

    function withdraw(uint256 wad) external;

    function transfer(address dst, uint256 wad) external;

    function balanceOf(address dst) external view returns(uint256);

}


// File: contracts\open-zeppelin-contracts\IFitMLM.sol

interface IFitMLM {

    function isOnFitMLM(address) external view returns(bool);

    function addFitMLM(address, uint256) external;

    function distributeRewards(uint256, address, address) external;

    function updateInvestment(address _user, uint256 _newInvestment) external;

    function investment(address _user) external view returns(uint256);

}


// File: contracts\open-zeppelin-contracts\IFarming.sol

interface IFarming {

    struct UserInfo {
        uint256 amount;
        uint256 rewardDebt;
    }
    struct PoolInfo {
        address lpToken;
        uint256 allocPoint;
        uint256 lastRewardBlock;
        uint256 accRewardPerShare;
    }

    function autoDeposit(uint256, uint256, uint256, uint256, uint256, address, uint256) external payable;

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


//{FitVaultsBank.sol}
// File: contracts\open-zeppelin-contracts\FitVaultsBank.sol

/**
 * @notice FitVaultsBank contract:
 * - Users can:
 *   # Deposit token
 *   # Deposit BNB
 *   # Withdraw assets
 */
contract FitVaultsBank is ReentrancyGuardUpgradeable, OwnableUpgradeable {

    using SafeERC20 for IERC20;

    /**
     * @notice Info of each user
     * @param shares: How many LP tokens the user has provided
     * @param rewardDebt: Reward debt. See explanation below
     * @dev Any point in time, the amount of UTACOs entitled to a user but is pending to be distributed is:
     *   amount = user.shares / sharesTotal * wantLockedTotal
     *   pending reward = (amount * pool.accRewardPerShare) - user.rewardDebt
     *   Whenever a user deposits or withdraws want tokens to a pool. Here's what happens:
     *   1. The pool's `accRewardPerShare` (and `lastStakeTime`) gets updated.
     *   2. User receives the pending reward sent to his/her address.
     *   3. User's `amount` gets updated.
     *   4. User's `rewardDebt` gets updated.
     */
    struct UserInfo {
        uint256 shares;
        uint256 rewardDebt;
    }
    /**
     * @notice Info of each pool
     * @param want: Address of want token contract
     * @param allocPoint: How many allocation points assigned to this pool. FIT to distribute per block
     * @param lastRewardBlock: Last block number that reward distribution occurs
     * @param accUTacoPerShare: Accumulated rewardPool per share, times 1e18
     * @param strategy: Address of strategy contract
     */
    struct PoolInfo {
        IERC20 want;
        uint256 allocPoint;
        uint256 lastRewardBlock;
        uint256 accRewardPerShare;
        address strategy;
    }
    /**
     * @notice Info of each rewartPool
     * @param rewardToken: Address of reward token contract
     * @param rewardPerBlock: How many reward tokens will user get per block
     * @param totalPaidRewards: Total amount of reward tokens was paid
     */
    struct RewardPoolInfo {
        address rewardToken;
        uint256 rewardPerBlock;
    }

    /// Percent of amount that will be sent to relationship contract
    uint256 public RELATIONSHIP_REWARD;
    uint256 public MANAGEMENT_REWARD;
    /// Total allocation points. Must be the sum of all allocation points in all pools.
    uint256 public totalAllocPoint;
    /// Startblock number
    uint256 public startBlock;
    uint256 public withdrawFee;
    uint256 private lastChangeBlock;
    uint256 private rewardPerBlockChangesCount;

    address public farming;
    // contracts[7] - RelationShip address
    address public relationship;
    /// Treasury address where will be sent all unused assets
    address public treasuryAddress;
    address[] private alpacaToWBNB;
    address public WBNBAddress;

    /// Info of each pool.
    PoolInfo[] public poolInfo;
    /// Info of reward pool
    RewardPoolInfo public rewardPoolInfo;

    /// Info of each user that stakes want tokens.
    mapping(uint256 => mapping(address => UserInfo)) public userInfo;
    modifier onlyOnFitMLM() {
        require(IFitMLM(relationship).isOnFitMLM(msg.sender), "FitVaultsBank: Don't have relationship");
        _;
    }

    /* ========== EVENTS ========== */

    event Initialized(address indexed executor, uint256 at);
    event Deposit(address indexed user, uint256 indexed pid, uint256 amount);
    event Withdraw(address indexed user, uint256 indexed pid, uint256 amount);
    event RewardPaid(address indexed token, address indexed user, uint256 amount);
    event ClaimUserReward(address indexed user, address indexed affilate);

    function initialize(uint256 _startBlock, address _fit, uint256 _fitRewardRate) external initializer {
        require(block.number < _startBlock, "FitVaultsBank: Start block must have a bigger value");
        startBlock = _startBlock;
        rewardPoolInfo = RewardPoolInfo({
            rewardToken: _fit,
            rewardPerBlock: _fitRewardRate
        });
        alpacaToWBNB = [0x8F0528cE5eF7B51152A59745bEfDD91D97091d2F, WBNBAddress];  //  AlpacaToken-contract_addr
        relationship = 0xEB2d370177c71516fae9947D143Bd173D4E7c306;  //  TransparentUpgradeableProxy-contract_addr
        WBNBAddress = 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c;  //  WBNB-contract_addr
        lastChangeBlock = _startBlock;
        rewardPerBlockChangesCount = 3;
        RELATIONSHIP_REWARD = 45;
        MANAGEMENT_REWARD = 10;
        __Ownable_init();
        __ReentrancyGuard_init();
        emit Initialized(msg.sender, block.number);
    }

    receive() external payable {}

    fallback() external payable {}

    function setRewardPoolInfo(address _rewardToken, uint256 _rewardPerBlock) external onlyOwner {
        rewardPoolInfo = RewardPoolInfo({
            rewardToken: _rewardToken,
            rewardPerBlock: _rewardPerBlock
        });
    }

    function updateStartBlock(uint256 _startBlock) external onlyOwner {
        startBlock = _startBlock;
    }

    function setMLMAddress(address _relationship) external onlyOwner {
        relationship = _relationship;
    }

    function setWBNBAddress(address _wbnb) external onlyOwner {
        WBNBAddress = _wbnb;
    }

    function rescueBNB() external onlyOwner {
        uint256 balance = address(this).balance;
        payable(owner()).transfer(balance);
    }

    /**
     * @notice Update the given pool's reward allocation point. Can only be called by the owner
     * @param _pid: Pool id that will be updated
     * @param _allocPoint: New allocPoint for pool
     */
    function set(uint256 _pid, uint256 _allocPoint) external onlyOwner {
        massUpdatePools();
        totalAllocPoint = totalAllocPoint - poolInfo[_pid].allocPoint + _allocPoint;
        poolInfo[_pid].allocPoint = _allocPoint;
    }

    /**
     * @notice Update the given pool's strategy. Can only be called by the owner
     * @param _pid: Pool id that will be updated
     * @param _strategy: New strategy contract address for pool
     */
    function resetStrategy(uint256 _pid, address _strategy) external onlyOwner {
        PoolInfo storage pool = poolInfo[_pid];
        require(pool.want.balanceOf(pool.strategy) == 0 || pool.accRewardPerShare == 0,"FitVaultsBank: Strategy not empty");
        pool.strategy = _strategy;
    }

    /**
     * @notice Migrates all assets to new strategy. Can only be called by the owner
     * @param _pid: Pool id that will be updated
     * @param _newStrategy: New strategy contract address for pool
     */
    function migrateStrategy(uint256 _pid, address _newStrategy) external onlyOwner {
        require(IStrategy(_newStrategy).wantLockedTotal() == 0 && IStrategy(_newStrategy).sharesTotal() == 0, "FitVaultsBank: New strategy not empty");
        PoolInfo storage pool = poolInfo[_pid];
        address _oldStrategy = pool.strategy;
        uint256 _oldSharesTotal = IStrategy(_oldStrategy).sharesTotal();
        uint256 _oldWantAmt = IStrategy(_oldStrategy).wantLockedTotal();
        IStrategy(_oldStrategy).withdraw(address(this), _oldWantAmt);
        pool.want.transfer(_newStrategy, _oldWantAmt);
        IStrategy(_newStrategy).migrateFrom(_oldStrategy, _oldWantAmt, _oldSharesTotal);
        pool.strategy = _newStrategy;
    }

    /**
     * @notice Updates amount of reward tokens  per block that user will get. Can only be called by the owner
     */
    function updateRewardPerBlock() external nonReentrant onlyOwner {
        massUpdatePools();
        if (block.number - lastChangeBlock > 20 && rewardPerBlockChangesCount > 0) {
            rewardPoolInfo.rewardPerBlock = (rewardPoolInfo.rewardPerBlock * 96774200000000) / 1e12;
            rewardPerBlockChangesCount -= 1;
            lastChangeBlock = block.number;
        }
    }

    /**
     * @notice View function to see pending reward on frontend.
     * @param _pid: Pool id where user has assets
     * @param _user: Users address
     */
    function pendingReward(uint256 _pid, address _user) external view returns(uint256) {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][_user];
        uint256 _accRewardPerShare = pool.accRewardPerShare;
        uint256 sharesTotal = IStrategy(pool.strategy).sharesTotal();
        if (block.number > pool.lastRewardBlock && sharesTotal != 0) {
            uint256 _multiplier = block.number - pool.lastRewardBlock;
            uint256 _reward = (_multiplier * rewardPoolInfo.rewardPerBlock * pool.allocPoint) / totalAllocPoint;
            _accRewardPerShare = _accRewardPerShare + ((_reward * 1e18) / sharesTotal);
        }
        return (user.shares * _accRewardPerShare) / 1e18 - user.rewardDebt;
    }

    /**
     * @notice View function to see staked Want tokens on frontend.
     * @param _pid: Pool id where user has assets
     * @param _user: Users address
     */
    function _stakedWantTokens(uint256 _pid, address _user) internal view returns(uint256) {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][_user];
        uint256 sharesTotal = IStrategy(pool.strategy).sharesTotal();
        uint256 wantLockedTotal = IStrategy(poolInfo[_pid].strategy).wantLockedTotal();
        if (sharesTotal == 0) {
            return 0;
        }
        return (user.shares * wantLockedTotal) / sharesTotal;
    }

    /**
     * @notice View function to see staked Want tokens on frontend.
     * @param _pid: Pool id where user has assets
     * @param _user: Users address
     */
    function stakedWantTokens(uint256 _pid, address _user) public view returns(uint256) {
        return _stakedWantTokens(_pid, _user);
    }

    /**
     * @notice View function to see Affilates BNB share from a user.
     * @param _pid: Pool id where user has assets
     * @param _user: Users address
     */
    function stakedWantTokensAffilate(uint256 _pid, address _user) public view returns(uint256) {
        uint256 userBalance = _stakedWantTokens(_pid, _user);
        uint256 investment = IFitMLM(relationship).investment(_user);
        return (userBalance - investment) * 45 / 100;
    }

    /**
     * @notice View function to see Affilates BNB share from a user.
     * @param _pid: Pool id where user has assets
     * @param _user: Users address
     */
    function claimUserBnbReward(uint256 _pid, address _user) public {
        updatePool(_pid);
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][_user];
        if (user.shares > 0) {
            _claim(_pid, _user);
            uint256 sharesTotal = IStrategy(pool.strategy).sharesTotal();
            uint256 wantLockedTotal = IStrategy(poolInfo[_pid].strategy).wantLockedTotal();
            uint256 wantBal = (user.shares * wantLockedTotal) / sharesTotal;
            uint256 investment = IFitMLM(relationship).investment(_user);
            uint256 accumulated = (wantBal - investment);
            if (accumulated >= 100) {
                uint256 sharesRemoved = IStrategy(poolInfo[_pid].strategy).withdraw(_user, accumulated);
                user.shares -= sharesRemoved;
                accumulated = IERC20(pool.want).balanceOf(address(this));
                uint256 amountToDistribute = (accumulated * RELATIONSHIP_REWARD) / 100;
                uint256 amountToTeamManagement = (accumulated * MANAGEMENT_REWARD) / 100;
                pool.want.safeTransfer(relationship, amountToDistribute);
                pool.want.safeTransfer(treasuryAddress, amountToTeamManagement);
                IFitMLM(relationship).distributeRewards(accumulated, WBNBAddress, _user);
                uint256 userReward = accumulated - amountToDistribute - amountToTeamManagement;
                pool.want.safeIncreaseAllowance(pool.strategy, userReward);
                uint256 sharesAdded = IStrategy(poolInfo[_pid].strategy).deposit(_user, userReward);
                user.shares += sharesAdded;
                sharesTotal = IStrategy(pool.strategy).sharesTotal();
                wantLockedTotal = IStrategy(poolInfo[_pid].strategy).wantLockedTotal();
                wantBal = (user.shares * wantLockedTotal) / sharesTotal;
                IFitMLM(relationship).updateInvestment(_user, wantBal);
                user.rewardDebt = (user.shares * (pool.accRewardPerShare)) / (1e18);
            }
        }
        emit ClaimUserReward(_user, msg.sender);
    }

    /**
     * @notice Deposit in given pool
     * @param _pid: Pool id
     * @param _wantAmt: Amount of want token that user wants to deposit
     * @param _referrerId: Referrer address
     */
    function deposit(uint256 _pid, uint256 _wantAmt, uint256 _referrerId) external payable {
        require(_wantAmt == 0 || msg.value == 0, "Cannot pass both BNB and BEP-20 assets");
        IFitMLM(relationship).addFitMLM(msg.sender, _referrerId);
        PoolInfo storage pool = poolInfo[_pid];
        if (address(pool.want) == WBNBAddress && _wantAmt == 0) {
            // If `want` is WBNB
            IWETH(WBNBAddress).deposit {
                value: msg.value
            }();
            _wantAmt = msg.value;
        }
        _deposit(_pid, _wantAmt);
    }

    /**
     * @notice Withdraw user`s assets from pool
     * @param _pid: Pool id
     * @param _wantAmt: Amount of want token that user wants to withdraw
     */
    function withdraw(uint256 _pid, uint256 _wantAmt) external nonReentrant {
        _withdraw(_pid, _wantAmt);
    }

    /**
     * @notice Claim users rewards and add deposit in Farming contract
     * @param _pid: pool Id
     */
    function claimAndDeposit(uint256 _pid, uint256 _amountTokenMin, uint256 _amountETHMin, uint256 _minAmountOut, uint256 _deadline) external payable {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][msg.sender];
        updatePool(_pid);
        uint256 pending = (user.shares * pool.accRewardPerShare) / (1e18) - (user.rewardDebt);
        if (pending > 0) {
            uint256 distributeRewardTokenAmt = pending * RELATIONSHIP_REWARD / 100;
            IERC20(rewardPoolInfo.rewardToken).safeTransfer(relationship, distributeRewardTokenAmt);
            _distributeRewards(pending, rewardPoolInfo.rewardToken);
            IERC20(rewardPoolInfo.rewardToken).approve(farming, (pending - distributeRewardTokenAmt));
            IFarming(farming).autoDeposit {
                value: msg.value
            }(0, (pending - distributeRewardTokenAmt), _amountTokenMin, _amountETHMin, _minAmountOut, msg.sender, _deadline);
        }
        user.rewardDebt = (user.shares * (pool.accRewardPerShare)) / (1e18);
    }

    /**
     * @notice Claim users rewards from all pools
     */
    function claimAll() external {
        uint256 length = poolLength();
        for (uint256 i = 0; i <= length - 1; i++) {
            claim(i);
        }
    }

    /**
     * @notice  Function to set Treasury address
     * @param _treasuryAddress Address of treasury address
     */
    function setTreasuryAddress(address _treasuryAddress) external nonReentrant onlyOwner {
        treasuryAddress = _treasuryAddress;
    }

    /**
     * @notice  Function to set Farming address
     * @param _farmingAddress Address of treasury address
     */
    function setFarmingAddress(address _farmingAddress) external nonReentrant onlyOwner {
        farming = _farmingAddress;
    }

    /**
     * @notice  Function to set withdraw fee
     * @param _fee 100 = 1%
     */
    function setWithdrawFee(uint256 _fee) external nonReentrant onlyOwner {
        withdrawFee = _fee;
    }

    function poolLength() public view returns(uint256) {
        return poolInfo.length;
    }

    /**
     * @notice Claim users rewards from given pool
     * @param _pid pool Id
     */
    function claim(uint256 _pid) public {
        updatePool(_pid);
        _claim(_pid, msg.sender);
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][msg.sender];
        user.rewardDebt = (user.shares * (pool.accRewardPerShare)) / (1e18);
    }

    /**
     * @notice Function to Add pool
     * @param _want: Address of want token contract
     * @param _allocPoint: AllocPoint for new pool
     * @param _withUpdate: If true will call massUpdatePools function
     * @param _strategy: Address of Strategy contract
     */
    function add(IERC20 _want, uint256 _allocPoint, bool _withUpdate, address _strategy) public onlyOwner {
        if (_withUpdate) {
            massUpdatePools();
        }
        uint256 lastRewardBlock = block.number > startBlock ? block.number : startBlock;
        totalAllocPoint = totalAllocPoint + _allocPoint;
        poolInfo.push(
            PoolInfo({
                want: _want,
                allocPoint: _allocPoint,
                lastRewardBlock: lastRewardBlock,
                accRewardPerShare: 0,
                strategy: _strategy
            })
        );
    }

    /**
     * @notice Update reward variables for all pools. Be careful of gas spending!
     */
    function massUpdatePools() public {
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            updatePool(pid);
        }
    }

    /**
     * @notice Update reward variables of the given pool to be up-to-date.
     * @param _pid: Pool id that will be updated
     */
    function updatePool(uint256 _pid) public {
        PoolInfo storage pool = poolInfo[_pid];
        if (block.number <= pool.lastRewardBlock) {
            return;
        }
        uint256 sharesTotal = IStrategy(pool.strategy).sharesTotal();
        if (sharesTotal == 0) {
            pool.lastRewardBlock = block.number;
            return;
        }
        uint256 multiplier = block.number - pool.lastRewardBlock;
        if (multiplier <= 0) {
            return;
        }
        uint256 _rewardPerBlock = rewardPoolInfo.rewardPerBlock;
        uint256 _reward = (multiplier * _rewardPerBlock * pool.allocPoint) / totalAllocPoint;
        pool.accRewardPerShare = pool.accRewardPerShare + ((_reward * 1e18) / sharesTotal);
        pool.lastRewardBlock = block.number;
    }

    /**
     * @notice  Safe transfer function for reward tokens
     * @param _rewardToken Address of reward token contract
     * @param _to Address of reciever
     * @param _amount Amount of reward tokens to transfer
     */
    function safeRewardTransfer(address _rewardToken, address _to, uint256 _amount) internal {
        uint256 _bal = IERC20(_rewardToken).balanceOf(address(this));
        if (_amount > _bal) {
            IERC20(_rewardToken).transfer(_to, _bal);
        } else {
            IERC20(_rewardToken).transfer(_to, _amount);
        }
    }

    /**
     * @notice Calculates amount of reward user will get.
     * @param _pid: Pool id
     */
    function _claim(uint256 _pid, address _user) internal {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][_user];
        uint256 pending = (user.shares * pool.accRewardPerShare) / (1e18) - (user.rewardDebt);
        if (pending > 0) {
            uint256 distributeRewardTokenAmt = pending * RELATIONSHIP_REWARD / 100;
            address rewardToken = rewardPoolInfo.rewardToken;
            safeRewardTransfer(rewardToken, relationship, distributeRewardTokenAmt);
            IFitMLM(relationship).distributeRewards(pending, rewardPoolInfo.rewardToken, _user);
            safeRewardTransfer(rewardToken, _user, (pending - distributeRewardTokenAmt));
            emit RewardPaid(rewardToken, _user, pending);
        }
    }

    /**
     * @notice Private deposit function
     * @param _pid: Pool id
     * @param _wantAmt: Amount of want token that user wants to deposit
     */
    function _deposit(uint256 _pid, uint256 _wantAmt) private {
        updatePool(_pid);
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][msg.sender];
        if (user.shares > 0) {
            _claim(_pid, msg.sender);
        }
        if (_wantAmt > 0) {
            if (msg.value == 0 || address(pool.want) != WBNBAddress) {
                // If `want` not WBNB
                pool.want.safeTransferFrom(address(msg.sender), address(this), _wantAmt);
            }
            uint256 wantBal = _stakedWantTokens(_pid, msg.sender);
            uint256 investment = IFitMLM(relationship).investment(msg.sender);
            uint256 accumulated = (wantBal - investment);
            if (user.shares > 0 && accumulated > 100) {
                uint256 sharesRemoved = IStrategy(poolInfo[_pid].strategy).withdraw(msg.sender, accumulated);
                user.shares -= sharesRemoved;
                uint256 amountToDistribute = (accumulated * RELATIONSHIP_REWARD) / 100;
                uint256 amountToTeamManagement = (accumulated * MANAGEMENT_REWARD) / 100;
                pool.want.safeTransfer(relationship, amountToDistribute);
                pool.want.safeTransfer(treasuryAddress, amountToTeamManagement);
                _distributeRewards(accumulated, WBNBAddress);
                _wantAmt = _wantAmt + (accumulated - amountToDistribute - amountToTeamManagement);
            }
            pool.want.safeIncreaseAllowance(pool.strategy, _wantAmt);
            uint256 sharesAdded = IStrategy(poolInfo[_pid].strategy).deposit(msg.sender, _wantAmt);
            user.shares += sharesAdded;
            uint256 activeInvestment = _stakedWantTokens(_pid, msg.sender);
            IFitMLM(relationship).updateInvestment(msg.sender, activeInvestment);
        }
        user.rewardDebt = (user.shares * (pool.accRewardPerShare)) / (1e18);
        // Send unsent rewards to the treasury address
        _transfer(address(pool.want), treasuryAddress, IERC20(pool.want).balanceOf(address(this)));
        emit Deposit(msg.sender, _pid, _wantAmt);
    }

    /**
     * @notice Private distribute rewards function
     * @param _wantAmt: Amount of want token that user wants to withdraw
     */
    function _distributeRewards(uint256 _wantAmt, address _wantAddr) private {
        // Distribute MLM rewards
        IFitMLM(relationship).distributeRewards(_wantAmt, _wantAddr, msg.sender);
    }

    /**
     * @notice Private withdraw function
     * @param _pid: Pool id
     * @param _wantAmt: Amount of want token that user wants to withdraw
     */
    function _withdraw(uint256 _pid, uint256 _wantAmt) private {
        updatePool(_pid);
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][msg.sender];
        uint256 wantLockedTotal = IStrategy(poolInfo[_pid].strategy).wantLockedTotal();
        uint256 sharesTotal = IStrategy(poolInfo[_pid].strategy).sharesTotal();
        require(user.shares > 0, "FitVaultsBank: user.shares is 0");
        require(sharesTotal > 0, "FitVaultsBank: sharesTotal is 0");
        _claim(_pid, msg.sender);
        // Withdraw want tokens
        uint256 amount = (user.shares * (wantLockedTotal)) / (sharesTotal);
        uint256 investment = IFitMLM(relationship).investment(msg.sender);
        uint256 accumulated = amount - investment > 100 ? amount - investment : 0;
        _wantAmt += accumulated > 100 ? accumulated * (RELATIONSHIP_REWARD + MANAGEMENT_REWARD) / 100 : 0;
        if (_wantAmt > amount) {
            _wantAmt = amount;
        }
        if (_wantAmt > 0) {
            uint256 sharesRemoved = IStrategy(poolInfo[_pid].strategy).withdraw(msg.sender, _wantAmt);
            user.shares -= sharesRemoved;
            if (accumulated > 0) {
                uint256 amountToDistribute = (accumulated * RELATIONSHIP_REWARD) / 100;
                uint256 amountToTeamManagement = (accumulated * MANAGEMENT_REWARD) / 100;
                pool.want.safeTransfer(relationship, amountToDistribute);
                pool.want.safeTransfer(treasuryAddress, amountToTeamManagement);
                _distributeRewards(accumulated, WBNBAddress);
            }
            _wantAmt = pool.want.balanceOf(address(this));
            if (_wantAmt > 0) {
                _transfer(address(pool.want), msg.sender, _wantAmt);
            }
        }
        user.rewardDebt = (user.shares * (pool.accRewardPerShare)) / (1e18);
        wantLockedTotal = IStrategy(poolInfo[_pid].strategy).wantLockedTotal();
        sharesTotal = IStrategy(poolInfo[_pid].strategy).sharesTotal();
        amount = (user.shares * (wantLockedTotal)) / (sharesTotal);
        IFitMLM(relationship).updateInvestment(msg.sender, amount);
        emit Withdraw(msg.sender, _pid, _wantAmt);
    }

    function _transfer(address _token, address _receiver, uint256 _amount) private {
        IERC20(_token).safeTransfer(_receiver, _amount);
        // if (_token == WBNBAddress) {
        //     If _token is WBNB
        //     IWETH(_token).withdraw(_amount);
        //     sendValue(address payable recipient, uint256 amount);
        // } else {
        // }
    }

}



/////**{FitMLM.sol}**/////

import "hardhat/console.sol";
// import{AddressUpgradeable.sol && IERC20.sol && IWETH.sol && Initializable.sol && ContextUpgradeable.sol && OwnableUpgradeable.sol}


//{FitMLM.sol}
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



/////**{NetFitFarming.sol}**/////

// import{/AddressUpgradeable.sol && SafeERC20.sol && IERC20.sol && IFitMLM.sol && IWETH.sol && IStrategy.sol && IPancakeRouter01.sol && IPancakeRouter02.sol && Initializable.sol && ContextUpgradeable.sol && OwnableUpgradeable.sol && ReentrancyGuardUpgradeable.sol}


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


// File: contracts\open-zeppelin-contracts\IPancakeswapPair.sol

interface IPancakeswapPair {

    function balanceOf(address owner) external view returns(uint256);

    function token0() external view returns(address);

    function token1() external view returns(address);

}


//{NetFitFarming.sol}
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
