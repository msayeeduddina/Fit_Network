// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;


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
