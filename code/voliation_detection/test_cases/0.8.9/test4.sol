pragma solidity ^0.8.0;

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
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

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
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 *
 * ==== Security Considerations
 *
 * There are two important considerations concerning the use of `permit`. The first is that a valid permit signature
 * expresses an allowance, and it should not be assumed to convey additional meaning. In particular, it should not be
 * considered as an intention to spend the allowance in any specific way. The second is that because permits have
 * built-in replay protection and can be submitted by anyone, they can be frontrun. A protocol that uses permits should
 * take this into consideration and allow a `permit` call to fail. Combining these two aspects, a pattern that may be
 * generally recommended is:
 *
 * ```solidity
 * function doThingWithPermit(..., uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) public {
 *     try token.permit(msg.sender, address(this), value, deadline, v, r, s) {} catch {}
 *     doThing(..., value);
 * }
 *
 * function doThing(..., uint256 value) public {
 *     token.safeTransferFrom(msg.sender, address(this), value);
 *     ...
 * }
 * ```
 *
 * Observe that: 1) `msg.sender` is used as the owner, leaving no ambiguity as to the signer intent, and 2) the use of
 * `try/catch` allows the permit to fail and makes the code tolerant to frontrunning. (See also
 * {SafeERC20-safeTransferFrom}).
 *
 * Additionally, note that smart contract wallets (such as Argent or Safe) are not able to produce permit signatures, so
 * contracts should have entry points that don't rely on permit.
 */
interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     *
     * CAUTION: See Security Considerations above.
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}
pragma solidity ^0.8.1;

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
     *
     * Furthermore, `isContract` will also return true if the target contract within
     * the same transaction is already scheduled for destruction by `SELFDESTRUCT`,
     * which only has an effect at the end of a transaction.
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
    function isContract(address account) internal view returns (bool) {
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
     * https://consensys.net/diligence/blog/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.8.0/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
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
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
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
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage) private pure {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}
pragma solidity ^0.8.0;


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
    using Address for address;

    /**
     * @dev Transfer `value` amount of `token` from the calling contract to `to`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    /**
     * @dev Transfer `value` amount of `token` from `from` to `to`, spending the approval given by `from` to the
     * calling contract. If `token` returns no value, non-reverting calls are assumed to be successful.
     */
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
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    /**
     * @dev Increase the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 oldAllowance = token.allowance(address(this), spender);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, oldAllowance + value));
    }

    /**
     * @dev Decrease the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, oldAllowance - value));
        }
    }

    /**
     * @dev Set the calling contract's allowance toward `spender` to `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful. Meant to be used with tokens that require the approval
     * to be set to zero before setting it to a non-zero value, such as USDT.
     */
    function forceApprove(IERC20 token, address spender, uint256 value) internal {
        bytes memory approvalCall = abi.encodeWithSelector(token.approve.selector, spender, value);

        if (!_callOptionalReturnBool(token, approvalCall)) {
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, 0));
            _callOptionalReturn(token, approvalCall);
        }
    }

    /**
     * @dev Use a ERC-2612 signature to set the `owner` approval toward `spender` on `token`.
     * Revert on invalid signature.
     */
    function safePermit(
        IERC20Permit token,
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        uint256 nonceBefore = token.nonces(owner);
        token.permit(owner, spender, value, deadline, v, r, s);
        uint256 nonceAfter = token.nonces(owner);
        require(nonceAfter == nonceBefore + 1, "SafeERC20: permit did not succeed");
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address-functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        require(returndata.length == 0 || abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     *
     * This is a variant of {_callOptionalReturn} that silents catches all reverts and returns a bool instead.
     */
    function _callOptionalReturnBool(IERC20 token, bytes memory data) private returns (bool) {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We cannot use {Address-functionCall} here since this should return false
        // and not revert is the subcall reverts.

        (bool success, bytes memory returndata) = address(token).call(data);
        return
            success && (returndata.length == 0 || abi.decode(returndata, (bool))) && Address.isContract(address(token));
    }
}
pragma solidity ^0.8.0;

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
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

pragma solidity ^0.8.0;


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
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
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

pragma solidity =0.8.9;

library VaderMath {
    /* ========== CONSTANTS ========== */

    uint256 public constant ONE = 1 ether;

    /* ========== LIBRARY FUNCTIONS ========== */

    /**
     * @dev Calculates the amount of liquidity units for the {vaderDeposited}
     * and {assetDeposited} amounts across {totalPoolUnits}.
     *
     * The {vaderBalance} and {assetBalance} are taken into account in order to
     * calculate any necessary slippage adjustment.
     */
    function calculateLiquidityUnits(
        uint256 vaderDeposited,
        uint256 vaderBalance,
        uint256 assetDeposited,
        uint256 assetBalance,
        uint256 totalPoolUnits
    ) public pure returns (uint256) {
        // slipAdjustment
        uint256 slip = calculateSlipAdjustment(
            vaderDeposited,
            vaderBalance,
            assetDeposited,
            assetBalance
        );

        // (Va + vA)
        uint256 poolUnitFactor = (vaderBalance * assetDeposited) +
            (vaderDeposited * assetBalance);

        // 2VA
        uint256 denominator = ONE * 2 * vaderBalance * assetBalance;

        // P * [(Va + vA) / (2 * V * A)] * slipAdjustment
        return ((totalPoolUnits * poolUnitFactor) / denominator) * slip;
    }

    /**
    * @dev Calculates the necessary slippage adjustment for the {vaderDeposited} and {assetDeposited}
    * amounts across the total {vaderBalance} and {assetBalance} amounts.
    */
    function calculateSlipAdjustment(
        uint256 vaderDeposited,
        uint256 vaderBalance,
        uint256 assetDeposited,
        uint256 assetBalance
    ) public pure returns (uint256) {
        // Va
        uint256 vaderAsset = vaderBalance * assetDeposited;

        // aV
        uint256 assetVader = assetBalance * vaderDeposited;

        // (v + V) * (a + A)
        uint256 denominator = (vaderDeposited + vaderBalance) *
            (assetDeposited + assetBalance);

        // 1 - [|Va - aV| / (v + V) * (a + A)]
        return ONE - (delta(vaderAsset, assetVader) / denominator);
    }

    /**
    * @dev Calculates the loss based on the supplied {releasedVader} and {releasedAsset}
    * compared to the supplied {originalVader} and {originalAsset}.
    */
    function calculateLoss(
        uint256 originalVader,
        uint256 originalAsset,
        uint256 releasedVader,
        uint256 releasedAsset
    ) public pure returns (uint256 loss) {
        //
        // TODO: Vader Formula Differs https://github.com/vetherasset/vaderprotocol-contracts/blob/main/contracts/Utils.sol#L347-L356
        //

        // [(A0 * P1) + V0]
        uint256 originalValue = ((originalAsset * releasedVader) /
            releasedAsset) + originalVader;

        // [(A1 * P1) + V1]
        uint256 releasedValue = ((releasedAsset * releasedVader) /
            releasedAsset) + releasedVader;

        // [(A0 * P1) + V0] - [(A1 * P1) + V1]
        if (originalValue > releasedValue) loss = originalValue - releasedValue;
    }

    /**
    * @dev Calculates the {amountOut} of the swap based on the supplied {amountIn}
    * across the supplied {reserveIn} and {reserveOut} amounts.
    */
    function calculateSwap(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) public pure returns (uint256 amountOut) {
        // x * Y * X
        uint256 numerator = amountIn * reserveIn * reserveOut;

        // (x + X) ^ 2
        uint256 denominator = pow(amountIn + reserveIn);

        amountOut = numerator / denominator;
    }

    /**
    * @dev Calculates the {amountIn} of the swap based on the supplied {amountOut}
    * across the supplied {reserveIn} and {reserveOut} amounts.
    */
    function calculateSwapReverse(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) public pure returns (uint256 amountIn) {
        // X * Y
        uint256 XY = reserveIn * reserveOut;

        // 2y
        uint256 y2 = amountOut * 2;

        // 4y
        uint256 y4 = y2 * 2;

        require(
            y4 < reserveOut,
            "VaderMath::calculateSwapReverse: Desired Output Exceeds Maximum Output Possible (1/4 of Liquidity Pool)"
        );

        // root(-X^2 * Y * (4y - Y))    =>    root(X^2 * Y * (Y - 4y)) as Y - 4y >= 0    =>    Y >= 4y holds true
        uint256 numeratorA = root(XY) * root(reserveIn * (reserveOut - y4));

        // X * (2y - Y)    =>    2yX - XY
        uint256 numeratorB = y2 * reserveIn;
        uint256 numeratorC = XY;

        // -1 * (root(-X^2 * Y * (4y - Y)) + (X * (2y - Y)))    =>    -1 * (root(X^2 * Y * (Y - 4y)) + 2yX - XY)    =>    XY - root(X^2 * Y * (Y - 4y) - 2yX
        uint256 numerator = numeratorC - numeratorA - numeratorB;

        // 2y
        uint256 denominator = y2;

        amountIn = numerator / denominator;
    }

    /**
    * @dev Calculates the difference between the supplied {a} and {b} values as a positive number.
    */
    function delta(uint256 a, uint256 b) public pure returns (uint256) {
        return a > b ? a - b : b - a;
    }

    /**
    * @dev Calculates the power of 2 of the supplied {a} value.
    */
    function pow(uint256 a) public pure returns (uint256) {
        return a * a;
    }

    /**
    * @dev Calculates the square root {c} of the supplied {a} value utilizing the Babylonian method:
    * https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method
    */
    function root(uint256 a) public pure returns (uint256 c) {
        if (a > 3) {
            c = a;
            uint256 x = a / 2 + 1;
            while (x < c) {
                c = x;
                x = (a / x + x) / 2;
            }
        } else if (a != 0) {
            c = 1;
        }
    }
}

pragma solidity =0.8.9;

interface IVaderReserve {
    /* ========== STRUCTS ========== */
    /* ========== FUNCTIONS ========== */

    function reimburseImpermanentLoss(address recipient, uint256 amount)
        external;

    function grant(address recipient, uint256 amount) external;

    function reserve() external view returns (uint256);

    /* ========== EVENTS ========== */

    event GrantDistributed(address recipient, uint256 amount);
    event LossCovered(address recipient, uint256 amount, uint256 actualAmount);
}

pragma solidity =0.8.9;


interface IVaderRouter {
    /* ========== STRUCTS ========== */
    /* ========== FUNCTIONS ========== */

    function addLiquidity(
        IERC20 tokenA,
        IERC20 tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256, // amountAMin = unused
        uint256, // amountBMin = unused
        address to,
        uint256 deadline
    )
        external
        returns (
            uint256 amountA,
            uint256 amountB,
            uint256 liquidity
        );

    function addLiquidity(
        IERC20 tokenA,
        IERC20 tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        address to,
        uint256 deadline
    )
        external
        returns (
            uint256 amountA,
            uint256 amountB,
            uint256 liquidity
        );

    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint256 id,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountA, uint256 amountB);

    function swapExactTokensForTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256 amountOut);

    /* ========== EVENTS ========== */
}

pragma solidity =0.8.9;

interface IBasePool {
    /* ========== STRUCTS ========== */

    struct Position {
        uint256 creation;
        uint256 liquidity;
        uint256 originalNative;
        uint256 originalForeign;
    }

    /* ========== FUNCTIONS ========== */

    function swap(
        uint256 nativeAmountIn,
        uint256 foreignAmountIn,
        address to
    ) external returns (uint256);

    function swap(
        uint256 nativeAmountIn,
        uint256 foreignAmountIn,
        address to,
        bytes calldata
    ) external returns (uint256);

    function mint(address to) external returns (uint256 liquidity);

    function getReserves() external view returns (
            uint112 reserveNative,
            uint112 reserveForeign,
            uint32 blockTimestampLast
        );

    /* ========== EVENTS ========== */

    event Mint(
        address indexed sender,
        address indexed to,
        uint256 amount0,
        uint256 amount1
    ); // Adjustment -> new argument to which didnt exist
    event Burn(
        address indexed sender,
        uint256 amount0,
        uint256 amount1,
        address indexed to
    );
    event Swap(
        address indexed sender,
        uint256 amount0In,
        uint256 amount1In,
        uint256 amount0Out,
        uint256 amount1Out,
        address indexed to
    );
    event Sync(uint256 reserve0, uint256 reserve1); // Adjustment -> 112 to 256
    event PositionOpened(address indexed sender, uint256 id, uint256 liquidity);
    event PositionClosed(
        address indexed sender,
        uint256 id,
        uint256 liquidity,
        uint256 loss
    );
}
pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[EIP].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165 {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[EIP section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}
pragma solidity ^0.8.0;


/**
 * @dev Required interface of an ERC721 compliant contract.
 */
interface IERC721 is IERC165 {
    /**
     * @dev Emitted when `tokenId` token is transferred from `from` to `to`.
     */
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);

    /**
     * @dev Emitted when `owner` enables `approved` to manage the `tokenId` token.
     */
    event Approval(address indexed owner, address indexed approved, uint256 indexed tokenId);

    /**
     * @dev Emitted when `owner` enables or disables (`approved`) `operator` to manage all of its assets.
     */
    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);

    /**
     * @dev Returns the number of tokens in ``owner``'s account.
     */
    function balanceOf(address owner) external view returns (uint256 balance);

    /**
     * @dev Returns the owner of the `tokenId` token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function ownerOf(uint256 tokenId) external view returns (address owner);

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If the caller is not `from`, it must be approved to move this token by either {approve} or {setApprovalForAll}.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function safeTransferFrom(address from, address to, uint256 tokenId, bytes calldata data) external;

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`, checking first that contract recipients
     * are aware of the ERC721 protocol to prevent tokens from being forever locked.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If the caller is not `from`, it must have been allowed to move this token by either {approve} or {setApprovalForAll}.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function safeTransferFrom(address from, address to, uint256 tokenId) external;

    /**
     * @dev Transfers `tokenId` token from `from` to `to`.
     *
     * WARNING: Note that the caller is responsible to confirm that the recipient is capable of receiving ERC721
     * or else they may be permanently lost. Usage of {safeTransferFrom} prevents loss, though the caller must
     * understand this adds an external call which potentially creates a reentrancy vulnerability.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must be owned by `from`.
     * - If the caller is not `from`, it must be approved to move this token by either {approve} or {setApprovalForAll}.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 tokenId) external;

    /**
     * @dev Gives permission to `to` to transfer `tokenId` token to another account.
     * The approval is cleared when the token is transferred.
     *
     * Only a single account can be approved at a time, so approving the zero address clears previous approvals.
     *
     * Requirements:
     *
     * - The caller must own the token or be an approved operator.
     * - `tokenId` must exist.
     *
     * Emits an {Approval} event.
     */
    function approve(address to, uint256 tokenId) external;

    /**
     * @dev Approve or remove `operator` as an operator for the caller.
     * Operators can call {transferFrom} or {safeTransferFrom} for any token owned by the caller.
     *
     * Requirements:
     *
     * - The `operator` cannot be the caller.
     *
     * Emits an {ApprovalForAll} event.
     */
    function setApprovalForAll(address operator, bool approved) external;

    /**
     * @dev Returns the account approved for `tokenId` token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function getApproved(uint256 tokenId) external view returns (address operator);

    /**
     * @dev Returns if the `operator` is allowed to manage all of the assets of `owner`.
     *
     * See {setApprovalForAll}
     */
    function isApprovedForAll(address owner, address operator) external view returns (bool);
}
pragma solidity =0.8.9;




interface IVaderPool is IBasePool, IERC721 {
    /* ========== STRUCTS ========== */
    /* ========== FUNCTIONS ========== */

    function burn(uint256 id, address to)
        external
        returns (
            uint256 amountNative,
            uint256 amountForeign,
            uint256 coveredLoss
        );

    function toggleQueue() external;

    /* ========== EVENTS ========== */

    event QueueActive(bool activated);
}
pragma solidity =0.8.9;



interface IVaderPoolFactory {
    /* ========== STRUCTS ========== */

    /* ========== FUNCTIONS ========== */

    function createPool(address tokenA, address tokenB)
        external
        returns (IVaderPool);

    function getPool(address tokenA, address tokenB)
        external
        view
        returns (IVaderPool);

    function nativeAsset() external view returns (address);

    /* ========== EVENTS ========== */

    event PoolCreated(
        address token0,
        address token1,
        IVaderPool pool,
        uint256 index
    );
}

pragma solidity =0.8.9;

abstract contract ProtocolConstants {
    /* ========== GENERAL ========== */

    // The zero address, utility
    address internal constant _ZERO_ADDRESS = address(0);

    // One year, utility
    uint256 internal constant _ONE_YEAR = 365 days;

    // Basis Points
    uint256 internal constant _MAX_BASIS_POINTS = 100_00;

    /* ========== VADER TOKEN ========== */

    // Max VADER supply
    uint256 internal constant _INITIAL_VADER_SUPPLY = 2_500_000_000 * 1 ether;

    // Allocation for VETH holders
    uint256 internal constant _VETH_ALLOCATION = 1_000_000_000 * 1 ether;

    // Team allocation vested over {VESTING_DURATION} years
    uint256 internal constant _TEAM_ALLOCATION = 250_000_000 * 1 ether;

    // Ecosystem growth fund unlocked for partnerships & USDV provision
    uint256 internal constant _ECOSYSTEM_GROWTH = 250_000_000 * 1 ether;

    // Emission Era
    uint256 internal constant _EMISSION_ERA = 24 hours;

    // Initial Emission Curve, 5
    uint256 internal constant _INITIAL_EMISSION_CURVE = 5;

    // Fee Basis Points
    uint256 internal constant _MAX_FEE_BASIS_POINTS = 1_00;

    /* ========== VESTING ========== */

    // Vesting Duration
    uint256 internal constant _VESTING_DURATION = 2 * _ONE_YEAR;

    /* ========== CONVERTER ========== */

    // Vader -> Vether Conversion Rate (1000:1)
    uint256 internal constant _VADER_VETHER_CONVERSION_RATE = 1000;

    // Burn Address
    address internal constant _BURN =
        0xdeaDDeADDEaDdeaDdEAddEADDEAdDeadDEADDEaD;

    /* ========== SWAP QUEUE ========== */

    // A minimum of 10 swaps will be executed per block
    uint256 internal constant _MIN_SWAPS_EXECUTED = 10;

    // Expressed in basis points (50%)
    uint256 internal constant _DEFAULT_SWAPS_EXECUTED = 50_00;

    // The queue size of each block is 100 units
    uint256 internal constant _QUEUE_SIZE = 100;

    /* ========== GAS QUEUE ========== */

    // Address of Chainlink Fast Gas Price Oracle
    address internal constant _FAST_GAS_ORACLE =
        0x169E633A2D1E6c10dD91238Ba11c4A708dfEF37C;

    /* ========== VADER RESERVE ========== */

    // Minimum delay between grants
    uint256 internal constant _GRANT_DELAY = 30 days;

    // Maximum grant size divisor
    uint256 internal constant _MAX_GRANT_BASIS_POINTS = 10_00;
}
pragma solidity =0.8.9;






/*
 @dev Implementation of {VaderRouter} contract.
 *
 * The contract VaderRouter inherits from {Ownable} and {ProtocolConstants} contracts.
 *
 * It allows adding of liquidity to Vader pools and facilitate creation of Vader pools if
 * it does not already exist when depositing liquidity.
 *
 * Allows removing of liquidity by the users and claiming the underlying assets from
 * the Vader pools.
 *
 * Allows swapping between native and foreign assets within a single Vader pool.
 *
 * Allows swapping of foreign assets across two different Vader pools.
 *
 * Contains helper functions to compute the destination asset amount given the exact source
 * asset amount and vice versa.
 **/
contract VaderRouter is IVaderRouter, ProtocolConstants, Ownable {
    /* ========== LIBRARIES ========== */

    // Used for safe token transfers
    using SafeERC20 for IERC20;

    /* ========== STATE VARIABLES ========== */

    // The address of Vader pool factory contract.
    IVaderPoolFactory public immutable factory;

    // The address of Reserve contract.
    IVaderReserve public reserve;

    /* ========== CONSTRUCTOR ========== */

    /*
     * @dev Initializes contract's state by setting the vader pool factory address.
     *
     * Requirements:
     * - Vader pool factory address must not be zero.
     **/
    constructor(IVaderPoolFactory _factory) {
        require(
            _factory != IVaderPoolFactory(_ZERO_ADDRESS),
            "VaderRouter::constructor: Incorrect Arguments"
        );

        factory = _factory;
    }

    /* ========== VIEWS ========== */

    /* ========== MUTATIVE FUNCTIONS ========== */

    /*
     * @dev Allows adding of liquidity to the Vader pools.
     *
     * Internally calls {addLiquidity} function.
     *
     * Returns the amounts of assetA and assetB used in liquidity and
     * the amount of liquidity units minted.
     **/
    // NOTE: For Uniswap V2 compliancy, necessary due to stack too deep
    function addLiquidity(
        IERC20 tokenA,
        IERC20 tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256, // amountAMin = unused
        uint256, // amountBMin = unused
        address to,
        uint256 deadline
    )
        external
        override
        returns (
            uint256 amountA,
            uint256 amountB,
            uint256 liquidity
        )
    {
        return
            addLiquidity(
                tokenA,
                tokenB,
                amountADesired,
                amountBDesired,
                to,
                deadline
            );
    }

    /*
     * @dev Allows adding of liquidity to the Vader pools.
     *
     * Internally calls {_addLiquidity} function.
     *
     * Transfers the amounts of tokenA and tokenB from {msg.sender} to the pool.
     *
     * Calls the {mint} function on the pool to deposit liquidity on the behalf of
     * {to} address.
     *
     * Returns the amounts of assetA and assetB used in liquidity and
     * the amount of liquidity units minted.
     *
     * Requirements:
     * - The current timestamp has not exceeded the param {deadline}.
     **/
    function addLiquidity(
        IERC20 tokenA,
        IERC20 tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        address to,
        uint256 deadline
    )
        public
        override
        ensure(deadline)
        returns (
            uint256 amountA,
            uint256 amountB,
            uint256 liquidity
        )
    {
        IVaderPool pool;
        (pool, amountA, amountB) = _addLiquidity(
            address(tokenA),
            address(tokenB),
            amountADesired,
            amountBDesired
        );
        tokenA.safeTransferFrom(msg.sender, address(pool), amountA);
        tokenB.safeTransferFrom(msg.sender, address(pool), amountB);
        liquidity = pool.mint(to);
    }

    /*
     * @dev Allows removing of liquidity by {msg.sender} and transfers the
     * underlying assets to {to} address.
     *
     * Transfers the NFT with Id {id} representing user's position, to the pool address,
     * so the pool is able to burn it in the `burn` function call.
     *
     * Calls the `burn` function on the pool contract.
     *
     * Calls the `reimburseImpermanentLoss` on reserve contract to cover impermanent loss
     * for the liquidity being removed.
     *
     * Requirements:
     * - The underlying assets amounts of {amountA} and {amountB} must
     *   be greater than or equal to {amountAMin} and {amountBMin}, respectively.
     * - The current timestamp has not exceeded the param {deadline}.
     **/
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint256 id,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    )
        public
        override
        ensure(deadline)
        returns (uint256 amountA, uint256 amountB)
    {
        IVaderPool pool = factory.getPool(tokenA, tokenB);

        pool.transferFrom(msg.sender, address(pool), id);

        (
            uint256 amountNative,
            uint256 amountForeign,
            uint256 coveredLoss
        ) = pool.burn(id, to);

        (amountA, amountB) = tokenA == factory.nativeAsset()
            ? (amountNative, amountForeign)
            : (amountForeign, amountNative);

        require(
            amountA >= amountAMin,
            "UniswapV2Router: INSUFFICIENT_A_AMOUNT"
        );
        require(
            amountB >= amountBMin,
            "UniswapV2Router: INSUFFICIENT_B_AMOUNT"
        );

        reserve.reimburseImpermanentLoss(msg.sender, coveredLoss);
    }

    /*
     * @dev Allows swapping of exact source token amount to destination
     * token amount.
     *
     * Internally calls {_swap} function.
     *
     * Requirements:
     * - The destination amount {amountOut} must greater than or equal to param {amountOutMin}.
     * - The current timestamp has not exceeded the param {deadline}.
     **/
    function swapExactTokensForTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external virtual override ensure(deadline) returns (uint256 amountOut) {
        amountOut = _swap(amountIn, path, to);

        require(
            amountOut >= amountOutMin,
            "VaderRouter::swapExactTokensForTokens: Insufficient Trade Output"
        );
    }

    /*
     * @dev Allows swapping of source token amount to exact destination token
     * amount.
     *
     * Internally calls {calculateInGivenOut} and {_swap} functions.
     *
     * Requirements:
     * - Param {amountInMax} must be greater than or equal to the source amount computed {amountIn}.
     * - The current timestamp has not exceeded the param {deadline}.
     **/
    function swapTokensForExactTokens(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external virtual ensure(deadline) returns (uint256 amountIn) {
        amountIn = calculateInGivenOut(amountOut, path);

        require(
            amountInMax >= amountIn,
            "VaderRouter::swapTokensForExactTokens: Large Trade Input"
        );

        _swap(amountIn, path, to);
    }

    /* ========== RESTRICTED FUNCTIONS ========== */

    /*
     * @dev Sets the reserve address and renounces contract's ownership.
     *
     * Requirements:
     * - Only existing owner can call this function.
     * - Param {_reserve} cannot be a zero address.
     **/
    function initialize(IVaderReserve _reserve) external onlyOwner {
        require(
            _reserve != IVaderReserve(_ZERO_ADDRESS),
            "VaderRouter::initialize: Incorrect Reserve Specified"
        );

        reserve = _reserve;

        renounceOwnership();
    }

    /* ========== INTERNAL FUNCTIONS ========== */

    /* ========== PRIVATE FUNCTIONS ========== */

    /*
     * @dev Allows swapping of assets from within a single Vader pool or
     * across two different Vader pools.
     *
     * In case of a single Vader pool, the native asset can be swapped for foreign
     * asset and vice versa.
     *
     * In case of two Vader pools, the foreign asset is swapped for native asset from
     * the first Vader pool and the native asset retrieved from the first Vader pool is swapped
     * for foreign asset from the second Vader pool.
     *
     * Requirements:
     * - Param {path} length can be either 2 or 3.
     * - If the {path} length is 3 the index 0 and 1 must contain foreign assets' addresses
     *   and index 1 must contain native asset's address.
     * - If the {path} length is 2 then either of indexes must contain foreign asset's address
     *   and the other one must contain native asset's address.
     **/
    // TODO: Refactor with central pool, perhaps diminishes security? would need directSwap & bridgeSwap
    function _swap(
        uint256 amountIn,
        address[] calldata path,
        address to
    ) private returns (uint256 amountOut) {
        if (path.length == 3) {
            require(
                path[0] != path[1] &&
                    path[1] == factory.nativeAsset() &&
                    path[2] != path[1],
                "VaderRouter::_swap: Incorrect Path"
            );

            IVaderPool pool0 = factory.getPool(path[0], path[1]);
            IVaderPool pool1 = factory.getPool(path[1], path[2]);

            IERC20(path[0]).safeTransferFrom(
                msg.sender,
                address(pool0),
                amountIn
            );

            return pool1.swap(0, pool0.swap(amountIn, 0, address(pool1)), to);
        } else {
            require(
                path.length == 2,
                "VaderRouter::_swap: Incorrect Path Length"
            );
            address nativeAsset = factory.nativeAsset();
            require(path[0] != path[1], "VaderRouter::_swap: Incorrect Path");

            IVaderPool pool = factory.getPool(path[0], path[1]);
            IERC20(path[0]).safeTransferFrom(
                msg.sender,
                address(pool),
                amountIn
            );
            if (path[0] == nativeAsset) {
                return pool.swap(amountIn, 0, to);
            } else {
                require(
                    path[1] == nativeAsset,
                    "VaderRouter::_swap: Incorrect Path"
                );
                return pool.swap(0, amountIn, to);
            }
        }
    }

    /*
     * @dev An internal function that returns Vader pool's address against
     * the provided assets of {tokenA} and {tokenB} if it exists, otherwise
     * a new Vader pool created against the provided assets.
     **/
    // NOTE: DEX allows asymmetric deposits
    function _addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired
    )
        private
        returns (
            IVaderPool pool,
            uint256 amountA,
            uint256 amountB
        )
    {
        // create the pair if it doesn't exist yet
        pool = factory.getPool(tokenA, tokenB);
        if (pool == IVaderPool(_ZERO_ADDRESS)) {
            pool = factory.createPool(tokenA, tokenB);
        }

        (amountA, amountB) = (amountADesired, amountBDesired);
    }

    /*
     * @dev Returns the amount of source asset given the amount of destination asset.
     *
     * Calls the {calculateSwapReverse} on VaderMath library to compute the source
     * token amount.
     *
     * Requirements:
     * - Param {path} length can be either 2 or 3.
     * - If the {path} length is 3 the index 0 and 1 must contain foreign assets' addresses
     *   and index 1 must contain native asset's address.
     * - If the {path} length is 2 then either of indexes must contain foreign asset's address
     *   and the other one must contain native asset's address.
     **/
    function calculateInGivenOut(uint256 amountOut, address[] calldata path)
        public
        view
        returns (uint256 amountIn)
    {
        if (path.length == 2) {
            address nativeAsset = factory.nativeAsset();
            IVaderPool pool = factory.getPool(path[0], path[1]);
            (uint256 nativeReserve, uint256 foreignReserve, ) = pool
                .getReserves();
            if (path[0] == nativeAsset) {
                return
                    VaderMath.calculateSwapReverse(
                        amountOut,
                        nativeReserve,
                        foreignReserve
                    );
            } else {
                return
                    VaderMath.calculateSwapReverse(
                        amountOut,
                        foreignReserve,
                        nativeReserve
                    );
            }
        } else {
            IVaderPool pool0 = factory.getPool(path[0], path[1]);
            IVaderPool pool1 = factory.getPool(path[1], path[2]);
            (uint256 nativeReserve0, uint256 foreignReserve0, ) = pool0
                .getReserves();
            (uint256 nativeReserve1, uint256 foreignReserve1, ) = pool1
                .getReserves();

            return
                VaderMath.calculateSwapReverse(
                    VaderMath.calculateSwapReverse(
                        amountOut,
                        nativeReserve1,
                        foreignReserve1
                    ),
                    foreignReserve0,
                    nativeReserve0
                );
        }
    }

    /*
     * @dev Returns the amount of destination asset given the amount of source asset.
     *
     * Calls the {calculateSwap} on VaderMath library to compute the destination
     * token amount.
     *
     * Requirements:
     * - Param {path} length can be either 2 or 3.
     * - If the {path} length is 3 the index 0 and 1 must contain foreign assets' addresses
     *   and index 1 must contain native asset's address.
     * - If the {path} length is 2 then either of indexes must contain foreign asset's address
     *   and the other one must contain native asset's address.
     **/
    function calculateOutGivenIn(uint256 amountIn, address[] calldata path)
        external
        view
        returns (uint256 amountOut)
    {
        if (path.length == 2) {
            address nativeAsset = factory.nativeAsset();
            IVaderPool pool = factory.getPool(path[0], path[1]);
            (uint256 nativeReserve, uint256 foreignReserve, ) = pool
                .getReserves();
            if (path[0] == nativeAsset) {
                return
                    VaderMath.calculateSwap(
                        amountIn,
                        nativeReserve,
                        foreignReserve
                    );
            } else {
                return
                    VaderMath.calculateSwap(
                        amountIn,
                        foreignReserve,
                        nativeReserve
                    );
            }
        } else {
            IVaderPool pool0 = factory.getPool(path[0], path[1]);
            IVaderPool pool1 = factory.getPool(path[1], path[2]);
            (uint256 nativeReserve0, uint256 foreignReserve0, ) = pool0
                .getReserves();
            (uint256 nativeReserve1, uint256 foreignReserve1, ) = pool1
                .getReserves();

            return
                VaderMath.calculateSwap(
                    VaderMath.calculateSwap(
                        amountIn,
                        nativeReserve1,
                        foreignReserve1
                    ),
                    foreignReserve0,
                    nativeReserve0
                );
        }
    }

    /* ========== MODIFIERS ========== */

    // Guard ensuring that the current timestamp has not exceeded the param {deadline}.
    modifier ensure(uint256 deadline) {
        require(deadline >= block.timestamp, "VaderRouter::ensure: Expired");
        _;
    }
}