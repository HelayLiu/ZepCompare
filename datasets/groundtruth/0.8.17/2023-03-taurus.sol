// Sources flattened with hardhat v2.12.7 https://hardhat.org

// File @openzeppelin/contracts-upgradeable/utils/AddressUpgradeable.sol@v4.8.1

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.8.0) (utils/Address.sol)

pragma solidity  ^0.8.17;

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
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
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
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
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


// File @openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.8.1) (proxy/utils/Initializable.sol)



/**
 * @dev This is a base contract to aid in writing upgradeable contracts, or any kind of contract that will be deployed
 * behind a proxy. Since proxied contracts do not make use of a constructor, it's common to move constructor logic to an
 * external initializer function, usually called `initialize`. It then becomes necessary to protect this initializer
 * function so it can only be called once. The {initializer} modifier provided by this contract will have this effect.
 *
 * The initialization functions use a version number. Once a version number is used, it is consumed and cannot be
 * reused. This mechanism prevents re-execution of each "step" but allows the creation of new initialization steps in
 * case an upgrade adds a module that needs to be initialized.
 *
 * For example:
 *
 * [.hljs-theme-light.nopadding]
 * ```
 * contract MyToken is ERC20Upgradeable {
 *     function initialize() initializer public {
 *         __ERC20_init("MyToken", "MTK");
 *     }
 * }
 * contract MyTokenV2 is MyToken, ERC20PermitUpgradeable {
 *     function initializeV2() reinitializer(2) public {
 *         __ERC20Permit_init("MyToken");
 *     }
 * }
 * ```
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
 * contract, which may impact the proxy. To prevent the implementation contract from being used, you should invoke
 * the {_disableInitializers} function in the constructor to automatically lock it when it is deployed:
 *
 * [.hljs-theme-light.nopadding]
 * ```
 * /// @custom:oz-upgrades-unsafe-allow constructor
 * constructor() {
 *     _disableInitializers();
 * }
 * ```
 * ====
 */
abstract contract Initializable {
    /**
     * @dev Indicates that the contract has been initialized.
     * @custom:oz-retyped-from bool
     */
    uint8 private _initialized;

    /**
     * @dev Indicates that the contract is in the process of being initialized.
     */
    bool private _initializing;

    /**
     * @dev Triggered when the contract has been initialized or reinitialized.
     */
    event Initialized(uint8 version);

    /**
     * @dev A modifier that defines a protected initializer function that can be invoked at most once. In its scope,
     * `onlyInitializing` functions can be used to initialize parent contracts.
     *
     * Similar to `reinitializer(1)`, except that functions marked with `initializer` can be nested in the context of a
     * constructor.
     *
     * Emits an {Initialized} event.
     */
    modifier initializer() {
        bool isTopLevelCall = !_initializing;
        require(
            (isTopLevelCall && _initialized < 1) || (!AddressUpgradeable.isContract(address(this)) && _initialized == 1),
            "Initializable: contract is already initialized"
        );
        _initialized = 1;
        if (isTopLevelCall) {
            _initializing = true;
        }
        _;
        if (isTopLevelCall) {
            _initializing = false;
            emit Initialized(1);
        }
    }

    /**
     * @dev A modifier that defines a protected reinitializer function that can be invoked at most once, and only if the
     * contract hasn't been initialized to a greater version before. In its scope, `onlyInitializing` functions can be
     * used to initialize parent contracts.
     *
     * A reinitializer may be used after the original initialization step. This is essential to configure modules that
     * are added through upgrades and that require initialization.
     *
     * When `version` is 1, this modifier is similar to `initializer`, except that functions marked with `reinitializer`
     * cannot be nested. If one is invoked in the context of another, execution will revert.
     *
     * Note that versions can jump in increments greater than 1; this implies that if multiple reinitializers coexist in
     * a contract, executing them in the right order is up to the developer or operator.
     *
     * WARNING: setting the version to 255 will prevent any future reinitialization.
     *
     * Emits an {Initialized} event.
     */
    modifier reinitializer(uint8 version) {
        require(!_initializing && _initialized < version, "Initializable: contract is already initialized");
        _initialized = version;
        _initializing = true;
        _;
        _initializing = false;
        emit Initialized(version);
    }

    /**
     * @dev Modifier to protect an initialization function so that it can only be invoked by functions with the
     * {initializer} and {reinitializer} modifiers, directly or indirectly.
     */
    modifier onlyInitializing() {
        require(_initializing, "Initializable: contract is not initializing");
        _;
    }

    /**
     * @dev Locks the contract, preventing any future reinitialization. This cannot be part of an initializer call.
     * Calling this in the constructor of a contract will prevent that contract from being initialized or reinitialized
     * to any version. It is recommended to use this to lock implementation contracts that are designed to be called
     * through proxies.
     *
     * Emits an {Initialized} event the first time it is successfully executed.
     */
    function _disableInitializers() internal virtual {
        require(!_initializing, "Initializable: contract is initializing");
        if (_initialized < type(uint8).max) {
            _initialized = type(uint8).max;
            emit Initialized(type(uint8).max);
        }
    }

    /**
     * @dev Returns the highest version that has been initialized. See {reinitializer}.
     */
    function _getInitializedVersion() internal view returns (uint8) {
        return _initialized;
    }

    /**
     * @dev Returns `true` if the contract is currently initializing. See {onlyInitializing}.
     */
    function _isInitializing() internal view returns (bool) {
        return _initializing;
    }
}


// File @openzeppelin/contracts-upgradeable/utils/ContextUpgradeable.sol@v4.8.1


// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)



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
    function __Context_init() internal onlyInitializing {
    }

    function __Context_init_unchained() internal onlyInitializing {
    }
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[50] private __gap;
}


// File @openzeppelin/contracts-upgradeable/security/PausableUpgradeable.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.7.0) (security/Pausable.sol)




/**
 * @dev Contract module which allows children to implement an emergency stop
 * mechanism that can be triggered by an authorized account.
 *
 * This module is used through inheritance. It will make available the
 * modifiers `whenNotPaused` and `whenPaused`, which can be applied to
 * the functions of your contract. Note that they will not be pausable by
 * simply including this module, only once the modifiers are put in place.
 */
abstract contract PausableUpgradeable is Initializable, ContextUpgradeable {
    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address account);

    bool private _paused;

    /**
     * @dev Initializes the contract in unpaused state.
     */
    function __Pausable_init() internal onlyInitializing {
        __Pausable_init_unchained();
    }

    function __Pausable_init_unchained() internal onlyInitializing {
        _paused = false;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        _requireNotPaused();
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        _requirePaused();
        _;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view virtual returns (bool) {
        return _paused;
    }

    /**
     * @dev Throws if the contract is paused.
     */
    function _requireNotPaused() internal view virtual {
        require(!paused(), "Pausable: paused");
    }

    /**
     * @dev Throws if the contract is not paused.
     */
    function _requirePaused() internal view virtual {
        require(paused(), "Pausable: not paused");
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }

    /**
     * @dev This empty reserved space is put in place to allow future versions to add new
     * variables without shifting down storage in the inheritance chain.
     * See https://docs.openzeppelin.com/contracts/4.x/upgradeable#storage_gaps
     */
    uint256[49] private __gap;
}


// File @openzeppelin/contracts/access/IAccessControl.sol@v4.8.1


// OpenZeppelin Contracts v4.4.1 (access/IAccessControl.sol)



/**
 * @dev External interface of AccessControl declared to support ERC165 detection.
 */
interface IAccessControl {
    /**
     * @dev Emitted when `newAdminRole` is set as ``role``'s admin role, replacing `previousAdminRole`
     *
     * `DEFAULT_ADMIN_ROLE` is the starting admin for all roles, despite
     * {RoleAdminChanged} not being emitted signaling this.
     *
     * _Available since v3.1._
     */
    event RoleAdminChanged(bytes32 indexed role, bytes32 indexed previousAdminRole, bytes32 indexed newAdminRole);

    /**
     * @dev Emitted when `account` is granted `role`.
     *
     * `sender` is the account that originated the contract call, an admin role
     * bearer except when using {AccessControl-_setupRole}.
     */
    event RoleGranted(bytes32 indexed role, address indexed account, address indexed sender);

    /**
     * @dev Emitted when `account` is revoked `role`.
     *
     * `sender` is the account that originated the contract call:
     *   - if using `revokeRole`, it is the admin role bearer
     *   - if using `renounceRole`, it is the role bearer (i.e. `account`)
     */
    event RoleRevoked(bytes32 indexed role, address indexed account, address indexed sender);

    /**
     * @dev Returns `true` if `account` has been granted `role`.
     */
    function hasRole(bytes32 role, address account) external view returns (bool);

    /**
     * @dev Returns the admin role that controls `role`. See {grantRole} and
     * {revokeRole}.
     *
     * To change a role's admin, use {AccessControl-_setRoleAdmin}.
     */
    function getRoleAdmin(bytes32 role) external view returns (bytes32);

    /**
     * @dev Grants `role` to `account`.
     *
     * If `account` had not been already granted `role`, emits a {RoleGranted}
     * event.
     *
     * Requirements:
     *
     * - the caller must have ``role``'s admin role.
     */
    function grantRole(bytes32 role, address account) external;

    /**
     * @dev Revokes `role` from `account`.
     *
     * If `account` had been granted `role`, emits a {RoleRevoked} event.
     *
     * Requirements:
     *
     * - the caller must have ``role``'s admin role.
     */
    function revokeRole(bytes32 role, address account) external;

    /**
     * @dev Revokes `role` from the calling account.
     *
     * Roles are often managed via {grantRole} and {revokeRole}: this function's
     * purpose is to provide a mechanism for accounts to lose their privileges
     * if they are compromised (such as when a trusted device is misplaced).
     *
     * If the calling account had been granted `role`, emits a {RoleRevoked}
     * event.
     *
     * Requirements:
     *
     * - the caller must be `account`.
     */
    function renounceRole(bytes32 role, address account) external;
}


// File @openzeppelin/contracts/utils/Context.sol@v4.8.1


// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)



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


// File @openzeppelin/contracts/utils/introspection/IERC165.sol@v4.8.1


// OpenZeppelin Contracts v4.4.1 (utils/introspection/IERC165.sol)



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


// File @openzeppelin/contracts/utils/introspection/ERC165.sol@v4.8.1


// OpenZeppelin Contracts v4.4.1 (utils/introspection/ERC165.sol)



/**
 * @dev Implementation of the {IERC165} interface.
 *
 * Contracts that want to implement ERC165 should inherit from this contract and override {supportsInterface} to check
 * for the additional interface id that will be supported. For example:
 *
 * ```solidity
 * function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
 *     return interfaceId == type(MyInterface).interfaceId || super.supportsInterface(interfaceId);
 * }
 * ```
 *
 * Alternatively, {ERC165Storage} provides an easier to use but more expensive implementation.
 */
abstract contract ERC165 is IERC165 {
    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IERC165).interfaceId;
    }
}


// File @openzeppelin/contracts/utils/math/Math.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.8.0) (utils/math/Math.sol)



/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    enum Rounding {
        Down, // Toward negative infinity
        Up, // Toward infinity
        Zero // Toward zero
    }

    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow.
        return (a & b) + (a ^ b) / 2;
    }

    /**
     * @dev Returns the ceiling of the division of two numbers.
     *
     * This differs from standard division with `/` in that it rounds up instead
     * of rounding down.
     */
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b - 1) / b can overflow on addition, so we distribute.
        return a == 0 ? 0 : (a - 1) / b + 1;
    }

    /**
     * @notice Calculates floor(x * y / denominator) with full precision. Throws if result overflows a uint256 or denominator == 0
     * @dev Original credit to Remco Bloemen under MIT license (https://xn--2-umb.com/21/muldiv)
     * with further edits by Uniswap Labs also under MIT license.
     */
    function mulDiv(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 result) {
        unchecked {
            // 512-bit multiply [prod1 prod0] = x * y. Compute the product mod 2^256 and mod 2^256 - 1, then use
            // use the Chinese Remainder Theorem to reconstruct the 512 bit result. The result is stored in two 256
            // variables such that product = prod1 * 2^256 + prod0.
            uint256 prod0; // Least significant 256 bits of the product
            uint256 prod1; // Most significant 256 bits of the product
            assembly {
                let mm := mulmod(x, y, not(0))
                prod0 := mul(x, y)
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }

            // Handle non-overflow cases, 256 by 256 division.
            if (prod1 == 0) {
                return prod0 / denominator;
            }

            // Make sure the result is less than 2^256. Also prevents denominator == 0.
            require(denominator > prod1);

            ///////////////////////////////////////////////
            // 512 by 256 division.
            ///////////////////////////////////////////////

            // Make division exact by subtracting the remainder from [prod1 prod0].
            uint256 remainder;
            assembly {
                // Compute remainder using mulmod.
                remainder := mulmod(x, y, denominator)

                // Subtract 256 bit number from 512 bit number.
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }

            // Factor powers of two out of denominator and compute largest power of two divisor of denominator. Always >= 1.
            // See https://cs.stackexchange.com/q/138556/92363.

            // Does not overflow because the denominator cannot be zero at this stage in the function.
            uint256 twos = denominator & (~denominator + 1);
            assembly {
                // Divide denominator by twos.
                denominator := div(denominator, twos)

                // Divide [prod1 prod0] by twos.
                prod0 := div(prod0, twos)

                // Flip twos such that it is 2^256 / twos. If twos is zero, then it becomes one.
                twos := add(div(sub(0, twos), twos), 1)
            }

            // Shift in bits from prod1 into prod0.
            prod0 |= prod1 * twos;

            // Invert denominator mod 2^256. Now that denominator is an odd number, it has an inverse modulo 2^256 such
            // that denominator * inv = 1 mod 2^256. Compute the inverse by starting with a seed that is correct for
            // four bits. That is, denominator * inv = 1 mod 2^4.
            uint256 inverse = (3 * denominator) ^ 2;

            // Use the Newton-Raphson iteration to improve the precision. Thanks to Hensel's lifting lemma, this also works
            // in modular arithmetic, doubling the correct bits in each step.
            inverse *= 2 - denominator * inverse; // inverse mod 2^8
            inverse *= 2 - denominator * inverse; // inverse mod 2^16
            inverse *= 2 - denominator * inverse; // inverse mod 2^32
            inverse *= 2 - denominator * inverse; // inverse mod 2^64
            inverse *= 2 - denominator * inverse; // inverse mod 2^128
            inverse *= 2 - denominator * inverse; // inverse mod 2^256

            // Because the division is now exact we can divide by multiplying with the modular inverse of denominator.
            // This will give us the correct result modulo 2^256. Since the preconditions guarantee that the outcome is
            // less than 2^256, this is the final result. We don't need to compute the high bits of the result and prod1
            // is no longer required.
            result = prod0 * inverse;
            return result;
        }
    }

    /**
     * @notice Calculates x * y / denominator with full precision, following the selected rounding direction.
     */
    function mulDiv(
        uint256 x,
        uint256 y,
        uint256 denominator,
        Rounding rounding
    ) internal pure returns (uint256) {
        uint256 result = mulDiv(x, y, denominator);
        if (rounding == Rounding.Up && mulmod(x, y, denominator) > 0) {
            result += 1;
        }
        return result;
    }

    /**
     * @dev Returns the square root of a number. If the number is not a perfect square, the value is rounded down.
     *
     * Inspired by Henry S. Warren, Jr.'s "Hacker's Delight" (Chapter 11).
     */
    function sqrt(uint256 a) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        // For our first guess, we get the biggest power of 2 which is smaller than the square root of the target.
        //
        // We know that the "msb" (most significant bit) of our target number `a` is a power of 2 such that we have
        // `msb(a) <= a < 2*msb(a)`. This value can be written `msb(a)=2**k` with `k=log2(a)`.
        //
        // This can be rewritten `2**log2(a) <= a < 2**(log2(a) + 1)`
        // → `sqrt(2**k) <= sqrt(a) < sqrt(2**(k+1))`
        // → `2**(k/2) <= sqrt(a) < 2**((k+1)/2) <= 2**(k/2 + 1)`
        //
        // Consequently, `2**(log2(a) / 2)` is a good first approximation of `sqrt(a)` with at least 1 correct bit.
        uint256 result = 1 << (log2(a) >> 1);

        // At this point `result` is an estimation with one bit of precision. We know the true value is a uint128,
        // since it is the square root of a uint256. Newton's method converges quadratically (precision doubles at
        // every iteration). We thus need at most 7 iteration to turn our partial result with one bit of precision
        // into the expected uint128 result.
        unchecked {
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            return min(result, a / result);
        }
    }

    /**
     * @notice Calculates sqrt(a), following the selected rounding direction.
     */
    function sqrt(uint256 a, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = sqrt(a);
            return result + (rounding == Rounding.Up && result * result < a ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 2, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 128;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 64;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 32;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 16;
            }
            if (value >> 8 > 0) {
                value >>= 8;
                result += 8;
            }
            if (value >> 4 > 0) {
                value >>= 4;
                result += 4;
            }
            if (value >> 2 > 0) {
                value >>= 2;
                result += 2;
            }
            if (value >> 1 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 2, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log2(value);
            return result + (rounding == Rounding.Up && 1 << result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 10, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10**64) {
                value /= 10**64;
                result += 64;
            }
            if (value >= 10**32) {
                value /= 10**32;
                result += 32;
            }
            if (value >= 10**16) {
                value /= 10**16;
                result += 16;
            }
            if (value >= 10**8) {
                value /= 10**8;
                result += 8;
            }
            if (value >= 10**4) {
                value /= 10**4;
                result += 4;
            }
            if (value >= 10**2) {
                value /= 10**2;
                result += 2;
            }
            if (value >= 10**1) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log10(value);
            return result + (rounding == Rounding.Up && 10**result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 256, rounded down, of a positive value.
     * Returns 0 if given 0.
     *
     * Adding one to the result gives the number of pairs of hex symbols needed to represent `value` as a hex string.
     */
    function log256(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 16;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 8;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 4;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 2;
            }
            if (value >> 8 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log256(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log256(value);
            return result + (rounding == Rounding.Up && 1 << (result * 8) < value ? 1 : 0);
        }
    }
}


// File @openzeppelin/contracts/utils/Strings.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.8.0) (utils/Strings.sol)



/**
 * @dev String operations.
 */
library Strings {
    bytes16 private constant _SYMBOLS = "0123456789abcdef";
    uint8 private constant _ADDRESS_LENGTH = 20;

    /**
     * @dev Converts a `uint256` to its ASCII `string` decimal representation.
     */
    function toString(uint256 value) internal pure returns (string memory) {
        unchecked {
            uint256 length = Math.log10(value) + 1;
            string memory buffer = new string(length);
            uint256 ptr;
            /// @solidity memory-safe-assembly
            assembly {
                ptr := add(buffer, add(32, length))
            }
            while (true) {
                ptr--;
                /// @solidity memory-safe-assembly
                assembly {
                    mstore8(ptr, byte(mod(value, 10), _SYMBOLS))
                }
                value /= 10;
                if (value == 0) break;
            }
            return buffer;
        }
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation.
     */
    function toHexString(uint256 value) internal pure returns (string memory) {
        unchecked {
            return toHexString(value, Math.log256(value) + 1);
        }
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation with fixed length.
     */
    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        bytes memory buffer = new bytes(2 * length + 2);
        buffer[0] = "0";
        buffer[1] = "x";
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = _SYMBOLS[value & 0xf];
            value >>= 4;
        }
        require(value == 0, "Strings: hex length insufficient");
        return string(buffer);
    }

    /**
     * @dev Converts an `address` with fixed length of 20 bytes to its not checksummed ASCII `string` hexadecimal representation.
     */
    function toHexString(address addr) internal pure returns (string memory) {
        return toHexString(uint256(uint160(addr)), _ADDRESS_LENGTH);
    }
}


// File @openzeppelin/contracts/access/AccessControl.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.8.0) (access/AccessControl.sol)






/**
 * @dev Contract module that allows children to implement role-based access
 * control mechanisms. This is a lightweight version that doesn't allow enumerating role
 * members except through off-chain means by accessing the contract event logs. Some
 * applications may benefit from on-chain enumerability, for those cases see
 * {AccessControlEnumerable}.
 *
 * Roles are referred to by their `bytes32` identifier. These should be exposed
 * in the external API and be unique. The best way to achieve this is by
 * using `public constant` hash digests:
 *
 * ```
 * bytes32 public constant MY_ROLE = keccak256("MY_ROLE");
 * ```
 *
 * Roles can be used to represent a set of permissions. To restrict access to a
 * function call, use {hasRole}:
 *
 * ```
 * function foo() public {
 *     require(hasRole(MY_ROLE, msg.sender));
 *     ...
 * }
 * ```
 *
 * Roles can be granted and revoked dynamically via the {grantRole} and
 * {revokeRole} functions. Each role has an associated admin role, and only
 * accounts that have a role's admin role can call {grantRole} and {revokeRole}.
 *
 * By default, the admin role for all roles is `DEFAULT_ADMIN_ROLE`, which means
 * that only accounts with this role will be able to grant or revoke other
 * roles. More complex role relationships can be created by using
 * {_setRoleAdmin}.
 *
 * WARNING: The `DEFAULT_ADMIN_ROLE` is also its own admin: it has permission to
 * grant and revoke this role. Extra precautions should be taken to secure
 * accounts that have been granted it.
 */
abstract contract AccessControl is Context, IAccessControl, ERC165 {
    struct RoleData {
        mapping(address => bool) members;
        bytes32 adminRole;
    }

    mapping(bytes32 => RoleData) private _roles;

    bytes32 public constant DEFAULT_ADMIN_ROLE = 0x00;

    /**
     * @dev Modifier that checks that an account has a specific role. Reverts
     * with a standardized message including the required role.
     *
     * The format of the revert reason is given by the following regular expression:
     *
     *  /^AccessControl: account (0x[0-9a-f]{40}) is missing role (0x[0-9a-f]{64})$/
     *
     * _Available since v4.1._
     */
    modifier onlyRole(bytes32 role) {
        _checkRole(role);
        _;
    }

    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IAccessControl).interfaceId || super.supportsInterface(interfaceId);
    }

    /**
     * @dev Returns `true` if `account` has been granted `role`.
     */
    function hasRole(bytes32 role, address account) public view virtual override returns (bool) {
        return _roles[role].members[account];
    }

    /**
     * @dev Revert with a standard message if `_msgSender()` is missing `role`.
     * Overriding this function changes the behavior of the {onlyRole} modifier.
     *
     * Format of the revert message is described in {_checkRole}.
     *
     * _Available since v4.6._
     */
    function _checkRole(bytes32 role) internal view virtual {
        _checkRole(role, _msgSender());
    }

    /**
     * @dev Revert with a standard message if `account` is missing `role`.
     *
     * The format of the revert reason is given by the following regular expression:
     *
     *  /^AccessControl: account (0x[0-9a-f]{40}) is missing role (0x[0-9a-f]{64})$/
     */
    function _checkRole(bytes32 role, address account) internal view virtual {
        if (!hasRole(role, account)) {
            revert(
                string(
                    abi.encodePacked(
                        "AccessControl: account ",
                        Strings.toHexString(account),
                        " is missing role ",
                        Strings.toHexString(uint256(role), 32)
                    )
                )
            );
        }
    }

    /**
     * @dev Returns the admin role that controls `role`. See {grantRole} and
     * {revokeRole}.
     *
     * To change a role's admin, use {_setRoleAdmin}.
     */
    function getRoleAdmin(bytes32 role) public view virtual override returns (bytes32) {
        return _roles[role].adminRole;
    }

    /**
     * @dev Grants `role` to `account`.
     *
     * If `account` had not been already granted `role`, emits a {RoleGranted}
     * event.
     *
     * Requirements:
     *
     * - the caller must have ``role``'s admin role.
     *
     * May emit a {RoleGranted} event.
     */
    function grantRole(bytes32 role, address account) public virtual override onlyRole(getRoleAdmin(role)) {
        _grantRole(role, account);
    }

    /**
     * @dev Revokes `role` from `account`.
     *
     * If `account` had been granted `role`, emits a {RoleRevoked} event.
     *
     * Requirements:
     *
     * - the caller must have ``role``'s admin role.
     *
     * May emit a {RoleRevoked} event.
     */
    function revokeRole(bytes32 role, address account) public virtual override onlyRole(getRoleAdmin(role)) {
        _revokeRole(role, account);
    }

    /**
     * @dev Revokes `role` from the calling account.
     *
     * Roles are often managed via {grantRole} and {revokeRole}: this function's
     * purpose is to provide a mechanism for accounts to lose their privileges
     * if they are compromised (such as when a trusted device is misplaced).
     *
     * If the calling account had been revoked `role`, emits a {RoleRevoked}
     * event.
     *
     * Requirements:
     *
     * - the caller must be `account`.
     *
     * May emit a {RoleRevoked} event.
     */
    function renounceRole(bytes32 role, address account) public virtual override {
        require(account == _msgSender(), "AccessControl: can only renounce roles for self");

        _revokeRole(role, account);
    }

    /**
     * @dev Grants `role` to `account`.
     *
     * If `account` had not been already granted `role`, emits a {RoleGranted}
     * event. Note that unlike {grantRole}, this function doesn't perform any
     * checks on the calling account.
     *
     * May emit a {RoleGranted} event.
     *
     * [WARNING]
     * ====
     * This function should only be called from the constructor when setting
     * up the initial roles for the system.
     *
     * Using this function in any other way is effectively circumventing the admin
     * system imposed by {AccessControl}.
     * ====
     *
     * NOTE: This function is deprecated in favor of {_grantRole}.
     */
    function _setupRole(bytes32 role, address account) internal virtual {
        _grantRole(role, account);
    }

    /**
     * @dev Sets `adminRole` as ``role``'s admin role.
     *
     * Emits a {RoleAdminChanged} event.
     */
    function _setRoleAdmin(bytes32 role, bytes32 adminRole) internal virtual {
        bytes32 previousAdminRole = getRoleAdmin(role);
        _roles[role].adminRole = adminRole;
        emit RoleAdminChanged(role, previousAdminRole, adminRole);
    }

    /**
     * @dev Grants `role` to `account`.
     *
     * Internal function without access restriction.
     *
     * May emit a {RoleGranted} event.
     */
    function _grantRole(bytes32 role, address account) internal virtual {
        if (!hasRole(role, account)) {
            _roles[role].members[account] = true;
            emit RoleGranted(role, account, _msgSender());
        }
    }

    /**
     * @dev Revokes `role` from `account`.
     *
     * Internal function without access restriction.
     *
     * May emit a {RoleRevoked} event.
     */
    function _revokeRole(bytes32 role, address account) internal virtual {
        if (hasRole(role, account)) {
            _roles[role].members[account] = false;
            emit RoleRevoked(role, account, _msgSender());
        }
    }
}


// File @openzeppelin/contracts/access/Ownable.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.7.0) (access/Ownable.sol)



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


// File @openzeppelin/contracts/interfaces/draft-IERC1822.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.5.0) (interfaces/draft-IERC1822.sol)



/**
 * @dev ERC1822: Universal Upgradeable Proxy Standard (UUPS) documents a method for upgradeability through a simplified
 * proxy whose upgrades are fully controlled by the current implementation.
 */
interface IERC1822Proxiable {
    /**
     * @dev Returns the storage slot that the proxiable contract assumes is being used to store the implementation
     * address.
     *
     * IMPORTANT: A proxy pointing at a proxiable contract should not be considered proxiable itself, because this risks
     * bricking a proxy that upgrades to it, by delegating to itself until out of gas. Thus it is critical that this
     * function revert if invoked through a proxy.
     */
    function proxiableUUID() external view returns (bytes32);
}


// File @openzeppelin/contracts/proxy/beacon/IBeacon.sol@v4.8.1


// OpenZeppelin Contracts v4.4.1 (proxy/beacon/IBeacon.sol)



/**
 * @dev This is the interface that {BeaconProxy} expects of its beacon.
 */
interface IBeacon {
    /**
     * @dev Must return an address that can be used as a delegate call target.
     *
     * {BeaconProxy} will check that this address is a contract.
     */
    function implementation() external view returns (address);
}


// File @openzeppelin/contracts/utils/Address.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.8.0) (utils/Address.sol)



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
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
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
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
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


// File @openzeppelin/contracts/utils/StorageSlot.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.7.0) (utils/StorageSlot.sol)



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
    function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `BooleanSlot` with member `value` located at `slot`.
     */
    function getBooleanSlot(bytes32 slot) internal pure returns (BooleanSlot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `Bytes32Slot` with member `value` located at `slot`.
     */
    function getBytes32Slot(bytes32 slot) internal pure returns (Bytes32Slot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `Uint256Slot` with member `value` located at `slot`.
     */
    function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := slot
        }
    }
}


// File @openzeppelin/contracts/proxy/ERC1967/ERC1967Upgrade.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.5.0) (proxy/ERC1967/ERC1967Upgrade.sol)






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
     * @dev Emitted when the implementation is upgraded.
     */
    event Upgraded(address indexed implementation);

    /**
     * @dev Returns the current implementation address.
     */
    function _getImplementation() internal view returns (address) {
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
    function _upgradeToAndCall(
        address newImplementation,
        bytes memory data,
        bool forceCall
    ) internal {
        _upgradeTo(newImplementation);
        if (data.length > 0 || forceCall) {
            Address.functionDelegateCall(newImplementation, data);
        }
    }

    /**
     * @dev Perform implementation upgrade with security checks for UUPS proxies, and additional setup call.
     *
     * Emits an {Upgraded} event.
     */
    function _upgradeToAndCallUUPS(
        address newImplementation,
        bytes memory data,
        bool forceCall
    ) internal {
        // Upgrades from old implementations will perform a rollback test. This test requires the new
        // implementation to upgrade back to the old, non-ERC1822 compliant, implementation. Removing
        // this special case will break upgrade paths from old UUPS implementation to new ones.
        if (StorageSlot.getBooleanSlot(_ROLLBACK_SLOT).value) {
            _setImplementation(newImplementation);
        } else {
            try IERC1822Proxiable(newImplementation).proxiableUUID() returns (bytes32 slot) {
                require(slot == _IMPLEMENTATION_SLOT, "ERC1967Upgrade: unsupported proxiableUUID");
            } catch {
                revert("ERC1967Upgrade: new implementation is not UUPS");
            }
            _upgradeToAndCall(newImplementation, data, forceCall);
        }
    }

    /**
     * @dev Storage slot with the admin of the contract.
     * This is the keccak-256 hash of "eip1967.proxy.admin" subtracted by 1, and is
     * validated in the constructor.
     */
    bytes32 internal constant _ADMIN_SLOT = 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103;

    /**
     * @dev Emitted when the admin account has changed.
     */
    event AdminChanged(address previousAdmin, address newAdmin);

    /**
     * @dev Returns the current admin.
     */
    function _getAdmin() internal view returns (address) {
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
     * @dev The storage slot of the UpgradeableBeacon contract which defines the implementation for this proxy.
     * This is bytes32(uint256(keccak256('eip1967.proxy.beacon')) - 1)) and is validated in the constructor.
     */
    bytes32 internal constant _BEACON_SLOT = 0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50;

    /**
     * @dev Emitted when the beacon is upgraded.
     */
    event BeaconUpgraded(address indexed beacon);

    /**
     * @dev Returns the current beacon.
     */
    function _getBeacon() internal view returns (address) {
        return StorageSlot.getAddressSlot(_BEACON_SLOT).value;
    }

    /**
     * @dev Stores a new beacon in the EIP1967 beacon slot.
     */
    function _setBeacon(address newBeacon) private {
        require(Address.isContract(newBeacon), "ERC1967: new beacon is not a contract");
        require(
            Address.isContract(IBeacon(newBeacon).implementation()),
            "ERC1967: beacon implementation is not a contract"
        );
        StorageSlot.getAddressSlot(_BEACON_SLOT).value = newBeacon;
    }

    /**
     * @dev Perform beacon upgrade with additional setup call. Note: This upgrades the address of the beacon, it does
     * not upgrade the implementation contained in the beacon (see {UpgradeableBeacon-_setImplementation} for that).
     *
     * Emits a {BeaconUpgraded} event.
     */
    function _upgradeBeaconToAndCall(
        address newBeacon,
        bytes memory data,
        bool forceCall
    ) internal {
        _setBeacon(newBeacon);
        emit BeaconUpgraded(newBeacon);
        if (data.length > 0 || forceCall) {
            Address.functionDelegateCall(IBeacon(newBeacon).implementation(), data);
        }
    }
}


// File @openzeppelin/contracts/proxy/utils/UUPSUpgradeable.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.8.0) (proxy/utils/UUPSUpgradeable.sol)




/**
 * @dev An upgradeability mechanism designed for UUPS proxies. The functions included here can perform an upgrade of an
 * {ERC1967Proxy}, when this contract is set as the implementation behind such a proxy.
 *
 * A security mechanism ensures that an upgrade does not turn off upgradeability accidentally, although this risk is
 * reinstated if the upgrade retains upgradeability but removes the security mechanism, e.g. by replacing
 * `UUPSUpgradeable` with a custom implementation of upgrades.
 *
 * The {_authorizeUpgrade} function must be overridden to include access restriction to the upgrade mechanism.
 *
 * _Available since v4.1._
 */
abstract contract UUPSUpgradeable is IERC1822Proxiable, ERC1967Upgrade {
    /// @custom:oz-upgrades-unsafe-allow state-variable-immutable state-variable-assignment
    address private immutable __self = address(this);

    /**
     * @dev Check that the execution is being performed through a delegatecall call and that the execution context is
     * a proxy contract with an implementation (as defined in ERC1967) pointing to self. This should only be the case
     * for UUPS and transparent proxies that are using the current contract as their implementation. Execution of a
     * function through ERC1167 minimal proxies (clones) would not normally pass this test, but is not guaranteed to
     * fail.
     */
    modifier onlyProxy() {
        require(address(this) != __self, "Function must be called through delegatecall");
        require(_getImplementation() == __self, "Function must be called through active proxy");
        _;
    }

    /**
     * @dev Check that the execution is not being performed through a delegate call. This allows a function to be
     * callable on the implementing contract but not through proxies.
     */
    modifier notDelegated() {
        require(address(this) == __self, "UUPSUpgradeable: must not be called through delegatecall");
        _;
    }

    /**
     * @dev Implementation of the ERC1822 {proxiableUUID} function. This returns the storage slot used by the
     * implementation. It is used to validate the implementation's compatibility when performing an upgrade.
     *
     * IMPORTANT: A proxy pointing at a proxiable contract should not be considered proxiable itself, because this risks
     * bricking a proxy that upgrades to it, by delegating to itself until out of gas. Thus it is critical that this
     * function revert if invoked through a proxy. This is guaranteed by the `notDelegated` modifier.
     */
    function proxiableUUID() external view virtual override notDelegated returns (bytes32) {
        return _IMPLEMENTATION_SLOT;
    }

    /**
     * @dev Upgrade the implementation of the proxy to `newImplementation`.
     *
     * Calls {_authorizeUpgrade}.
     *
     * Emits an {Upgraded} event.
     */
    function upgradeTo(address newImplementation) external virtual onlyProxy {
        _authorizeUpgrade(newImplementation);
        _upgradeToAndCallUUPS(newImplementation, new bytes(0), false);
    }

    /**
     * @dev Upgrade the implementation of the proxy to `newImplementation`, and subsequently execute the function call
     * encoded in `data`.
     *
     * Calls {_authorizeUpgrade}.
     *
     * Emits an {Upgraded} event.
     */
    function upgradeToAndCall(address newImplementation, bytes memory data) external payable virtual onlyProxy {
        _authorizeUpgrade(newImplementation);
        _upgradeToAndCallUUPS(newImplementation, data, true);
    }

    /**
     * @dev Function that should revert when `msg.sender` is not authorized to upgrade the contract. Called by
     * {upgradeTo} and {upgradeToAndCall}.
     *
     * Normally, this function will use an xref:access.adoc[access control] modifier such as {Ownable-onlyOwner}.
     *
     * ```solidity
     * function _authorizeUpgrade(address) internal override onlyOwner {}
     * ```
     */
    function _authorizeUpgrade(address newImplementation) internal virtual;
}


// File @openzeppelin/contracts/token/ERC20/IERC20.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC20/IERC20.sol)



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
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}


// File @openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol@v4.8.1


// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/IERC20Metadata.sol)



/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}


// File @openzeppelin/contracts/token/ERC20/ERC20.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC20/ERC20.sol)





/**
 * @dev Implementation of the {IERC20} interface.
 *
 * This implementation is agnostic to the way tokens are created. This means
 * that a supply mechanism has to be added in a derived contract using {_mint}.
 * For a generic mechanism see {ERC20PresetMinterPauser}.
 *
 * TIP: For a detailed writeup see our guide
 * https://forum.openzeppelin.com/t/how-to-implement-erc20-supply-mechanisms/226[How
 * to implement supply mechanisms].
 *
 * We have followed general OpenZeppelin Contracts guidelines: functions revert
 * instead returning `false` on failure. This behavior is nonetheless
 * conventional and does not conflict with the expectations of ERC20
 * applications.
 *
 * Additionally, an {Approval} event is emitted on calls to {transferFrom}.
 * This allows applications to reconstruct the allowance for all accounts just
 * by listening to said events. Other implementations of the EIP may not emit
 * these events, as it isn't required by the specification.
 *
 * Finally, the non-standard {decreaseAllowance} and {increaseAllowance}
 * functions have been added to mitigate the well-known issues around setting
 * allowances. See {IERC20-approve}.
 */
contract ERC20 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;

    /**
     * @dev Sets the values for {name} and {symbol}.
     *
     * The default value of {decimals} is 18. To select a different value for
     * {decimals} you should overload it.
     *
     * All two of these values are immutable: they can only be set once during
     * construction.
     */
    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5.05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless this function is
     * overridden;
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view virtual override returns (uint8) {
        return 18;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address to, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _transfer(owner, to, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * NOTE: If `amount` is the maximum `uint256`, the allowance is not updated on
     * `transferFrom`. This is semantically equivalent to an infinite approval.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * NOTE: Does not update the allowance if the current allowance
     * is the maximum `uint256`.
     *
     * Requirements:
     *
     * - `from` and `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     * - the caller must have allowance for ``from``'s tokens of at least
     * `amount`.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) public virtual override returns (bool) {
        address spender = _msgSender();
        _spendAllowance(from, spender, amount);
        _transfer(from, to, amount);
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, allowance(owner, spender) + addedValue);
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        address owner = _msgSender();
        uint256 currentAllowance = allowance(owner, spender);
        require(currentAllowance >= subtractedValue, "ERC20: decreased allowance below zero");
        unchecked {
            _approve(owner, spender, currentAllowance - subtractedValue);
        }

        return true;
    }

    /**
     * @dev Moves `amount` of tokens from `from` to `to`.
     *
     * This internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     */
    function _transfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(from, to, amount);

        uint256 fromBalance = _balances[from];
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        unchecked {
            _balances[from] = fromBalance - amount;
            // Overflow not possible: the sum of all balances is capped by totalSupply, and the sum is preserved by
            // decrementing then incrementing.
            _balances[to] += amount;
        }

        emit Transfer(from, to, amount);

        _afterTokenTransfer(from, to, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply += amount;
        unchecked {
            // Overflow not possible: balance + amount is at most totalSupply + amount, which is checked above.
            _balances[account] += amount;
        }
        emit Transfer(address(0), account, amount);

        _afterTokenTransfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
            // Overflow not possible: amount <= accountBalance <= totalSupply.
            _totalSupply -= amount;
        }

        emit Transfer(account, address(0), amount);

        _afterTokenTransfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Updates `owner` s allowance for `spender` based on spent `amount`.
     *
     * Does not update the allowance amount in case of infinite allowance.
     * Revert if not enough allowance is available.
     *
     * Might emit an {Approval} event.
     */
    function _spendAllowance(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        uint256 currentAllowance = allowance(owner, spender);
        if (currentAllowance != type(uint256).max) {
            require(currentAllowance >= amount, "ERC20: insufficient allowance");
            unchecked {
                _approve(owner, spender, currentAllowance - amount);
            }
        }
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {}

    /**
     * @dev Hook that is called after any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * has been transferred to `to`.
     * - when `from` is zero, `amount` tokens have been minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens have been burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _afterTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {}
}


// File @openzeppelin/contracts/token/ERC20/extensions/ERC20Burnable.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.5.0) (token/ERC20/extensions/ERC20Burnable.sol)




/**
 * @dev Extension of {ERC20} that allows token holders to destroy both their own
 * tokens and those that they have an allowance for, in a way that can be
 * recognized off-chain (via event analysis).
 */
abstract contract ERC20Burnable is Context, ERC20 {
    /**
     * @dev Destroys `amount` tokens from the caller.
     *
     * See {ERC20-_burn}.
     */
    function burn(uint256 amount) public virtual {
        _burn(_msgSender(), amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, deducting from the caller's
     * allowance.
     *
     * See {ERC20-_burn} and {ERC20-allowance}.
     *
     * Requirements:
     *
     * - the caller must have allowance for ``accounts``'s tokens of at least
     * `amount`.
     */
    function burnFrom(address account, uint256 amount) public virtual {
        _spendAllowance(account, _msgSender(), amount);
        _burn(account, amount);
    }
}


// File @openzeppelin/contracts/token/ERC20/extensions/draft-IERC20Permit.sol@v4.8.1


// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/draft-IERC20Permit.sol)



/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
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


// File @openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol@v4.8.1


// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC20/utils/SafeERC20.sol)





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

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

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
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}


// File taurus-contracts/contracts/Libs/Constants.sol





// Basic contract to hold some constants used throughout the Taurus system
library Constants {
    // Roles
    // Role for keepers, trusted accounts which manage system operations.
    bytes32 internal constant KEEPER_ROLE = keccak256("KEEPER_ROLE");

    // Role for the team multisig, which adds/removes keepers and may perform other administrative functions in the future.
    bytes32 internal constant MULTISIG_ROLE = keccak256("MULTISIG_ROLE");

    // Governance has DEFAULT_ADMIN_ROLE i.e. bytes32(0). This puts it in charge of the multisig as well. It's exposed here for convenience.
    bytes32 internal constant DEFAULT_ADMIN_ROLE = bytes32(0);

    // SwapAdapter names
    bytes32 internal constant UNISWAP_SWAP_ADAPTER = keccak256("UNISWAP_SWAP_ADAPTER");
    bytes32 internal constant CURVE_SWAP_ADAPTER = keccak256("CURVE_SWAP_ADAPTER");

    // Role for accounts that can liquidate the underwater accounts in the system
    bytes32 internal constant LIQUIDATOR_ROLE = keccak256("LIQUIDATOR_ROLE");

    uint256 internal constant PRECISION = 1e18;

    // Fees

    uint256 internal constant MAX_FEE_PERC = 4e17; // Max protocol fees are 40%
    uint256 internal constant PERCENT_PRECISION = 1e18; // i.e. 1% will be represented as 1e16.

    // Fee names
    // Fraction of yield from GLP vault which will be sent to the feeSplitter, i.e. the protocol. Precision is PERCENT_PRECISION.
    bytes32 internal constant GLP_VAULT_PROTOCOL_FEE = keccak256("GLP_VAULT_PROTOCOL_FEE");

    bytes32 internal constant LIQUIDATOR_FEE = keccak256("LIQUIDATOR_FEE");

    bytes32 internal constant TAURUS_LIQUIDATION_FEE = keccak256("TAURUS_LIQUIDATION_FEE");

    bytes32 internal constant PRICE_ORACLE_MANAGER = keccak256("PRICE_ORACLE_MANAGER");

    bytes32 internal constant FEE_SPLITTER = keccak256("FEE_SPLITTER");
}


// File taurus-contracts/contracts/Controller/SwapAdapterRegistry.sol





contract SwapAdapterRegistry is AccessControl {
    // Mapping (hash of SwapAdapter name => SwapAdapter address).
    // Note that if the result is address(0) then there is no swap adapter registered with that hash.
    // The purpose of this is to force keepers to work only with endorsed swap modules, which helps minimize necessary trust in keepers.
    mapping(bytes32 => address) public swapAdapters;

    /**
     * @dev function to allow governance to add new swap adapters.
     * Note that this function is also capable of editing existing swap adapter addresses.
     * @param _swapAdapterHash is the hash of the swap adapter name, i.e. keccak256("UniswapSwapAdapter")
     * @param _swapAdapterAddress is the address of the swap adapter contract.
     */
    function registerSwapAdapter(
        bytes32 _swapAdapterHash,
        address _swapAdapterAddress
    ) external onlyRole(DEFAULT_ADMIN_ROLE) {
        swapAdapters[_swapAdapterHash] = _swapAdapterAddress;
    }
}


// File taurus-contracts/contracts/Controller/Controller.sol








error notOwner();
error notContract();

contract Controller is AccessControl, SwapAdapterRegistry {
    using Address for address;

    // Addresses of Taurus contracts

    address public immutable tau;
    address public immutable tgt;

    mapping(bytes32 => address) public addressMapper;

    // Functions

    /**
     * @param _tau address of the TAU token
     * @param _tgt address of the TGT token
     * @param _governance address of the Governor
     * @param _multisig address of the team multisig
     */
    constructor(address _tau, address _tgt, address _governance, address _multisig) {
        tau = _tau;
        tgt = _tgt;

        // Set up access control
        _setupRole(DEFAULT_ADMIN_ROLE, _governance);
        _setupRole(Constants.MULTISIG_ROLE, _multisig);
        _setRoleAdmin(Constants.KEEPER_ROLE, Constants.MULTISIG_ROLE); // Set multisig as keeper manager
    }

    function setAddress(bytes32 _name, address _addr) external onlyRole(DEFAULT_ADMIN_ROLE) {
        addressMapper[_name] = _addr;
    }
}


// File taurus-contracts/contracts/Controller/Controllable.sol






error notGovernance();
error notKeeper();
error notMultisig();
error notLiquidator();

// Contains logic to fetch access control info from the Controller.
contract Controllable {
    address public immutable controller;

    constructor(address _controller) {
        controller = _controller;
    }

    // Revert if msg.sender is not the Controller's Governor
    modifier onlyGovernor() {
        if (!AccessControl(controller).hasRole(Constants.DEFAULT_ADMIN_ROLE, msg.sender)) {
            revert notGovernance();
        }
        _;
    }

    // Revert if msg.sender is not registered as a keeper in the Controller
    modifier onlyKeeper() {
        if (!AccessControl(controller).hasRole(Constants.KEEPER_ROLE, msg.sender)) {
            revert notKeeper();
        }
        _;
    }

    modifier onlyMultisig() {
        if (!AccessControl(controller).hasRole(Constants.MULTISIG_ROLE, msg.sender)) {
            revert notMultisig();
        }
        _;
    }

    modifier onlyLiquidator() {
        if (!AccessControl(controller).hasRole(Constants.LIQUIDATOR_ROLE, msg.sender)) {
            revert notLiquidator();
        }
        _;
    }
}


// File taurus-contracts/contracts/Controller/ControllableUpgradeable.sol








// Contains logic to fetch access control info from the Controller.
contract ControllableUpgradeable is Initializable {
    address public controller;

    function __Controllable_init(address _controller) internal initializer {
        controller = _controller;
    }

    // Revert if msg.sender is not the Controller's Governor
    modifier onlyGovernor() {
        if (!AccessControl(controller).hasRole(Constants.DEFAULT_ADMIN_ROLE, msg.sender)) {
            revert notGovernance();
        }
        _;
    }

    // Revert if msg.sender is not registered as a keeper in the Controller
    modifier onlyKeeper() {
        if (!AccessControl(controller).hasRole(Constants.KEEPER_ROLE, msg.sender)) {
            revert notKeeper();
        }
        _;
    }

    modifier onlyMultisig() {
        if (!AccessControl(controller).hasRole(Constants.MULTISIG_ROLE, msg.sender)) {
            revert notMultisig();
        }
        _;
    }

    modifier onlyLiquidator() {
        if (!AccessControl(controller).hasRole(Constants.LIQUIDATOR_ROLE, msg.sender)) {
            revert notLiquidator();
        }
        _;
    }

    uint256[49] private __gap;
}


// File taurus-contracts/contracts/Libs/TauMath.sol





library TauMath {
    /**
     * @dev function to calculate the collateral ratio of an account.
     */
    function _computeCR(
        uint256 _coll,
        uint256 _debt,
        uint256 _price,
        uint8 priceDecimals
    ) internal pure returns (uint256) {
        if (_debt > 0) {
            uint256 newCollRatio = (_coll * _price * Constants.PRECISION) / (_debt * 10 ** priceDecimals);

            return newCollRatio;
        }
        // Return the maximal value for uint256 if the account has a debt of 0. Represents "infinite" CR.
        else {
            // if (_debt == 0)
            return type(uint256).max;
        }
    }
}


// File taurus-contracts/contracts/Oracle/OracleInterface/IOracleWrapper.sol




interface IOracleWrapper {
    struct OracleResponse {
        uint8 decimals;
        uint256 currentPrice;
        uint256 lastPrice;
        uint256 lastUpdateTimestamp;
        bool success;
    }

    error TokenIsNotRegistered(address _underlying);
    error ResponseFromOracleIsInvalid(address _token, address _oracle);
    error ZeroAddress();
    error NotContract(address _address);
    error InvalidDecimals();

    event NewOracle(address indexed _aggregatorAddress, address _underlying);

    function getExternalPrice(
        address _underlying,
        bytes calldata _flag
    ) external view returns (uint256 price, uint8 decimals, bool success);
}


// File taurus-contracts/contracts/Oracle/OracleInterface/IPriceOracleManager.sol




interface IPriceOracleManager {
    event NewWrapperRegistered(address indexed _underlying, address indexed _wrapperAddress);

    event WrapperUpdated(address indexed _underlying, address indexed _wrapperAddress);

    function setWrapper(address _underlying, address _wrapperAddress) external;

    function updateWrapper(address _underlying, address _wrapperAddress) external;

    function getExternalPrice(
        address _underlying,
        bytes calldata _data
    ) external returns (uint256 price, uint8 decimals, bool success);
}


// File taurus-contracts/contracts/Oracle/PriceOracleManager.sol







error duplicateWrapper(address);
error wrapperNotRegistered(address);
error priceNotUpdated(address);
error oracleCorrupted(address);

contract PriceOracleManager is IPriceOracleManager, Ownable {
    using Address for address;

    // This is a mapping of wrapper addresses for a particular target asset and all the assets are measured in USD by default
    // maps address(underlying)  => address(wrapper)
    // Wherein, the underlying is the target asset
    // Eg: If we consider ETH/USD pair, ETH will be quoted in terms of USD by default
    mapping(address => address) public wrapperAddressMap;

    uint256 public constant TIME_OFFSET = 4 hours;

    function setWrapper(address _underlying, address _wrapperAddress) external override onlyOwner {
        if (!_wrapperAddress.isContract()) revert notContract();
        if (wrapperAddressMap[_underlying] != address(0)) revert duplicateWrapper(_wrapperAddress);

        wrapperAddressMap[_underlying] = _wrapperAddress;

        emit NewWrapperRegistered(_underlying, _wrapperAddress);
    }

    function updateWrapper(address _underlying, address _wrapperAddress) external override onlyOwner {
        if (!_wrapperAddress.isContract()) revert notContract();
        if (wrapperAddressMap[_underlying] == address(0)) revert wrapperNotRegistered(_wrapperAddress);

        wrapperAddressMap[_underlying] = _wrapperAddress;

        emit WrapperUpdated(_underlying, _wrapperAddress);
    }

    /**
     * @dev This function is used to get the external price of the underlying asset
     * @param _underlying is the asset whose price is desired
     * e.g. if the underlying is ETH and the strike is USDC, then the returned price will represent USDC per ETH.
     * @param _data contains any flags which the active oracle may use.
     */
    function getExternalPrice(
        address _underlying,
        bytes calldata _data
    ) external view override returns (uint256 price, uint8 decimals, bool success) {
        IOracleWrapper wrapper = IOracleWrapper(wrapperAddressMap[_underlying]);

        if (address(wrapper) == address(0)) revert wrapperNotRegistered(address(wrapper));

        return wrapper.getExternalPrice(_underlying, _data);
    }
}


// File taurus-contracts/contracts/TAU.sol






error mintLimitExceeded(uint256 newAmount, uint256 maxMintAmount);

contract TAU is ERC20, ERC20Burnable {
    address public governance;

    // Max amount of tokens which a given vault can mint. Since this is set to zero by default, there is no need to register vaults.
    mapping(address => uint256) public mintLimit;
    mapping(address => uint256) public currentMinted;

    constructor(address _governance) ERC20("TAU", "TAU") {
        governance = _governance;
    }

    /**
     * @dev Set new mint limit for a given vault. Only governance can call this function.
     * note if the new limit is lower than the vault's current amount minted, this will disable future mints for that vault,
        but will do nothing to its existing minted amount.
     * @param vault The address of the vault whose mintLimit will be updated
     * @param newLimit The new mint limit for the target vault
     */
    function setMintLimit(address vault, uint256 newLimit) external {
        if (msg.sender != governance) {
            revert notGovernance();
        }
        mintLimit[vault] = newLimit;
    }

    function mint(address recipient, uint256 amount) external {
        // Check whether mint amount exceeds mintLimit for msg.sender
        uint256 newMinted = currentMinted[msg.sender] + amount;
        if (newMinted > mintLimit[msg.sender]) {
            revert mintLimitExceeded(newMinted, mintLimit[msg.sender]);
        }

        // Update vault currentMinted
        currentMinted[msg.sender] = newMinted;

        // Mint TAU to recipient
        _mint(recipient, amount);
    }

    /**
     * @dev Destroys `amount` tokens from the caller.
     *
     * See {ERC20-_burn}.
     */
    function burn(uint256 amount) public virtual override {
        address account = _msgSender();
        _burn(account, amount);
        _decreaseCurrentMinted(account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, deducting from the caller's
     * allowance. Also decreases the burner's currentMinted amount if the burner is a vault.
     *
     * See {ERC20-_burn} and {ERC20-allowance}.
     *
     * Requirements:
     *
     * - the caller must have allowance for ``accounts``'s tokens of at least
     * `amount`.
     */
    function burnFrom(address account, uint256 amount) public virtual override {
        super.burnFrom(account, amount);
        _decreaseCurrentMinted(account, amount);
    }

    function _decreaseCurrentMinted(address account, uint256 amount) internal virtual {
        // If the burner is a vault, subtract burnt TAU from its currentMinted.
        // This has a few highly unimportant edge cases which can generally be rectified by increasing the relevant vault's mintLimit.
        uint256 accountMinted = currentMinted[account];
        if (accountMinted >= amount) {
            currentMinted[msg.sender] = accountMinted - amount;
        }
    }
}


// File taurus-contracts/contracts/SwapAdapters/BaseSwapAdapter.sol




/**
 * @dev abstract contract meant solely to force all SwapAdapters to implement the same swap() function.
 */
abstract contract BaseSwapAdapter {
    function swap(address _outputToken, bytes calldata _swapData) external virtual returns (uint256);
}


// File taurus-contracts/contracts/Vault/FeeMapping.sol





abstract contract FeeMapping is ControllableUpgradeable {
    error feePercTooLarge();
    error indexOutOfBound();

    /// @dev keep track of fee types being used by the vault
    mapping(bytes32 => uint256) internal feeMapping;

    /// @dev add the fee types being used by the vault
    /// note if we want to delete the mapping, pass _feeType with empty array
    function addFeePerc(bytes32[] memory _feeType, uint256[] memory _perc) public onlyMultisig {
        uint256 _feeTypeLength = _feeType.length;
        if (_feeTypeLength != _perc.length) revert indexOutOfBound();

        for (uint256 i; i < _feeTypeLength; ++i) {
            if (_perc[i] > Constants.MAX_FEE_PERC) revert feePercTooLarge();
            feeMapping[_feeType[i]] = _perc[i];
        }
    }

    function getFeePerc(bytes32 _feeType) public view returns (uint256 perc) {
        return (feeMapping[_feeType]);
    }

    uint256[49] private __gap;
}


// File taurus-contracts/contracts/Vault/TauDripFeed.sol








// @dev contains logic for accepting TAU yield and distributing it to users over time to protect against sandwich attacks.
abstract contract TauDripFeed is PausableUpgradeable, ControllableUpgradeable {
    // @dev total amount of tau tokens that have ever been rewarded to the contract, divided by the total collateral present at the time of each deposit.
    // This number can only increase.
    uint256 public cumulativeTauRewardPerCollateral;

    /// @dev Tau tokens yet to be doled out to the vault. Tokens yet to be doled out are not counted towards cumulativeTauRewardPerCollateral.
    uint256 public tauWithheld;

    /// @dev timestamp at which tokens were most recently disbursed. Updated only when tauWithheld > 0. Used in conjunction with DRIP_DURATION to
    /// calculate next token disbursal amount.
    uint256 public tokensLastDisbursedTimestamp;

    /// @dev duration of the drip feed. Deposited TAU is steadily distributed to the contract over this amount of time.
    uint256 public constant DRIP_DURATION = 1 days;

    /// @dev address of TAU
    address public tau;

    /// @dev address of token used as collateral by this vault.
    address public collateralToken;

    function __TauDripFeed_init(address _tau, address _collateralToken) internal initializer {
        __Pausable_init();
        tau = _tau;
        collateralToken = _collateralToken;
    }

    function pause() external onlyMultisig {
        _pause();
    }

    function unpause() external onlyMultisig {
        _unpause();
    }

    /**
     * @dev function to deposit TAU into the contract while averting sandwich attacks.
     * @param amount is the amount of TAU to be burned and used to cancel out debt.
     * note the main source of TAU is the SwapHandler. This function is just a safeguard in case some other source of TAU arises.
     */
    function distributeTauRewards(uint256 amount) external whenNotPaused {
        // Burn depositor's Tau
        ERC20Burnable(tau).burnFrom(msg.sender, amount);

        // Disburse available tau
        _disburseTau();

        // Set new tau aside to protect against sandwich attacks
        _withholdTau(amount);
    }

    function disburseTau() external whenNotPaused {
        _disburseTau();
    }

    /**
     * @dev disburse TAU to the contract by updating cumulativeTauRewardPerCollateral.
     * Note that since rewards are distributed based on timeElapsed / DRIP_DURATION, this function will technically only distribute 100% of rewards if it is not called
        until the DRIP_DURATION has elapsed. This isn't too much of an issue--at worst, about 2/3 of the rewards will be distributed per DRIP_DURATION, the rest carrying over
        to the next DRIP_DURATION.
     * Note that if collateral == 0, tokens will not be disbursed. This prevents undefined behavior when rewards are deposited before collateral is.
     */
    function _disburseTau() internal {
        if (tauWithheld > 0) {
            uint256 _currentCollateral = IERC20(collateralToken).balanceOf(address(this));

            if (_currentCollateral > 0) {
                // Get tokens to disburse since last disbursal
                uint256 _timeElapsed = block.timestamp - tokensLastDisbursedTimestamp;

                uint256 _tokensToDisburse;
                if (_timeElapsed >= DRIP_DURATION) {
                    _tokensToDisburse = tauWithheld;
                    tauWithheld = 0;
                } else {
                    _tokensToDisburse = (_timeElapsed * tauWithheld) / DRIP_DURATION;
                    tauWithheld -= _tokensToDisburse;
                }

                // Divide by current collateral to get the additional tokensPerCollateral which we'll be adding to the cumulative sum
                uint256 _extraRewardPerCollateral = (_tokensToDisburse * Constants.PRECISION) / _currentCollateral;

                cumulativeTauRewardPerCollateral += _extraRewardPerCollateral;

                tokensLastDisbursedTimestamp = block.timestamp;
            }
        }
    }

    /**
     * @dev internal function to deposit TAU into the contract while averting sandwich attacks.
     * This is primarily meant to be called by the SwapHandler, which is the smart contract's source of TAU.
     * It is also called by the BaseVault when an account earns TAU rewards in excess of their debt.
     * Note that this function should generally only be called after disburseTau has been called.
     */
    function _withholdTau(uint256 amount) internal {
        // Update block.timestamp in case it hasn't been updated yet this transaction.
        tokensLastDisbursedTimestamp = block.timestamp;
        tauWithheld += amount;
    }

    uint256[45] private __gap;
}


// File taurus-contracts/contracts/Vault/SwapHandler.sol











// Libraries

abstract contract SwapHandler is FeeMapping, TauDripFeed {
    using SafeERC20 for IERC20;

    // Errors
    error notContract();
    error oracleCorrupt();
    error tokenCannotBeSwapped();
    error tooMuchSlippage(uint256 actualTauReturned, uint256 _minTauReturned);
    error unregisteredSwapAdapter();
    error zeroAmount();

    event Swap(address indexed fromToken, uint256 feesToProtocol, uint256 fromAmount, uint256 tauReturned);

    /**
     * @dev function called as part of the yield pull process. This will fetch swap modules from the Controller, use them 
        to handle a swap from vault yield to tau, then validate that the swap did not encounter too much slippage.
     * @param _yieldTokenAddress is the address of the token to be swapped. Must be a yield token, so cannot be the vault's collateral token or tau.
     * @param _yieldTokenAmount is the amount of yield token. Some will be transferred to the FeeSplitter for use by the protocol. The rest will be swapped for tau.
     * note that slippage parameters must be built based on the amount to be swapped, not based on _yieldTokenAmount above (some of which will not be swapped).
     * @param _swapAdapterHash is the hash of the swap adapter to be used, i.e. keccak256("UniswapSwapAdapter") for the UniswapSwapAdapter.
     * @param _rewardProportion refers to the proportion of received tau which will be rewarded (i.e. pay back user loans). The remainder will simply be burned without
     * being distributed to users. This undistributed tau cancels out bad debt in the vault. All vaults retain a growing reserve of yield to ensure bad debt
     * will always be covered.
     * _rewardProportion has a precision of 1e18. If _rewardProportion = 1e18, all tau will be disbursed to users. If _rewardProportion = 0, none of the burned tau will be disbursed.
     * @param _swapParams is the params to be passed to the SwapAdapter.
     * note that this function may only be called by a registered keeper.
     */
    function swapForTau(
        address _yieldTokenAddress,
        uint256 _yieldTokenAmount,
        uint256 _minTauReturned,
        bytes32 _swapAdapterHash,
        uint256 _rewardProportion,
        bytes calldata _swapParams
    ) external onlyKeeper whenNotPaused {
        // Ensure keeper is allowed to swap this token
        if (_yieldTokenAddress == collateralToken) {
            revert tokenCannotBeSwapped();
        }

        if (_yieldTokenAmount == 0) {
            revert zeroAmount();
        }

        // Get and validate swap adapter address
        address swapAdapterAddress = SwapAdapterRegistry(controller).swapAdapters(_swapAdapterHash);
        if (swapAdapterAddress == address(0)) {
            // The given hash has not yet been approved as a swap adapter.
            revert unregisteredSwapAdapter();
        }

        // Calculate portion of tokens which will be swapped for TAU and disbursed to the vault, and portion which will be sent to the protocol.
        uint256 protocolFees = (feeMapping[Constants.GLP_VAULT_PROTOCOL_FEE] * _yieldTokenAmount) /
            Constants.PERCENT_PRECISION;
        uint256 swapAmount = _yieldTokenAmount - protocolFees;

        // Transfer tokens to swap adapter
        IERC20(_yieldTokenAddress).safeTransfer(swapAdapterAddress, swapAmount);

        // Call swap function, which will transfer resulting tau back to this contract and return the amount transferred.
        // Note that this contract does not check that the swap adapter has transferred the correct amount of tau. This check
        // is handled by the swap adapter, and for this reason any registered swap adapter must be a completely trusted contract.
        uint256 tauReturned = BaseSwapAdapter(swapAdapterAddress).swap(tau, _swapParams);

        if (tauReturned < _minTauReturned) {
            revert tooMuchSlippage(tauReturned, _minTauReturned);
        }

        // Burn received Tau
        ERC20Burnable(tau).burn(tauReturned);

        // Add Tau rewards to withheldTAU to avert sandwich attacks
        _disburseTau();
        _withholdTau((tauReturned * _rewardProportion) / Constants.PERCENT_PRECISION);

        // Send protocol fees to FeeSplitter
        IERC20(_yieldTokenAddress).safeTransfer(
            Controller(controller).addressMapper(Constants.FEE_SPLITTER),
            protocolFees
        );

        // Emit event
        emit Swap(_yieldTokenAddress, protocolFees, swapAmount, tauReturned);
    }

    uint256[50] private __gap;
}


// File taurus-contracts/contracts/Vault/BaseVault.sol




// Contracts







// Libraries





// Note that this contract is not compatible with ERC777 tokens due to potential reentrancy concerns.
abstract contract BaseVault is SwapHandler, UUPSUpgradeable {
    using SafeERC20 for IERC20;
    using Address for address;

    /// Define the errors
    error insufficientCollateral();
    error userNotFound();
    error wrongLiquidationAmount();
    error incorrectDebtRepayAmount();
    error insufficientCollateralLiquidated(uint256 debtRepaid, uint256 collateralReceived);
    error cannotLiquidateHealthyAccount();

    // Events
    event Repay(address indexed _repayer, uint256 _amountTau);
    event Borrow(address indexed _borrower, uint256 _amountTau);
    event Deposit(address indexed _depositer, uint256 _amountAsset);
    event Withdraw(address indexed _withdrawer, uint256 _amountAsset);
    event AccountLiquidated(address _liquidator, address _account, uint256 _amount, uint256 _liqFees);
    event TauEarned(address indexed _account, uint256 _amount); // Emitted when a user's debt is cancelled

    struct UserDetails {
        uint256 collateral; // Collateral amount deposited by user
        uint256 debt; // Debt amount borrowed by user
        uint256 lastUpdatedRewardPerCollateral; // Last updated reward per collateral for the user
        uint256 startTimestamp; // Time when the first deposit was made by the user
    }

    /// @dev mapping of user and UserDetails
    mapping(address => UserDetails) public userDetails;

    /// @dev keep track of user addresses to index the userDetails for liquidation
    address[] public userAddresses;

    // Liquidation constants

    // Minimum collateral ratio
    uint256 public constant MIN_COL_RATIO = 1.2e18; // 120 %

    // Maximum collateral ratio an account can have after being liquidated (limits liquidation size to only what is necessary)
    uint256 public constant MAX_LIQ_COLL_RATIO = 1.3e18; // 130 %

    uint256 public constant MAX_LIQ_DISCOUNT = 0.2e18; // 20 %

    // 2% of the liquidated amount is sent to the FeeSplitter to fund protocol stability
    // and disincentivize self-liquidation
    uint256 public constant LIQUIDATION_SURCHARGE = 0.02e18;

    function __BaseVault_init(address _controller, address _tau, address _collateralToken) internal initializer {
        __Controllable_init(_controller);
        __TauDripFeed_init(_tau, _collateralToken);
    }

    /**
     * @dev modifier to update user's reward per collateral and pay off some of their debt. This is
        executed before any function that modifies a user's collateral or debt.
     * note if there is surplus TAU after the debt is paid off, it is added back to the drip feed.
     */
    modifier updateReward(address _account) {
        // Disburse available yield from the drip feed
        _disburseTau();

        // If user has collateral, pay down their debt and recycle surplus rewards back into the tauDripFeed.
        uint256 _userCollateral = userDetails[_account].collateral;
        if (_userCollateral > 0) {
            // Get diff between global rewardPerCollateral and user lastUpdatedRewardPerCollateral
            uint256 _rewardDiff = cumulativeTauRewardPerCollateral -
                userDetails[_account].lastUpdatedRewardPerCollateral;

            // Calculate user's TAU earned since the last update, use it to pay off debt
            uint256 _tauEarned = (_rewardDiff * _userCollateral) / Constants.PRECISION;

            if (_tauEarned > 0) {
                uint256 _userDebt = userDetails[_account].debt;
                if (_tauEarned > _userDebt) {
                    // If user has earned more than enough TAU to pay off their debt, pay off debt and add surplus to drip feed
                    userDetails[_account].debt = 0;

                    _withholdTau(_tauEarned - _userDebt);
                    _tauEarned = _userDebt;
                } else {
                    // Pay off as much debt as possible
                    userDetails[_account].debt = _userDebt - _tauEarned;
                }

                emit TauEarned(_account, _tauEarned);
            }
        } else {
            // If this is a new user, add them to the userAddresses array to keep track of them.
            if (userDetails[_account].startTimestamp == 0) {
                userAddresses.push(_account);
                userDetails[_account].startTimestamp = block.timestamp;
            }
        }

        // Update user lastUpdatedRewardPerCollateral
        userDetails[_account].lastUpdatedRewardPerCollateral = cumulativeTauRewardPerCollateral;
        _;
    }

    //------------------------------------------------------------View functions------------------------------------------------------------

    /// @dev In this function, we assume that TAU is worth $1 exactly. This allows users to arbitrage the difference, if any.
    function getAccountHealth(address _account) public view returns (bool) {
        uint256 ratio = _getCollRatio(_account);

        return (ratio > MIN_COL_RATIO);
    }

    /**
     * @dev calculate the max amount of debt that can be liquidated from an account
     * @param _account is the address of the account to be liquidated
     * @return maxRepay is the maximum amount of debt that can be liquidated from the account
     */
    function getMaxLiquidation(address _account) external view returns (uint256 maxRepay) {
        (uint256 price, uint8 decimals) = _getCollPrice();
        UserDetails memory accDetails = userDetails[_account];
        uint256 _collRatio = TauMath._computeCR(accDetails.collateral, accDetails.debt, price, decimals);

        // This call will revert if the account is healthy
        uint256 totalLiquidationDiscount = _calcLiquidationDiscount(_collRatio);

        maxRepay = _getMaxLiquidation(
            accDetails.collateral,
            accDetails.debt,
            price,
            decimals,
            totalLiquidationDiscount
        );
        return maxRepay;
    }

    /// @dev Get the number of users
    function getUsersCount() public view returns (uint256) {
        return userAddresses.length;
    }

    /** @dev Get the user details in the range given start and end index.
     * note the start and end index are inclusive
     */
    function getUsersDetailsInRange(uint256 _start, uint256 _end) public view returns (UserDetails[] memory users) {
        if (_end > getUsersCount() || _start > _end) revert indexOutOfBound();

        users = new UserDetails[](_end - _start + 1);

        for (uint i = _start; i < _end; ++i) {
            users[i - _start] = userDetails[userAddresses[i]];
        }
    }

    /** @dev Get the user addresses in the range given start and end index
     * note the start and end index are inclusive
     */
    function getUsers(uint256 _start, uint256 _end) public view returns (address[] memory users) {
        if (_end > getUsersCount() || _start > _end) revert indexOutOfBound();

        users = new address[](_end - _start + 1);

        for (uint256 i = _start; i < _end; ++i) {
            users[i - _start] = userAddresses[i];
        }
    }

    function _checkAccountHealth(address _account) internal view {
        if (!getAccountHealth(_account)) {
            revert insufficientCollateral();
        }
    }

    /// @dev In this function, we calculate the collateral ratio
    function _getCollRatio(address _account) internal view returns (uint256 ratio) {
        // Fetch the price from oracle manager
        (uint256 price, uint8 decimals) = _getCollPrice();

        // Check that user's collateral ratio is above minimum healthy ratio
        ratio = TauMath._computeCR(userDetails[_account].collateral, userDetails[_account].debt, price, decimals);
    }

    function _getCollPrice() internal view virtual returns (uint256 price, uint8 decimals) {
        bool success;

        // Fetch the price from oracle manager
        (price, decimals, success) = PriceOracleManager(
            Controller(controller).addressMapper(Constants.PRICE_ORACLE_MANAGER)
        ).getExternalPrice(collateralToken, abi.encodePacked(false));
        if (!success) {
            revert oracleCorrupt();
        }
    }

    //------------------------------------------------------------User functions------------------------------------------------------------

    function modifyPosition(
        uint256 _collateralDelta,
        uint256 _debtDelta,
        bool _increaseCollateral,
        bool _increaseDebt
    ) external whenNotPaused updateReward(msg.sender) {
        _modifyPosition(msg.sender, _collateralDelta, _debtDelta, _increaseCollateral, _increaseDebt);
    }

    /**
     * @dev Function allowing a user to automatically close their position.
     * Note that this function is available even when the contract is paused.
     * Note that since this function does not call updateReward, it should only be used when the contract is paused.
     *
     */
    function emergencyClosePosition() external {
        _modifyPosition(msg.sender, userDetails[msg.sender].collateral, userDetails[msg.sender].debt, false, false);
    }

    /**
     * @dev Find the max amount of debt that can be liquidated from an account.
     * @param _collateral is the amount of collateral the user has.
     * @param _debt is the amount of debt the user has.
     * @param _price is $ / collateral
     * @param _decimals is the number of decimals in price
     * @param _liquidationDiscount is the liquidation discount in percentage, e.g. 120% * PRECISION
     * @return maxRepay is the max amount of debt which can be repaid as part of the liquidation process, 0 if the user's account is healthy.
     */
    function _getMaxLiquidation(
        uint256 _collateral,
        uint256 _debt,
        uint256 _price,
        uint8 _decimals,
        uint256 _liquidationDiscount
    ) internal pure returns (uint256 maxRepay) {
        // Formula to find the liquidation amount is as follows
        // [(collateral * price) - (liqDiscount * liqAmount)] / (debt - liqAmount) = max liq ratio
        // Therefore
        // liqAmount = [(max liq ratio * debt) - (collateral * price)] / (max liq ratio - liqDiscount)
        maxRepay =
            ((MAX_LIQ_COLL_RATIO * _debt) - ((_collateral * _price * Constants.PRECISION) / (10 ** _decimals))) /
            (MAX_LIQ_COLL_RATIO - _liquidationDiscount);

        // Liquidators cannot repay more than the account's debt
        if (maxRepay > _debt) {
            maxRepay = _debt;
        }

        return maxRepay;
    }

    //------------------------------------------------------------BaseVault internal functions------------------------------------------------------------

    /**
     * @dev function to modify user collateral and debt in any way. If debt is increased or collateral reduced, the account must be healthy at the end of the tx.
     * note that generally this function is called after updateReward, meaning that user details are up to date.
     * @param _account is the account to be modified
     * @param _collateralDelta is the absolute value of the change in collateral.
     *  note that withdrawals cannot attempt to withdraw more than the user collateral balance, or the transaction will revert.
     * @param _debtDelta is the absolute value of the change in debt
     *  note that repayments can attempt to repay more than their debt balance. Only their debt balance will be pulled, and used to cancel out their debt.
     * @param _increaseCollateral is true if collateral is being deposited, false if collateralDelta is 0 or collateral is being withdrawn
     * @param _increaseDebt is true if debt is being borrowed, false if debtDelta is 0 or debt is being repaid
     */
    function _modifyPosition(
        address _account,
        uint256 _collateralDelta,
        uint256 _debtDelta,
        bool _increaseCollateral,
        bool _increaseDebt
    ) internal virtual {
        bool mustCheckHealth; // False until an action is taken which can reduce account health

        // Handle debt first, since TAU has no reentrancy concerns.
        if (_debtDelta != 0) {
            if (_increaseDebt) {
                // Borrow TAU from the vault
                userDetails[_account].debt += _debtDelta;
                mustCheckHealth = true;
                TAU(tau).mint(_account, _debtDelta);

                emit Borrow(_account, _debtDelta);
            } else {
                // Repay TAU debt
                uint256 currentDebt = userDetails[_account].debt;
                if (_debtDelta > currentDebt) _debtDelta = currentDebt;
                userDetails[_account].debt = currentDebt - _debtDelta;
                // Burn Tau used to repay debt
                TAU(tau).burnFrom(_account, _debtDelta);

                emit Repay(_account, _debtDelta);
            }
        }

        if (_collateralDelta != 0) {
            if (_increaseCollateral) {
                // Deposit collateral
                userDetails[_account].collateral += _collateralDelta;
                IERC20(collateralToken).safeTransferFrom(msg.sender, address(this), _collateralDelta);

                emit Deposit(_account, _collateralDelta);
            } else {
                // Withdraw collateral
                uint256 currentCollateral = userDetails[_account].collateral;
                if (_collateralDelta > currentCollateral) revert insufficientCollateral();
                userDetails[_account].collateral = currentCollateral - _collateralDelta;
                mustCheckHealth = true;
                IERC20(collateralToken).safeTransfer(msg.sender, _collateralDelta);

                emit Withdraw(_account, _collateralDelta);
            }
        }

        if (mustCheckHealth) {
            _checkAccountHealth(_account);
        }
    }

    //------------------------------------------------------------Liquidator/governance functions------------------------------------------------------------

    /**
     * @param _account is the account to be liquidated. It must be unhealthy.
     * @param _debtAmount is the amount of debt to be repaid. It must be greater than 0. If the entire account is liquidateable, an arbitrarily
     high debt amount will signal that the entire account should be liquidated. Otherwise, _debtAmount must be less than or equal to the max
     debt which can be liquidated from the acount.
     * @param _minExchangeRate represents the minimum number of collateral tokens which the liquidator is willing to receive in exchange for 
      1 debt token. A value of PRECISION will mean that the liquidation will revert unless the liquidator receives at least 1 collateral per
      debt token repaid. A value of 0 means that slippage is not checked, and the liquidator will accept whatever the exchange rate happens to be.
     * @return true if the liquidation was successful
     */
    function liquidate(
        address _account,
        uint256 _debtAmount,
        uint256 _minExchangeRate
    ) external onlyLiquidator whenNotPaused updateReward(_account) returns (bool) {
        if (_debtAmount == 0) revert wrongLiquidationAmount();

        UserDetails memory accDetails = userDetails[_account];

        // Since Taurus accounts' debt continuously decreases, liquidators may pass in an arbitrarily large number in order to
        // request to liquidate the entire account.
        if (_debtAmount > accDetails.debt) {
            _debtAmount = accDetails.debt;
        }

        // Get total fee charged to the user for this liquidation. Collateral equal to (liquidated taurus debt value * feeMultiplier) will be deducted from the user's account.
        // This call reverts if the account is healthy or if the liquidation amount is too large.
        (uint256 collateralToLiquidate, uint256 liquidationSurcharge) = _calcLiquidation(
            accDetails.collateral,
            accDetails.debt,
            _debtAmount
        );

        // Check that collateral received is sufficient for liquidator
        uint256 collateralToLiquidator = collateralToLiquidate - liquidationSurcharge;
        if (collateralToLiquidator < (_debtAmount * _minExchangeRate) / Constants.PRECISION) {
            revert insufficientCollateralLiquidated(_debtAmount, collateralToLiquidator);
        }

        // Update user info
        userDetails[_account].collateral = accDetails.collateral - collateralToLiquidate;
        userDetails[_account].debt = accDetails.debt - _debtAmount;

        // Burn liquidator's Tau
        TAU(tau).burnFrom(msg.sender, _debtAmount);

        // Transfer part of _debtAmount to liquidator and Taurus as fees for liquidation
        IERC20(collateralToken).safeTransfer(msg.sender, collateralToLiquidator);
        IERC20(collateralToken).safeTransfer(
            Controller(controller).addressMapper(Constants.FEE_SPLITTER),
            liquidationSurcharge
        );

        emit AccountLiquidated(msg.sender, _account, collateralToLiquidate, liquidationSurcharge);

        return true;
    }

    /**
     * @dev calculate relevant liquidation parameters. If 100 TAU are liquidated, and the discount is 105%, then 100 * 1.05 = 105 TAU worth of collateral
     * will be liquidated.
     * @return collateralToLiquidate is the amount of the user's collateral which will be liquidated
     * @return liquidationSurcharge is the amount of collateral which will be sent to the Taurus treasury as a liquidation fee
     */
    function _calcLiquidation(
        uint256 _accountCollateral,
        uint256 _accountDebt,
        uint256 _debtToLiquidate
    ) internal view returns (uint256 collateralToLiquidate, uint256 liquidationSurcharge) {
        (uint256 price, uint8 decimals) = _getCollPrice();
        uint256 _collRatio = TauMath._computeCR(_accountCollateral, _accountDebt, price, decimals);

        uint256 totalLiquidationDiscount = _calcLiquidationDiscount(_collRatio);

        uint256 collateralToLiquidateWithoutDiscount = (_debtToLiquidate * (10 ** decimals)) / price;
        collateralToLiquidate = (collateralToLiquidateWithoutDiscount * totalLiquidationDiscount) / Constants.PRECISION;
        if (collateralToLiquidate > _accountCollateral) {
            collateralToLiquidate = _accountCollateral;
        }

        // Revert if requested liquidation amount is greater than allowed
        if (
            _debtToLiquidate >
            _getMaxLiquidation(_accountCollateral, _accountDebt, price, decimals, totalLiquidationDiscount)
        ) revert wrongLiquidationAmount();

        return (
            collateralToLiquidate,
            (collateralToLiquidateWithoutDiscount * LIQUIDATION_SURCHARGE) / Constants.PRECISION
        );
    }

    /**
     * @dev calculate the current liquidation discount for a given account
     * @return liquidationDiscount -- the discount applied to the price of the user's collateral. If 100 TAU of debt are liquidated, 100 * liquidationDiscount / PRECISION collateral 
     will be liquidated.
     * note that the calculated discount includes the liquidation surcharge, so not all of the discounted funds will be sent to the liquidator.
     * note that the discount cannot exceed MAX_LIQ_DISCOUNT.
     * The liquidation discount may be any value in the range of (PRECISION, MAX_LIQ_DISCOUNT]. 
     */
    function _calcLiquidationDiscount(uint256 _accountHealth) internal pure returns (uint256 liquidationDiscount) {
        if (_accountHealth >= MIN_COL_RATIO) {
            revert cannotLiquidateHealthyAccount();
        }

        // The liquidator's discount on user funds is based on how far underwater the position is, to simulate a dutch auction.
        // The discount is capped at MAX_LIQ_DISCOUNT.
        uint256 diff = (MIN_COL_RATIO + LIQUIDATION_SURCHARGE) - _accountHealth;
        if (diff > MAX_LIQ_DISCOUNT) {
            diff = MAX_LIQ_DISCOUNT;
        }

        liquidationDiscount = Constants.PRECISION + diff;
    }

    /**
     * @dev Updates a user's rewards. Callable by anyone, but really only useful for keepers
     *  to update inactive accounts (thus redistributing their excess rewards to the vault).
     * @param _account is the account whose rewards will be updated
     */
    function updateRewards(address _account) external whenNotPaused updateReward(_account) {}

    function _authorizeUpgrade(address newImplementation) internal virtual override onlyGovernor {}

    uint256[48] private __gap;
}


// File taurus-contracts/contracts/Vault/YieldAdapters/GMX/IRewardRouter.sol




interface IRewardRouter {
    function claimFees() external;

    function compound() external;
}


// File taurus-contracts/contracts/Vault/YieldAdapters/GMX/GmxYieldAdapter.sol





contract GmxYieldAdapter is BaseVault {
    // Reward router for GMX. Note that this must be V1, not V2, for now.
    address public rewardRouter;

    function initialize(
        address _controller,
        address _tau,
        address _collateralToken,
        address _rewardRouter
    ) external initializer {
        __BaseVault_init(_controller, _tau, _collateralToken);
        rewardRouter = _rewardRouter;
    }

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() {
        _disableInitializers();
    }

    // Vault management functions

    /**
     * @dev function to collect yield from Gmx. Callable by anyone since we have sandwich attack protections in place.
     * Note that we do not vest any esGmx tokens. They are simply staked immediately. Long-term this will lead to greater protocol yield.
     */
    function collectYield() external {
        IRewardRouter(rewardRouter).claimFees(); // Claim WETH yield from staked esGmx and Glp
        IRewardRouter(rewardRouter).compound(); // Claim and stake esGmx and bnGmx earned from staked esGmx and Glp
    }

    function updateRewardRouter(address _newRewardRouter) external onlyMultisig {
        rewardRouter = _newRewardRouter;
    }

    uint256[49] private __gap;
}
