// SPDX-License-Identifier: MIT
pragma solidity ^0.8.13;

// contracts/lib/openzeppelin-contracts/contracts/interfaces/IERC1271.sol

// OpenZeppelin Contracts v4.4.1 (interfaces/IERC1271.sol)

/**
 * @dev Interface of the ERC1271 standard signature validation method for
 * contracts as defined in https://eips.ethereum.org/EIPS/eip-1271[ERC-1271].
 *
 * _Available since v4.1._
 */
interface IERC1271 {
    /**
     * @dev Should return whether the signature provided is valid for the provided data
     * @param hash      Hash of the data to be signed
     * @param signature Signature byte array associated with _data
     */
    function isValidSignature(bytes32 hash, bytes memory signature) external view returns (bytes4 magicValue);
}

// contracts/lib/openzeppelin-contracts/contracts/utils/Address.sol

// OpenZeppelin Contracts (last updated v4.5.0) (utils/Address.sol)

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
        return functionCall(target, data, "Address: low-level call failed");
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
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResult(success, returndata, errorMessage);
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
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResult(success, returndata, errorMessage);
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
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verifies that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason using the provided one.
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
}

// contracts/lib/openzeppelin-contracts/contracts/utils/Context.sol

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

// contracts/lib/openzeppelin-contracts/contracts/utils/Strings.sol

// OpenZeppelin Contracts v4.4.1 (utils/Strings.sol)

/**
 * @dev String operations.
 */
library Strings {
    bytes16 private constant _HEX_SYMBOLS = "0123456789abcdef";
    uint8 private constant _ADDRESS_LENGTH = 20;

    /**
     * @dev Converts a `uint256` to its ASCII `string` decimal representation.
     */
    function toString(uint256 value) internal pure returns (string memory) {
        // Inspired by OraclizeAPI's implementation - MIT licence
        // https://github.com/oraclize/ethereum-api/blob/b42146b063c7d6ee1358846c198246239e9360e8/oraclizeAPI_0.4.25.sol

        if (value == 0) {
            return "0";
        }
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }
        return string(buffer);
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation.
     */
    function toHexString(uint256 value) internal pure returns (string memory) {
        if (value == 0) {
            return "0x00";
        }
        uint256 temp = value;
        uint256 length = 0;
        while (temp != 0) {
            length++;
            temp >>= 8;
        }
        return toHexString(value, length);
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation with fixed length.
     */
    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        bytes memory buffer = new bytes(2 * length + 2);
        buffer[0] = "0";
        buffer[1] = "x";
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = _HEX_SYMBOLS[value & 0xf];
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

// contracts/lib/solmate/src/tokens/ERC20.sol

/// @notice Modern and gas efficient ERC20 + EIP-2612 implementation.
/// @author Solmate (https://github.com/Rari-Capital/solmate/blob/main/src/tokens/ERC20.sol)
/// @author Modified from Uniswap (https://github.com/Uniswap/uniswap-v2-core/blob/master/contracts/UniswapV2ERC20.sol)
/// @dev Do not manually set balances without updating totalSupply, as the sum of all user balances must not exceed it.
abstract contract ERC20 {
    /*//////////////////////////////////////////////////////////////
                                 EVENTS
    //////////////////////////////////////////////////////////////*/

    event Transfer(address indexed from, address indexed to, uint256 amount);

    event Approval(address indexed owner, address indexed spender, uint256 amount);

    /*//////////////////////////////////////////////////////////////
                            METADATA STORAGE
    //////////////////////////////////////////////////////////////*/

    string public name;

    string public symbol;

    uint8 public immutable decimals;

    /*//////////////////////////////////////////////////////////////
                              ERC20 STORAGE
    //////////////////////////////////////////////////////////////*/

    uint256 public totalSupply;

    mapping(address => uint256) public balanceOf;

    mapping(address => mapping(address => uint256)) public allowance;

    /*//////////////////////////////////////////////////////////////
                            EIP-2612 STORAGE
    //////////////////////////////////////////////////////////////*/

    uint256 internal immutable INITIAL_CHAIN_ID;

    bytes32 internal immutable INITIAL_DOMAIN_SEPARATOR;

    mapping(address => uint256) public nonces;

    /*//////////////////////////////////////////////////////////////
                               CONSTRUCTOR
    //////////////////////////////////////////////////////////////*/

    constructor(
        string memory _name,
        string memory _symbol,
        uint8 _decimals
    ) {
        name = _name;
        symbol = _symbol;
        decimals = _decimals;

        INITIAL_CHAIN_ID = block.chainid;
        INITIAL_DOMAIN_SEPARATOR = computeDomainSeparator();
    }

    /*//////////////////////////////////////////////////////////////
                               ERC20 LOGIC
    //////////////////////////////////////////////////////////////*/

    function approve(address spender, uint256 amount) public virtual returns (bool) {
        allowance[msg.sender][spender] = amount;

        emit Approval(msg.sender, spender, amount);

        return true;
    }

    function transfer(address to, uint256 amount) public virtual returns (bool) {
        balanceOf[msg.sender] -= amount;

        // Cannot overflow because the sum of all user
        // balances can't exceed the max uint256 value.
        unchecked {
            balanceOf[to] += amount;
        }

        emit Transfer(msg.sender, to, amount);

        return true;
    }

    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) public virtual returns (bool) {
        uint256 allowed = allowance[from][msg.sender]; // Saves gas for limited approvals.

        if (allowed != type(uint256).max) allowance[from][msg.sender] = allowed - amount;

        balanceOf[from] -= amount;

        // Cannot overflow because the sum of all user
        // balances can't exceed the max uint256 value.
        unchecked {
            balanceOf[to] += amount;
        }

        emit Transfer(from, to, amount);

        return true;
    }

    /*//////////////////////////////////////////////////////////////
                             EIP-2612 LOGIC
    //////////////////////////////////////////////////////////////*/

    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) public virtual {
        require(deadline >= block.timestamp, "PERMIT_DEADLINE_EXPIRED");

        // Unchecked because the only math done is incrementing
        // the owner's nonce which cannot realistically overflow.
        unchecked {
            address recoveredAddress = ecrecover(
                keccak256(
                    abi.encodePacked(
                        "\x19\x01",
                        DOMAIN_SEPARATOR(),
                        keccak256(
                            abi.encode(
                                keccak256(
                                    "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"
                                ),
                                owner,
                                spender,
                                value,
                                nonces[owner]++,
                                deadline
                            )
                        )
                    )
                ),
                v,
                r,
                s
            );

            require(recoveredAddress != address(0) && recoveredAddress == owner, "INVALID_SIGNER");

            allowance[recoveredAddress][spender] = value;
        }

        emit Approval(owner, spender, value);
    }

    function DOMAIN_SEPARATOR() public view virtual returns (bytes32) {
        return block.chainid == INITIAL_CHAIN_ID ? INITIAL_DOMAIN_SEPARATOR : computeDomainSeparator();
    }

    function computeDomainSeparator() internal view virtual returns (bytes32) {
        return
            keccak256(
                abi.encode(
                    keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                    keccak256(bytes(name)),
                    keccak256("1"),
                    block.chainid,
                    address(this)
                )
            );
    }

    /*//////////////////////////////////////////////////////////////
                        INTERNAL MINT/BURN LOGIC
    //////////////////////////////////////////////////////////////*/

    function _mint(address to, uint256 amount) internal virtual {
        totalSupply += amount;

        // Cannot overflow because the sum of all user
        // balances can't exceed the max uint256 value.
        unchecked {
            balanceOf[to] += amount;
        }

        emit Transfer(address(0), to, amount);
    }

    function _burn(address from, uint256 amount) internal virtual {
        balanceOf[from] -= amount;

        // Cannot underflow because a user's balance
        // will never be larger than the total supply.
        unchecked {
            totalSupply -= amount;
        }

        emit Transfer(from, address(0), amount);
    }
}

// contracts/lib/solmate/src/tokens/ERC721.sol

/// @notice Modern, minimalist, and gas efficient ERC-721 implementation.
/// @author Solmate (https://github.com/Rari-Capital/solmate/blob/main/src/tokens/ERC721.sol)
abstract contract ERC721 {
    /*//////////////////////////////////////////////////////////////
                                 EVENTS
    //////////////////////////////////////////////////////////////*/

    event Transfer(address indexed from, address indexed to, uint256 indexed id);

    event Approval(address indexed owner, address indexed spender, uint256 indexed id);

    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);

    /*//////////////////////////////////////////////////////////////
                         METADATA STORAGE/LOGIC
    //////////////////////////////////////////////////////////////*/

    string public name;

    string public symbol;

    function tokenURI(uint256 id) public view virtual returns (string memory);

    /*//////////////////////////////////////////////////////////////
                      ERC721 BALANCE/OWNER STORAGE
    //////////////////////////////////////////////////////////////*/

    mapping(uint256 => address) internal _ownerOf;

    mapping(address => uint256) internal _balanceOf;

    function ownerOf(uint256 id) public view virtual returns (address owner) {
        require((owner = _ownerOf[id]) != address(0), "NOT_MINTED");
    }

    function balanceOf(address owner) public view virtual returns (uint256) {
        require(owner != address(0), "ZERO_ADDRESS");

        return _balanceOf[owner];
    }

    /*//////////////////////////////////////////////////////////////
                         ERC721 APPROVAL STORAGE
    //////////////////////////////////////////////////////////////*/

    mapping(uint256 => address) public getApproved;

    mapping(address => mapping(address => bool)) public isApprovedForAll;

    /*//////////////////////////////////////////////////////////////
                               CONSTRUCTOR
    //////////////////////////////////////////////////////////////*/

    constructor(string memory _name, string memory _symbol) {
        name = _name;
        symbol = _symbol;
    }

    /*//////////////////////////////////////////////////////////////
                              ERC721 LOGIC
    //////////////////////////////////////////////////////////////*/

    function approve(address spender, uint256 id) public virtual {
        address owner = _ownerOf[id];

        require(msg.sender == owner || isApprovedForAll[owner][msg.sender], "NOT_AUTHORIZED");

        getApproved[id] = spender;

        emit Approval(owner, spender, id);
    }

    function setApprovalForAll(address operator, bool approved) public virtual {
        isApprovedForAll[msg.sender][operator] = approved;

        emit ApprovalForAll(msg.sender, operator, approved);
    }

    function transferFrom(
        address from,
        address to,
        uint256 id
    ) public virtual {
        require(from == _ownerOf[id], "WRONG_FROM");

        require(to != address(0), "INVALID_RECIPIENT");

        require(
            msg.sender == from || isApprovedForAll[from][msg.sender] || msg.sender == getApproved[id],
            "NOT_AUTHORIZED"
        );

        // Underflow of the sender's balance is impossible because we check for
        // ownership above and the recipient's balance can't realistically overflow.
        unchecked {
            _balanceOf[from]--;

            _balanceOf[to]++;
        }

        _ownerOf[id] = to;

        delete getApproved[id];

        emit Transfer(from, to, id);
    }

    function safeTransferFrom(
        address from,
        address to,
        uint256 id
    ) public virtual {
        transferFrom(from, to, id);

        require(
            to.code.length == 0 ||
                ERC721TokenReceiver(to).onERC721Received(msg.sender, from, id, "") ==
                ERC721TokenReceiver.onERC721Received.selector,
            "UNSAFE_RECIPIENT"
        );
    }

    function safeTransferFrom(
        address from,
        address to,
        uint256 id,
        bytes calldata data
    ) public virtual {
        transferFrom(from, to, id);

        require(
            to.code.length == 0 ||
                ERC721TokenReceiver(to).onERC721Received(msg.sender, from, id, data) ==
                ERC721TokenReceiver.onERC721Received.selector,
            "UNSAFE_RECIPIENT"
        );
    }

    /*//////////////////////////////////////////////////////////////
                              ERC165 LOGIC
    //////////////////////////////////////////////////////////////*/

    function supportsInterface(bytes4 interfaceId) public view virtual returns (bool) {
        return
            interfaceId == 0x01ffc9a7 || // ERC165 Interface ID for ERC165
            interfaceId == 0x80ac58cd || // ERC165 Interface ID for ERC721
            interfaceId == 0x5b5e139f; // ERC165 Interface ID for ERC721Metadata
    }

    /*//////////////////////////////////////////////////////////////
                        INTERNAL MINT/BURN LOGIC
    //////////////////////////////////////////////////////////////*/

    function _mint(address to, uint256 id) internal virtual {
        require(to != address(0), "INVALID_RECIPIENT");

        require(_ownerOf[id] == address(0), "ALREADY_MINTED");

        // Counter overflow is incredibly unrealistic.
        unchecked {
            _balanceOf[to]++;
        }

        _ownerOf[id] = to;

        emit Transfer(address(0), to, id);
    }

    function _burn(uint256 id) internal virtual {
        address owner = _ownerOf[id];

        require(owner != address(0), "NOT_MINTED");

        // Ownership check above ensures no underflow.
        unchecked {
            _balanceOf[owner]--;
        }

        delete _ownerOf[id];

        delete getApproved[id];

        emit Transfer(owner, address(0), id);
    }

    /*//////////////////////////////////////////////////////////////
                        INTERNAL SAFE MINT LOGIC
    //////////////////////////////////////////////////////////////*/

    function _safeMint(address to, uint256 id) internal virtual {
        _mint(to, id);

        require(
            to.code.length == 0 ||
                ERC721TokenReceiver(to).onERC721Received(msg.sender, address(0), id, "") ==
                ERC721TokenReceiver.onERC721Received.selector,
            "UNSAFE_RECIPIENT"
        );
    }

    function _safeMint(
        address to,
        uint256 id,
        bytes memory data
    ) internal virtual {
        _mint(to, id);

        require(
            to.code.length == 0 ||
                ERC721TokenReceiver(to).onERC721Received(msg.sender, address(0), id, data) ==
                ERC721TokenReceiver.onERC721Received.selector,
            "UNSAFE_RECIPIENT"
        );
    }
}

/// @notice A generic interface for a contract which properly accepts ERC721 tokens.
/// @author Solmate (https://github.com/Rari-Capital/solmate/blob/main/src/tokens/ERC721.sol)
abstract contract ERC721TokenReceiver {
    function onERC721Received(
        address,
        address,
        uint256,
        bytes calldata
    ) external virtual returns (bytes4) {
        return ERC721TokenReceiver.onERC721Received.selector;
    }
}

// contracts/src/lib/IWETH.sol

interface IWETH {
    event Approval(address indexed src, address indexed guy, uint256 wad);
    event Transfer(address indexed src, address indexed dst, uint256 wad);
    event Deposit(address indexed dst, uint256 wad);
    event Withdrawal(address indexed src, uint256 wad);

    function deposit() external payable;

    function withdraw(uint256 wad) external;

    function totalSupply() external view returns (uint256);

    function approve(address guy, uint256 wad) external returns (bool);

    function transfer(address dst, uint256 wad) external returns (bool);

    function transferFrom(
        address src,
        address dst,
        uint256 wad
    ) external returns (bool);
}

// contracts/lib/openzeppelin-contracts/contracts/access/Ownable.sol

// OpenZeppelin Contracts v4.4.1 (access/Ownable.sol)

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
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
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

// contracts/lib/openzeppelin-contracts/contracts/utils/cryptography/ECDSA.sol

// OpenZeppelin Contracts (last updated v4.5.0) (utils/cryptography/ECDSA.sol)

/**
 * @dev Elliptic Curve Digital Signature Algorithm (ECDSA) operations.
 *
 * These functions can be used to verify that a message was signed by the holder
 * of the private keys of a given address.
 */
library ECDSA {
    enum RecoverError {
        NoError,
        InvalidSignature,
        InvalidSignatureLength,
        InvalidSignatureS,
        InvalidSignatureV
    }

    function _throwError(RecoverError error) private pure {
        if (error == RecoverError.NoError) {
            return; // no error: do nothing
        } else if (error == RecoverError.InvalidSignature) {
            revert("ECDSA: invalid signature");
        } else if (error == RecoverError.InvalidSignatureLength) {
            revert("ECDSA: invalid signature length");
        } else if (error == RecoverError.InvalidSignatureS) {
            revert("ECDSA: invalid signature 's' value");
        } else if (error == RecoverError.InvalidSignatureV) {
            revert("ECDSA: invalid signature 'v' value");
        }
    }

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature` or error string. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM opcode allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {toEthSignedMessageHash} on it.
     *
     * Documentation for signature generation:
     * - with https://web3js.readthedocs.io/en/v1.3.4/web3-eth-accounts.html#sign[Web3.js]
     * - with https://docs.ethers.io/v5/api/signer/#Signer-signMessage[ethers]
     *
     * _Available since v4.3._
     */
    function tryRecover(bytes32 hash, bytes memory signature) internal pure returns (address, RecoverError) {
        // Check the signature length
        // - case 65: r,s,v signature (standard)
        // - case 64: r,vs signature (cf https://eips.ethereum.org/EIPS/eip-2098) _Available since v4.1._
        if (signature.length == 65) {
            bytes32 r;
            bytes32 s;
            uint8 v;
            // ecrecover takes the signature parameters, and the only way to get them
            // currently is to use assembly.
            /// @solidity memory-safe-assembly
            assembly {
                r := mload(add(signature, 0x20))
                s := mload(add(signature, 0x40))
                v := byte(0, mload(add(signature, 0x60)))
            }
            return tryRecover(hash, v, r, s);
        } else if (signature.length == 64) {
            bytes32 r;
            bytes32 vs;
            // ecrecover takes the signature parameters, and the only way to get them
            // currently is to use assembly.
            /// @solidity memory-safe-assembly
            assembly {
                r := mload(add(signature, 0x20))
                vs := mload(add(signature, 0x40))
            }
            return tryRecover(hash, r, vs);
        } else {
            return (address(0), RecoverError.InvalidSignatureLength);
        }
    }

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature`. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM opcode allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {toEthSignedMessageHash} on it.
     */
    function recover(bytes32 hash, bytes memory signature) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, signature);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `r` and `vs` short-signature fields separately.
     *
     * See https://eips.ethereum.org/EIPS/eip-2098[EIP-2098 short signatures]
     *
     * _Available since v4.3._
     */
    function tryRecover(
        bytes32 hash,
        bytes32 r,
        bytes32 vs
    ) internal pure returns (address, RecoverError) {
        bytes32 s = vs & bytes32(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
        uint8 v = uint8((uint256(vs) >> 255) + 27);
        return tryRecover(hash, v, r, s);
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `r and `vs` short-signature fields separately.
     *
     * _Available since v4.2._
     */
    function recover(
        bytes32 hash,
        bytes32 r,
        bytes32 vs
    ) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, r, vs);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `v`,
     * `r` and `s` signature fields separately.
     *
     * _Available since v4.3._
     */
    function tryRecover(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal pure returns (address, RecoverError) {
        // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
        // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
        // the valid range for s in (301): 0 < s < secp256k1n ÷ 2 + 1, and for v in (302): v ∈ {27, 28}. Most
        // signatures from current libraries generate a unique signature with an s-value in the lower half order.
        //
        // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
        // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
        // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
        // these malleable signatures as well.
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return (address(0), RecoverError.InvalidSignatureS);
        }
        if (v != 27 && v != 28) {
            return (address(0), RecoverError.InvalidSignatureV);
        }

        // If the signature is valid (and not malleable), return the signer address
        address signer = ecrecover(hash, v, r, s);
        if (signer == address(0)) {
            return (address(0), RecoverError.InvalidSignature);
        }

        return (signer, RecoverError.NoError);
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `v`,
     * `r` and `s` signature fields separately.
     */
    function recover(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal pure returns (address) {
        (address recovered, RecoverError error) = tryRecover(hash, v, r, s);
        _throwError(error);
        return recovered;
    }

    /**
     * @dev Returns an Ethereum Signed Message, created from a `hash`. This
     * produces hash corresponding to the one signed with the
     * https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`]
     * JSON-RPC method as part of EIP-191.
     *
     * See {recover}.
     */
    function toEthSignedMessageHash(bytes32 hash) internal pure returns (bytes32) {
        // 32 is the length in bytes of hash,
        // enforced by the type signature above
        return keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n32", hash));
    }

    /**
     * @dev Returns an Ethereum Signed Message, created from `s`. This
     * produces hash corresponding to the one signed with the
     * https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`]
     * JSON-RPC method as part of EIP-191.
     *
     * See {recover}.
     */
    function toEthSignedMessageHash(bytes memory s) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n", Strings.toString(s.length), s));
    }

    /**
     * @dev Returns an Ethereum Signed Typed Data, created from a
     * `domainSeparator` and a `structHash`. This produces hash corresponding
     * to the one signed with the
     * https://eips.ethereum.org/EIPS/eip-712[`eth_signTypedData`]
     * JSON-RPC method as part of EIP-712.
     *
     * See {recover}.
     */
    function toTypedDataHash(bytes32 domainSeparator, bytes32 structHash) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));
    }
}

// contracts/lib/solmate/src/utils/SafeTransferLib.sol

/// @notice Safe ETH and ERC20 transfer library that gracefully handles missing return values.
/// @author Solmate (https://github.com/Rari-Capital/solmate/blob/main/src/utils/SafeTransferLib.sol)
/// @dev Use with caution! Some functions in this library knowingly create dirty bits at the destination of the free memory pointer.
/// @dev Note that none of the functions in this library check that a token has code at all! That responsibility is delegated to the caller.
library SafeTransferLib {
    /*//////////////////////////////////////////////////////////////
                             ETH OPERATIONS
    //////////////////////////////////////////////////////////////*/

    function safeTransferETH(address to, uint256 amount) internal {
        bool success;

        assembly {
            // Transfer the ETH and store if it succeeded or not.
            success := call(gas(), to, amount, 0, 0, 0, 0)
        }

        require(success, "ETH_TRANSFER_FAILED");
    }

    /*//////////////////////////////////////////////////////////////
                            ERC20 OPERATIONS
    //////////////////////////////////////////////////////////////*/

    function safeTransferFrom(
        ERC20 token,
        address from,
        address to,
        uint256 amount
    ) internal {
        bool success;

        assembly {
            // Get a pointer to some free memory.
            let freeMemoryPointer := mload(0x40)

            // Write the abi-encoded calldata into memory, beginning with the function selector.
            mstore(freeMemoryPointer, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
            mstore(add(freeMemoryPointer, 4), from) // Append the "from" argument.
            mstore(add(freeMemoryPointer, 36), to) // Append the "to" argument.
            mstore(add(freeMemoryPointer, 68), amount) // Append the "amount" argument.

            success := and(
                // Set success to whether the call reverted, if not we check it either
                // returned exactly 1 (can't just be non-zero data), or had no return data.
                or(and(eq(mload(0), 1), gt(returndatasize(), 31)), iszero(returndatasize())),
                // We use 100 because the length of our calldata totals up like so: 4 + 32 * 3.
                // We use 0 and 32 to copy up to 32 bytes of return data into the scratch space.
                // Counterintuitively, this call must be positioned second to the or() call in the
                // surrounding and() call or else returndatasize() will be zero during the computation.
                call(gas(), token, 0, freeMemoryPointer, 100, 0, 32)
            )
        }

        require(success, "TRANSFER_FROM_FAILED");
    }

    function safeTransfer(
        ERC20 token,
        address to,
        uint256 amount
    ) internal {
        bool success;

        assembly {
            // Get a pointer to some free memory.
            let freeMemoryPointer := mload(0x40)

            // Write the abi-encoded calldata into memory, beginning with the function selector.
            mstore(freeMemoryPointer, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
            mstore(add(freeMemoryPointer, 4), to) // Append the "to" argument.
            mstore(add(freeMemoryPointer, 36), amount) // Append the "amount" argument.

            success := and(
                // Set success to whether the call reverted, if not we check it either
                // returned exactly 1 (can't just be non-zero data), or had no return data.
                or(and(eq(mload(0), 1), gt(returndatasize(), 31)), iszero(returndatasize())),
                // We use 68 because the length of our calldata totals up like so: 4 + 32 * 2.
                // We use 0 and 32 to copy up to 32 bytes of return data into the scratch space.
                // Counterintuitively, this call must be positioned second to the or() call in the
                // surrounding and() call or else returndatasize() will be zero during the computation.
                call(gas(), token, 0, freeMemoryPointer, 68, 0, 32)
            )
        }

        require(success, "TRANSFER_FAILED");
    }

    function safeApprove(
        ERC20 token,
        address to,
        uint256 amount
    ) internal {
        bool success;

        assembly {
            // Get a pointer to some free memory.
            let freeMemoryPointer := mload(0x40)

            // Write the abi-encoded calldata into memory, beginning with the function selector.
            mstore(freeMemoryPointer, 0x095ea7b300000000000000000000000000000000000000000000000000000000)
            mstore(add(freeMemoryPointer, 4), to) // Append the "to" argument.
            mstore(add(freeMemoryPointer, 36), amount) // Append the "amount" argument.

            success := and(
                // Set success to whether the call reverted, if not we check it either
                // returned exactly 1 (can't just be non-zero data), or had no return data.
                or(and(eq(mload(0), 1), gt(returndatasize(), 31)), iszero(returndatasize())),
                // We use 68 because the length of our calldata totals up like so: 4 + 32 * 2.
                // We use 0 and 32 to copy up to 32 bytes of return data into the scratch space.
                // Counterintuitively, this call must be positioned second to the or() call in the
                // surrounding and() call or else returndatasize() will be zero during the computation.
                call(gas(), token, 0, freeMemoryPointer, 68, 0, 32)
            )
        }

        require(success, "APPROVE_FAILED");
    }
}

// contracts/lib/openzeppelin-contracts/contracts/utils/cryptography/draft-EIP712.sol

// OpenZeppelin Contracts v4.4.1 (utils/cryptography/draft-EIP712.sol)

/**
 * @dev https://eips.ethereum.org/EIPS/eip-712[EIP 712] is a standard for hashing and signing of typed structured data.
 *
 * The encoding specified in the EIP is very generic, and such a generic implementation in Solidity is not feasible,
 * thus this contract does not implement the encoding itself. Protocols need to implement the type-specific encoding
 * they need in their contracts using a combination of `abi.encode` and `keccak256`.
 *
 * This contract implements the EIP 712 domain separator ({_domainSeparatorV4}) that is used as part of the encoding
 * scheme, and the final step of the encoding to obtain the message digest that is then signed via ECDSA
 * ({_hashTypedDataV4}).
 *
 * The implementation of the domain separator was designed to be as efficient as possible while still properly updating
 * the chain id to protect against replay attacks on an eventual fork of the chain.
 *
 * NOTE: This contract implements the version of the encoding known as "v4", as implemented by the JSON RPC method
 * https://docs.metamask.io/guide/signing-data.html[`eth_signTypedDataV4` in MetaMask].
 *
 * _Available since v3.4._
 */
abstract contract EIP712 {
    /* solhint-disable var-name-mixedcase */
    // Cache the domain separator as an immutable value, but also store the chain id that it corresponds to, in order to
    // invalidate the cached domain separator if the chain id changes.
    bytes32 private immutable _CACHED_DOMAIN_SEPARATOR;
    uint256 private immutable _CACHED_CHAIN_ID;
    address private immutable _CACHED_THIS;

    bytes32 private immutable _HASHED_NAME;
    bytes32 private immutable _HASHED_VERSION;
    bytes32 private immutable _TYPE_HASH;

    /* solhint-enable var-name-mixedcase */

    /**
     * @dev Initializes the domain separator and parameter caches.
     *
     * The meaning of `name` and `version` is specified in
     * https://eips.ethereum.org/EIPS/eip-712#definition-of-domainseparator[EIP 712]:
     *
     * - `name`: the user readable name of the signing domain, i.e. the name of the DApp or the protocol.
     * - `version`: the current major version of the signing domain.
     *
     * NOTE: These parameters cannot be changed except through a xref:learn::upgrading-smart-contracts.adoc[smart
     * contract upgrade].
     */
    constructor(string memory name, string memory version) {
        bytes32 hashedName = keccak256(bytes(name));
        bytes32 hashedVersion = keccak256(bytes(version));
        bytes32 typeHash = keccak256(
            "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"
        );
        _HASHED_NAME = hashedName;
        _HASHED_VERSION = hashedVersion;
        _CACHED_CHAIN_ID = block.chainid;
        _CACHED_DOMAIN_SEPARATOR = _buildDomainSeparator(typeHash, hashedName, hashedVersion);
        _CACHED_THIS = address(this);
        _TYPE_HASH = typeHash;
    }

    /**
     * @dev Returns the domain separator for the current chain.
     */
    function _domainSeparatorV4() internal view returns (bytes32) {
        if (address(this) == _CACHED_THIS && block.chainid == _CACHED_CHAIN_ID) {
            return _CACHED_DOMAIN_SEPARATOR;
        } else {
            return _buildDomainSeparator(_TYPE_HASH, _HASHED_NAME, _HASHED_VERSION);
        }
    }

    function _buildDomainSeparator(
        bytes32 typeHash,
        bytes32 nameHash,
        bytes32 versionHash
    ) private view returns (bytes32) {
        return keccak256(abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this)));
    }

    /**
     * @dev Given an already https://eips.ethereum.org/EIPS/eip-712#definition-of-hashstruct[hashed struct], this
     * function returns the hash of the fully encoded EIP712 message for this domain.
     *
     * This hash can be used together with {ECDSA-recover} to obtain the signer of a message. For example:
     *
     * ```solidity
     * bytes32 digest = _hashTypedDataV4(keccak256(abi.encode(
     *     keccak256("Mail(address to,string contents)"),
     *     mailTo,
     *     keccak256(bytes(mailContents))
     * )));
     * address signer = ECDSA.recover(digest, signature);
     * ```
     */
    function _hashTypedDataV4(bytes32 structHash) internal view virtual returns (bytes32) {
        return ECDSA.toTypedDataHash(_domainSeparatorV4(), structHash);
    }
}

// contracts/src/PuttyV2Nft.sol

// removes balanceOf modifications
// questionable tradeoff but given our use-case it's reasonable
abstract contract PuttyV2Nft is ERC721("Putty", "OPUT") {
    // remove balanceOf modifications
    function _mint(address to, uint256 id) internal override {
        require(to != address(0), "INVALID_RECIPIENT");
        require(_ownerOf[id] == address(0), "ALREADY_MINTED");

        _ownerOf[id] = to;

        emit Transfer(address(0), to, id);
    }

    // remove balanceOf modifications
    function transferFrom(
        address from,
        address to,
        uint256 id
    ) public override {
        require(from == _ownerOf[id], "WRONG_FROM");
        require(to != address(0), "INVALID_RECIPIENT");
        require(
            msg.sender == from || isApprovedForAll[from][msg.sender] || msg.sender == getApproved[id],
            "NOT_AUTHORIZED"
        );

        _ownerOf[id] = to;
        delete getApproved[id];

        emit Transfer(from, to, id);
    }

    // set balanceOf to max for all users
    function balanceOf(address owner) public pure override returns (uint256) {
        require(owner != address(0), "ZERO_ADDRESS");
        return type(uint256).max;
    }
}

// contracts/lib/openzeppelin-contracts/contracts/utils/cryptography/SignatureChecker.sol

// OpenZeppelin Contracts (last updated v4.5.0) (utils/cryptography/SignatureChecker.sol)

/**
 * @dev Signature verification helper that can be used instead of `ECDSA.recover` to seamlessly support both ECDSA
 * signatures from externally owned accounts (EOAs) as well as ERC1271 signatures from smart contract wallets like
 * Argent and Gnosis Safe.
 *
 * _Available since v4.1._
 */
library SignatureChecker {
    /**
     * @dev Checks if a signature is valid for a given signer and data hash. If the signer is a smart contract, the
     * signature is validated against that smart contract using ERC1271, otherwise it's validated using `ECDSA.recover`.
     *
     * NOTE: Unlike ECDSA signatures, contract signatures are revocable, and the outcome of this function can thus
     * change through time. It could return true at block N and false at block N+1 (or the opposite).
     */
    function isValidSignatureNow(
        address signer,
        bytes32 hash,
        bytes memory signature
    ) internal view returns (bool) {
        (address recovered, ECDSA.RecoverError error) = ECDSA.tryRecover(hash, signature);
        if (error == ECDSA.RecoverError.NoError && recovered == signer) {
            return true;
        }

        (bool success, bytes memory result) = signer.staticcall(
            abi.encodeWithSelector(IERC1271.isValidSignature.selector, hash, signature)
        );
        return (success && result.length == 32 && abi.decode(result, (bytes4)) == IERC1271.isValidSignature.selector);
    }
}

// contracts/src/PuttyV2.sol

/**

    ██████╗ ██╗   ██╗████████╗████████╗██╗   ██╗    ██╗   ██╗██████╗ 
    ██╔══██╗██║   ██║╚══██╔══╝╚══██╔══╝╚██╗ ██╔╝    ██║   ██║╚════██╗
    ██████╔╝██║   ██║   ██║      ██║    ╚████╔╝     ██║   ██║ █████╔╝
    ██╔═══╝ ██║   ██║   ██║      ██║     ╚██╔╝      ╚██╗ ██╔╝██╔═══╝ 
    ██║     ╚██████╔╝   ██║      ██║      ██║        ╚████╔╝ ███████╗
    ╚═╝      ╚═════╝    ╚═╝      ╚═╝      ╚═╝         ╚═══╝  ╚══════╝
    
                                
            _..._               
          .'     '.      _       
         /    .-""-\   _/ \ 
       .-|   /:.   |  |   |   bussin
       |  \  |:.   /.-'-./
       | .-'-;:__.'    =/
       .'=  *=|     _.='
      /   _.  |    ;        minister you satoshi
     ;-.-'|    \   |
    /   | \    _\  _\
    \__/'._;.  ==' ==\
             \    \   |
             /    /   / 
             /-._/-._/
      jgs    \   `\  \
              `-._/._/

    this is a public good.
    by out.eth and tamagoyaki
    
 */

/**
    @title PuttyV2
    @author out.eth
    @notice An otc erc721 and erc20 option market.
 */
contract PuttyV2 is PuttyV2Nft, EIP712("Putty", "2.0"), ERC721TokenReceiver, Ownable {
    /* ~~~ TYPES ~~~ */

    using SafeTransferLib for ERC20;

    struct ERC20Asset {
        address token;
        uint256 tokenAmount;
    }

    struct ERC721Asset {
        address token;
        uint256 tokenId;
    }

    struct Order {
        address maker;
        bool isCall;
        bool isLong;
        address baseAsset;
        uint256 strike;
        uint256 premium;
        uint256 duration;
        uint256 expiration;
        uint256 nonce;
        address[] whitelist;
        address[] floorTokens;
        ERC20Asset[] erc20Assets;
        ERC721Asset[] erc721Assets;
    }

    /* ~~~ STATE VARIABLES ~~~ */

    /**
        @dev ERC721Asset type hash used for EIP-712 encoding.
     */
    bytes32 public constant ERC721ASSET_TYPE_HASH =
        keccak256(abi.encodePacked("ERC721Asset(address token,uint256 tokenId)"));

    /**
        @dev ERC20Asset type hash used for EIP-712 encoding.
     */
    bytes32 public constant ERC20ASSET_TYPE_HASH =
        keccak256(abi.encodePacked("ERC20Asset(address token,uint256 tokenAmount)"));

    /**
        @dev ERC721Asset type hash used for EIP-712 encoding.
     */
    bytes32 public constant ORDER_TYPE_HASH =
        keccak256(
            abi.encodePacked(
                "Order(",
                "address maker,",
                "bool isCall,",
                "bool isLong,",
                "address baseAsset,",
                "uint256 strike,",
                "uint256 premium,",
                "uint256 duration,",
                "uint256 expiration,",
                "uint256 nonce,",
                "address[] whitelist,",
                "address[] floorTokens,",
                "ERC20Asset[] erc20Assets,",
                "ERC721Asset[] erc721Assets",
                ")",
                "ERC20Asset(address token,uint256 tokenAmount)",
                "ERC721Asset(address token,uint256 tokenId)"
            )
        );

    /**
        @dev Contract address for Wrapped Ethereum.
     */
    address public immutable weth;

    /**
        @dev baseURI used to generate the tokenURI for PuttyV2 NFTs.
    */
    string public baseURI;

    /**
        @notice Fee rate that is applied on exercise.
    */
    uint256 public fee;

    /**
        @notice Whether or not an order has been cancelled. Maps 
                from orderHash to isCancelled.
    */
    mapping(bytes32 => bool) public cancelledOrders;

    /**
        @notice The current expiration timestamp of a position. Maps 
                from positionId to an expiration unix timestamp.
    */
    mapping(uint256 => uint256) public positionExpirations;

    /**
        @notice Whether or not a position has been exercised. Maps 
                from positionId to isExercised.
    */
    mapping(uint256 => bool) public exercisedPositions;

    /**
        @notice The floor asset token ids for a position. Maps from 
                positionId to floor asset token ids. This should only 
                be set for a long call position in `fillOrder`, or for 
                a short put position in `exercise`.
    */
    mapping(uint256 => uint256[]) public positionFloorAssetTokenIds;

    /* ~~~ EVENTS ~~~ */

    /**
        @notice Emitted when a new base URI is set.
        @param baseURI The new baseURI.
     */
    event NewBaseURI(string baseURI);

    /**
        @notice Emitted when a new fee is set.
        @param fee The new fee.
     */
    event NewFee(uint256 fee);

    /**
        @notice Emitted when an order is filled.
        @param orderHash The hash of the order that was filled.
        @param floorAssetTokenIds The floor asset token ids that were used.
        @param order The order that was filled.
     */
    event FilledOrder(bytes32 indexed orderHash, uint256[] floorAssetTokenIds, Order order);

    /**
        @notice Emitted when an order is exercised.
        @param orderHash The hash of the order that was exercised.
        @param floorAssetTokenIds The floor asset token ids that were used.
        @param order The order that was exercised.
     */
    event ExercisedOrder(bytes32 indexed orderHash, uint256[] floorAssetTokenIds, Order order);

    /**
        @notice Emitted when an order is withdrawn.
        @param orderHash The hash of the order that was withdrawn.
        @param order The order that was withdrawn.
     */
    event WithdrawOrder(bytes32 indexed orderHash, Order order);

    /**
        @notice emitted When an order is cancelled.
        @param orderHash The hash of the order that was cancelled.
        @param order The order that was cancelled.
     */
    event CancelledOrder(bytes32 indexed orderHash, Order order);

    constructor(
        string memory _baseURI,
        uint256 _fee,
        address _weth
    ) {
        require(_weth != address(0), "Unset weth address");

        setBaseURI(_baseURI);
        setFee(_fee);
        weth = _weth;
    }

    /* ~~~ ADMIN FUNCTIONS ~~~ */

    /**
        @notice Sets a new baseURI that is used in the construction
                of the tokenURI for each NFT position. Admin/DAO only.
        @param _baseURI The new base URI to use.
     */
    function setBaseURI(string memory _baseURI) public payable onlyOwner {
        baseURI = _baseURI;

        emit NewBaseURI(_baseURI);
    }

    /**
        @notice Sets a new fee rate that is applied on exercise. The
                fee has a precision of 1 decimal. e.g. 1000 = 100%,
                100 = 10%, 1 = 0.1%. Admin/DAO only.
        @param _fee The new fee rate to use.
     */
    function setFee(uint256 _fee) public payable onlyOwner {
        require(_fee < 30, "fee must be less than 3%");

        fee = _fee;

        emit NewFee(_fee);
    }

    /*
        ~~~ MAIN LOGIC FUNCTIONS ~~~

        Standard lifecycle:
            [1] fillOrder()
            [2] exercise()
            [3] withdraw()

            * It is also possible to cancel() an order before fillOrder()
    */

    /**
        @notice Fills an offchain order and settles it onchain. Mints two
                NFTs that represent the long and short position for the order.
        @param order The order to fill.
        @param signature The signature for the order. Signature must recover to order.maker.
        @param floorAssetTokenIds The floor asset token ids to use. Should only be set 
               when filling a long call order.
        @return positionId The id of the position NFT that the msg.sender receives.
     */
    function fillOrder(
        Order memory order,
        bytes calldata signature,
        uint256[] memory floorAssetTokenIds
    ) public payable returns (uint256 positionId) {
        /* ~~~ CHECKS ~~~ */

        bytes32 orderHash = hashOrder(order);

        // check signature is valid using EIP-712
        require(SignatureChecker.isValidSignatureNow(order.maker, orderHash, signature), "Invalid signature");

        // check order is not cancelled
        require(!cancelledOrders[orderHash], "Order has been cancelled");

        // check msg.sender is allowed to fill the order
        require(order.whitelist.length == 0 || isWhitelisted(order.whitelist, msg.sender), "Not whitelisted");

        // check duration is valid
        require(order.duration < 10_000 days, "Duration too long");

        // check order has not expired
        require(block.timestamp < order.expiration, "Order has expired");

        // check base asset exists
        require(order.baseAsset.code.length > 0, "baseAsset is not contract");

        // check floor asset token ids length is 0 unless the order type is call and side is long
        order.isCall && order.isLong
            ? require(floorAssetTokenIds.length == order.floorTokens.length, "Wrong amount of floor tokenIds")
            : require(floorAssetTokenIds.length == 0, "Invalid floor tokens length");

        /*  ~~~ EFFECTS ~~~ */

        // create long/short position for maker
        _mint(order.maker, uint256(orderHash));

        // create opposite long/short position for taker
        bytes32 oppositeOrderHash = hashOppositeOrder(order);
        positionId = uint256(oppositeOrderHash);
        _mint(msg.sender, positionId);

        // save floorAssetTokenIds if filling a long call order
        if (order.isLong && order.isCall) {
            positionFloorAssetTokenIds[uint256(orderHash)] = floorAssetTokenIds;
        }

        // save the long position expiration
        positionExpirations[order.isLong ? uint256(orderHash) : positionId] = block.timestamp + order.duration;

        emit FilledOrder(orderHash, floorAssetTokenIds, order);

        /* ~~~ INTERACTIONS ~~~ */

        // transfer premium to whoever is short from whomever is long
        if (order.isLong) {
            ERC20(order.baseAsset).safeTransferFrom(order.maker, msg.sender, order.premium);
        } else {
            // handle the case where the user uses native ETH instead of WETH to pay the premium
            if (weth == order.baseAsset && msg.value > 0) {
                // check enough ETH was sent to cover the premium
                require(msg.value == order.premium, "Incorrect ETH amount sent");

                // convert ETH to WETH and send premium to maker
                // converting to WETH instead of forwarding native ETH to the maker has two benefits;
                // 1) active market makers will mostly be using WETH not native ETH
                // 2) attack surface for re-entrancy is reduced
                IWETH(weth).deposit{value: msg.value}();
                IWETH(weth).transfer(order.maker, msg.value);
            } else {
                ERC20(order.baseAsset).safeTransferFrom(msg.sender, order.maker, order.premium);
            }
        }

        // filling short put: transfer strike from maker to contract
        if (!order.isLong && !order.isCall) {
            ERC20(order.baseAsset).safeTransferFrom(order.maker, address(this), order.strike);
            return positionId;
        }

        // filling long put: transfer strike from taker to contract
        if (order.isLong && !order.isCall) {
            // handle the case where the taker uses native ETH instead of WETH to deposit the strike
            if (weth == order.baseAsset && msg.value > 0) {
                // check enough ETH was sent to cover the strike
                require(msg.value == order.strike, "Incorrect ETH amount sent");

                // convert ETH to WETH
                // we convert the strike ETH to WETH so that the logic in exercise() works
                // - because exercise() assumes an ERC20 interface on the base asset.
                IWETH(weth).deposit{value: msg.value}();
            } else {
                ERC20(order.baseAsset).safeTransferFrom(msg.sender, address(this), order.strike);
            }

            return positionId;
        }

        // filling short call: transfer assets from maker to contract
        if (!order.isLong && order.isCall) {
            _transferERC20sIn(order.erc20Assets, order.maker);
            _transferERC721sIn(order.erc721Assets, order.maker);
            return positionId;
        }

        // filling long call: transfer assets from taker to contract
        if (order.isLong && order.isCall) {
            _transferERC20sIn(order.erc20Assets, msg.sender);
            _transferERC721sIn(order.erc721Assets, msg.sender);
            _transferFloorsIn(order.floorTokens, floorAssetTokenIds, msg.sender);
            return positionId;
        }
    }

    /**
        @notice Exercises a long order and also burns the long position NFT which 
                represents it.
        @param order The order of the position to exercise.
        @param floorAssetTokenIds The floor asset token ids to use. Should only be set 
               when exercising a put order.
     */
    function exercise(Order memory order, uint256[] calldata floorAssetTokenIds) public payable {
        /* ~~~ CHECKS ~~~ */

        bytes32 orderHash = hashOrder(order);

        // check user owns the position
        require(ownerOf(uint256(orderHash)) == msg.sender, "Not owner");

        // check position is long
        require(order.isLong, "Can only exercise long positions");

        // check position has not expired
        require(block.timestamp < positionExpirations[uint256(orderHash)], "Position has expired");

        // check floor asset token ids length is 0 unless the position type is put
        !order.isCall
            ? require(floorAssetTokenIds.length == order.floorTokens.length, "Wrong amount of floor tokenIds")
            : require(floorAssetTokenIds.length == 0, "Invalid floor tokenIds length");

        /* ~~~ EFFECTS ~~~ */

        // send the long position to 0xdead.
        // instead of doing a standard burn by sending to 0x000...000, sending
        // to 0xdead ensures that the same position id cannot be minted again.
        transferFrom(msg.sender, address(0xdead), uint256(orderHash));

        // mark the position as exercised
        exercisedPositions[uint256(orderHash)] = true;

        emit ExercisedOrder(orderHash, floorAssetTokenIds, order);

        /* ~~~ INTERACTIONS ~~~ */

        if (order.isCall) {
            // -- exercising a call option

            // transfer strike from exerciser to putty
            // handle the case where the taker uses native ETH instead of WETH to pay the strike
            if (weth == order.baseAsset && msg.value > 0) {
                // check enough ETH was sent to cover the strike
                require(msg.value == order.strike, "Incorrect ETH amount sent");

                // convert ETH to WETH
                // we convert the strike ETH to WETH so that the logic in withdraw() works
                // - because withdraw() assumes an ERC20 interface on the base asset.
                IWETH(weth).deposit{value: msg.value}();
            } else {
                ERC20(order.baseAsset).safeTransferFrom(msg.sender, address(this), order.strike);
            }

            // transfer assets from putty to exerciser
            _transferERC20sOut(order.erc20Assets);
            _transferERC721sOut(order.erc721Assets);
            _transferFloorsOut(order.floorTokens, positionFloorAssetTokenIds[uint256(orderHash)]);
        } else {
            // -- exercising a put option

            // save the floor asset token ids to the short position
            uint256 shortPositionId = uint256(hashOppositeOrder(order));
            positionFloorAssetTokenIds[shortPositionId] = floorAssetTokenIds;

            // transfer strike from putty to exerciser
            ERC20(order.baseAsset).safeTransfer(msg.sender, order.strike);

            // transfer assets from exerciser to putty
            _transferERC20sIn(order.erc20Assets, msg.sender);
            _transferERC721sIn(order.erc721Assets, msg.sender);
            _transferFloorsIn(order.floorTokens, floorAssetTokenIds, msg.sender);
        }
    }

    /**
        @notice Withdraws the assets from a short order and also burns the short position 
                that represents it. The assets that are withdrawn are dependent on whether 
                the order is exercised or expired and if the order is a put or call.
        @param order The order to withdraw.
     */
    function withdraw(Order memory order) public {
        /* ~~~ CHECKS ~~~ */

        // check order is short
        require(!order.isLong, "Must be short position");

        bytes32 orderHash = hashOrder(order);

        // check msg.sender owns the position
        require(ownerOf(uint256(orderHash)) == msg.sender, "Not owner");

        uint256 longPositionId = uint256(hashOppositeOrder(order));
        bool isExercised = exercisedPositions[longPositionId];

        // check long position has either been exercised or is expired
        require(block.timestamp > positionExpirations[longPositionId] || isExercised, "Must be exercised or expired");

        /* ~~~ EFFECTS ~~~ */

        // send the short position to 0xdead.
        // instead of doing a standard burn by sending to 0x000...000, sending
        // to 0xdead ensures that the same position id cannot be minted again.
        transferFrom(msg.sender, address(0xdead), uint256(orderHash));

        emit WithdrawOrder(orderHash, order);

        /* ~~~ INTERACTIONS ~~~ */

        // transfer strike to owner if put is expired or call is exercised
        if ((order.isCall && isExercised) || (!order.isCall && !isExercised)) {
            // send the fee to the admin/DAO if fee is greater than 0%
            uint256 feeAmount = 0;
            if (fee > 0) {
                feeAmount = (order.strike * fee) / 1000;
                ERC20(order.baseAsset).safeTransfer(owner(), feeAmount);
            }

            ERC20(order.baseAsset).safeTransfer(msg.sender, order.strike - feeAmount);

            return;
        }

        // transfer assets from putty to owner if put is exercised or call is expired
        if ((order.isCall && !isExercised) || (!order.isCall && isExercised)) {
            _transferERC20sOut(order.erc20Assets);
            _transferERC721sOut(order.erc721Assets);

            // for call options the floor token ids are saved in the long position in fillOrder(),
            // and for put options the floor tokens ids are saved in the short position in exercise()
            uint256 floorPositionId = order.isCall ? longPositionId : uint256(orderHash);
            _transferFloorsOut(order.floorTokens, positionFloorAssetTokenIds[floorPositionId]);

            return;
        }
    }

    /**
        @notice Cancels an order which prevents it from being filled in the future.
        @param order The order to cancel.
     */
    function cancel(Order memory order) public {
        require(msg.sender == order.maker, "Not your order");

        bytes32 orderHash = hashOrder(order);

        // mark the order as cancelled
        cancelledOrders[orderHash] = true;

        emit CancelledOrder(orderHash, order);
    }

    /* ~~~ PERIPHERY LOGIC FUNCTIONS ~~~ */

    /**
        @notice Batch fills multiple orders.
        @param orders The orders to fill.
        @param signatures The signatures to use for each respective order.
        @param floorAssetTokenIds The floorAssetTokenIds to use for each respective order.
        @return positionIds The ids of the position NFT that the msg.sender receives.
     */
    function batchFillOrder(
        Order[] memory orders,
        bytes[] calldata signatures,
        uint256[][] memory floorAssetTokenIds
    ) public returns (uint256[] memory positionIds) {
        require(orders.length == signatures.length, "Length mismatch in input");
        require(signatures.length == floorAssetTokenIds.length, "Length mismatch in input");

        positionIds = new uint256[](orders.length);

        for (uint256 i = 0; i < orders.length; i++) {
            positionIds[i] = fillOrder(orders[i], signatures[i], floorAssetTokenIds[i]);
        }
    }

    /**
        @notice Accepts a counter offer for an order. It fills the counter offer, and then
                cancels the original order that the counter offer was made for.
        @dev There is no need for floorTokenIds here because there is no situation in which
             it makes sense to have them when accepting counter offers. When accepting a counter 
             offer for a short call order, the complementary long call order already knows what 
             tokenIds are used in the short call so floorTokens should always be empty.
        @param order The counter offer to accept.
        @param signature The signature for the counter offer.
        @param originalOrder The original order that the counter was made for.
        @return positionId The id of the position NFT that the msg.sender receives.
     */
    function acceptCounterOffer(
        Order memory order,
        bytes calldata signature,
        Order memory originalOrder
    ) public payable returns (uint256 positionId) {
        // cancel the original order
        cancel(originalOrder);

        // accept the counter offer
        uint256[] memory floorAssetTokenIds = new uint256[](0);
        positionId = fillOrder(order, signature, floorAssetTokenIds);
    }

    /* ~~~ HELPER FUNCTIONS ~~~ */

    /**
        @notice Transfers an array of erc20s into the contract from an address.
        @param assets The erc20 tokens and amounts to transfer in.
        @param from Who to transfer the erc20 assets from.
     */
    function _transferERC20sIn(ERC20Asset[] memory assets, address from) internal {
        for (uint256 i = 0; i < assets.length; i++) {
            address token = assets[i].token;
            uint256 tokenAmount = assets[i].tokenAmount;

            require(token.code.length > 0, "ERC20: Token is not contract");
            require(tokenAmount > 0, "ERC20: Amount too small");

            ERC20(token).safeTransferFrom(from, address(this), tokenAmount);
        }
    }

    /**
        @notice Transfers an array of erc721s into the contract from an address.
        @param assets The erc721 tokens and token ids to transfer in.
        @param from Who to transfer the erc721 assets from.
     */
    function _transferERC721sIn(ERC721Asset[] memory assets, address from) internal {
        for (uint256 i = 0; i < assets.length; i++) {
            ERC721(assets[i].token).safeTransferFrom(from, address(this), assets[i].tokenId);
        }
    }

    /**
        @notice Transfers an array of erc721 floor tokens into the contract from an address.
        @param floorTokens The contract addresses of each erc721.
        @param floorTokenIds The token id of each erc721.
        @param from Who to transfer the floor tokens from.
     */
    function _transferFloorsIn(
        address[] memory floorTokens,
        uint256[] memory floorTokenIds,
        address from
    ) internal {
        for (uint256 i = 0; i < floorTokens.length; i++) {
            ERC721(floorTokens[i]).safeTransferFrom(from, address(this), floorTokenIds[i]);
        }
    }

    /**
        @notice Transfers an array of erc20 tokens to the msg.sender.
        @param assets The erc20 tokens and amounts to send.
     */
    function _transferERC20sOut(ERC20Asset[] memory assets) internal {
        for (uint256 i = 0; i < assets.length; i++) {
            ERC20(assets[i].token).safeTransfer(msg.sender, assets[i].tokenAmount);
        }
    }

    /**
        @notice Transfers an array of erc721 tokens to the msg.sender.
        @param assets The erc721 tokens and token ids to send.
     */
    function _transferERC721sOut(ERC721Asset[] memory assets) internal {
        for (uint256 i = 0; i < assets.length; i++) {
            ERC721(assets[i].token).safeTransferFrom(address(this), msg.sender, assets[i].tokenId);
        }
    }

    /**
        @notice Transfers an array of erc721 floor tokens to the msg.sender.
        @param floorTokens The contract addresses for each floor token.
        @param floorTokenIds The token id of each floor token.
     */
    function _transferFloorsOut(address[] memory floorTokens, uint256[] memory floorTokenIds) internal {
        for (uint256 i = 0; i < floorTokens.length; i++) {
            ERC721(floorTokens[i]).safeTransferFrom(address(this), msg.sender, floorTokenIds[i]);
        }
    }

    /**
        @notice Checks whether or not an address exists in the whitelist.
        @param whitelist The whitelist to check against.
        @param target The target address to check.
        @return If it exists in the whitelist or not.
     */
    function isWhitelisted(address[] memory whitelist, address target) public pure returns (bool) {
        for (uint256 i = 0; i < whitelist.length; i++) {
            if (target == whitelist[i]) return true;
        }

        return false;
    }

    /**
        @notice Get the orderHash for a complementary short/long order - e.g for a long order,
                this returns the hash of it's opposite short order.
        @param order The order to find the complementary long/short hash for.
        @return orderHash The hash of the opposite order.
     */
    function hashOppositeOrder(Order memory order) public view returns (bytes32 orderHash) {
        // use decode/encode to get a copy instead of reference
        Order memory oppositeOrder = abi.decode(abi.encode(order), (Order));

        // get the opposite side of the order (short/long)
        oppositeOrder.isLong = !order.isLong;
        orderHash = hashOrder(oppositeOrder);
    }

    /* ~~~ EIP-712 HELPERS ~~~ */

    /**
        @notice Hashes an order based on the eip-712 encoding scheme.
        @param order The order to hash.
        @return orderHash The eip-712 compliant hash of the order.
     */
    function hashOrder(Order memory order) public view returns (bytes32 orderHash) {
        orderHash = keccak256(
            abi.encode(
                ORDER_TYPE_HASH,
                order.maker,
                order.isCall,
                order.isLong,
                order.baseAsset,
                order.strike,
                order.premium,
                order.duration,
                order.expiration,
                order.nonce,
                keccak256(abi.encodePacked(order.whitelist)),
                keccak256(abi.encodePacked(order.floorTokens)),
                keccak256(encodeERC20Assets(order.erc20Assets)),
                keccak256(encodeERC721Assets(order.erc721Assets))
            )
        );

        orderHash = _hashTypedDataV4(orderHash);
    }

    /**
        @notice Encodes an array of erc20 assets following the eip-712 encoding scheme.
        @param arr Array of erc20 assets to hash.
        @return encoded The eip-712 encoded array of erc20 assets.
     */
    function encodeERC20Assets(ERC20Asset[] memory arr) public pure returns (bytes memory encoded) {
        for (uint256 i = 0; i < arr.length; i++) {
            encoded = abi.encodePacked(
                encoded,
                keccak256(abi.encode(ERC20ASSET_TYPE_HASH, arr[i].token, arr[i].tokenAmount))
            );
        }
    }

    /**
        @notice Encodes an array of erc721 assets following the eip-712 encoding scheme.
        @param arr Array of erc721 assets to hash.
        @return encoded The eip-712 encoded array of erc721 assets.
     */
    function encodeERC721Assets(ERC721Asset[] memory arr) public pure returns (bytes memory encoded) {
        for (uint256 i = 0; i < arr.length; i++) {
            encoded = abi.encodePacked(
                encoded,
                keccak256(abi.encode(ERC721ASSET_TYPE_HASH, arr[i].token, arr[i].tokenId))
            );
        }
    }

    /**
        @return The domain seperator used when calculating the eip-712 hash.
     */
    function domainSeparatorV4() public view returns (bytes32) {
        return _domainSeparatorV4();
    }

    /* ~~~ OVERRIDES ~~~ */

    /**
        @notice Gets the token URI for an NFT.
        @param id The id of the position NFT.
        @return The tokenURI of the position NFT.
     */
    function tokenURI(uint256 id) public view override returns (string memory) {
        require(_ownerOf[id] != address(0), "URI query for NOT_MINTED token");

        return string.concat(baseURI, Strings.toString(id));
    }
}

