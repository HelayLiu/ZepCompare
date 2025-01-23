// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

// contracts/TokenReceiver.sol

abstract contract TokenReceiver {
    function onERC721Received(
        address,
        address,
        uint256,
        bytes calldata
    ) external pure returns (bytes4) {
        return this.onERC721Received.selector;
    }

    function onERC1155Received(
        address,
        address,
        uint256,
        uint256,
        bytes memory
    ) external virtual returns (bytes4) {
        return this.onERC1155Received.selector;
    }

    function onERC1155BatchReceived(
        address,
        address,
        uint256[] memory,
        uint256[] memory,
        bytes memory
    ) external virtual returns (bytes4) {
        return this.onERC1155BatchReceived.selector;
    }
}

// contracts/interfaces/IERC1155.sol

interface IERC1155 {
    event TransferSingle(address indexed operator, address indexed from, address indexed to, uint256 id, uint256 value);

    event TransferBatch(
        address indexed operator,
        address indexed from,
        address indexed to,
        uint256[] ids,
        uint256[] values
    );

    event ApprovalForAll(address indexed account, address indexed operator, bool approved);

    event URI(string value, uint256 indexed id);

    function balanceOf(address account, uint256 id) external view returns (uint256);

    function balanceOfBatch(address[] calldata accounts, uint256[] calldata ids)
        external
        view
        returns (uint256[] memory);

    function setApprovalForAll(address operator, bool approved) external;

    function isApprovedForAll(address account, address operator) external view returns (bool);

    function safeTransferFrom(
        address from,
        address to,
        uint256 id,
        uint256 amount,
        bytes calldata data
    ) external;

    function safeBatchTransferFrom(
        address from,
        address to,
        uint256[] calldata ids,
        uint256[] calldata amounts,
        bytes calldata data
    ) external;
}

// contracts/interfaces/IERC1271.sol

interface IERC1271 {
    function isValidSignature(bytes32 hash, bytes memory signature) external view returns (bytes4 magicValue);
}

// contracts/interfaces/IERC20.sol

interface IERC20 {
    event Transfer(address indexed from, address indexed to, uint256 value);

    event Approval(address indexed owner, address indexed spender, uint256 value);

    function totalSupply() external view returns (uint256);

    function balanceOf(address account) external view returns (uint256);

    function transfer(address to, uint256 amount) external returns (bool);

    function allowance(address owner, address spender) external view returns (uint256);

    function approve(address spender, uint256 amount) external returns (bool);

    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}

// contracts/interfaces/IERC721.sol

interface IERC721 {
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);

    event Approval(address indexed owner, address indexed approved, uint256 indexed tokenId);

    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);

    function balanceOf(address owner) external view returns (uint256 balance);

    function ownerOf(uint256 tokenId) external view returns (address owner);

    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId,
        bytes calldata data
    ) external;

    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;

    function transferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;

    function approve(address to, uint256 tokenId) external;

    function setApprovalForAll(address operator, bool _approved) external;

    function getApproved(uint256 tokenId) external view returns (address operator);

    function isApprovedForAll(address owner, address operator) external view returns (bool);
}

// contracts/interfaces/IOwnableTwoSteps.sol

/**
 * @title IOwnableTwoSteps
 */
contract IOwnableTwoSteps {
    enum Status {
        NoOngoingTransfer,
        TransferInProgress,
        RenouncementInProgress
    }

    // Custom errors
    error NoOngoingTransferInProgress();
    error NotOwner();
    error RenouncementTooEarly();
    error RenouncementNotInProgress();
    error TransferAlreadyInProgress();
    error TransferNotInProgress();
    error WrongPotentialOwner();

    // Events
    event CancelOwnershipTransfer();
    event InitiateOwnershipRenouncement(uint256 earliestOwnershipRenouncementTime);
    event InitiateOwnershipTransfer(address previousOwner, address potentialOwner);
    event NewOwner(address newOwner);
}

// contracts/interfaces/IReentrancyGuard.sol

/**
 * @title IReentrancyGuard
 */
interface IReentrancyGuard {
    error ReentrancyFail();
}

// contracts/interfaces/ISignatureChecker.sol

/**
 * @title ISignatureChecker
 */
interface ISignatureChecker {
    // Custom errors
    error BadSignatureS();
    error BadSignatureV(uint8 v);
    error InvalidSignatureERC1271();
    error InvalidSignatureEOA();
    error NullSignerAddress();
    error WrongSignatureLength(uint256 length);
}

// contracts/interfaces/IWETH.sol

interface IWETH {
    function deposit() external payable;

    function transfer(address dst, uint256 wad) external returns (bool);

    function withdraw(uint256 wad) external;
}

// contracts/libraries/OrderEnums.sol

enum CollectionType { ERC721, ERC1155 }

// node_modules/@looksrare/contracts-exchange-v1/contracts/libraries/OrderTypes.sol

/**
 * @title OrderTypes
 * @notice This library contains order types for the LooksRare exchange.
 */
library OrderTypes {
    // keccak256("MakerOrder(bool isOrderAsk,address signer,address collection,uint256 price,uint256 tokenId,uint256 amount,address strategy,address currency,uint256 nonce,uint256 startTime,uint256 endTime,uint256 minPercentageToAsk,bytes params)")
    bytes32 internal constant MAKER_ORDER_HASH = 0x40261ade532fa1d2c7293df30aaadb9b3c616fae525a0b56d3d411c841a85028;

    struct MakerOrder {
        bool isOrderAsk; // true --> ask / false --> bid
        address signer; // signer of the maker order
        address collection; // collection address
        uint256 price; // price (used as )
        uint256 tokenId; // id of the token
        uint256 amount; // amount of tokens to sell/purchase (must be 1 for ERC721, 1+ for ERC1155)
        address strategy; // strategy for trade execution (e.g., DutchAuction, StandardSaleForFixedPrice)
        address currency; // currency (e.g., WETH)
        uint256 nonce; // order nonce (must be unique unless new maker order is meant to override existing one e.g., lower ask price)
        uint256 startTime; // startTime in timestamp
        uint256 endTime; // endTime in timestamp
        uint256 minPercentageToAsk; // slippage protection (9000 --> 90% of the final price must return to ask)
        bytes params; // additional parameters
        uint8 v; // v: parameter (27 or 28)
        bytes32 r; // r: parameter
        bytes32 s; // s: parameter
    }

    struct TakerOrder {
        bool isOrderAsk; // true --> ask / false --> bid
        address taker; // msg.sender
        uint256 price; // final price for the purchase
        uint256 tokenId;
        uint256 minPercentageToAsk; // // slippage protection (9000 --> 90% of the final price must return to ask)
        bytes params; // other params (e.g., tokenId)
    }

    function hash(MakerOrder memory makerOrder) internal pure returns (bytes32) {
        return
            keccak256(
                abi.encode(
                    MAKER_ORDER_HASH,
                    makerOrder.isOrderAsk,
                    makerOrder.signer,
                    makerOrder.collection,
                    makerOrder.price,
                    makerOrder.tokenId,
                    makerOrder.amount,
                    makerOrder.strategy,
                    makerOrder.currency,
                    makerOrder.nonce,
                    makerOrder.startTime,
                    makerOrder.endTime,
                    makerOrder.minPercentageToAsk,
                    keccak256(makerOrder.params)
                )
            );
    }
}

// contracts/OwnableTwoSteps.sol

/**
 * @title OwnableTwoSteps
 * @notice This contract offers transfer of ownership in two steps with potential owner having to confirm the transaction.
 *         Renouncement of the ownership is also a two-step process with a timelock since the next potential owner is address(0).
 */
abstract contract OwnableTwoSteps is IOwnableTwoSteps {
    // Address of the current owner
    address public owner;

    // Address of the potential owner
    address public potentialOwner;

    // Delay for the timelock (in seconds)
    uint256 public delay;

    // Earliest ownership renouncement timestamp
    uint256 public earliestOwnershipRenouncementTime;

    // Ownership status
    Status public ownershipStatus;

    /**
     * @notice Modifier to wrap functions for contracts that inherit this contract
     */
    modifier onlyOwner() {
        if (msg.sender != owner) {
            revert NotOwner();
        }
        _;
    }

    /**
     * @notice Constructor
     *         Initial owner is the deployment address.
     *         Delay (for the timelock) must be set by the contract that inherits from this.
     */
    constructor() {
        owner = msg.sender;
    }

    /**
     * @notice Cancel transfer of ownership
     * @dev This function can be used for both cancelling a transfer to a new owner and
     *      cancelling the renouncement of the ownership.
     */
    function cancelOwnershipTransfer() external onlyOwner {
        if (ownershipStatus == Status.NoOngoingTransfer) revert NoOngoingTransferInProgress();

        if (ownershipStatus == Status.TransferInProgress) {
            delete potentialOwner;
        } else if (ownershipStatus == Status.RenouncementInProgress) {
            delete earliestOwnershipRenouncementTime;
        }

        delete ownershipStatus;

        emit CancelOwnershipTransfer();
    }

    /**
     * @notice Confirm ownership renouncement
     */
    function confirmOwnershipRenouncement() external onlyOwner {
        if (ownershipStatus != Status.RenouncementInProgress) revert RenouncementNotInProgress();
        if (block.timestamp < earliestOwnershipRenouncementTime) revert RenouncementTooEarly();

        delete earliestOwnershipRenouncementTime;
        delete owner;
        delete ownershipStatus;

        emit NewOwner(address(0));
    }

    /**
     * @notice Confirm ownership transfer
     * @dev This function can only be called by the current potential owner.
     */
    function confirmOwnershipTransfer() external {
        if (ownershipStatus != Status.TransferInProgress) revert TransferNotInProgress();
        if (msg.sender != potentialOwner) revert WrongPotentialOwner();

        owner = msg.sender;
        delete ownershipStatus;
        delete potentialOwner;

        emit NewOwner(owner);
    }

    /**
     * @notice Initiate transfer of ownership to a new owner
     * @param newPotentialOwner New potential owner address
     */
    function initiateOwnershipTransfer(address newPotentialOwner) external onlyOwner {
        if (ownershipStatus != Status.NoOngoingTransfer) revert TransferAlreadyInProgress();

        ownershipStatus = Status.TransferInProgress;
        potentialOwner = newPotentialOwner;

        emit InitiateOwnershipTransfer(owner, newPotentialOwner);
    }

    /**
     * @notice Initiate ownership renouncement
     */
    function initiateOwnershipRenouncement() external onlyOwner {
        if (ownershipStatus != Status.NoOngoingTransfer) revert TransferAlreadyInProgress();

        ownershipStatus = Status.RenouncementInProgress;
        earliestOwnershipRenouncementTime = block.timestamp + delay;

        emit InitiateOwnershipRenouncement(earliestOwnershipRenouncementTime);
    }

    /**
     * @notice Set up the timelock delay for renouncing ownership
     * @param _delay Timelock delay for the owner to confirm renouncing the ownership
     * @dev This function is expected to be included in the constructor of the contract that inherits this contract.
     *      If it is not set, there is no timelock to renounce the ownership.
     */
    function _setupDelayForRenouncingOwnership(uint256 _delay) internal {
        delay = _delay;
    }
}

// contracts/ReentrancyGuard.sol

/**
 * @title ReentrancyGuard
 * @notice This contract protects against reentrancy attacks.
 *         It is adjusted from OpenZeppelin.
 */
abstract contract ReentrancyGuard is IReentrancyGuard {
    uint256 private _status;

    constructor() {
        _status = 1;
    }

    /**
     * @notice Modifier to wrap functions to prevent reentrancy calls
     */
    modifier nonReentrant() {
        if (_status == 2) revert ReentrancyFail();

        _status = 2;
        _;
        _status = 1;
    }
}

// contracts/libraries/OrderStructs.sol

struct BasicOrder {
  address signer; // The order's maker
  address collection; // The address of the ERC721/ERC1155 token to be purchased
  CollectionType collectionType; // 0 for ERC721, 1 for ERC1155
  uint256[] tokenIds; // The IDs of the tokens to be purchased
  uint256[] amounts; // Always 1 when ERC721, can be > 1 if ERC1155
  uint256 price; // The *taker bid* price to pay for the order
  address currency; // The order's currency, address(0) for ETH
  uint256 startTime; // The timestamp when the order starts becoming valid
  uint256 endTime; // The timestamp when the order stops becoming valid
  bytes signature; // split to v,r,s for LooksRare
}

struct TokenTransfer {
    uint256 amount; // ERC20 transfer amount
    address currency; // ERC20 transfer currency
}

struct FeeData {
    uint256 bp; // Aggregator fee basis point
    address recipient; // Aggregator fee recipient
}

// contracts/lowLevelCallers/LowLevelERC1155Transfer.sol

/**
 * @title LowLevelERC1155Transfer
 * @notice This contract contains low-level calls to transfer ERC1155 tokens.
 * @author LooksRare protocol team (👀,💎)
 */
contract LowLevelERC1155Transfer {
    error ERC1155SafeTransferFromFail();
    error ERC1155SafeBatchTransferFrom();

    /**
     * @notice Execute ERC1155 safeTransferFrom
     * @param collection Address of the collection
     * @param from Address of the sender
     * @param to Address of the recipient
     * @param tokenId tokenId to transfer
     * @param amount Amount to transfer
     */
    function _executeERC1155SafeTransferFrom(
        address collection,
        address from,
        address to,
        uint256 tokenId,
        uint256 amount
    ) internal {
        (bool status, ) = collection.call(
            abi.encodeWithSelector(IERC1155.safeTransferFrom.selector, from, to, tokenId, amount, "")
        );

        if (!status) revert ERC1155SafeTransferFromFail();
    }

    /**
     * @notice Execute ERC1155 safeBatchTransferFrom
     * @param collection Address of the collection
     * @param from Address of the sender
     * @param to Address of the recipient
     * @param tokenIds Array of tokenIds to transfer
     * @param amounts Array of amounts to transfer
     */
    function _executeERC1155SafeBatchTransferFrom(
        address collection,
        address from,
        address to,
        uint256[] calldata tokenIds,
        uint256[] calldata amounts
    ) internal {
        (bool status, ) = collection.call(
            abi.encodeWithSelector(IERC1155.safeBatchTransferFrom.selector, from, to, tokenIds, amounts, "")
        );

        if (!status) revert ERC1155SafeBatchTransferFrom();
    }
}

// contracts/lowLevelCallers/LowLevelERC20Approve.sol

/**
 * @title LowLevelERC20Approve
 * @notice This contract contains low-level calls to approve ERC20 tokens.
 * @author LooksRare protocol team (👀,💎)
 */
contract LowLevelERC20Approve {
    error ERC20ApprovalFail();

    /**
     * @notice Execute ERC20 approve
     * @param currency Currency address
     * @param to Operator address
     * @param amount Amount to approve
     */
    function _executeERC20Approve(
        address currency,
        address to,
        uint256 amount
    ) internal {
        (bool status, bytes memory data) = currency.call(abi.encodeWithSelector(IERC20.approve.selector, to, amount));

        if (!status) revert ERC20ApprovalFail();
        if (data.length > 0) {
            if (!abi.decode(data, (bool))) revert ERC20ApprovalFail();
        }
    }
}

// contracts/lowLevelCallers/LowLevelERC20Transfer.sol

/**
 * @title LowLevelERC20Transfer
 * @notice This contract contains low-level calls to transfer ERC20 tokens.
 * @author LooksRare protocol team (👀,💎)
 */
contract LowLevelERC20Transfer {
    error ERC20TransferFail();
    error ERC20TransferFromFail();

    /**
     * @notice Execute ERC20 transferFrom
     * @param currency Currency address
     * @param from Sender address
     * @param to Recipient address
     * @param amount Amount to transfer
     */
    function _executeERC20TransferFrom(
        address currency,
        address from,
        address to,
        uint256 amount
    ) internal {
        (bool status, bytes memory data) = currency.call(
            abi.encodeWithSelector(IERC20.transferFrom.selector, from, to, amount)
        );

        if (!status) revert ERC20TransferFromFail();
        if (data.length > 0) {
            if (!abi.decode(data, (bool))) revert ERC20TransferFromFail();
        }
    }

    /**
     * @notice Execute ERC20 (direct) transfer
     * @param currency Currency address
     * @param to Recipient address
     * @param amount Amount to transfer
     */
    function _executeERC20DirectTransfer(
        address currency,
        address to,
        uint256 amount
    ) internal {
        (bool status, bytes memory data) = currency.call(abi.encodeWithSelector(IERC20.transfer.selector, to, amount));

        if (!status) revert ERC20TransferFail();
        if (data.length > 0) {
            if (!abi.decode(data, (bool))) revert ERC20TransferFail();
        }
    }
}

// contracts/lowLevelCallers/LowLevelERC721Transfer.sol

/**
 * @title LowLevelERC721Transfer
 * @notice This contract contains low-level calls to transfer ERC721 tokens.
 * @author LooksRare protocol team (👀,💎)
 */
contract LowLevelERC721Transfer {
    error ERC721TransferFromFail();

    /**
     * @notice Execute ERC721 transferFrom
     * @param collection Address of the collection
     * @param from Address of the sender
     * @param to Address of the recipient
     * @param tokenId tokenId to transfer
     */
    function _executeERC721TransferFrom(
        address collection,
        address from,
        address to,
        uint256 tokenId
    ) internal {
        (bool status, ) = collection.call(abi.encodeWithSelector(IERC721.transferFrom.selector, from, to, tokenId));
        if (!status) revert ERC721TransferFromFail();
    }
}

// contracts/lowLevelCallers/LowLevelETH.sol

/**
 * @title LowLevelETH
 * @notice This contract contains low-level calls to transfer ETH.
 * @author LooksRare protocol team (👀,💎)
 */
contract LowLevelETH {
    error ETHTransferFail();

    /**
     * @notice Transfer ETH to a recipient address
     * @param _to Recipient address
     * @param _amount Amount to transfer
     */
    function _transferETH(address _to, uint256 _amount) internal {
        bool status;

        assembly {
            status := call(gas(), _to, _amount, 0, 0, 0, 0)
        }

        if (!status) revert ETHTransferFail();
    }

    /**
     * @notice Return ETH back to the original sender if any ETH is left in the payable call.
     */
    function _returnETHIfAny() internal {
        assembly {
            if gt(selfbalance(), 0) {
                let status := call(gas(), caller(), selfbalance(), 0, 0, 0, 0)
            }
        }
    }

    /**
     * @notice Return ETH back to the designated sender if any ETH is left in the payable call.
     */
    function _returnETHIfAny(address recipient) internal {
        assembly {
            if gt(selfbalance(), 0) {
                let status := call(gas(), recipient, selfbalance(), 0, 0, 0, 0)
            }
        }
    }

    /**
     * @notice Return ETH to the original sender if any is left in the payable call but leave 1 wei of ETH in the contract.
     */
    function _returnETHIfAnyWithOneWeiLeft() internal {
        assembly {
            if gt(selfbalance(), 1) {
                let status := call(gas(), caller(), sub(selfbalance(), 1), 0, 0, 0, 0)
            }
        }
    }
}

// node_modules/@looksrare/contracts-exchange-v1/contracts/interfaces/ILooksRareExchange.sol

interface ILooksRareExchange {
    function matchAskWithTakerBidUsingETHAndWETH(
        OrderTypes.TakerOrder calldata takerBid,
        OrderTypes.MakerOrder calldata makerAsk
    ) external payable;

    function matchAskWithTakerBid(OrderTypes.TakerOrder calldata takerBid, OrderTypes.MakerOrder calldata makerAsk)
        external;

    function matchBidWithTakerAsk(OrderTypes.TakerOrder calldata takerAsk, OrderTypes.MakerOrder calldata makerBid)
        external;
}

// contracts/SignatureChecker.sol

/**
 * @title SignatureChecker
 * @notice This contract is used to verify signatures for EOAs (with length of both 65 and 64 bytes) and contracts (ERC-1271).
 */
abstract contract SignatureChecker is ISignatureChecker {
    /**
     * @notice Split a signature into r,s,v outputs
     * @param signature A 64 or 65 bytes signature
     * @return r The r output of the signature
     * @return s The s output of the signature
     * @return v The recovery identifier, must be 27 or 28
     */
    function _splitSignature(bytes memory signature)
        internal
        pure
        returns (
            bytes32 r,
            bytes32 s,
            uint8 v
        )
    {
        if (signature.length == 64) {
            bytes32 vs;
            assembly {
                r := mload(add(signature, 0x20))
                vs := mload(add(signature, 0x40))
                s := and(vs, 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
                v := add(shr(255, vs), 27)
            }
        } else if (signature.length == 65) {
            assembly {
                r := mload(add(signature, 0x20))
                s := mload(add(signature, 0x40))
                v := byte(0, mload(add(signature, 0x60)))
            }
        } else {
            revert WrongSignatureLength(signature.length);
        }

        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) revert BadSignatureS();

        if (v != 27 && v != 28) revert BadSignatureV(v);
    }

    /**
     * @notice Recover the signer of a signature (for EOA)
     * @param hash Hash of the signed message
     * @param signature Bytes containing the signature (64 or 65 bytes)
     */
    function _recoverEOASigner(bytes32 hash, bytes memory signature) internal pure returns (address signer) {
        (bytes32 r, bytes32 s, uint8 v) = _splitSignature(signature);

        // If the signature is valid (and not malleable), return the signer address
        signer = ecrecover(hash, v, r, s);

        if (signer == address(0)) revert NullSignerAddress();
    }

    /**
     * @notice Checks whether the signer is valid
     * @param hash Data hash
     * @param signer Signer address (to confirm message validity)
     * @param signature Signature parameters encoded (v, r, s)
     * @dev For EIP-712 signatures, the hash must be the digest (computed with signature hash and domain separator)
     */
    function _verify(
        bytes32 hash,
        address signer,
        bytes memory signature
    ) internal view {
        if (signer.code.length == 0) {
            if (_recoverEOASigner(hash, signature) != signer) revert InvalidSignatureEOA();
        } else {
            if (IERC1271(signer).isValidSignature(hash, signature) != 0x1626ba7e) revert InvalidSignatureERC1271();
        }
    }
}

// contracts/interfaces/ILooksRareAggregator.sol

interface ILooksRareAggregator {
    struct TradeData {
        address proxy; // The marketplace proxy's address
        bytes4 selector; // The marketplace proxy's function selector
        uint256 value; // The amount of ETH passed to the proxy during the function call
        uint256 maxFeeBp; // The maximum fee basis point the buyer is willing to pay
        BasicOrder[] orders; // Orders to be executed by the marketplace
        bytes[] ordersExtraData; // Extra data for each order, specific for each marketplace
        bytes extraData; // Extra data specific for each marketplace
    }

    /**
     * @notice Execute NFT sweeps in different marketplaces in a single transaction
     * @param tokenTransfers Aggregated ERC20 token transfers for all markets
     * @param tradeData Data object to be passed downstream to each marketplace's proxy for execution
     * @param originator The address that originated the transaction, hardcoded as msg.sender if it is called directly
     * @param recipient The address to receive the purchased NFTs
     * @param isAtomic Flag to enable atomic trades (all or nothing) or partial trades
     */
    function execute(
        TokenTransfer[] calldata tokenTransfers,
        TradeData[] calldata tradeData,
        address originator,
        address recipient,
        bool isAtomic
    ) external payable;

    /**
     * @dev Emitted when erc20EnabledLooksRareAggregator is set
     */
    event ERC20EnabledLooksRareAggregatorSet();

    /**
     * @dev Emitted when fee is updated
     * @param proxy Proxy to apply the fee to
     * @param bp Fee basis point
     * @param recipient Fee recipient
     */
    event FeeUpdated(address proxy, uint256 bp, address recipient);

    /**
     * @notice Emitted when a marketplace proxy's function is enabled.
     * @param proxy The marketplace proxy's address
     * @param selector The marketplace proxy's function selector
     */
    event FunctionAdded(address indexed proxy, bytes4 selector);

    /**
     * @notice Emitted when a marketplace proxy's function is disabled.
     * @param proxy The marketplace proxy's address
     * @param selector The marketplace proxy's function selector
     */
    event FunctionRemoved(address indexed proxy, bytes4 selector);

    /**
     * @notice Emitted when execute is complete
     * @param sweeper The address that submitted the transaction
     */
    event Sweep(address indexed sweeper);

    error AlreadySet();
    error FeeTooHigh();
    error InvalidFunction();
    error InvalidOrderLength();
    error TradeExecutionFailed();
    error UseERC20EnabledLooksRareAggregator();
    error ZeroAddress();
}

// contracts/interfaces/IProxy.sol

interface IProxy {
    error InvalidCaller();
    error InvalidOrderLength();
    error ZeroAddress();

    /**
     * @notice Execute NFT sweeps in a single transaction
     * @param orders Orders to be executed
     * @param ordersExtraData Extra data for each order
     * @param extraData Extra data for the whole transaction
     * @param recipient The address to receive the purchased NFTs
     * @param isAtomic Flag to enable atomic trades (all or nothing) or partial trades
     * @param feeBp Fee basis point to pay for the trade, set by the aggregator
     * @param feeRecipient Fee recipient for the trade, set by the aggregator
     */
    function execute(
        BasicOrder[] calldata orders,
        bytes[] calldata ordersExtraData,
        bytes calldata extraData,
        address recipient,
        bool isAtomic,
        uint256 feeBp,
        address feeRecipient
    ) external payable;
}

// contracts/TokenTransferrer.sol

/**
 * @title TokenTransferrer
 * @notice This contract contains a function to transfer NFTs from a proxy to the recipient
 * @author LooksRare protocol team (👀,💎)
 */
abstract contract TokenTransferrer {
    function _transferTokenToRecipient(
        CollectionType collectionType,
        address recipient,
        address collection,
        uint256 tokenId,
        uint256 amount
    ) internal {
        if (collectionType == CollectionType.ERC721) {
            IERC721(collection).transferFrom(address(this), recipient, tokenId);
        } else if (collectionType == CollectionType.ERC1155) {
            IERC1155(collection).safeTransferFrom(address(this), recipient, tokenId, amount, "");
        }
    }
}

// contracts/TokenRescuer.sol

/**
 * @title TokenRescuer
 * @notice This contract contains functions to move tokens
 * @author LooksRare protocol team (👀,💎)
 */
contract TokenRescuer is OwnableTwoSteps, LowLevelETH, LowLevelERC20Transfer {
    error InsufficientAmount();

    /**
     * @notice Rescue the contract's trapped ETH
     * @dev Must be called by the current owner
     * @param to Send the contract's ETH balance to this address
     */
    function rescueETH(address to) external onlyOwner {
        uint256 withdrawAmount = address(this).balance - 1;
        if (withdrawAmount == 0) revert InsufficientAmount();
        _transferETH(to, withdrawAmount);
    }

    /**
     * @notice Rescue any of the contract's trapped ERC20 tokens
     * @dev Must be called by the current owner
     * @param currency The address of the ERC20 token to rescue from the contract
     * @param to Send the contract's specified ERC20 token balance to this address
     */
    function rescueERC20(address currency, address to) external onlyOwner {
        uint256 withdrawAmount = IERC20(currency).balanceOf(address(this)) - 1;
        if (withdrawAmount == 0) revert InsufficientAmount();
        _executeERC20DirectTransfer(currency, to, withdrawAmount);
    }
}

// contracts/proxies/LooksRareProxy.sol

/**
 * @title LooksRareProxy
 * @notice This contract allows NFT sweepers to batch buy NFTs from LooksRare
 *         by passing high-level structs + low-level bytes as calldata.
 * @author LooksRare protocol team (👀,💎)
 */
contract LooksRareProxy is IProxy, TokenRescuer, TokenTransferrer, SignatureChecker {
    struct OrderExtraData {
        uint256 makerAskPrice; // Maker ask price, which is not necessarily equal to the taker bid price
        uint256 minPercentageToAsk; // The maker's minimum % to receive from the sale
        uint256 nonce; // The maker's nonce
        address strategy; // LooksRare execution strategy
    }

    ILooksRareExchange public immutable marketplace;
    address public immutable aggregator;

    /**
     * @param _marketplace LooksRareExchange's address
     * @param _aggregator LooksRareAggregator's address
     */
    constructor(address _marketplace, address _aggregator) {
        marketplace = ILooksRareExchange(_marketplace);
        aggregator = _aggregator;
    }

    /**
     * @notice Execute LooksRare NFT sweeps in a single transaction
     * @dev extraData, feeBp and feeRecipient are not used
     * @param orders Orders to be executed by LooksRare
     * @param ordersExtraData Extra data for each order
     * @param recipient The address to receive the purchased NFTs
     * @param isAtomic Flag to enable atomic trades (all or nothing) or partial trades
     */
    function execute(
        BasicOrder[] calldata orders,
        bytes[] calldata ordersExtraData,
        bytes memory,
        address recipient,
        bool isAtomic,
        uint256,
        address
    ) external payable override {
        if (address(this) != aggregator) revert InvalidCaller();

        uint256 ordersLength = orders.length;
        if (ordersLength == 0 || ordersLength != ordersExtraData.length) revert InvalidOrderLength();

        for (uint256 i; i < ordersLength; ) {
            BasicOrder memory order = orders[i];

            OrderExtraData memory orderExtraData = abi.decode(ordersExtraData[i], (OrderExtraData));

            OrderTypes.MakerOrder memory makerAsk;
            {
                makerAsk.isOrderAsk = true;
                makerAsk.signer = order.signer;
                makerAsk.collection = order.collection;
                makerAsk.tokenId = order.tokenIds[0];
                makerAsk.price = orderExtraData.makerAskPrice;
                makerAsk.amount = order.amounts[0];
                makerAsk.strategy = orderExtraData.strategy;
                makerAsk.nonce = orderExtraData.nonce;
                makerAsk.minPercentageToAsk = orderExtraData.minPercentageToAsk;
                makerAsk.currency = order.currency;
                makerAsk.startTime = order.startTime;
                makerAsk.endTime = order.endTime;

                (bytes32 r, bytes32 s, uint8 v) = _splitSignature(order.signature);
                makerAsk.v = v;
                makerAsk.r = r;
                makerAsk.s = s;
            }

            OrderTypes.TakerOrder memory takerBid;
            {
                takerBid.isOrderAsk = false;
                takerBid.taker = address(this);
                takerBid.price = order.price;
                takerBid.tokenId = makerAsk.tokenId;
                takerBid.minPercentageToAsk = makerAsk.minPercentageToAsk;
            }

            _executeSingleOrder(takerBid, makerAsk, recipient, order.collectionType, isAtomic);

            unchecked {
                ++i;
            }
        }
    }

    function _executeSingleOrder(
        OrderTypes.TakerOrder memory takerBid,
        OrderTypes.MakerOrder memory makerAsk,
        address recipient,
        CollectionType collectionType,
        bool isAtomic
    ) private {
        if (isAtomic) {
            marketplace.matchAskWithTakerBidUsingETHAndWETH{value: takerBid.price}(takerBid, makerAsk);
            _transferTokenToRecipient(
                collectionType,
                recipient,
                makerAsk.collection,
                makerAsk.tokenId,
                makerAsk.amount
            );
        } else {
            try marketplace.matchAskWithTakerBidUsingETHAndWETH{value: takerBid.price}(takerBid, makerAsk) {
                _transferTokenToRecipient(
                    collectionType,
                    recipient,
                    makerAsk.collection,
                    makerAsk.tokenId,
                    makerAsk.amount
                );
            } catch {}
        }
    }
}

// contracts/LooksRareAggregator.sol

/**
 * @title LooksRareAggregator
 * @notice This contract allows NFT sweepers to buy NFTs from different marketplaces
 *         by passing high-level structs + low-level bytes as calldata.
 * @author LooksRare protocol team (👀,💎)
 */
contract LooksRareAggregator is
    ILooksRareAggregator,
    TokenRescuer,
    TokenReceiver,
    ReentrancyGuard,
    LowLevelERC20Approve,
    LowLevelERC721Transfer,
    LowLevelERC1155Transfer
{
    /**
     * @notice Transactions that only involve ETH orders should be submitted to this contract
     *         directly. Transactions that involve ERC20 orders should be submitted to the contract
     *         ERC20EnabledLooksRareAggregator and it will call this contract's execution function.
     *         The purpose is to prevent a malicious proxy from stealing users' ERC20 tokens if
     *         this contract's ownership is compromised. By not providing any allowances to this
     *         aggregator, even if a malicious proxy is added, it cannot call
     *         token.transferFrom(victim, attacker, amount) inside the proxy within the context of the
     *         aggregator.
     */
    address public erc20EnabledLooksRareAggregator;
    mapping(address => mapping(bytes4 => bool)) private _proxyFunctionSelectors;
    mapping(address => FeeData) private _proxyFeeData;

    /**
     * @inheritdoc ILooksRareAggregator
     */
    function execute(
        TokenTransfer[] calldata tokenTransfers,
        TradeData[] calldata tradeData,
        address originator,
        address recipient,
        bool isAtomic
    ) external payable nonReentrant {
        if (recipient == address(0)) revert ZeroAddress();
        uint256 tradeDataLength = tradeData.length;
        if (tradeDataLength == 0) revert InvalidOrderLength();

        uint256 tokenTransfersLength = tokenTransfers.length;
        if (tokenTransfersLength == 0) {
            originator = msg.sender;
        } else if (msg.sender != erc20EnabledLooksRareAggregator) {
            revert UseERC20EnabledLooksRareAggregator();
        }

        for (uint256 i; i < tradeDataLength; ) {
            TradeData calldata singleTradeData = tradeData[i];
            if (!_proxyFunctionSelectors[singleTradeData.proxy][singleTradeData.selector]) revert InvalidFunction();

            (bytes memory proxyCalldata, bool maxFeeBpViolated) = _encodeCalldataAndValidateFeeBp(
                singleTradeData,
                recipient,
                isAtomic
            );
            if (maxFeeBpViolated) {
                if (isAtomic) {
                    revert FeeTooHigh();
                } else {
                    unchecked {
                        ++i;
                    }
                    continue;
                }
            }
            (bool success, bytes memory returnData) = singleTradeData.proxy.delegatecall(proxyCalldata);

            if (!success) {
                if (isAtomic) {
                    if (returnData.length > 0) {
                        assembly {
                            let returnDataSize := mload(returnData)
                            revert(add(32, returnData), returnDataSize)
                        }
                    } else {
                        revert TradeExecutionFailed();
                    }
                }
            }

            unchecked {
                ++i;
            }
        }

        if (tokenTransfersLength > 0) _returnERC20TokensIfAny(tokenTransfers, originator);
        _returnETHIfAny(originator);

        emit Sweep(originator);
    }

    /**
     * @notice Enable making ERC20 trades by setting the ERC20 enabled LooksRare aggregator
     * @dev Must be called by the current owner. It can only be set once to prevent
     *      a malicious aggregator from being set in case of an ownership compromise.
     * @param _erc20EnabledLooksRareAggregator The ERC20 enabled LooksRare aggregator's address
     */
    function setERC20EnabledLooksRareAggregator(address _erc20EnabledLooksRareAggregator) external onlyOwner {
        if (erc20EnabledLooksRareAggregator != address(0)) revert AlreadySet();
        erc20EnabledLooksRareAggregator = _erc20EnabledLooksRareAggregator;
        emit ERC20EnabledLooksRareAggregatorSet();
    }

    /**
     * @notice Enable calling the specified proxy's trade function
     * @dev Must be called by the current owner
     * @param proxy The marketplace proxy's address
     * @param selector The marketplace proxy's function selector
     */
    function addFunction(address proxy, bytes4 selector) external onlyOwner {
        _proxyFunctionSelectors[proxy][selector] = true;
        emit FunctionAdded(proxy, selector);
    }

    /**
     * @notice Disable calling the specified proxy's trade function
     * @dev Must be called by the current owner
     * @param proxy The marketplace proxy's address
     * @param selector The marketplace proxy's function selector
     */
    function removeFunction(address proxy, bytes4 selector) external onlyOwner {
        delete _proxyFunctionSelectors[proxy][selector];
        emit FunctionRemoved(proxy, selector);
    }

    /**
     * @param proxy Proxy to apply the fee to
     * @param bp Fee basis point
     * @param recipient Fee recipient
     */
    function setFee(
        address proxy,
        uint256 bp,
        address recipient
    ) external onlyOwner {
        if (bp > 10000) revert FeeTooHigh();
        _proxyFeeData[proxy].bp = bp;
        _proxyFeeData[proxy].recipient = recipient;

        emit FeeUpdated(proxy, bp, recipient);
    }

    /**
     * @notice Approve marketplaces to transfer ERC20 tokens from the aggregator
     * @param marketplace The marketplace address to approve
     * @param currency The ERC20 token address to approve
     * @param amount The amount of ERC20 token to approve
     */
    function approve(
        address marketplace,
        address currency,
        uint256 amount
    ) external onlyOwner {
        _executeERC20Approve(currency, marketplace, amount);
    }

    /**
     * @param proxy The marketplace proxy's address
     * @param selector The marketplace proxy's function selector
     * @return Whether the marketplace proxy's function can be called from the aggregator
     */
    function supportsProxyFunction(address proxy, bytes4 selector) external view returns (bool) {
        return _proxyFunctionSelectors[proxy][selector];
    }

    /**
     * @notice Rescue any of the contract's trapped ERC721 tokens
     * @dev Must be called by the current owner
     * @param collection The address of the ERC721 token to rescue from the contract
     * @param tokenId The token ID of the ERC721 token to rescue from the contract
     * @param to Send the contract's specified ERC721 token ID to this address
     */
    function rescueERC721(
        address collection,
        address to,
        uint256 tokenId
    ) external onlyOwner {
        _executeERC721TransferFrom(collection, address(this), to, tokenId);
    }

    /**
     * @notice Rescue any of the contract's trapped ERC1155 tokens
     * @dev Must be called by the current owner
     * @param collection The address of the ERC1155 token to rescue from the contract
     * @param tokenIds The token IDs of the ERC1155 token to rescue from the contract
     * @param amounts The amount of each token ID to rescue
     * @param to Send the contract's specified ERC1155 token ID to this address
     */
    function rescueERC1155(
        address collection,
        address to,
        uint256[] calldata tokenIds,
        uint256[] calldata amounts
    ) external onlyOwner {
        _executeERC1155SafeBatchTransferFrom(collection, address(this), to, tokenIds, amounts);
    }

    receive() external payable {}

    function _encodeCalldataAndValidateFeeBp(
        TradeData calldata singleTradeData,
        address recipient,
        bool isAtomic
    ) private view returns (bytes memory proxyCalldata, bool maxFeeBpViolated) {
        FeeData memory feeData = _proxyFeeData[singleTradeData.proxy];
        maxFeeBpViolated = singleTradeData.maxFeeBp < feeData.bp;
        proxyCalldata = abi.encodeWithSelector(
            singleTradeData.selector,
            singleTradeData.orders,
            singleTradeData.ordersExtraData,
            singleTradeData.extraData,
            recipient,
            isAtomic,
            feeData.bp,
            feeData.recipient
        );
    }

    function _returnERC20TokensIfAny(TokenTransfer[] calldata tokenTransfers, address recipient) private {
        uint256 tokenTransfersLength = tokenTransfers.length;
        for (uint256 i; i < tokenTransfersLength; ) {
            uint256 balance = IERC20(tokenTransfers[i].currency).balanceOf(address(this));
            if (balance > 0) _executeERC20DirectTransfer(tokenTransfers[i].currency, recipient, balance);

            unchecked {
                ++i;
            }
        }
    }
}

