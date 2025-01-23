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

abstract contract CERC20 is ERC20 {
    /// @notice Deposit an amount of underlying tokens to the CERC20.
    /// @param underlyingAmount Amount of underlying tokens to deposit.
    /// @return An error code or zero if there was no error in the deposit.
    function mint(uint256 underlyingAmount) external virtual returns (uint256);

    /// @notice Borrow an amount of underlying tokens from the CERC20.
    /// @param underlyingAmount Amount of underlying tokens to borrow.
    /// @return An error code or zero if there was no error in the borrow.
    function borrow(uint256 underlyingAmount) external virtual returns (uint256);

    /// @notice Repay an amount of underlying tokens to the CERC20.
    /// @param underlyingAmount Amount of underlying tokens to repay.
    /// @return An error code or zero if there was no error in the repay.
    function repayBorrow(uint256 underlyingAmount) external virtual returns (uint256);

    /// @notice Returns the underlying balance of a specific user.
    /// @param user The user who's balance the CERC20 will retrieve.
    /// @return The amount of underlying tokens the user is entitled to.
    function balanceOfUnderlying(address user) external view virtual returns (uint256);

    /// @notice Returns the amount of underlying tokens a cToken redeemable for.
    /// @return The amount of underlying tokens a cToken is redeemable for.
    function exchangeRateStored() external view virtual returns (uint256);

    /// @notice Withdraw a specific amount of underlying tokens from the CERC20.
    /// @param underlyingAmount Amount of underlying tokens to withdraw.
    /// @return An error code or zero if there was no error in the withdraw.
    function redeemUnderlying(uint256 underlyingAmount) external virtual returns (uint256);

    /// @notice Return teh current borrow balance of a user in the CERC20.
    /// @param user The user to get the borrow balance for.
    /// @return The current borrow balance of the user.
    function borrowBalanceCurrent(address user) external virtual returns (uint256);

    /// @notice Repay a user's borrow on their behalf.
    /// @param user The user who's borrow to repay.
    /// @param underlyingAmount The amount of debt to repay.
    /// @return An error code or zero if there was no error in the repayBorrowBehalf.
    function repayBorrowBehalf(address user, uint256 underlyingAmount) external virtual returns (uint256);
}
interface PriceFeed {
    /// @notice Get the underlying price of the cToken's asset.
    /// @param cToken The cToken to get the underlying price of.
    /// @return The underlying asset price scaled by 1e18.
    function getUnderlyingPrice(CERC20 cToken) external view returns (uint256);
}

interface FuseAdmin {
    /// @notice Whitelists or blacklists a user from accessing the cTokens in the pool.
    /// @param users The users to whitelist or blacklist.
    /// @param enabled Whether to whitelist or blacklist each user.
    function _setWhitelistStatuses(address[] calldata users, bool[] calldata enabled) external;

    function _deployMarket(
        address underlying,
        address irm,
        string calldata name,
        string calldata symbol,
        address impl,
        bytes calldata data,
        uint256 reserveFactor,
        uint256 adminFee,
        uint256 collateralFactorMantissa
    ) external;
}
abstract contract Fei is ERC20 {
    function mint(address to, uint256 amount) external virtual;
}
interface Comptroller {
    /// @notice Retrieves the admin of the Comptroller.
    /// @return The current administrator of the Comptroller.
    function admin() external view returns (address);

    /// @notice Retrieves the price feed of the Comptroller.
    /// @return The current price feed of the Comptroller.
    function oracle() external view returns (PriceFeed);

    /// @notice Maps underlying tokens to their equivalent cTokens in a pool.
    /// @param token The underlying token to find the equivalent cToken for.
    /// @return The equivalent cToken for the given underlying token.
    function cTokensByUnderlying(ERC20 token) external view returns (CERC20);

    /// @notice Get's data about a cToken.
    /// @param cToken The cToken to get data about.
    /// @return isListed Whether the cToken is listed in the Comptroller.
    /// @return collateralFactor The collateral factor of the cToken.

    function markets(CERC20 cToken) external view returns (bool isListed, uint256 collateralFactor);

    /// @notice Enters into a list of cToken markets, enabling them as collateral.
    /// @param cTokens The list of cTokens to enter into, enabling them as collateral.
    /// @return A list of error codes, or 0 if there were no failures in entering the cTokens.
    function enterMarkets(CERC20[] calldata cTokens) external returns (uint256[] memory);
}



library SafeTransferLib {
    /*//////////////////////////////////////////////////////////////
                             ETH OPERATIONS
    //////////////////////////////////////////////////////////////*/

    function safeTransferETH(address to, uint256 amount) internal {
        bool success;

        /// @solidity memory-safe-assembly
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

        /// @solidity memory-safe-assembly
        assembly {
            // Get a pointer to some free memory.
            let freeMemoryPointer := mload(0x40)

            // Write the abi-encoded calldata into memory, beginning with the function selector.
            mstore(freeMemoryPointer, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
            mstore(add(freeMemoryPointer, 4), and(from, 0xffffffffffffffffffffffffffffffffffffffff)) // Append and mask the "from" argument.
            mstore(add(freeMemoryPointer, 36), and(to, 0xffffffffffffffffffffffffffffffffffffffff)) // Append and mask the "to" argument.
            mstore(add(freeMemoryPointer, 68), amount) // Append the "amount" argument. Masking not required as it's a full 32 byte type.

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

        /// @solidity memory-safe-assembly
        assembly {
            // Get a pointer to some free memory.
            let freeMemoryPointer := mload(0x40)

            // Write the abi-encoded calldata into memory, beginning with the function selector.
            mstore(freeMemoryPointer, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
            mstore(add(freeMemoryPointer, 4), and(to, 0xffffffffffffffffffffffffffffffffffffffff)) // Append and mask the "to" argument.
            mstore(add(freeMemoryPointer, 36), amount) // Append the "amount" argument. Masking not required as it's a full 32 byte type.

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

        /// @solidity memory-safe-assembly
        assembly {
            // Get a pointer to some free memory.
            let freeMemoryPointer := mload(0x40)

            // Write the abi-encoded calldata into memory, beginning with the function selector.
            mstore(freeMemoryPointer, 0x095ea7b300000000000000000000000000000000000000000000000000000000)
            mstore(add(freeMemoryPointer, 4), and(to, 0xffffffffffffffffffffffffffffffffffffffff)) // Append and mask the "to" argument.
            mstore(add(freeMemoryPointer, 36), amount) // Append the "amount" argument. Masking not required as it's a full 32 byte type.

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

library FixedPointMathLib {
    /*//////////////////////////////////////////////////////////////
                    SIMPLIFIED FIXED POINT OPERATIONS
    //////////////////////////////////////////////////////////////*/

    uint256 internal constant MAX_UINT256 = 2**256 - 1;

    uint256 internal constant WAD = 1e18; // The scalar of ETH and most ERC20s.

    function mulWadDown(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivDown(x, y, WAD); // Equivalent to (x * y) / WAD rounded down.
    }

    function mulWadUp(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivUp(x, y, WAD); // Equivalent to (x * y) / WAD rounded up.
    }

    function divWadDown(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivDown(x, WAD, y); // Equivalent to (x * WAD) / y rounded down.
    }

    function divWadUp(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivUp(x, WAD, y); // Equivalent to (x * WAD) / y rounded up.
    }

    /*//////////////////////////////////////////////////////////////
                    LOW LEVEL FIXED POINT OPERATIONS
    //////////////////////////////////////////////////////////////*/

    function mulDivDown(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            // Equivalent to require(denominator != 0 && (y == 0 || x <= type(uint256).max / y))
            if iszero(mul(denominator, iszero(mul(y, gt(x, div(MAX_UINT256, y)))))) {
                revert(0, 0)
            }

            // Divide x * y by the denominator.
            z := div(mul(x, y), denominator)
        }
    }

    function mulDivUp(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            // Equivalent to require(denominator != 0 && (y == 0 || x <= type(uint256).max / y))
            if iszero(mul(denominator, iszero(mul(y, gt(x, div(MAX_UINT256, y)))))) {
                revert(0, 0)
            }

            // If x * y modulo the denominator is strictly greater than 0,
            // 1 is added to round up the division of x * y by the denominator.
            z := add(gt(mod(mul(x, y), denominator), 0), div(mul(x, y), denominator))
        }
    }

    function rpow(
        uint256 x,
        uint256 n,
        uint256 scalar
    ) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            switch x
            case 0 {
                switch n
                case 0 {
                    // 0 ** 0 = 1
                    z := scalar
                }
                default {
                    // 0 ** n = 0
                    z := 0
                }
            }
            default {
                switch mod(n, 2)
                case 0 {
                    // If n is even, store scalar in z for now.
                    z := scalar
                }
                default {
                    // If n is odd, store x in z for now.
                    z := x
                }

                // Shifting right by 1 is like dividing by 2.
                let half := shr(1, scalar)

                for {
                    // Shift n right by 1 before looping to halve it.
                    n := shr(1, n)
                } n {
                    // Shift n right by 1 each iteration to halve it.
                    n := shr(1, n)
                } {
                    // Revert immediately if x ** 2 would overflow.
                    // Equivalent to iszero(eq(div(xx, x), x)) here.
                    if shr(128, x) {
                        revert(0, 0)
                    }

                    // Store x squared.
                    let xx := mul(x, x)

                    // Round to the nearest number.
                    let xxRound := add(xx, half)

                    // Revert if xx + half overflowed.
                    if lt(xxRound, xx) {
                        revert(0, 0)
                    }

                    // Set x to scaled xxRound.
                    x := div(xxRound, scalar)

                    // If n is even:
                    if mod(n, 2) {
                        // Compute z * x.
                        let zx := mul(z, x)

                        // If z * x overflowed:
                        if iszero(eq(div(zx, x), z)) {
                            // Revert if x is non-zero.
                            if iszero(iszero(x)) {
                                revert(0, 0)
                            }
                        }

                        // Round to the nearest number.
                        let zxRound := add(zx, half)

                        // Revert if zx + half overflowed.
                        if lt(zxRound, zx) {
                            revert(0, 0)
                        }

                        // Return properly scaled zxRound.
                        z := div(zxRound, scalar)
                    }
                }
            }
        }
    }

    /*//////////////////////////////////////////////////////////////
                        GENERAL NUMBER UTILITIES
    //////////////////////////////////////////////////////////////*/

    function sqrt(uint256 x) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            let y := x // We start y at x, which will help us make our initial estimate.

            z := 181 // The "correct" value is 1, but this saves a multiplication later.

            // This segment is to get a reasonable initial estimate for the Babylonian method. With a bad
            // start, the correct # of bits increases ~linearly each iteration instead of ~quadratically.

            // We check y >= 2^(k + 8) but shift right by k bits
            // each branch to ensure that if x >= 256, then y >= 256.
            if iszero(lt(y, 0x10000000000000000000000000000000000)) {
                y := shr(128, y)
                z := shl(64, z)
            }
            if iszero(lt(y, 0x1000000000000000000)) {
                y := shr(64, y)
                z := shl(32, z)
            }
            if iszero(lt(y, 0x10000000000)) {
                y := shr(32, y)
                z := shl(16, z)
            }
            if iszero(lt(y, 0x1000000)) {
                y := shr(16, y)
                z := shl(8, z)
            }

            // Goal was to get z*z*y within a small factor of x. More iterations could
            // get y in a tighter range. Currently, we will have y in [256, 256*2^16).
            // We ensured y >= 256 so that the relative difference between y and y+1 is small.
            // That's not possible if x < 256 but we can just verify those cases exhaustively.

            // Now, z*z*y <= x < z*z*(y+1), and y <= 2^(16+8), and either y >= 256, or x < 256.
            // Correctness can be checked exhaustively for x < 256, so we assume y >= 256.
            // Then z*sqrt(y) is within sqrt(257)/sqrt(256) of sqrt(x), or about 20bps.

            // For s in the range [1/256, 256], the estimate f(s) = (181/1024) * (s+1) is in the range
            // (1/2.84 * sqrt(s), 2.84 * sqrt(s)), with largest error when s = 1 and when s = 256 or 1/256.

            // Since y is in [256, 256*2^16), let a = y/65536, so that a is in [1/256, 256). Then we can estimate
            // sqrt(y) using sqrt(65536) * 181/1024 * (a + 1) = 181/4 * (y + 65536)/65536 = 181 * (y + 65536)/2^18.

            // There is no overflow risk here since y < 2^136 after the first branch above.
            z := shr(18, mul(z, add(y, 65536))) // A mul() is saved from starting z at 181.

            // Given the worst case multiplicative error of 2.84 above, 7 iterations should be enough.
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))

            // If x+1 is a perfect square, the Babylonian method cycles between
            // floor(sqrt(x)) and ceil(sqrt(x)). This statement ensures we return floor.
            // See: https://en.wikipedia.org/wiki/Integer_square_root#Using_only_integer_division
            // Since the ceil is rare, we save gas on the assignment and repeat division in the rare case.
            // If you don't care whether the floor or ceil square root is returned, you can remove this statement.
            z := sub(z, lt(div(x, z), z))
        }
    }

    function unsafeMod(uint256 x, uint256 y) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            // Mod x by y. Note this will return
            // 0 instead of reverting if y is zero.
            z := mod(x, y)
        }
    }

    function unsafeDiv(uint256 x, uint256 y) internal pure returns (uint256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            // Divide x by y. Note this will return
            // 0 instead of reverting if y is zero.
            r := div(x, y)
        }
    }

    function unsafeDivUp(uint256 x, uint256 y) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            // Add 1 to x * y if x % y > 0. Note this will
            // return 0 instead of reverting if y is zero.
            z := add(gt(mod(x, y), 0), div(x, y))
        }
    }
}
abstract contract ERC4626 is ERC20 {
    using SafeTransferLib for ERC20;
    using FixedPointMathLib for uint256;

    /*//////////////////////////////////////////////////////////////
                                 EVENTS
    //////////////////////////////////////////////////////////////*/

    event Deposit(address indexed caller, address indexed owner, uint256 assets, uint256 shares);

    event Withdraw(
        address indexed caller,
        address indexed receiver,
        address indexed owner,
        uint256 assets,
        uint256 shares
    );

    /*//////////////////////////////////////////////////////////////
                               IMMUTABLES
    //////////////////////////////////////////////////////////////*/

    ERC20 public immutable asset;

    constructor(
        ERC20 _asset,
        string memory _name,
        string memory _symbol
    ) ERC20(_name, _symbol, _asset.decimals()) {
        asset = _asset;
    }

    /*//////////////////////////////////////////////////////////////
                        DEPOSIT/WITHDRAWAL LOGIC
    //////////////////////////////////////////////////////////////*/

    function deposit(uint256 assets, address receiver) public virtual returns (uint256 shares) {
        // Check for rounding error since we round down in previewDeposit.
        require((shares = previewDeposit(assets)) != 0, "ZERO_SHARES");

        // Need to transfer before minting or ERC777s could reenter.
        asset.safeTransferFrom(msg.sender, address(this), assets);

        _mint(receiver, shares);

        emit Deposit(msg.sender, receiver, assets, shares);

        afterDeposit(assets, shares);
    }

    function mint(uint256 shares, address receiver) public virtual returns (uint256 assets) {
        assets = previewMint(shares); // No need to check for rounding error, previewMint rounds up.

        // Need to transfer before minting or ERC777s could reenter.
        asset.safeTransferFrom(msg.sender, address(this), assets);

        _mint(receiver, shares);

        emit Deposit(msg.sender, receiver, assets, shares);

        afterDeposit(assets, shares);
    }

    function withdraw(
        uint256 assets,
        address receiver,
        address owner
    ) public virtual returns (uint256 shares) {
        shares = previewWithdraw(assets); // No need to check for rounding error, previewWithdraw rounds up.

        if (msg.sender != owner) {
            uint256 allowed = allowance[owner][msg.sender]; // Saves gas for limited approvals.

            if (allowed != type(uint256).max) allowance[owner][msg.sender] = allowed - shares;
        }

        beforeWithdraw(assets, shares);

        _burn(owner, shares);

        emit Withdraw(msg.sender, receiver, owner, assets, shares);

        asset.safeTransfer(receiver, assets);
    }

    function redeem(
        uint256 shares,
        address receiver,
        address owner
    ) public virtual returns (uint256 assets) {
        if (msg.sender != owner) {
            uint256 allowed = allowance[owner][msg.sender]; // Saves gas for limited approvals.

            if (allowed != type(uint256).max) allowance[owner][msg.sender] = allowed - shares;
        }

        // Check for rounding error since we round down in previewRedeem.
        require((assets = previewRedeem(shares)) != 0, "ZERO_ASSETS");

        beforeWithdraw(assets, shares);

        _burn(owner, shares);

        emit Withdraw(msg.sender, receiver, owner, assets, shares);

        asset.safeTransfer(receiver, assets);
    }

    /*//////////////////////////////////////////////////////////////
                            ACCOUNTING LOGIC
    //////////////////////////////////////////////////////////////*/

    function totalAssets() public view virtual returns (uint256);

    function convertToShares(uint256 assets) public view virtual returns (uint256) {
        uint256 supply = totalSupply; // Saves an extra SLOAD if totalSupply is non-zero.

        return supply == 0 ? assets : assets.mulDivDown(supply, totalAssets());
    }

    function convertToAssets(uint256 shares) public view virtual returns (uint256) {
        uint256 supply = totalSupply; // Saves an extra SLOAD if totalSupply is non-zero.

        return supply == 0 ? shares : shares.mulDivDown(totalAssets(), supply);
    }

    function previewDeposit(uint256 assets) public view virtual returns (uint256) {
        return convertToShares(assets);
    }

    function previewMint(uint256 shares) public view virtual returns (uint256) {
        uint256 supply = totalSupply; // Saves an extra SLOAD if totalSupply is non-zero.

        return supply == 0 ? shares : shares.mulDivUp(totalAssets(), supply);
    }

    function previewWithdraw(uint256 assets) public view virtual returns (uint256) {
        uint256 supply = totalSupply; // Saves an extra SLOAD if totalSupply is non-zero.

        return supply == 0 ? assets : assets.mulDivUp(supply, totalAssets());
    }

    function previewRedeem(uint256 shares) public view virtual returns (uint256) {
        return convertToAssets(shares);
    }

    /*//////////////////////////////////////////////////////////////
                     DEPOSIT/WITHDRAWAL LIMIT LOGIC
    //////////////////////////////////////////////////////////////*/

    function maxDeposit(address) public view virtual returns (uint256) {
        return type(uint256).max;
    }

    function maxMint(address) public view virtual returns (uint256) {
        return type(uint256).max;
    }

    function maxWithdraw(address owner) public view virtual returns (uint256) {
        return convertToAssets(balanceOf[owner]);
    }

    function maxRedeem(address owner) public view virtual returns (uint256) {
        return balanceOf[owner];
    }

    /*//////////////////////////////////////////////////////////////
                          INTERNAL HOOKS LOGIC
    //////////////////////////////////////////////////////////////*/

    function beforeWithdraw(uint256 assets, uint256 shares) internal virtual {}

    function afterDeposit(uint256 assets, uint256 shares) internal virtual {}
}

abstract contract Auth {
    event OwnershipTransferred(address indexed user, address indexed newOwner);

    event AuthorityUpdated(address indexed user, Authority indexed newAuthority);

    address public owner;

    Authority public authority;

    constructor(address _owner, Authority _authority) {
        owner = _owner;
        authority = _authority;

        emit OwnershipTransferred(msg.sender, _owner);
        emit AuthorityUpdated(msg.sender, _authority);
    }

    modifier requiresAuth() virtual {
        require(isAuthorized(msg.sender, msg.sig), "UNAUTHORIZED");

        _;
    }

    function isAuthorized(address user, bytes4 functionSig) internal view virtual returns (bool) {
        Authority auth = authority; // Memoizing authority saves us a warm SLOAD, around 100 gas.

        // Checking if the caller is the owner only after calling the authority saves gas in most cases, but be
        // aware that this makes protected functions uncallable even to the owner if the authority is out of order.
        return (address(auth) != address(0) && auth.canCall(user, address(this), functionSig)) || user == owner;
    }

    function setAuthority(Authority newAuthority) public virtual {
        // We check if the caller is the owner first because we want to ensure they can
        // always swap out the authority even if it's reverting or using up a lot of gas.
        require(msg.sender == owner || authority.canCall(msg.sender, address(this), msg.sig));

        authority = newAuthority;

        emit AuthorityUpdated(msg.sender, newAuthority);
    }

    function transferOwnership(address newOwner) public virtual requiresAuth {
        owner = newOwner;

        emit OwnershipTransferred(msg.sender, newOwner);
    }
}

/// @notice A generic interface for a contract which provides authorization data to an Auth instance.
/// @author Solmate (https://github.com/transmissions11/solmate/blob/main/src/auth/Auth.sol)
/// @author Modified from Dappsys (https://github.com/dapphub/ds-auth/blob/master/src/auth.sol)
interface Authority {
    function canCall(
        address user,
        address target,
        bytes4 functionSig
    ) external view returns (bool);
}

abstract contract ReentrancyGuard {
    uint256 private locked = 1;

    modifier nonReentrant() virtual {
        require(locked == 1, "REENTRANCY");

        locked = 2;

        _;

        locked = 1;
    }
}

contract TurboBooster is Auth {
    /*///////////////////////////////////////////////////////////////
                              CONSTRUCTOR
    //////////////////////////////////////////////////////////////*/

    /// @notice Creates a new Turbo Booster contract.
    /// @param _owner The owner of the Booster.
    /// @param _authority The Authority of the Booster.
    constructor(address _owner, Authority _authority) Auth(_owner, _authority) {}

    /*///////////////////////////////////////////////////////////////
                      GLOBAL FREEZE CONFIGURATION
    //////////////////////////////////////////////////////////////*/

    /// @notice Whether boosting is currently frozen.
    bool public frozen;

    /// @notice Emitted when boosting is frozen or unfrozen.
    /// @param user The user who froze or unfroze boosting.
    /// @param frozen Whether boosting is now frozen.
    event FreezeStatusUpdated(address indexed user, bool frozen);

    /// @notice Sets whether boosting is frozen.
    /// @param freeze Whether boosting will be frozen.
    function setFreezeStatus(bool freeze) external requiresAuth {
        // Update freeze status.
        frozen = freeze;

        emit FreezeStatusUpdated(msg.sender, freeze);
    }

    /*///////////////////////////////////////////////////////////////
                     VAULT BOOST CAP CONFIGURATION
    //////////////////////////////////////////////////////////////*/

    /// @notice Maps Vaults to the cap on the amount of Fei used to boost them.
    mapping(ERC4626 => uint256) public getBoostCapForVault;

    /// @notice Emitted when a Vault's boost cap is updated.
    /// @param vault The Vault who's boost cap was updated.
    /// @param newBoostCap The new boost cap for the Vault.
    event BoostCapUpdatedForVault(address indexed user, ERC4626 indexed vault, uint256 newBoostCap);

    /// @notice Sets a Vault's boost cap.
    /// @param vault The Vault to set the boost cap for.
    /// @param newBoostCap The new boost cap for the Vault.
    function setBoostCapForVault(ERC4626 vault, uint256 newBoostCap) external requiresAuth {
        // Update the boost cap for the Vault.
        getBoostCapForVault[vault] = newBoostCap;

        emit BoostCapUpdatedForVault(msg.sender, vault, newBoostCap);
    }

    /*///////////////////////////////////////////////////////////////
                     COLLATERAL BOOST CAP CONFIGURATION
    //////////////////////////////////////////////////////////////*/

    /// @notice Maps collateral types to the cap on the amount of Fei boosted against them.
    mapping(ERC20 => uint256) public getBoostCapForCollateral;

    /// @notice Emitted when a collateral type's boost cap is updated.
    /// @param collateral The collateral type who's boost cap was updated.
    /// @param newBoostCap The new boost cap for the collateral type.
    event BoostCapUpdatedForCollateral(address indexed user, ERC20 indexed collateral, uint256 newBoostCap);

    /// @notice Sets a collateral type's boost cap.
    /// @param collateral The collateral type to set the boost cap for.
    /// @param newBoostCap The new boost cap for the collateral type.
    function setBoostCapForCollateral(ERC20 collateral, uint256 newBoostCap) external requiresAuth {
        // Update the boost cap for the collateral type.
        getBoostCapForCollateral[collateral] = newBoostCap;

        emit BoostCapUpdatedForCollateral(msg.sender, collateral, newBoostCap);
    }

    /*///////////////////////////////////////////////////////////////
                          AUTHORIZATION LOGIC
    //////////////////////////////////////////////////////////////*/

    /// @notice Returns whether a Safe is authorized to boost a Vault.
    /// @param safe The Safe to check is authorized to boost the Vault.
    /// @param collateral The collateral/asset of the Safe.
    /// @param vault The Vault to check the Safe is authorized to boost.
    /// @param feiAmount The amount of Fei asset to check the Safe is authorized boost the Vault with.
    /// @param newTotalBoostedForVault The total amount of Fei that will boosted to the Vault after boost (if it is not rejected).
    /// @param newTotalBoostedAgainstCollateral The total amount of Fei that will be boosted against the Safe's collateral type after this boost.
    /// @return Whether the Safe is authorized to boost the Vault with the given amount of Fei asset.
    function canSafeBoostVault(
        TurboSafe safe,
        ERC20 collateral,
        ERC4626 vault,
        uint256 feiAmount,
        uint256 newTotalBoostedForVault,
        uint256 newTotalBoostedAgainstCollateral
    ) external view returns (bool) {
        return
            !frozen &&
            getBoostCapForVault[vault] >= newTotalBoostedForVault &&
            getBoostCapForCollateral[collateral] >= newTotalBoostedAgainstCollateral;
    }
}

contract TurboClerk is Auth {
    /*///////////////////////////////////////////////////////////////
                              CONSTRUCTOR
    //////////////////////////////////////////////////////////////*/

    /// @notice Creates a new Turbo Clerk contract.
    /// @param _owner The owner of the Clerk.
    /// @param _authority The Authority of the Clerk.
    constructor(address _owner, Authority _authority) Auth(_owner, _authority) {}

    /*///////////////////////////////////////////////////////////////
                        DEFAULT FEE CONFIGURATION
    //////////////////////////////////////////////////////////////*/

    /// @notice The default fee on Safe interest taken by the protocol.
    /// @dev A fixed point number where 1e18 represents 100% and 0 represents 0%.
    uint256 public defaultFeePercentage;

    /// @notice Emitted when the default fee percentage is updated.
    /// @param newDefaultFeePercentage The new default fee percentage.
    event DefaultFeePercentageUpdated(address indexed user, uint256 newDefaultFeePercentage);

    /// @notice Sets the default fee percentage.
    /// @param newDefaultFeePercentage The new default fee percentage.
    function setDefaultFeePercentage(uint256 newDefaultFeePercentage) external requiresAuth {
        // A fee percentage over 100% makes no sense.
        require(newDefaultFeePercentage <= 1e18, "FEE_TOO_HIGH");

        // Update the default fee percentage.
        defaultFeePercentage = newDefaultFeePercentage;

        emit DefaultFeePercentageUpdated(msg.sender, newDefaultFeePercentage);
    }

    /*///////////////////////////////////////////////////////////////
                        CUSTOM FEE CONFIGURATION
    //////////////////////////////////////////////////////////////*/

    /// @notice Maps collaterals to their custom fees on interest taken by the protocol.
    /// @dev A fixed point number where 1e18 represents 100% and 0 represents 0%.
    mapping(ERC20 => uint256) public getCustomFeePercentageForCollateral;

    /// @notice Maps Safes to their custom fees on interest taken by the protocol.
    /// @dev A fixed point number where 1e18 represents 100% and 0 represents 0%.
    mapping(TurboSafe => uint256) public getCustomFeePercentageForSafe;

    /// @notice Emitted when a collateral's custom fee percentage is updated.
    /// @param collateral The collateral who's custom fee percentage was updated.
    /// @param newFeePercentage The new custom fee percentage.
    event CustomFeePercentageUpdatedForCollateral(
        address indexed user,
        ERC20 indexed collateral,
        uint256 newFeePercentage
    );

    /// @notice Sets a collateral's custom fee percentage.
    /// @param collateral The collateral to set the custom fee percentage for.
    /// @param newFeePercentage The new custom fee percentage for the collateral.
    function setCustomFeePercentageForCollateral(ERC20 collateral, uint256 newFeePercentage) external requiresAuth {
        // A fee percentage over 100% makes no sense.
        require(newFeePercentage <= 1e18, "FEE_TOO_HIGH");

        // Update the custom fee percentage for the Safe.
        getCustomFeePercentageForCollateral[collateral] = newFeePercentage;

        emit CustomFeePercentageUpdatedForCollateral(msg.sender, collateral, newFeePercentage);
    }

    /// @notice Emitted when a Safe's custom fee percentage is updated.
    /// @param safe The Safe who's custom fee percentage was updated.
    /// @param newFeePercentage The new custom fee percentage.
    event CustomFeePercentageUpdatedForSafe(address indexed user, TurboSafe indexed safe, uint256 newFeePercentage);

    /// @notice Sets a Safe's custom fee percentage.
    /// @param safe The Safe to set the custom fee percentage for.
    /// @param newFeePercentage The new custom fee percentage for the Safe.
    function setCustomFeePercentageForSafe(TurboSafe safe, uint256 newFeePercentage) external requiresAuth {
        // A fee percentage over 100% makes no sense.
        require(newFeePercentage <= 1e18, "FEE_TOO_HIGH");

        // Update the custom fee percentage for the Safe.
        getCustomFeePercentageForSafe[safe] = newFeePercentage;

        emit CustomFeePercentageUpdatedForSafe(msg.sender, safe, newFeePercentage);
    }

    /*///////////////////////////////////////////////////////////////
                          ACCOUNTING LOGIC
    //////////////////////////////////////////////////////////////*/

    /// @notice Returns the fee on interest taken by the protocol for a Safe.
    /// @param safe The Safe to get the fee percentage for.
    /// @param collateral The collateral/asset of the Safe.
    /// @return The fee percentage for the Safe.
    function getFeePercentageForSafe(TurboSafe safe, ERC20 collateral) external view returns (uint256) {
        // Get the custom fee percentage for the Safe.
        uint256 customFeePercentageForSafe = getCustomFeePercentageForSafe[safe];

        // If a custom fee percentage is set for the Safe, return it.
        if (customFeePercentageForSafe != 0) return customFeePercentageForSafe;

        // Get the custom fee percentage for the collateral type.
        uint256 customFeePercentageForCollateral = getCustomFeePercentageForCollateral[collateral];

        // If a custom fee percentage is set for the collateral, return it.
        if (customFeePercentageForCollateral != 0) return customFeePercentageForCollateral;

        // Otherwise, return the default fee percentage.
        return defaultFeePercentage;
    }
}

contract TurboMaster is Auth {
    using SafeTransferLib for ERC20;

    /*///////////////////////////////////////////////////////////////
                               IMMUTABLES
    //////////////////////////////////////////////////////////////*/

    /// @notice The Turbo Fuse Pool the Safes will interact with.
    Comptroller public immutable pool;

    /// @notice The Fei token on the network.
    ERC20 public immutable fei;

    /*///////////////////////////////////////////////////////////////
                              CONSTRUCTOR
    //////////////////////////////////////////////////////////////*/

    /// @notice Creates a new Turbo Master contract.
    /// @param _pool The Turbo Fuse Pool the Master will use.
    /// @param _fei The Fei token on the network.
    /// @param _owner The owner of the Master.
    /// @param _authority The Authority of the Master.
    constructor(
        Comptroller _pool,
        ERC20 _fei,
        address _owner,
        Authority _authority
    ) Auth(_owner, _authority) {
        pool = _pool;

        fei = _fei;

        // Prevent the first safe from getting id 0.
        safes.push(TurboSafe(address(0)));
    }

    /*///////////////////////////////////////////////////////////////
                            BOOSTER STORAGE
    //////////////////////////////////////////////////////////////*/

    /// @notice The Booster module used by the Master and its Safes.
    TurboBooster public booster;

    /// @notice Emitted when the Booster is updated.
    /// @param user The user who triggered the update of the Booster.
    /// @param newBooster The new Booster contract used by the Master.
    event BoosterUpdated(address indexed user, TurboBooster newBooster);

    /// @notice Update the Booster used by the Master.
    /// @param newBooster The new Booster contract to be used by the Master.
    function setBooster(TurboBooster newBooster) external requiresAuth {
        booster = newBooster;

        emit BoosterUpdated(msg.sender, newBooster);
    }

    /*///////////////////////////////////////////////////////////////
                             CLERK STORAGE
    //////////////////////////////////////////////////////////////*/

    /// @notice The Clerk module used by the Master and its Safes.
    TurboClerk public clerk;

    /// @notice Emitted when the Clerk is updated.
    /// @param user The user who triggered the update of the Clerk.
    /// @param newClerk The new Clerk contract used by the Master.
    event ClerkUpdated(address indexed user, TurboClerk newClerk);

    /// @notice Update the Clerk used by the Master.
    /// @param newClerk The new Clerk contract to be used by the Master.
    function setClerk(TurboClerk newClerk) external requiresAuth {
        clerk = newClerk;

        emit ClerkUpdated(msg.sender, newClerk);
    }

    /*///////////////////////////////////////////////////////////////
                  DEFAULT SAFE AUTHORITY CONFIGURATION
    //////////////////////////////////////////////////////////////*/

    /// @notice The default authority to be used by created Safes.
    Authority public defaultSafeAuthority;

    /// @notice Emitted when the default safe authority is updated.
    /// @param user The user who triggered the update of the default safe authority.
    /// @param newDefaultSafeAuthority The new default authority to be used by created Safes.
    event DefaultSafeAuthorityUpdated(address indexed user, Authority newDefaultSafeAuthority);

    /// @notice Set the default authority to be used by created Safes.
    /// @param newDefaultSafeAuthority The new default safe authority.
    function setDefaultSafeAuthority(Authority newDefaultSafeAuthority) external requiresAuth {
        // Update the default safe authority.
        defaultSafeAuthority = newDefaultSafeAuthority;

        emit DefaultSafeAuthorityUpdated(msg.sender, newDefaultSafeAuthority);
    }

    /*///////////////////////////////////////////////////////////////
                             SAFE STORAGE
    //////////////////////////////////////////////////////////////*/

    /// @notice The total Fei currently boosting Vaults.
    uint256 public totalBoosted;

    /// @notice Maps Safe addresses to the id they are stored under in the Safes array.
    mapping(TurboSafe => uint256) public getSafeId;

    /// @notice Maps Vault addresses to the total amount of Fei they've being boosted with.
    mapping(ERC4626 => uint256) public getTotalBoostedForVault;

    /// @notice Maps collateral types to the total amount of Fei boosted by Safes using it as collateral.
    mapping(ERC20 => uint256) public getTotalBoostedAgainstCollateral;

    /// @notice An array of all Safes created by the Master.
    /// @dev The first Safe is purposely invalid to prevent any Safes from having an id of 0.
    TurboSafe[] public safes;

    /// @notice Returns all Safes created by the Master.
    /// @return An array of all Safes created by the Master.
    /// @dev This is provided because Solidity converts public arrays into index getters,
    /// but we need a way to allow external contracts and users to access the whole array.
    function getAllSafes() external view returns (TurboSafe[] memory) {
        return safes;
    }

    /*///////////////////////////////////////////////////////////////
                          SAFE CREATION LOGIC
    //////////////////////////////////////////////////////////////*/

    /// @notice Emitted when a new Safe is created.
    /// @param user The user who created the Safe.
    /// @param asset The asset of the Safe.
    /// @param safe The newly deployed Safe contract.
    /// @param id The index of the Safe in the safes array.
    event TurboSafeCreated(address indexed user, ERC20 indexed asset, TurboSafe safe, uint256 id);

    /// @notice Creates a new Turbo Safe which supports a specific asset.
    /// @param asset The ERC20 token that the Safe should accept.
    /// @return safe The newly deployed Turbo Safe which accepts the provided asset.
    function createSafe(ERC20 asset) external requiresAuth returns (TurboSafe safe, uint256 id) {
        // Create a new Safe using the default authority and provided asset.
        safe = new TurboSafe(msg.sender, defaultSafeAuthority, asset);

        // Add the safe to the list of Safes.
        safes.push(safe);

        unchecked {
            // Get the index/id of the new Safe.
            // Cannot underflow, we just pushed to it.
            id = safes.length - 1;
        }

        // Store the id/index of the new Safe.
        getSafeId[safe] = id;

        emit TurboSafeCreated(msg.sender, asset, safe, id);

        // Prepare a users array to whitelist the Safe.
        address[] memory users = new address[](1);
        users[0] = address(safe);

        // Prepare an enabled array to whitelist the Safe.
        bool[] memory enabled = new bool[](1);
        enabled[0] = true;

        // Whitelist the Safe to access the Turbo Fuse Pool.
        FuseAdmin(pool.admin())._setWhitelistStatuses(users, enabled);
    }

    /*///////////////////////////////////////////////////////////////
                          SAFE CALLBACK LOGIC
    //////////////////////////////////////////////////////////////*/

    /// @notice Callback triggered whenever a Safe boosts a Vault.
    /// @param asset The asset of the Safe.
    /// @param vault The Vault that was boosted.
    /// @param feiAmount The amount of Fei used to boost the Vault.
    function onSafeBoost(
        ERC20 asset,
        ERC4626 vault,
        uint256 feiAmount
    ) external {
        // Get the caller as a Safe instance.
        TurboSafe safe = TurboSafe(msg.sender);

        // Ensure the Safe was created by this Master.
        require(getSafeId[safe] != 0, "INVALID_SAFE");

        // Update the total amount of Fei being using to boost Vaults.
        totalBoosted += feiAmount;

        // Cache the new total boosted for the Vault.
        uint256 newTotalBoostedForVault;

        // Cache the new total boosted against the Vault's collateral.
        uint256 newTotalBoostedAgainstCollateral;

        unchecked {
            // Update the total amount of Fei being using to boost the Vault.
            // Cannot overflow because a Safe's total will never be greater than global total.
            getTotalBoostedForVault[vault] = (newTotalBoostedForVault = getTotalBoostedForVault[vault] + feiAmount);

            // Update the total amount of Fei boosted against the collateral type.
            // Cannot overflow because a collateral type's total will never be greater than global total.
            getTotalBoostedAgainstCollateral[asset] = (newTotalBoostedAgainstCollateral =
                getTotalBoostedAgainstCollateral[asset] +
                feiAmount);
        }

        // Check with the booster that the Safe is allowed to boost the Vault using this amount of Fei.
        require(
            booster.canSafeBoostVault(
                safe,
                asset,
                vault,
                feiAmount,
                newTotalBoostedForVault,
                newTotalBoostedAgainstCollateral
            ),
            "BOOSTER_REJECTED"
        );
    }

    /// @notice Callback triggered whenever a Safe withdraws from a Vault.
    /// @param asset The asset of the Safe.
    /// @param vault The Vault that was withdrawn from.
    /// @param feiAmount The amount of Fei withdrawn from the Vault.
    function onSafeLess(
        ERC20 asset,
        ERC4626 vault,
        uint256 feiAmount
    ) external {
        // Get the caller as a Safe instance.
        TurboSafe safe = TurboSafe(msg.sender);

        // Ensure the Safe was created by this Master.
        require(getSafeId[safe] != 0, "INVALID_SAFE");

        unchecked {
            // Update the total amount of Fei being using to boost the Vault.
            // Cannot underflow as the Safe validated the withdrawal amount before.
            getTotalBoostedForVault[vault] -= feiAmount;

            // Update the total amount of Fei being using to boost Vaults.
            // Cannot underflow as the Safe validated the withdrawal amount earlier.
            totalBoosted -= feiAmount;

            // Update the total amount of Fei boosted against the collateral type.
            // Cannot underflow as the Safe validated the withdrawal amount previously.
            getTotalBoostedAgainstCollateral[asset] -= feiAmount;
        }
    }

    /// @notice Callback triggered whenever a Safe harvests from a Vault.
    /// @param asset The asset of the Safe.
    /// @param vault The Vault that was harvested from.
    /// @param feiAmount The amount of Fei accrued as interest to the Safe.
    function onSafeSlurp(
        ERC20 asset,
        ERC4626 vault,
        uint256 feiAmount
    ) external {
        // Get the caller as a Safe instance.
        TurboSafe safe = TurboSafe(msg.sender);

        // Ensure the Safe was created by this Master.
        require(getSafeId[safe] != 0, "INVALID_SAFE");

        // Update the total amount of Fei being using to boost Vaults.
        totalBoosted += feiAmount;

        unchecked {
            // Update the total amount of Fei being using to boost the Vault.
            // Cannot overflow because a Safe's total will never be greater than global total.
            getTotalBoostedForVault[vault] += feiAmount;

            // Update the total amount of Fei boosted against the collateral type.
            // Cannot overflow because a collateral type's total will never be greater than global total.
            getTotalBoostedAgainstCollateral[asset] += feiAmount;
        }
    }

    /*///////////////////////////////////////////////////////////////
                              SWEEP LOGIC
    //////////////////////////////////////////////////////////////*/

    /// @notice Emitted a token is sweeped from the Master.
    /// @param user The user who sweeped the token from the Master.
    /// @param to The recipient of the sweeped tokens.
    /// @param amount The amount of the token that was sweeped.
    event TokenSweeped(address indexed user, address indexed to, ERC20 indexed token, uint256 amount);

    /// @notice Claim tokens sitting idly in the Master.
    /// @param to The recipient of the sweeped tokens.
    /// @param token The token to sweep and send.
    /// @param amount The amount of the token to sweep.
    function sweep(
        address to,
        ERC20 token,
        uint256 amount
    ) external requiresAuth {
        emit TokenSweeped(msg.sender, to, token, amount);

        // Transfer the sweeped tokens to the recipient.
        token.safeTransfer(to, amount);
    }
}

contract TurboSafe is Auth, ERC4626, ReentrancyGuard {
    using SafeTransferLib for ERC20;
    using FixedPointMathLib for uint256;

    /*///////////////////////////////////////////////////////////////
                               IMMUTABLES
    //////////////////////////////////////////////////////////////*/

    /// @notice The Master contract that created the Safe.
    /// @dev Fees are paid directly to the Master, where they can be swept.
    TurboMaster public immutable master;

    /// @notice The Fei token on the network.
    ERC20 public immutable fei;

    /// @notice The Turbo Fuse Pool contract that collateral is held in and Fei is borrowed from.
    Comptroller public immutable pool;

    /// @notice The Fei cToken in the Turbo Fuse Pool that Fei is borrowed from.
    CERC20 public immutable feiTurboCToken;

    /// @notice The cToken that accepts the asset in the Turbo Fuse Pool.
    CERC20 public immutable assetTurboCToken;

    /*///////////////////////////////////////////////////////////////
                              CONSTRUCTOR
    //////////////////////////////////////////////////////////////*/

    /// @notice Creates a new Safe that accepts a specific asset.
    /// @param _owner The owner of the Safe.
    /// @param _authority The Authority of the Safe.
    /// @param _asset The ERC20 compliant token the Safe should accept.
    constructor(
        address _owner,
        Authority _authority,
        ERC20 _asset
    )
        Auth(_owner, _authority)
        ERC4626(
            _asset,
            // ex: Dai Stablecoin Turbo Safe
            string(abi.encodePacked(_asset.name(), " Turbo Safe")),
            // ex: tsDAI
            string(abi.encodePacked("ts", _asset.symbol()))
        )
    {
        master = TurboMaster(msg.sender);

        fei = master.fei();

        // An asset of Fei makes no sense.
        require(asset != fei, "INVALID_ASSET");

        pool = master.pool();

        feiTurboCToken = pool.cTokensByUnderlying(fei);

        assetTurboCToken = pool.cTokensByUnderlying(asset);

        // If the provided asset is not supported by the Turbo Fuse Pool, revert.
        require(address(assetTurboCToken) != address(0), "UNSUPPORTED_ASSET");

        // Construct an array of market(s) to enable as collateral.
        CERC20[] memory marketsToEnter = new CERC20[](1);
        marketsToEnter[0] = assetTurboCToken;

        // Enter the market(s) and ensure to properly revert if there is an error.
        require(pool.enterMarkets(marketsToEnter)[0] == 0, "ENTER_MARKETS_FAILED");

        // Preemptively approve the asset to the Turbo Fuse Pool's corresponding cToken.
        asset.safeApprove(address(assetTurboCToken), type(uint256).max);

        // Preemptively approve Fei to the Turbo Fuse Pool's Fei cToken.
        fei.safeApprove(address(feiTurboCToken), type(uint256).max);
    }

    /*///////////////////////////////////////////////////////////////
                               SAFE STORAGE
    //////////////////////////////////////////////////////////////*/

    /// @notice The current total amount of Fei the Safe is using to boost Vaults.
    uint256 public totalFeiBoosted;

    /// @notice Maps Vaults to the total amount of Fei they've being boosted with.
    /// @dev Used to determine the fees to be paid back to the Master.
    mapping(ERC4626 => uint256) public getTotalFeiBoostedForVault;

    /*///////////////////////////////////////////////////////////////
                               MODIFIERS
    //////////////////////////////////////////////////////////////*/

    /// @dev Checks the caller is authorized using either the Master's Authority or the Safe's local Authority.
    modifier requiresLocalOrMasterAuth() {
        // Check if the caller is the owner first:
        if (msg.sender != owner) {
            Authority masterAuth = master.authority(); // Saves a warm SLOAD, about 100 gas.

            // If the Master's Authority does not exist or does not accept upfront:
            if (address(masterAuth) == address(0) || !masterAuth.canCall(msg.sender, address(this), msg.sig)) {
                Authority auth = authority; // Memoizing saves us a warm SLOAD, around 100 gas.

                // The only authorization option left is via the local Authority, otherwise revert.
                require(
                    address(auth) != address(0) && auth.canCall(msg.sender, address(this), msg.sig),
                    "UNAUTHORIZED"
                );
            }
        }

        _;
    }

    /*///////////////////////////////////////////////////////////////
                             ERC4626 LOGIC
    //////////////////////////////////////////////////////////////*/

    /// @notice Called after any type of deposit occurs.
    /// @param assetAmount The amount of assets being deposited.
    /// @dev Using requiresAuth here prevents unauthorized users from depositing.
    function afterDeposit(uint256 assetAmount, uint256) internal override nonReentrant requiresAuth {
        // Collateralize the assets in the Turbo Fuse Pool.
        require(assetTurboCToken.mint(assetAmount) == 0, "MINT_FAILED");
    }

    /// @notice Called before any type of withdrawal occurs.
    /// @param assetAmount The amount of assets being withdrawn.
    /// @dev Using requiresAuth here prevents unauthorized users from withdrawing.
    function beforeWithdraw(uint256 assetAmount, uint256) internal override nonReentrant requiresAuth {
        // Withdraw the assets from the Turbo Fuse Pool.
        require(assetTurboCToken.redeemUnderlying(assetAmount) == 0, "REDEEM_FAILED");
    }

    /// @notice Returns the total amount of assets held in the Safe.
    /// @return The total amount of assets held in the Safe.
    function totalAssets() public view override returns (uint256) {
        return assetTurboCToken.balanceOf(address(this)).mulWadDown(assetTurboCToken.exchangeRateStored());
    }

    /*///////////////////////////////////////////////////////////////
                           BOOST/LESS LOGIC
    //////////////////////////////////////////////////////////////*/

    /// @notice Emitted when a Vault is boosted by the Safe.
    /// @param user The user who boosted the Vault.
    /// @param vault The Vault that was boosted.
    /// @param feiAmount The amount of Fei that was boosted to the Vault.
    event VaultBoosted(address indexed user, ERC4626 indexed vault, uint256 feiAmount);

    /// @notice Borrow Fei from the Turbo Fuse Pool and deposit it into an authorized Vault.
    /// @param vault The Vault to deposit the borrowed Fei into.
    /// @param feiAmount The amount of Fei to borrow and supply into the Vault.
    /// @dev Automatically accrues any fees earned by the Safe in the Vault to the Master.
    function boost(ERC4626 vault, uint256 feiAmount) external nonReentrant requiresAuth {
        // Ensure the Vault accepts Fei asset.
        require(vault.asset() == fei, "NOT_FEI");

        // Call the Master where it will do extra validation
        // and update it's total count of funds used for boosting.
        master.onSafeBoost(asset, vault, feiAmount);

        // Increase the boost total proportionately.
        totalFeiBoosted += feiAmount;

        unchecked {
            // Update the total Fei deposited into the Vault proportionately.
            // Cannot overflow because the total cannot be less than a single Vault.
            getTotalFeiBoostedForVault[vault] += feiAmount;
        }

        emit VaultBoosted(msg.sender, vault, feiAmount);

        // Borrow the Fei amount from the Fei cToken in the Turbo Fuse Pool.
        require(feiTurboCToken.borrow(feiAmount) == 0, "BORROW_FAILED");

        // Approve the borrowed Fei to the specified Vault.
        fei.safeApprove(address(vault), feiAmount);

        // Deposit the Fei into the specified Vault.
        vault.deposit(feiAmount, address(this));
    }

    /// @notice Emitted when a Vault is withdrawn from by the Safe.
    /// @param user The user who lessed the Vault.
    /// @param vault The Vault that was withdrawn from.
    /// @param feiAmount The amount of Fei that was withdrawn from the Vault.
    event VaultLessened(address indexed user, ERC4626 indexed vault, uint256 feiAmount);

    /// @notice Withdraw Fei from a deposited Vault and use it to repay debt in the Turbo Fuse Pool.
    /// @param vault The Vault to withdraw the Fei from.
    /// @param feiAmount The amount of Fei to withdraw from the Vault and repay in the Turbo Fuse Pool.
    /// @dev Automatically accrues any fees earned by the Safe in the Vault to the Master.
    function less(ERC4626 vault, uint256 feiAmount) external nonReentrant requiresLocalOrMasterAuth {
        // Update the total Fei deposited into the Vault proportionately.
        getTotalFeiBoostedForVault[vault] -= feiAmount;

        unchecked {
            // Decrease the boost total proportionately.
            // Cannot underflow because the total cannot be less than a single Vault.
            totalFeiBoosted -= feiAmount;
        }

        emit VaultLessened(msg.sender, vault, feiAmount);

        // Withdraw the specified amount of Fei from the Vault.
        vault.withdraw(feiAmount, address(this), address(this));

        // Get out current amount of Fei debt in the Turbo Fuse Pool.
        uint256 feiDebt = feiTurboCToken.borrowBalanceCurrent(address(this));

        // If our debt balance decreased, repay the minimum.
        // The surplus Fei will accrue as fees and can be sweeped.
        if (feiAmount > feiDebt) feiAmount = feiDebt;

        // Repay Fei debt in the Turbo Fuse Pool, unless we would repay nothing.
        if (feiAmount != 0) require(feiTurboCToken.repayBorrow(feiAmount) == 0, "REPAY_FAILED");

        // Call the Master to allow it to update its accounting.
        master.onSafeLess(asset, vault, feiAmount);
    }

    /*///////////////////////////////////////////////////////////////
                              SLURP LOGIC
    //////////////////////////////////////////////////////////////*/

    /// @notice Emitted when a Vault is slurped from by the Safe.
    /// @param user The user who slurped the Vault.
    /// @param vault The Vault that was slurped.
    /// @param protocolFeeAmount The amount of Fei accrued as fees to the Master.
    /// @param safeInterestAmount The amount of Fei accrued as interest to the Safe.
    event VaultSlurped(
        address indexed user,
        ERC4626 indexed vault,
        uint256 protocolFeeAmount,
        uint256 safeInterestAmount
    );

    /// @notice Accrue any interest earned by the Safe in the Vault.
    /// @param vault The Vault to accrue interest from, if any.
    /// @dev Sends a portion of the interest to the Master, as determined by the Clerk.
    function slurp(ERC4626 vault) external nonReentrant requiresLocalOrMasterAuth {
        // Ensure the Safe has Fei currently boosting the Vault.
        require(getTotalFeiBoostedForVault[vault] != 0, "NO_FEI_BOOSTED");

        // Compute the amount of Fei interest the Safe generated by boosting the Vault.
        uint256 interestEarned = vault.assetsOf(address(this)) - getTotalFeiBoostedForVault[vault];

        // Compute what percentage of the interest earned will go back to the Safe.
        uint256 protocolFeePercent = master.clerk().getFeePercentageForSafe(this, asset);

        // Compute the amount of Fei the protocol will retain as fees.
        uint256 protocolFeeAmount = interestEarned.mulWadDown(protocolFeePercent);

        // Compute the amount of Fei the Safe will retain as interest.
        uint256 safeInterestAmount = interestEarned - protocolFeeAmount;

        // Increase the boost total proportionately.
        totalFeiBoosted += safeInterestAmount;

        unchecked {
            // Update the total Fei held in the Vault proportionately.
            // Cannot overflow because the total cannot be less than a single Vault.
            getTotalFeiBoostedForVault[vault] += safeInterestAmount;
        }

        emit VaultSlurped(msg.sender, vault, protocolFeeAmount, safeInterestAmount);

        // If we have unaccrued fees, withdraw them from the Vault and transfer them to the Master.
        if (protocolFeeAmount != 0) vault.withdraw(protocolFeeAmount, address(master), address(this));

        // Call the Master to allow it to update its accounting.
        master.onSafeSlurp(asset, vault, safeInterestAmount);
    }

    /*///////////////////////////////////////////////////////////////
                              SWEEP LOGIC
    //////////////////////////////////////////////////////////////*/

    /// @notice Emitted a token is sweeped from the Safe.
    /// @param user The user who sweeped the token from the Safe.
    /// @param to The recipient of the sweeped tokens.
    /// @param amount The amount of the token that was sweeped.
    event TokenSweeped(address indexed user, address indexed to, ERC20 indexed token, uint256 amount);

    /// @notice Claim tokens sitting idly in the Safe.
    /// @param to The recipient of the sweeped tokens.
    /// @param token The token to sweep and send.
    /// @param amount The amount of the token to sweep.
    function sweep(
        address to,
        ERC20 token,
        uint256 amount
    ) external nonReentrant requiresAuth {
        // Ensure the caller is not trying to steal Vault shares or collateral cTokens.
        require(getTotalFeiBoostedForVault[ERC4626(address(token))] == 0 && token != assetTurboCToken, "INVALID_TOKEN");

        emit TokenSweeped(msg.sender, to, token, amount);

        // Transfer the sweeped tokens to the recipient.
        token.safeTransfer(to, amount);
    }

    /*///////////////////////////////////////////////////////////////
                               GIB LOGIC
    //////////////////////////////////////////////////////////////*/

    /// @notice Emitted when a Safe is gibbed.
    /// @param user The user who gibbed the Safe.
    /// @param to The recipient of the impounded collateral.
    /// @param assetAmount The amount of underling tokens impounded.
    event SafeGibbed(address indexed user, address indexed to, uint256 assetAmount);

    /// @notice Impound a specific amount of a Safe's collateral.
    /// @param to The address to send the impounded collateral to.
    /// @param assetAmount The amount of the asset to impound.
    /// @dev Can only be called by the Gibber, not by the Safe owner.
    /// @dev Debt must be repaid in advance, or the redemption will fail.
    function gib(address to, uint256 assetAmount) external nonReentrant requiresLocalOrMasterAuth {
        emit SafeGibbed(msg.sender, to, assetAmount);

        // Withdraw the specified amount of assets from the Turbo Fuse Pool.
        require(assetTurboCToken.redeemUnderlying(assetAmount) == 0, "REDEEM_FAILED");

        // Transfer the assets to the authorized caller.
        asset.safeTransfer(to, assetAmount);
    }
}

abstract contract ERC4626RouterBase is IERC4626RouterBase, SelfPermit, Multicall, PeripheryPayments {
    using SafeTransferLib for ERC20;

    /// @inheritdoc IERC4626RouterBase
    function mint(
        IERC4626 vault, 
        address to,
        uint256 shares,
        uint256 maxAmountIn
    ) public payable virtual override returns (uint256 amountIn) {
        if ((amountIn = vault.mint(shares, to)) > maxAmountIn) {
            revert MinAmountError();
        }
    }

    /// @inheritdoc IERC4626RouterBase
    function deposit(
        IERC4626 vault, 
        address to,
        uint256 amount,
        uint256 minSharesOut
    ) public payable virtual override returns (uint256 sharesOut) {
        if ((sharesOut = vault.deposit(amount, to)) < minSharesOut) {
            revert MinAmountError();
        }
    }

    /// @inheritdoc IERC4626RouterBase
    function withdraw(
        IERC4626 vault,
        address to,
        uint256 amount,
        uint256 minSharesOut
    ) public payable virtual override returns (uint256 sharesOut) {
        if ((sharesOut = vault.withdraw(amount, to, msg.sender)) < minSharesOut) {
            revert MinAmountError();
        }
    }

    /// @inheritdoc IERC4626RouterBase
    function redeem(
        IERC4626 vault,
        address to,
        uint256 shares,
        uint256 minAmountOut
    ) public payable virtual override returns (uint256 amountOut) {
        if ((amountOut = vault.redeem(shares, to, msg.sender)) < minAmountOut) {
            revert MinAmountError();
        }
    }
}
contract TurboRouter is ERC4626RouterBase, ENSReverseRecord {
    using SafeTransferLib for ERC20;

    TurboMaster public immutable master;

    constructor (TurboMaster _master, string memory name, IWETH9 weth) ENSReverseRecord(name) PeripheryPayments(weth) {
        master = _master;
    }

    modifier authenticate(address target) {
        require(msg.sender == Auth(target).owner(), "NOT_AUTHED");

        _;
    }

    function createSafe(ERC20 underlying) external {
        (TurboSafe safe, ) = master.createSafe(underlying);

        safe.setOwner(msg.sender);
    }

    function createSafeAndDeposit(ERC20 underlying, address to, uint256 amount, uint256 minSharesOut) external {
        (TurboSafe safe, ) = master.createSafe(underlying);

        super.deposit(IERC4626(address(safe)), to, amount, minSharesOut);

        safe.setOwner(msg.sender);
    }

    function createSafeAndDepositAndBoost(
        ERC20 underlying, 
        address to, 
        uint256 amount, 
        uint256 minSharesOut, 
        ERC4626 boostedVault, 
        uint256 boostedFeiAmount
    ) public {
        (TurboSafe safe, ) = master.createSafe(underlying);

        super.deposit(IERC4626(address(safe)), to, amount, minSharesOut);

        safe.boost(boostedVault, boostedFeiAmount);

        safe.setOwner(msg.sender);
    }

    function deposit(IERC4626 safe, address to, uint256 amount, uint256 minSharesOut) 
        public 
        payable 
        override 
        authenticate(address(safe)) 
        returns (uint256) 
    {
        return super.deposit(safe, to, amount, minSharesOut);
    }

    function mint(IERC4626 safe, address to, uint256 shares, uint256 maxAmountIn) 
        public 
        payable 
        override 
        authenticate(address(safe)) 
        returns (uint256) 
    {
        return super.mint(safe, to, shares, maxAmountIn);
    }

    function withdraw(IERC4626 safe, address to, uint256 amount, uint256 minSharesOut) 
        public 
        payable 
        override 
        authenticate(address(safe)) 
        returns (uint256) 
    {
        return super.withdraw(safe, to, amount, minSharesOut);
    }

    function redeem(IERC4626 safe, address to, uint256 shares, uint256 minAmountOut) 
        public 
        payable 
        override 
        authenticate(address(safe)) 
        returns (uint256) 
    {
        return super.redeem(safe, to, shares, minAmountOut);
    }

    function slurp(TurboSafe safe, ERC4626 vault) external authenticate(address(safe)) {
        safe.slurp(vault);
    }

    function boost(TurboSafe safe, ERC4626 vault, uint256 feiAmount) public authenticate(address(safe)) {
        safe.boost(vault, feiAmount);
    }

    function less(TurboSafe safe, ERC4626 vault, uint256 feiAmount) external authenticate(address(safe)) {
        safe.less(vault, feiAmount);
    }

    function sweep(TurboSafe safe, address to, ERC20 token, uint256 amount) external authenticate(address(safe)) {
        safe.sweep(to, token, amount);
    }

    function slurpAndLess(TurboSafe safe, ERC4626 vault, uint256 feiAmount) external authenticate(address(safe)) {
        safe.slurp(vault);
        safe.less(vault, feiAmount);
    }
}