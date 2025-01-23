// SPDX-License-Identifier: MIT
pragma solidity 0.8.4;

abstract contract UniPairLike {
    function factory() public view virtual returns (address);

    function getReserves()
        public
        view
        virtual
        returns (
            uint112 _reserve0,
            uint112 _reserve1,
            uint32 _blockTimestampLast
        );

    function mint(address to) external virtual returns (uint256 liquidity);

    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external virtual;

    function totalSupply() external virtual returns (uint256);
}

abstract contract PyroTokenLike {
  function mint(address to, uint256 baseTokenAmount) external payable virtual returns (uint256);

  function redeemRate() public view virtual returns (uint256);
}



abstract contract AngbandLike {
      function executePower(address powerInvoker)   public virtual;
}
interface IERC20 {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external view returns (string memory);
    function symbol() external view returns (string memory);
    function decimals() external view returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);
}


abstract contract BehodlerLike {
    function withdrawLiquidityFindSCX(
        address outputToken,
        uint256 tokensToRelease,
        uint256 scx,
        uint256 passes
    ) external view virtual returns (uint256);

    function burn(uint256 value) public virtual returns (bool);

    function config()
        public
        virtual
        view
        returns (
            uint256,
            uint256,
            address
        );

    function transfer(address dest, uint256 amount)
        external
        virtual
        returns (bool);

    function totalSupply () external virtual returns (uint);
}

abstract contract MigratorLike {
    function execute(
        address token,
        bool burnable,
        uint256 flanQuoteDivergenceTolerance,
        uint256 minQuoteWaitDuration
    ) public virtual;
}
abstract contract LimboDAOLike {
    function approveFlanMintingPower(address minter, bool enabled)
        public
        virtual;

    function makeProposal(address proposal, address proposer) public virtual;

    function currentProposalState() public view virtual returns (uint,uint,address,uint,address);

    function setProposalConfig(
        uint256 votingDuration,
        uint256 requiredFateStake,
        address proposalFactory
    ) public virtual;

    function setApprovedAsset(address asset, bool approved) public virtual;

    function successfulProposal(address proposal)
        public
        view
        virtual
        returns (bool);

    function domainConfig()
        public
        virtual
        returns (
            address,
            address,
            address,
            address,
            bool,
            address,
            address
        );

    function getFlashGoverner() external view virtual returns (address);

    function proposalConfig() public virtual view returns (uint,uint,address);

  function setFateToFlan(uint256 rate) public virtual;
}

abstract contract FlashGovernanceArbiterLike {
    function assertGovernanceApproved(address sender, address target, bool emergency)
        public
        virtual;

    function enforceToleranceInt(int256 v1, int256 v2) public view virtual;

    function enforceTolerance(uint256 v1, uint256 v2) public view virtual;

    function burnFlashGovernanceAsset(
        address targetContract,
        address user,
        address asset,
        uint256 amount
    ) public virtual;

     function setEnforcement(bool enforce) public virtual;
}


abstract contract Burnable {
    function burn (uint amount) public virtual;
}

abstract contract LimboAddTokenToBehodlerPowerLike {
    function parameterize(address soul, bool burnable) public virtual;
}


abstract contract AMMHelper {
    function stabilizeFlan(uint256 rectangleOfFairness)
        public
        virtual
        returns (uint256 lpMinted);

    function generateFLNQuote() public virtual;

    function minAPY_to_FPS(uint256 minAPY, uint256 daiThreshold)
        public
        view
        virtual
        returns (uint256 fps);

    function buyFlanAndBurn(
        address inputToken,
        uint256 amount,
        address recipient
    ) public virtual;
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

interface IERC677Receiver {
  function onTokenTransfer(address _sender, uint _value, bytes memory  _data) external;
}
abstract contract LimboLike {
  function latestIndex(address) public view virtual returns (uint256);

  function souls(address, uint256)
    public
    view
    virtual
    returns (
      uint256, //lastRewardTimeStamp
      uint256, //accumulatedFlanPerShare
      uint256, //crossingThreshold
      uint256, //soulType
      uint256, //state
      uint256 //flanPerSecond
    );

  function tokenCrossingParameters(address, uint256)
    public
    view
    virtual
    returns (
      uint256,
      uint256,
      int256,
      uint256,
      bool
    );

  function userInfo(
    address,
    address,
    uint256
  )
    public
    view
    virtual
    returns (
      uint256,
      uint256,
      bool
    );

  function configureSoul(
    address token,
    uint256 crossingThreshold,
    uint256 soulType,
    uint256 state,
    uint256 index,
    uint256 fps
  ) public virtual;

  function withdrawERC20(address token, address destination) public virtual;

  function userTokenBalance(address token) public virtual returns (uint256);
}

abstract contract ProposalFactoryLike {
     function toggleWhitelistProposal(address proposal) public virtual;
     function soulUpdateProposal () public  virtual view returns (address); 
}
abstract contract SwapFactoryLike {
    mapping(address => mapping(address => address)) public getPair;
}

abstract contract MorgothTokenApproverLike{
    function approved(address token) public virtual view returns (bool);
}
pragma experimental ABIEncoderV2;

/// @title Multicall - Aggregate results from multiple read-only function calls
/// @author Michael Elliot <mike@makerdao.com>
/// @author Joshua Levine <joshua@makerdao.com>
/// @author Nick Johnson <arachnid@notdot.net>

contract Multicall {
    struct Call {
        address target;
        bytes callData;
    }
    function aggregate(Call[] memory calls) public returns (uint256 blockNumber, bytes[] memory returnData) {
        blockNumber = block.number;
        returnData = new bytes[](calls.length);
        for(uint256 i = 0; i < calls.length; i++) {
            (bool success, bytes memory ret) = calls[i].target.call(calls[i].callData);
            require(success);
            returnData[i] = ret;
        }
    }
    // Helper functions
    function getEthBalance(address addr) public view returns (uint256 balance) {
        balance = addr.balance;
    }
    function getBlockHash(uint256 blockNumber) public view returns (bytes32 blockHash) {
        blockHash = blockhash(blockNumber);
    }
    function getLastBlockHash() public view returns (bytes32 blockHash) {
        blockHash = blockhash(block.number - 1);
    }
    function getCurrentBlockTimestamp() public view returns (uint256 timestamp) {
        timestamp = block.timestamp;
    }
    function getCurrentBlockDifficulty() public view returns (uint256 difficulty) {
        difficulty = block.difficulty;
    }
    function getCurrentBlockGasLimit() public view returns (uint256 gaslimit) {
        gaslimit = block.gaslimit;
    }
    function getCurrentBlockCoinbase() public view returns (address coinbase) {
        coinbase = block.coinbase;
    }
}
contract UniswapFactory {
    
}
contract Ownable {
  address private _owner;

  event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

  constructor() {
    _owner = msg.sender;
    emit OwnershipTransferred(address(0), msg.sender);
  }

  function owner() public view returns (address) {
    return _owner;
  }

  /**
   * @dev Throws if called by any account other than the owner.
   */
  modifier onlyOwner() {
    require(_owner == msg.sender, "Ownable: caller is not the owner");
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
    emit OwnershipTransferred(_owner, address(0));
    _owner = address(0);
  }

  /**
   * @dev Transfers ownership of the contract to a new account (`newOwner`).
   * Can only be called by the current owner.
   */
  function transferOwnership(address newOwner) public virtual onlyOwner {
    require(newOwner != address(0), "Ownable: new owner is the zero address");
    emit OwnershipTransferred(_owner, newOwner);
    _owner = newOwner;
  }
}



abstract contract LachesisLike {
  function measure(
    address token,
    bool valid,
    bool burnable
  ) public virtual;

  function updateBehodler(address token) public virtual;

  function setBehodler(address b) public virtual;
}





contract LimboAddTokenToBehodlerTestNet {
    event PowerInvoked(address user, bytes32 minion, bytes32 domain);

  struct Parameters {
    address soul;
    bool burnable;
    address limbo;
  }

  struct Config{
    address behodler;
    address lachesis;
    address angband;
  }

  Parameters public params;
  Config config;

  constructor(address angband, address behodler,address lachesis, address limbo){
    params.limbo = limbo;
    config.angband = angband;
    config.lachesis = lachesis;
    config.behodler = behodler;
  }

  function parameterize(address soul, bool burnable) public {
    require(msg.sender == params.limbo, "MORGOTH: Only Limbo can migrate tokens from Limbo.");
    params.soul = soul;
    params.burnable = burnable;
  }

 function invoke(bytes32 minion, address sender) public {
    require(msg.sender == address(config.angband), "MORGOTH: angband only");
    require(orchestrate(), "MORGOTH: Power invocation");
    emit PowerInvoked(sender, minion, "domain");
  }

  function orchestrate() internal returns (bool) {
    require(params.soul != address(0), "MORGOTH: PowerInvoker not parameterized.");
    LachesisLike lachesis = LachesisLike(config.lachesis);
    lachesis.measure(params.soul, true, params.burnable);
    lachesis.updateBehodler(params.soul);
    uint256 balanceOfToken = IERC20(params.soul).balanceOf(address(this));
    require(balanceOfToken > 0, "MORGOTH: remember to seed contract");
    IERC20(params.soul).approve(config.behodler, type(uint256).max);
    // BehodlerLike(config.behodler).addLiquidity(params.soul, balanceOfToken);
    uint256 scxBal = IERC20(config.behodler).balanceOf(address(this));
    IERC20(config.behodler).transfer(params.limbo, scxBal);
    params.soul = address(0); // prevent non limbo from executing.
    return true;
  }
}

library SafeMath {
    function add(uint x, uint y) internal pure returns (uint z) {
        require((z = x + y) >= x, 'ds-math-add-overflow');
    }

    function sub(uint x, uint y) internal pure returns (uint z) {
        require((z = x - y) <= x, 'ds-math-sub-underflow');
    }

    function mul(uint x, uint y) internal pure returns (uint z) {
        require(y == 0 || (z = x * y) / y == x, 'ds-math-mul-overflow');
    }
}

interface IUniswapV2ERC20 {
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

interface IUniswapV2Callee {
    function uniswapV2Call(address sender, uint amount0, uint amount1, bytes calldata data) external;
}

library UQ112x112 {
    uint224 constant Q112 = 2**112;

    // encode a uint112 as a UQ112x112
    function encode(uint112 y) internal pure returns (uint224 z) {
        z = uint224(y) * Q112; // never overflows
    }

    // divide a UQ112x112 by a uint112, returning a UQ112x112
    function uqdiv(uint224 x, uint112 y) internal pure returns (uint224 z) {
        z = x / uint224(y);
    }
}

library Math {
    function min(uint x, uint y) internal pure returns (uint z) {
        z = x < y ? x : y;
    }

    // babylonian method (https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method)
    function sqrt(uint y) internal pure returns (uint z) {
        if (y > 3) {
            z = y;
            uint x = y / 2 + 1;
            while (x < z) {
                z = x;
                x = (y / x + x) / 2;
            }
        } else if (y != 0) {
            z = 1;
        }
    }
}

interface CommonIERC20 {
    function totalSupply() external view returns (uint256);

    function balanceOf(address account) external view returns (uint256);

    function decimals() external returns (uint8);

    function transfer(address recipient, uint256 amount)
        external
        returns (bool);

    function allowance(address owner, address spender)
        external
        view
        returns (uint256);

    function approve(address spender, uint256 amount) external returns (bool);

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}
enum FeeExemption{
    NO_EXEMPTIONS,
    
    SENDER_EXEMPT,
    SENDER_AND_RECEIVER_EXEMPT,
    REDEEM_EXEMPT_AND_SENDER_EXEMPT,
    
    REDEEM_EXEMPT_AND_SENDER_AND_RECEIVER_EXEMPT,

    RECEIVER_EXEMPT,
    REDEEM_EXEMPT_AND_RECEIVER_EXEMPT,
    REDEEM_EXEMPT_ONLY
}

abstract contract LiquidityReceiverLike {
    function setFeeExemptionStatusOnPyroForContract(
        address pyroToken,
        address target,
        FeeExemption exemption
    ) public virtual;

    function setPyroTokenLoanOfficer(address pyroToken, address loanOfficer)
        public
        virtual;

    function getPyroToken(address baseToken)
        public
        view
        virtual
        returns (address);

    function registerPyroToken(
        address baseToken,
        string memory name,
        string memory symbol
    ) public virtual;

    function drain(address baseToken) external virtual returns (uint);
}


/*Snuffs out fees for given address */
abstract contract SnufferCap {
    LiquidityReceiverLike public _liquidityReceiver;

    constructor(address liquidityReceiver) {
        _liquidityReceiver = LiquidityReceiverLike(liquidityReceiver);
    }

    function snuff (address pyroToken, address targetContract, FeeExemption exempt) public virtual returns (bool);

    //after perfroming business logic, call this function
    function _snuff(address pyroToken, address targetContract, FeeExemption exempt)
        internal
    {
        _liquidityReceiver.setFeeExemptionStatusOnPyroForContract(pyroToken,targetContract,exempt);
    }
}


abstract contract Context {
  function _msgSender() internal view virtual returns (address) {
    return msg.sender;
  }

  function _msgData() internal view virtual returns (bytes calldata) {
    return msg.data;
  }
}

abstract contract ERC20 is Context, IERC20 {
  mapping(address => uint256) internal _balances;

  mapping(address => mapping(address => uint256)) internal _allowances;

  uint256 internal _totalSupply;

  string internal _name;
  string internal _symbol;

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
   * @dev See {IERC20-allowance}.
   */
  function allowance(address owner, address spender) public view virtual override returns (uint256) {
    return _allowances[owner][spender];
  }

  /**
   * @dev See {IERC20-approve}.
   *
   * Requirements:
   *
   * - `spender` cannot be the zero address.
   */
  function approve(address spender, uint256 amount) public virtual override returns (bool) {
    _approve(_msgSender(), spender, amount);
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
    _approve(_msgSender(), spender, _allowances[_msgSender()][spender] + addedValue);
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
    uint256 currentAllowance = _allowances[_msgSender()][spender];
    require(currentAllowance >= subtractedValue, "ERC20: decreased allowance below zero");
    unchecked {
      _approve(_msgSender(), spender, currentAllowance - subtractedValue);
    }

    return true;
  }

  /**
   * @dev Moves `amount` of tokens from `sender` to `recipient`.
   *
   * This internal function is equivalent to {transfer}, and can be used to
   * e.g. implement automatic token fees, slashing mechanisms, etc.
   *
   * Emits a {Transfer} event.
   *
   * Requirements:
   *
   * - `sender` cannot be the zero address.
   * - `recipient` cannot be the zero address.
   * - `sender` must have a balance of at least `amount`.
   */
  function _transfer(
    address sender,
    address recipient,
    uint256 amount
  ) internal virtual;

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

    _totalSupply += amount;
    _balances[account] += amount;
    emit Transfer(address(0), account, uint128(amount));
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

    uint256 accountBalance = _balances[account];
    require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
    unchecked {
      _balances[account] = accountBalance - amount;
    }
    _totalSupply -= amount;

    emit Transfer(account, address(0), uint128(amount));
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
    uint256 currentAllowance = allowance(account, _msgSender());
    require(currentAllowance >= amount, "ERC20: burn amount exceeds allowance");
    unchecked {
      _approve(account, _msgSender(), currentAllowance - amount);
    }
    _burn(account, amount);
  }
}

// File @openzeppelin/contracts/token/ERC20/extensions/ERC20Burnable.sol@v4.3.2

// : MIT

// File contracts/BurnableToken.sol

//: Unlicense

interface LiquidiyReceiverLike {
  function drain(address baseToken) external returns (uint256);
}

abstract contract ReentrancyGuard {
  uint256 private constant _NOT_ENTERED = 1;
  uint256 private constant _ENTERED = 2;

  uint256 private _status;

  constructor() {
    _status = _NOT_ENTERED;
  }

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
}

contract PyroToken is ERC20, ReentrancyGuard {
  struct Configuration {
    address liquidityReceiver;
    IERC20 baseToken;
    address loanOfficer;
    bool pullPendingFeeRevenue;
  }
  struct DebtObligation {
    uint256 base;
    uint256 pyro;
    uint256 redeemRate;
  }
  Configuration public config;
  uint256 private constant ONE = 1 ether;
  /*
    Exemptions aren't a form of cronyism. Rather, it will be decided on fair, open cryptoeconomic rules to allow protocols that need to
    frequently work with pyroTokens to be able to do so without incurring untenable cost to themselves. Always bear in mind that the big
    AMMs including Behodler will burn PyroTokens with abandon and without exception.
    We don't need every single protocol to bear the cost of Pyro growth and would 
    prefer to hit the high volume bots where they benefit most.
    Regarding fair cryptoeconomic incentives, a contract that requires burning a certain level of EYE would be a good example though we may get more sophisticated than that. 
    As a pertinent example, since Behodler burns as a primitive, 
    if we list a pyroToken for trade as burnable, then the total fee will be the Behodler burn fee plus the incoming transfer burn as well as the outgoing transfer burn when it is bought.
    This might be a little too much burning. In this case, we can turn of the transfer burns and still get the pyroToken burning on sale.  
    */
  mapping(address => FeeExemption) feeExemptionStatus;

  //By separating logic (loan officer) from state(debtObligations), we can upgrade the loan system without requiring existing borrowers migrate.
  //Seamless upgrade. This allows for better loan logic to replace the initial version.
  //By mapping debt on an individual pyroToken basis, it means each pyroToken can have it's own loan system. Potentially creating
  //a flourising of competing ideas. Seasteading for debt.
  mapping(address => DebtObligation) debtObligations;

  constructor() {
    config.liquidityReceiver = _msgSender();
    config.pullPendingFeeRevenue = true;
  }

  modifier initialized() {
    require(address(config.baseToken) != address(0), "PyroToken: base token not set");
    _;
  }

  function initialize(
    address baseToken,
    string memory name_,
    string memory symbol_
  ) public onlyReceiver {
    config.baseToken = IERC20(baseToken);
    _name = name_;
    _symbol = symbol_;
  }

  modifier onlyReceiver() {
    require(_msgSender() == config.liquidityReceiver, "PyroToken: Only Liquidity Receiver.");
    _;
  }

  modifier updateReserve() {
    if (config.pullPendingFeeRevenue) {
      LiquidiyReceiverLike(config.liquidityReceiver).drain(address(config.baseToken));
    }
    _;
  }

  modifier onlyLoanOfficer() {
    require(_msgSender() == config.loanOfficer, "PyroToken: Only Loan Officer.");
    _;
  }

  function setLoanOfficer(address loanOfficer) external onlyReceiver {
    config.loanOfficer = loanOfficer;
  }

  function togglePullPendingFeeRevenue(bool pullPendingFeeRevenue) external onlyReceiver {
    config.pullPendingFeeRevenue = pullPendingFeeRevenue;
  }

  function setFeeExemptionStatusFor(address exempt, FeeExemption status) public onlyReceiver {
    feeExemptionStatus[exempt] = status;
  }

  function transferToNewLiquidityReceiver(address liquidityReceiver) external onlyReceiver {
    require(liquidityReceiver != address(0), "PyroToken: New Liquidity Receiver cannot be the zero address.");
    config.liquidityReceiver = liquidityReceiver;
  }

  function mint(address recipient, uint256 baseTokenAmount) external updateReserve initialized returns (uint256) {
    uint256 _redeemRate = redeemRate();
    uint initialBalance = config.baseToken.balanceOf(address(this));
    require(config.baseToken.transferFrom(_msgSender(), address(this), baseTokenAmount));

    //fee on transfer tokens
    uint256 trueTransfer = config.baseToken.balanceOf(address(this)) - initialBalance;
    uint256 pyro = ( ONE* trueTransfer) / _redeemRate;
    _mint(recipient, pyro);
    emit Transfer(address(0), recipient, uint128(pyro));
    return pyro;
  }

  function redeemFrom(
    address owner,
    address recipient,
    uint256 amount
  ) external returns (uint256) {
    uint256 currentAllowance = _allowances[owner][_msgSender()];
    _approve(owner, _msgSender(), currentAllowance - amount);
    return _redeem(owner, recipient, amount);
  }

  function redeem(address recipient, uint256 amount) external returns (uint256) {
    return _redeem(recipient, _msgSender(), amount);
  }

  function _redeem(
    address recipient,
    address owner,
    uint256 amount
  ) internal updateReserve returns (uint256) {
    uint256 _redeemRate = redeemRate();
    _balances[owner] -= amount;
    uint256 fee = calculateRedemptionFee(amount, owner);

    uint256 net = amount - fee;
    uint256 baseTokens = (net * ONE) / _redeemRate;
    _totalSupply -= amount;
    emit Transfer(owner, address(0), uint128(amount));
    require(config.baseToken.transfer(recipient, baseTokens), "PyroToken reserve transfer failed.");
    return baseTokens;
  }

  function redeemRate() public view returns (uint256) {
    uint256 balanceOfBase = config.baseToken.balanceOf(address(this));
    if (_totalSupply == 0 || balanceOfBase == 0) return ONE;

    return (balanceOfBase * ONE) / _totalSupply;
  }

  function transfer(address recipient, uint256 amount) public virtual override returns (bool) {
    _transfer(_msgSender(), recipient, amount);
    return true;
  }

  function transferFrom(
    address sender,
    address recipient,
    uint256 amount
  ) public virtual override returns (bool) {
    _transfer(sender, recipient, amount);

    uint256 currentAllowance = _allowances[sender][_msgSender()];
    require(currentAllowance >= amount, "ERC20: transfer amount exceeds allowance");
    unchecked {
      _approve(sender, _msgSender(), currentAllowance - amount);
    }

    return true;
  }

  function setObligationFor(
    address borrower,
    uint256 baseTokenBorrowed,
    uint256 pyroTokenStaked
  ) external onlyLoanOfficer nonReentrant returns (bool success) {
    DebtObligation memory currentDebt = debtObligations[borrower];
    uint256 rate = redeemRate();
    uint256 minPyroStake = (baseTokenBorrowed * ONE) / rate;
    require(pyroTokenStaked >= minPyroStake, "Pyro: Unsustainable loan.");

    debtObligations[borrower] = DebtObligation(baseTokenBorrowed, pyroTokenStaked, rate);

    int256 netStake = int256(pyroTokenStaked) - int256(currentDebt.pyro);
    uint256 stake;
    if (netStake > 0) {
      stake = uint256(netStake);

      uint256 currentAllowance = _allowances[borrower][_msgSender()];
      _approve(borrower, _msgSender(), currentAllowance - stake);

      _balances[borrower] -= stake;
      _balances[address(this)] += stake;
    } else if (netStake < 0) {
      stake = uint256(-netStake);
      _balances[borrower] += stake;
      _balances[address(this)] -= stake;
    }

    int256 netBorrowing = int256(baseTokenBorrowed) - int256(currentDebt.base);
    if (netBorrowing > 0) {
      config.baseToken.transfer(borrower, uint256(netBorrowing));
    } else if (netBorrowing < 0) {
      config.baseToken.transferFrom(borrower, address(this), uint256(-netBorrowing));
    }

    success = true;
  }

  function _transfer(
    address sender,
    address recipient,
    uint256 amount
  ) internal override {
    if (recipient == address(0)) {
      burn(amount);
      return;
    }
    uint256 senderBalance = _balances[sender];
    uint256 fee = calculateTransferFee(amount, sender, recipient);

    _totalSupply -= fee;

    uint256 netReceived = amount - fee;
    _balances[sender] = senderBalance - amount;
    _balances[recipient] += netReceived;

    emit Transfer(sender, recipient, uint128(amount)); //extra parameters don't throw off parsers when interpreted through JSON.
  }

  function calculateTransferFee(
    uint256 amount,
    address sender,
    address receiver
  ) public view returns (uint256) {
    uint256 senderStatus = uint256(feeExemptionStatus[sender]);
    uint256 receiverStatus = uint256(feeExemptionStatus[receiver]);
    if (
      (senderStatus >= 1 && senderStatus <= 4) || (receiverStatus == 2 || (receiverStatus >= 4 && receiverStatus <= 6))
    ) {
      return 0;
    }
    return amount / 1000;
  }

  function calculateRedemptionFee(uint256 amount, address redeemer) public view returns (uint256) {
    uint256 status = uint256(feeExemptionStatus[redeemer]);
    if ((status >= 3 && status <= 4) || status > 5) return 0;
    return (amount * 2) / 100;
  }
}



// File contracts/LiquidityReceiver.sol

// Se-Identifier: MIT

// import "hardhat/console.sol";

library Create2 {
  /**
   * @dev Deploys a contract using `CREATE2`. The address where the contract
   * will be deployed can be known in advance via {computeAddress}. Note that
   * a contract cannot be deployed twice using the same salt.
   */
  function deploy(bytes32 salt, bytes memory bytecode) internal returns (address) {
    address addr;
    // solhint-disable-next-line no-inline-assembly
    assembly {
      addr := create2(0, add(bytecode, 0x20), mload(bytecode), salt)
    }
    require(addr != address(0), "Create2: Failed on deploy");
    return addr;
  }

  /**
   * @dev Returns the address where a contract will be stored if deployed via {deploy}. Any change in the `bytecode`
   * or `salt` will result in a new destination address.
   */
  function computeAddress(bytes32 salt, bytes memory bytecode) internal view returns (address) {
    return computeAddress(salt, bytecode, address(this));
  }

  /**
   * @dev Returns the address where a contract will be stored if deployed via {deploy} from a contract located at
   * `deployer`. If `deployer` is this contract's address, returns the same value as {computeAddress}.
   */
  function computeAddress(
    bytes32 salt,
    bytes memory bytecodeHash,
    address deployer
  ) internal pure returns (address) {
    bytes32 bytecodeHashHash = keccak256(bytecodeHash);
    bytes32 _data = keccak256(abi.encodePacked(bytes1(0xff), deployer, salt, bytecodeHashHash));
    return address(bytes20(_data << 96));
  }
}

contract LiquidityReceiver is Ownable {
  struct Configuration {
    LachesisLike lachesis;
    SnufferCap snufferCap;
  }
  Configuration public config;
  bytes internal constant PYROTOKEN_BYTECODE = type(PyroToken).creationCode;
  modifier onlySnufferCap() {
    require(msg.sender == address(config.snufferCap), "LR: only snufferCap");
    _;
  }

  constructor(address _lachesis) {
    config.lachesis = LachesisLike(_lachesis);
  }

  function setSnufferCap(address snufferCap) public onlyOwner {
    config.snufferCap = SnufferCap(snufferCap);
  }

  function drain(address baseToken) external returns (uint256) {
    address pyroToken = getPyroToken(baseToken);
    IERC20 reserve = IERC20(baseToken);
    uint256 amount = reserve.balanceOf(address(this));
    reserve.transfer(pyroToken, amount);
    return amount;
  }

  function togglePyroTokenPullFeeRevenue(address pyroToken, bool pull) public onlyOwner {
    PyroToken(pyroToken).togglePullPendingFeeRevenue(pull);
  }

  function setPyroTokenLoanOfficer(address pyroToken, address loanOfficer) public onlyOwner {
    require(loanOfficer != address(0) && pyroToken != address(0), "LR: zero address detected");
    PyroToken(pyroToken).setLoanOfficer(loanOfficer);
  }

  function setLachesis(address _lachesis) public onlyOwner {
    config.lachesis = LachesisLike(_lachesis);
  }

  function setFeeExemptionStatusOnPyroForContract(
    address pyroToken,
    address target,
    FeeExemption exemption
  ) public onlySnufferCap {
    require(isContract(target), "LR: EOAs cannot be exempt.");
    PyroToken(pyroToken).setFeeExemptionStatusFor(target, exemption);
  }

  function registerPyroToken(
    address baseToken,
    string memory name,
    string memory symbol
  ) public onlyOwner {
    address expectedAddress = getPyroToken(baseToken);

    require(!isContract(expectedAddress), "PyroToken Address occupied");
    (bool valid, bool burnable) = (true,true);
    require(valid && !burnable, "PyroToken: invalid base token");
    address p = Create2.deploy(keccak256(abi.encode(baseToken)), PYROTOKEN_BYTECODE);
    PyroToken(p).initialize(baseToken, name, symbol);

    require(address(p) == expectedAddress, "PyroToken: address prediction failed");
  }

  function transferPyroTokenToNewReceiver(address pyroToken, address receiver) public onlyOwner {
    PyroToken(pyroToken).transferToNewLiquidityReceiver(receiver);
  }

  //by using salted deployments (CREATE2), we get a cheaper version of mapping by not having to hit an SLOAD op
  function getPyroToken(address baseToken) public view returns (address) {
    bytes32 salt = keccak256(abi.encode(baseToken));
    return Create2.computeAddress(salt, PYROTOKEN_BYTECODE);
  }

  function isContract(address addr) private view returns (bool) {
    uint256 size;
    assembly {
      size := extcodesize(addr)
    }
    return size > 0;
  }
}

interface IERC2612 {
  /**
   * @dev Sets `amount` as the allowance of `spender` over `owner`'s tokens,
   * given `owner`'s signed approval.
   *
   * IMPORTANT: The same issues {IERC20-approve} has related to transaction
   * ordering also apply here.
   *
   * Emits an {Approval} event.
   *
   * Requirements:
   *
   * - `owner` cannot be the zero address.
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
    uint256 amount,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s
  ) external;

  /**
   * @dev Returns the current ERC2612 nonce for `owner`. This value must be
   * included whenever a signature is generated for {permit}.
   *
   * Every successful call to {permit} increases ``owner``'s nonce by one. This
   * prevents a signature from being used multiple times.
   */
  function nonces(address owner) external view returns (uint256);
}

interface IERC3156FlashBorrower {
  /**
   * @dev Receive a flash loan.
   * @param initiator The initiator of the loan.
   * @param token The loan currency.
   * @param amount The amount of tokens lent.
   * @param fee The additional amount of tokens to repay.
   * @param data Arbitrary data structure, intended to contain user-defined parameters.
   * @return The keccak256 hash of "ERC3156FlashBorrower.onFlashLoan"
   */
  function onFlashLoan(
    address initiator,
    address token,
    uint256 amount,
    uint256 fee,
    bytes calldata data
  ) external returns (bytes32);
}

interface IERC3156FlashLender {
  /**
   * @dev The amount of currency available to be lended.
   * @param token The loan currency.
   * @return The amount of `token` that can be borrowed.
   */
  function maxFlashLoan(address token) external view returns (uint256);

  /**
   * @dev The fee to be charged for a given loan.
   * @param token The loan currency.
   * @param amount The amount of tokens lent.
   * @return The amount of `token` to be charged for the loan, on top of the returned principal.
   */
  function flashFee(address token, uint256 amount) external view returns (uint256);

  /**
   * @dev Initiate a flash loan.
   * @param receiver The receiver of the tokens in the loan, and the receiver of the callback.
   * @param token The loan currency.
   * @param amount The amount of tokens lent.
   * @param data Arbitrary data structure, intended to contain user-defined parameters.
   */
  function flashLoan(
    IERC3156FlashBorrower receiver,
    address token,
    uint256 amount,
    bytes calldata data
  ) external returns (bool);
}

/// @dev Wrapped Ether v10 (WETH10) is an Ether (ETH) ERC-20 wrapper. You can `deposit` ETH and obtain an WETH10 balance which can then be operated as an ERC-20 token. You can
/// `withdraw` ETH from WETH10, which will then burn WETH10 token in your wallet. The amount of WETH10 token in any wallet is always identical to the
/// balance of ETH deposited minus the ETH withdrawn with that specific wallet.
interface IWETH10 is IERC20, IERC2612, IERC3156FlashLender {
  /// @dev Returns current amount of flash-minted WETH10 token.
  function flashMinted() external view returns (uint256);

  /// @dev `msg.value` of ETH sent to this contract grants caller account a matching increase in WETH10 token balance.
  /// Emits {Transfer} event to reflect WETH10 token mint of `msg.value` from zero address to caller account.
  function deposit() external payable;

  /// @dev `msg.value` of ETH sent to this contract grants `to` account a matching increase in WETH10 token balance.
  /// Emits {Transfer} event to reflect WETH10 token mint of `msg.value` from zero address to `to` account.
  function depositTo(address to) external payable;

  /// @dev Burn `value` WETH10 token from caller account and withdraw matching ETH to the same.
  /// Emits {Transfer} event to reflect WETH10 token burn of `value` to zero address from caller account.
  /// Requirements:
  ///   - caller account must have at least `value` balance of WETH10 token.
  function withdraw(uint256 value) external;

  /// @dev Burn `value` WETH10 token from caller account and withdraw matching ETH to account (`to`).
  /// Emits {Transfer} event to reflect WETH10 token burn of `value` to zero address from caller account.
  /// Requirements:
  ///   - caller account must have at least `value` balance of WETH10 token.
  function withdrawTo(address payable to, uint256 value) external;

  /// @dev Burn `value` WETH10 token from account (`from`) and withdraw matching ETH to account (`to`).
  /// Emits {Approval} event to reflect reduced allowance `value` for caller account to spend from account (`from`),
  /// unless allowance is set to `type(uint256).max`
  /// Emits {Transfer} event to reflect WETH10 token burn of `value` to zero address from account (`from`).
  /// Requirements:
  ///   - `from` account must have at least `value` balance of WETH10 token.
  ///   - `from` account must have approved caller to spend at least `value` of WETH10 token, unless `from` and caller are the same account.
  function withdrawFrom(
    address from,
    address payable to,
    uint256 value
  ) external;

  /// @dev `msg.value` of ETH sent to this contract grants `to` account a matching increase in WETH10 token balance,
  /// after which a call is executed to an ERC677-compliant contract with the `data` parameter.
  /// Emits {Transfer} event.
  /// Returns boolean value indicating whether operation succeeded.
  /// For more information on *transferAndCall* format, see https://github.com/ethereum/EIPs/issues/677.
  function depositToAndCall(address to, bytes calldata data) external payable returns (bool);

  /// @dev Sets `value` as allowance of `spender` account over caller account's WETH10 token,
  /// after which a call is executed to an ERC677-compliant contract with the `data` parameter.
  /// Emits {Approval} event.
  /// Returns boolean value indicating whether operation succeeded.
  /// For more information on approveAndCall format, see https://github.com/ethereum/EIPs/issues/677.
  function approveAndCall(
    address spender,
    uint256 value,
    bytes calldata data
  ) external returns (bool);

  /// @dev Moves `value` WETH10 token from caller's account to account (`to`),
  /// after which a call is executed to an ERC677-compliant contract with the `data` parameter.
  /// A transfer to `address(0)` triggers an ETH withdraw matching the sent WETH10 token in favor of caller.
  /// Emits {Transfer} event.
  /// Returns boolean value indicating whether operation succeeded.
  /// Requirements:
  ///   - caller account must have at least `value` WETH10 token.
  /// For more information on transferAndCall format, see https://github.com/ethereum/EIPs/issues/677.
  function transferAndCall(
    address to,
    uint256 value,
    bytes calldata data
  ) external returns (bool);
}

interface ITransferReceiver {
  function onTokenTransfer(
    address,
    uint256,
    bytes calldata
  ) external returns (bool);
}

interface IApprovalReceiver {
  function onTokenApproval(
    address,
    uint256,
    bytes calldata
  ) external returns (bool);
}

/// @dev Wrapped Ether v10 (WETH10) is an Ether (ETH) ERC-20 wrapper. You can `deposit` ETH and obtain an WETH10 balance which can then be operated as an ERC-20 token. You can
/// `withdraw` ETH from WETH10, which will then burn WETH10 token in your wallet. The amount of WETH10 token in any wallet is always identical to the
/// balance of ETH deposited minus the ETH withdrawn with that specific wallet.
contract WETH10 is IWETH10 {
  string public constant override name = "WETH10";
  string public constant override symbol = "WETH10";
  uint8 public constant override decimals = 18;

  bytes32 public immutable CALLBACK_SUCCESS = keccak256("ERC3156FlashBorrower.onFlashLoan");
  bytes32 public immutable PERMIT_TYPEHASH =
    keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");

  /// @dev Records amount of WETH10 token owned by account.
  mapping(address => uint256) public override balanceOf;

  /// @dev Records current ERC2612 nonce for account. This value must be included whenever signature is generated for {permit}.
  /// Every successful call to {permit} increases account's nonce by one. This prevents signature from being used multiple times.
  mapping(address => uint256) public override nonces;

  /// @dev Records number of WETH10 token that account (second) will be allowed to spend on behalf of another account (first) through {transferFrom}.
  mapping(address => mapping(address => uint256)) public override allowance;

  /// @dev Current amount of flash-minted WETH10 token.
  uint256 public override flashMinted;

  /// @dev Returns the total supply of WETH10 token as the ETH held in this contract.
  function totalSupply() external view override returns (uint256) {
    return address(this).balance + flashMinted;
  }

  /// @dev Fallback, `msg.value` of ETH sent to this contract grants caller account a matching increase in WETH10 token balance.
  /// Emits {Transfer} event to reflect WETH10 token mint of `msg.value` from zero address to caller account.
  receive() external payable {
    // _mintTo(msg.sender, msg.value);
    balanceOf[msg.sender] += msg.value;
    emit Transfer(address(0), msg.sender, msg.value);
  }

  /// @dev `msg.value` of ETH sent to this contract grants caller account a matching increase in WETH10 token balance.
  /// Emits {Transfer} event to reflect WETH10 token mint of `msg.value` from zero address to caller account.
  function deposit() external payable override {
    // _mintTo(msg.sender, msg.value);
    balanceOf[msg.sender] += msg.value;
    emit Transfer(address(0), msg.sender, msg.value);
  }

  /// @dev `msg.value` of ETH sent to this contract grants `to` account a matching increase in WETH10 token balance.
  /// Emits {Transfer} event to reflect WETH10 token mint of `msg.value` from zero address to `to` account.
  function depositTo(address to) external payable override {
    // _mintTo(to, msg.value);
    balanceOf[to] += msg.value;
    emit Transfer(address(0), to, msg.value);
  }

  /// @dev `msg.value` of ETH sent to this contract grants `to` account a matching increase in WETH10 token balance,
  /// after which a call is executed to an ERC677-compliant contract with the `data` parameter.
  /// Emits {Transfer} event.
  /// Returns boolean value indicating whether operation succeeded.
  /// For more information on *transferAndCall* format, see https://github.com/ethereum/EIPs/issues/677.
  function depositToAndCall(address to, bytes calldata data) external payable override returns (bool success) {
    // _mintTo(to, msg.value);
    balanceOf[to] += msg.value;
    emit Transfer(address(0), to, msg.value);

    return ITransferReceiver(to).onTokenTransfer(msg.sender, msg.value, data);
  }

  /// @dev Return the amount of WETH10 token that can be flash-lent.
  function maxFlashLoan(address token) external view override returns (uint256) {
    return token == address(this) ? type(uint112).max - flashMinted : 0; // Can't underflow
  }

  /// @dev Return the fee (zero) for flash-lending an amount of WETH10 token.
  function flashFee(address token, uint256) external view override returns (uint256) {
    require(token == address(this), "WETH: flash mint only WETH10");
    return 0;
  }

  /// @dev Flash lends `value` WETH10 token to the receiver address.
  /// By the end of the transaction, `value` WETH10 token will be burned from the receiver.
  /// The flash-minted WETH10 token is not backed by real ETH, but can be withdrawn as such up to the ETH balance of this contract.
  /// Arbitrary data can be passed as a bytes calldata parameter.
  /// Emits {Approval} event to reflect reduced allowance `value` for this contract to spend from receiver account (`receiver`),
  /// unless allowance is set to `type(uint256).max`
  /// Emits two {Transfer} events for minting and burning of the flash-minted amount.
  /// Returns boolean value indicating whether operation succeeded.
  /// Requirements:
  ///   - `value` must be less or equal to type(uint112).max.
  ///   - The total of all flash loans in a tx must be less or equal to type(uint112).max.
  function flashLoan(
    IERC3156FlashBorrower receiver,
    address token,
    uint256 value,
    bytes calldata data
  ) external override returns (bool) {
    require(token == address(this), "WETH: flash mint only WETH10");
    require(value <= type(uint112).max, "WETH: individual loan limit exceeded");
    flashMinted = flashMinted + value;
    require(flashMinted <= type(uint112).max, "WETH: total loan limit exceeded");

    // _mintTo(address(receiver), value);
    balanceOf[address(receiver)] += value;
    emit Transfer(address(0), address(receiver), value);

    require(
      receiver.onFlashLoan(msg.sender, address(this), value, 0, data) == CALLBACK_SUCCESS,
      "WETH: flash loan failed"
    );

    // _decreaseAllowance(address(receiver), address(this), value);
    uint256 allowed = allowance[address(receiver)][address(this)];
    if (allowed != type(uint256).max) {
      require(allowed >= value, "WETH: request exceeds allowance");
      uint256 reduced = allowed - value;
      allowance[address(receiver)][address(this)] = reduced;
      emit Approval(address(receiver), address(this), reduced);
    }

    // _burnFrom(address(receiver), value);
    uint256 balance = balanceOf[address(receiver)];
    require(balance >= value, "WETH: burn amount exceeds balance");
    balanceOf[address(receiver)] = balance - value;
    emit Transfer(address(receiver), address(0), value);

    flashMinted = flashMinted - value;
    return true;
  }

  /// @dev Burn `value` WETH10 token from caller account and withdraw matching ETH to the same.
  /// Emits {Transfer} event to reflect WETH10 token burn of `value` to zero address from caller account.
  /// Requirements:
  ///   - caller account must have at least `value` balance of WETH10 token.
  function withdraw(uint256 value) external override {
    // _burnFrom(msg.sender, value);
    uint256 balance = balanceOf[msg.sender];
    require(balance >= value, "WETH: burn amount exceeds balance");
    balanceOf[msg.sender] = balance - value;
    emit Transfer(msg.sender, address(0), value);

    // _transferEther(msg.sender, value);
    (bool success, ) = msg.sender.call{value: value}("");
    require(success, "WETH: ETH transfer failed");
  }

  /// @dev Burn `value` WETH10 token from caller account and withdraw matching ETH to account (`to`).
  /// Emits {Transfer} event to reflect WETH10 token burn of `value` to zero address from caller account.
  /// Requirements:
  ///   - caller account must have at least `value` balance of WETH10 token.
  function withdrawTo(address payable to, uint256 value) external override {
    // _burnFrom(msg.sender, value);
    uint256 balance = balanceOf[msg.sender];
    require(balance >= value, "WETH: burn amount exceeds balance");
    balanceOf[msg.sender] = balance - value;
    emit Transfer(msg.sender, address(0), value);

    // _transferEther(to, value);
    (bool success, ) = to.call{value: value}("");
    require(success, "WETH: ETH transfer failed");
  }

  /// @dev Burn `value` WETH10 token from account (`from`) and withdraw matching ETH to account (`to`).
  /// Emits {Approval} event to reflect reduced allowance `value` for caller account to spend from account (`from`),
  /// unless allowance is set to `type(uint256).max`
  /// Emits {Transfer} event to reflect WETH10 token burn of `value` to zero address from account (`from`).
  /// Requirements:
  ///   - `from` account must have at least `value` balance of WETH10 token.
  ///   - `from` account must have approved caller to spend at least `value` of WETH10 token, unless `from` and caller are the same account.
  function withdrawFrom(
    address from,
    address payable to,
    uint256 value
  ) external override {
    if (from != msg.sender) {
      // _decreaseAllowance(from, msg.sender, value);
      uint256 allowed = allowance[from][msg.sender];
      if (allowed != type(uint256).max) {
        require(allowed >= value, "WETH: request exceeds allowance");
        uint256 reduced = allowed - value;
        allowance[from][msg.sender] = reduced;
        emit Approval(from, msg.sender, reduced);
      }
    }

    // _burnFrom(from, value);
    uint256 balance = balanceOf[from];
    require(balance >= value, "WETH: burn amount exceeds balance");
    balanceOf[from] = balance - value;
    emit Transfer(from, address(0), value);

    // _transferEther(to, value);
    (bool success, ) = to.call{value: value}("");
    require(success, "WETH: Ether transfer failed");
  }

  /// @dev Sets `value` as allowance of `spender` account over caller account's WETH10 token.
  /// Emits {Approval} event.
  /// Returns boolean value indicating whether operation succeeded.
  function approve(address spender, uint256 value) external override returns (bool) {
    // _approve(msg.sender, spender, value);
    allowance[msg.sender][spender] = value;
    emit Approval(msg.sender, spender, value);

    return true;
  }

  /// @dev Sets `value` as allowance of `spender` account over caller account's WETH10 token,
  /// after which a call is executed to an ERC677-compliant contract with the `data` parameter.
  /// Emits {Approval} event.
  /// Returns boolean value indicating whether operation succeeded.
  /// For more information on approveAndCall format, see https://github.com/ethereum/EIPs/issues/677.
  function approveAndCall(
    address spender,
    uint256 value,
    bytes calldata data
  ) external override returns (bool) {
    // _approve(msg.sender, spender, value);
    allowance[msg.sender][spender] = value;
    emit Approval(msg.sender, spender, value);

    return IApprovalReceiver(spender).onTokenApproval(msg.sender, value, data);
  }

  /// @dev Sets `value` as allowance of `spender` account over `owner` account's WETH10 token, given `owner` account's signed approval.
  /// Emits {Approval} event.
  /// Requirements:
  ///   - `deadline` must be timestamp in future.
  ///   - `v`, `r` and `s` must be valid `secp256k1` signature from `owner` account over EIP712-formatted function arguments.
  ///   - the signature must use `owner` account's current nonce (see {nonces}).
  ///   - the signer cannot be zero address and must be `owner` account.
  /// For more information on signature format, see https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP section].
  /// WETH10 token implementation adapted from https://github.com/albertocuestacanada/ERC20Permit/blob/master/contracts/ERC20Permit.sol.
  function permit(
    address owner,
    address spender,
    uint256 value,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s
  ) external override {
    require(block.timestamp <= deadline, "WETH: Expired permit");

    uint256 chainId;
    assembly {
      chainId := chainid()
    }
    bytes32 DOMAIN_SEPARATOR = keccak256(
      abi.encode(
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
        keccak256(bytes(name)),
        keccak256(bytes("1")),
        chainId,
        address(this)
      )
    );

    bytes32 hashStruct = keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonces[owner]++, deadline));

    bytes32 hash = keccak256(abi.encodePacked("\x19\x01", DOMAIN_SEPARATOR, hashStruct));

    address signer = ecrecover(hash, v, r, s);
    require(signer != address(0) && signer == owner, "WETH: invalid permit");

    // _approve(owner, spender, value);
    allowance[owner][spender] = value;
    emit Approval(owner, spender, value);
  }

  /// @dev Moves `value` WETH10 token from caller's account to account (`to`).
  /// A transfer to `address(0)` triggers an ETH withdraw matching the sent WETH10 token in favor of caller.
  /// Emits {Transfer} event.
  /// Returns boolean value indicating whether operation succeeded.
  /// Requirements:
  ///   - caller account must have at least `value` WETH10 token.
  function transfer(address to, uint256 value) external override returns (bool) {
    // _transferFrom(msg.sender, to, value);
    if (to != address(0)) {
      // Transfer
      uint256 balance = balanceOf[msg.sender];
      require(balance >= value, "WETH: transfer amount exceeds balance");

      balanceOf[msg.sender] = balance - value;
      balanceOf[to] += value;
      emit Transfer(msg.sender, to, value);
    } else {
      // Withdraw
      uint256 balance = balanceOf[msg.sender];
      require(balance >= value, "WETH: burn amount exceeds balance");
      balanceOf[msg.sender] = balance - value;
      emit Transfer(msg.sender, address(0), value);

      (bool success, ) = msg.sender.call{value: value}("");
      require(success, "WETH: ETH transfer failed");
    }

    return true;
  }

  /// @dev Moves `value` WETH10 token from account (`from`) to account (`to`) using allowance mechanism.
  /// `value` is then deducted from caller account's allowance, unless set to `type(uint256).max`.
  /// A transfer to `address(0)` triggers an ETH withdraw matching the sent WETH10 token in favor of caller.
  /// Emits {Approval} event to reflect reduced allowance `value` for caller account to spend from account (`from`),
  /// unless allowance is set to `type(uint256).max`
  /// Emits {Transfer} event.
  /// Returns boolean value indicating whether operation succeeded.
  /// Requirements:
  ///   - `from` account must have at least `value` balance of WETH10 token.
  ///   - `from` account must have approved caller to spend at least `value` of WETH10 token, unless `from` and caller are the same account.
  function transferFrom(
    address from,
    address to,
    uint256 value
  ) external override returns (bool) {
    if (from != msg.sender) {
      // _decreaseAllowance(from, msg.sender, value);

      uint256 allowed = allowance[from][msg.sender];
      if (allowed != type(uint256).max) {
        require(allowed >= value, "WETH: request exceeds allowance");
        uint256 reduced = allowed - value;
        allowance[from][msg.sender] = reduced;
        emit Approval(from, msg.sender, reduced);
      }
    }

    // _transferFrom(from, to, value);
    if (to != address(0)) {
      // Transfer
      uint256 balance = balanceOf[from];
      require(balance >= value, "WETH: transfer amount exceeds balance");

      balanceOf[from] = balance - value;
      balanceOf[to] += value;
      emit Transfer(from, to, value);
    } else {
      // Withdraw
      uint256 balance = balanceOf[from];
      require(balance >= value, "WETH: burn amount exceeds balance");
      balanceOf[from] = balance - value;
      emit Transfer(from, address(0), value);

      (bool success, ) = msg.sender.call{value: value}("");
      require(success, "WETH: ETH transfer failed");
    }

    return true;
  }

  /// @dev Moves `value` WETH10 token from caller's account to account (`to`),
  /// after which a call is executed to an ERC677-compliant contract with the `data` parameter.
  /// A transfer to `address(0)` triggers an ETH withdraw matching the sent WETH10 token in favor of caller.
  /// Emits {Transfer} event.
  /// Returns boolean value indicating whether operation succeeded.
  /// Requirements:
  ///   - caller account must have at least `value` WETH10 token.
  /// For more information on transferAndCall format, see https://github.com/ethereum/EIPs/issues/677.
  function transferAndCall(
    address to,
    uint256 value,
    bytes calldata data
  ) external override returns (bool) {
    // _transferFrom(msg.sender, to, value);
    if (to != address(0)) {
      // Transfer
      uint256 balance = balanceOf[msg.sender];
      require(balance >= value, "WETH: transfer amount exceeds balance");

      balanceOf[msg.sender] = balance - value;
      balanceOf[to] += value;
      emit Transfer(msg.sender, to, value);
    } else {
      // Withdraw
      uint256 balance = balanceOf[msg.sender];
      require(balance >= value, "WETH: burn amount exceeds balance");
      balanceOf[msg.sender] = balance - value;
      emit Transfer(msg.sender, address(0), value);

      (bool success, ) = msg.sender.call{value: value}("");
      require(success, "WETH: ETH transfer failed");
    }

    return ITransferReceiver(to).onTokenTransfer(msg.sender, value, data);
  }
}

contract PyroWeth10Proxy is Ownable {
  // address public baseToken;
  IWETH10 public weth10;
  uint256 constant ONE = 1e18;
  bool unlocked = true;
  address public baseToken;
  modifier reentrancyGuard() {
    require(unlocked, "PyroProxy: reentrancy guard active");
    unlocked = false;
    _;
    unlocked = true;
  }

  constructor(address pyroWeth) {
    baseToken = pyroWeth;
    // (, address weth, , ) = PyroTokenLike(pyroWeth).config();
    address weth=address(0);
    weth10 = IWETH10(weth);
    IERC20(weth10).approve(baseToken, type(uint256).max);
  }

  function balanceOf(address holder) external view returns (uint256) {
    return IERC20(baseToken).balanceOf(holder);
  }

  function redeem(uint256 pyroTokenAmount) external reentrancyGuard returns (uint256) {
    IERC20(baseToken).transferFrom(msg.sender, address(this), pyroTokenAmount); //0.1% fee
    uint256 actualAmount = IERC20(baseToken).balanceOf(address(this));
    // PyroTokenLike(baseToken).redeem(actualAmount);
    uint256 balanceOfWeth = weth10.balanceOf(address(this));
    weth10.withdrawTo(payable(msg.sender), balanceOfWeth);
    return balanceOfWeth;
  }

  function mint(uint256 baseTokenAmount) external payable reentrancyGuard returns (uint256) {
    require(msg.value == baseTokenAmount && baseTokenAmount > 0, "PyroWethProxy: amount invariant");
    weth10.deposit{value: msg.value}();
    uint256 weth10Balance = weth10.balanceOf(address(this));
    // PyroTokenLike(baseToken).mint(weth10Balance);
    uint256 pyroWethBalance = IERC20(baseToken).balanceOf(address(this));
    IERC20(baseToken).transfer(msg.sender, pyroWethBalance);
    return (pyroWethBalance * 999) / 1000; //0.1% fee
  }

  function calculateMintedPyroWeth(uint256 baseTokenAmount) external view returns (uint256) {
    uint256 pyroTokenRedeemRate = PyroTokenLike(baseToken).redeemRate();
    uint256 mintedPyroTokens = (baseTokenAmount * ONE) / (pyroTokenRedeemRate);
    return (mintedPyroTokens * 999) / 1000; //0.1% fee
  }

  function calculateRedeemedWeth(uint256 pyroTokenAmount) external view returns (uint256) {
    uint256 pyroTokenSupply = IERC20(baseToken).totalSupply() - ((pyroTokenAmount * 1) / 1000);
    uint256 wethBalance = IERC20(weth10).balanceOf(baseToken);
    uint256 newRedeemRate = (wethBalance * ONE) / pyroTokenSupply;
    uint256 newPyroTokenbalance = (pyroTokenAmount * 999) / 1000;
    uint256 fee = (newPyroTokenbalance * 2) / 100;
    uint256 net = newPyroTokenbalance - fee;
    return (net * newRedeemRate) / ONE;
  }

  function redeemRate() public view returns (uint256) {
    return PyroTokenLike(baseToken).redeemRate();
  }
}

abstract contract TokenProxyLike is IERC20 {
    address internal baseToken;
    uint constant internal ONE = 1 ether;
    constructor (address _baseToken) {
        baseToken=_baseToken;
    }

    function mint(address to, uint256 amount) public virtual returns (uint);
    function redeem(address to, uint256 amount) public virtual returns (uint);
}
abstract contract FlanLike is IERC20 {
    function mint(address recipient, uint256 amount)
        public
        virtual
        returns (bool);

    function setBurnOnTransferFee(uint8 fee) public virtual;

    function burn(uint256 amount) public virtual returns (bool); 
}

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */

// File temp/@openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol

/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() override external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() override external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() override external view returns (uint8);
}




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
    function burnFrom(address account, uint256 amount) override public virtual {
        uint256 currentAllowance = allowance(account, _msgSender());
        require(
            currentAllowance >= amount,
            "ERC20: burn amount exceeds allowance"
        );
        _approve(account, _msgSender(), currentAllowance - amount);
        _burn(account, amount);
    }
}

/**
 *@title SoulReader
 * @author Justin Goro
 * @notice Coneptually similar to the Router contracts in Uniswap, this is a helper contract for reading Limbo data in a manner more friendly to a UI
 * @dev passing the limbo contract address in allows the SoulReader to remain stateless and also allows front end devs to perform comparisons and experiments in real time.
 */
contract SoulReader {
  uint256 constant TERA = 1E12;
  struct Soul {
    uint256 lastRewardTimestamp; //I know masterchef counts by block but this is less reliable than timestamp.
    uint256 accumulatedFlanPerShare;
    uint256 crossingThreshold; //the value at which this soul is elligible to cross over to Behodler
    uint256 soulType;
    uint256 state;
    uint256 flanPerSecond;
  }

  function getLimbo(address _limbo) internal pure returns (LimboLike) {
    return LimboLike(_limbo);
  }

  /**
   *@param token the token contract address
   *@param _limbo the limbo contract address
   */
  function SoulStats(address token, address _limbo)
    public
    view
    returns (
      uint256, //state
      uint256, //staked balance
      uint256 //fps
    )
  {
    LimboLike limbo = getLimbo(_limbo);
    uint256 latestIndex = limbo.latestIndex(token);
    (, , , , uint256 state, uint256 fps) = limbo.souls(token, latestIndex);
    uint256 stakeBalance = IERC20(token).balanceOf(address(limbo));
    return (state, stakeBalance, fps);
  }

  /**
   *@param token the token contract address
   *@param _limbo the limbo contract address
   */
  function CrossingParameters(address token, address _limbo)
    public
    view
    returns (
      uint256, //initialCrossingbonus
      int256, //bonusDelta,
      uint256 //fps
    )
  {
    LimboLike limbo = getLimbo(_limbo);
    uint256 latestIndex = limbo.latestIndex(token);
    (, , , , , uint256 flanPerSecond) = limbo.souls(token, latestIndex);

    (, , int256 crossingBonusDelta, uint256 initialCrossingBonus, ) = limbo.tokenCrossingParameters(token, latestIndex);
    return (initialCrossingBonus, crossingBonusDelta, flanPerSecond);
  }

  /**
   *@notice Query the pending rewards for a given soul by a given staked user
   *@dev performing these calculations client side is difficult and frought with bugs.
   *@param account staked user
   *@param token the token contract address
   *@param _limbo the limbo contract address
   */
  function GetPendingReward(
    address account,
    address token,
    address _limbo
  ) external view returns (uint256) {
    LimboLike limbo = getLimbo(_limbo);
    uint256 latestIndex = limbo.latestIndex(token);
    Soul memory soul; //stack too deep avoidance
    (soul.lastRewardTimestamp, soul.accumulatedFlanPerShare, , , soul.state, soul.flanPerSecond) = limbo.souls(
      token,
      latestIndex
    );

    (, uint256 stakingEndsTimestamp, , , ) = limbo.tokenCrossingParameters(token, latestIndex);
    uint256 finalTimeStamp = soul.state != 1 ? stakingEndsTimestamp : block.timestamp;
    uint256 limboBalance = IERC20(token).balanceOf(address(limbo));

    (uint256 stakedAmount, uint256 rewardDebt, ) = limbo.userInfo(token, account, latestIndex);
    if (limboBalance > 0) {
      soul.accumulatedFlanPerShare =
        soul.accumulatedFlanPerShare +
        (((finalTimeStamp - soul.lastRewardTimestamp) * soul.flanPerSecond * (1e12)) / limboBalance);
    }
    uint256 accumulated = ((stakedAmount * soul.accumulatedFlanPerShare) / (1e12));
    if (accumulated >= rewardDebt) return accumulated - rewardDebt;
    return 0;
  }

  //For rebase tokens, make the appropriate adjustments on the front end, not here.
  //Only call this on live souls.
  /**
   * @notice For threshold souls, calculate the crossing bonus for a given staked user
   * @param holder user staked
   * @param token the soul
   * @param _limbo the limbo contract address
   */
  function ExpectedCrossingBonus(
    address holder,
    address token,
    address _limbo
  ) external view returns (uint256 flanBonus) {
    LimboLike limbo = getLimbo(_limbo);
    uint256 latestIndex = limbo.latestIndex(token);
    (uint256 stakedAmount, , bool bonusPaid) = limbo.userInfo(token, holder, latestIndex);
    if (bonusPaid) return 0;
    uint256 bonusRate = ExpectedCrossingBonusRate(holder, token, _limbo);
    flanBonus = (bonusRate * stakedAmount) / TERA;
  }

  function ExpectedCrossingBonusRate(
    address holder,
    address token,
    address _limbo
  ) public view returns (uint256 bonusRate) {
    LimboLike limbo = getLimbo(_limbo);
    uint256 latestIndex = limbo.latestIndex(token);

    (uint256 stakedAmount, , bool bonusPaid) = limbo.userInfo(token, holder, latestIndex);
    if (bonusPaid) return 0;

    (uint256 stakingBegins, uint256 stakingEnds, int256 crossingBonusDelta, uint256 initialCrossingBonus, ) = limbo
      .tokenCrossingParameters(token, latestIndex);
    stakingEnds = stakingEnds == 0 ? block.timestamp : stakingEnds;
    stakingBegins = stakingBegins == 0 ? block.timestamp - 1 : stakingBegins;

    int256 accumulatedFlanPerTeraToken = crossingBonusDelta * int256(stakingEnds - stakingBegins);
    // console.log("token: %d", token);
    // console.log("time elapsed %d", stakingEnds - stakingBegins);
    // console.log(
    //   "accumulatedFlanPerTeraToken %d, initialCrossingBonus %d",
    //   uint256(accumulatedFlanPerTeraToken),
    //   uint256(initialCrossingBonus)
    // );
    int256 finalFlanPerTeraToken = int256(initialCrossingBonus) +
      (stakedAmount > 0 ? accumulatedFlanPerTeraToken : int256(0));
    bonusRate = finalFlanPerTeraToken > 0 ? uint256(finalFlanPerTeraToken) : 0;
  }
}

/**@dev Contracts that implement this can be governed by LimboDAO.
 * Depending on the importance and context, you can enforce governance oversight with one of two modifiers:
 *       -enforceGovernance will execute if either a proposal passes with a yes vote or if the caller is using flash governance
 *       -onlySuccessfulProposals will only execute if a proposal passes with a yes vote.
 */
abstract contract Governable {
  FlashGovernanceArbiterLike internal flashGoverner;

  bool public configured;
  address public DAO;

  /**@notice during initial setup, requiring strict multiday proposals for calibration would unecessarily delay release. 
    As long as configured is false, the contract has no governance enforcement. Calling endConfiguration is a one way operation 
    to ensure governance mechanisms kicks in. As a user, do not interact with these contracts if configured is false.
    */
  function endConfiguration() public {
    configured = true;
  }

  modifier onlySuccessfulProposal() {
    //modifiers are inline macros so you'd get a lot of code duplication if you don't refactor (EIP-170)
    assertSuccessfulProposal(msg.sender);
    _;
  }

  modifier onlySoulUpdateProposal() {
    assertSoulUpdateProposal(msg.sender);
    _;
  }

  function assertSoulUpdateProposal(address sender) internal view {
    (, , address proposalFactory) = LimboDAOLike(DAO).proposalConfig();
    require(!configured || sender == ProposalFactoryLike(proposalFactory).soulUpdateProposal(), "EJ");
    assertSuccessfulProposal(sender);
  }

  function _governanceApproved(bool emergency) internal {
    bool successfulProposal = LimboDAOLike(DAO).successfulProposal(msg.sender);
    if (successfulProposal) {
      flashGoverner.setEnforcement(false);
    } else if (configured) flashGoverner.assertGovernanceApproved(msg.sender, address(this), emergency);
  }

  modifier governanceApproved(bool emergency) {
    _governanceApproved(emergency);
    _;
    flashGoverner.setEnforcement(true);
  }

  function assertSuccessfulProposal(address sender) internal view {
    require(!configured || LimboDAOLike(DAO).successfulProposal(sender), "EJ");
  }

  constructor(address dao) {
    setDAO(dao);
  }

  ///@param dao The LimboDAO contract address
  function setDAO(address dao) public {
    require(DAO == address(0) || msg.sender == DAO || !configured, "EK");
    DAO = dao;
    flashGoverner = FlashGovernanceArbiterLike(LimboDAOLike(dao).getFlashGoverner());
  }
}

contract MockMorgothTokenApprover is MorgothTokenApproverLike {
    mapping(address => bool) public approvedTokens;

    function toggleManyTokens(address[] memory tokens, bool value) public {
        for (uint256 i = 0; i < tokens.length; i++) approvedTokens[tokens[i]] = value;
    }

    function addToken(address token) public {
        approvedTokens[token] = true;
    }

    function removeToken(address token) public {
        approvedTokens[token] = false;
    }

    function approved(address token) public view override returns (bool) {
        return approvedTokens[token];
    }
}

contract Angband {
  function executePower(address invoker) public {
    LimboAddTokenToBehodlerTestNet(invoker).invoke("test", msg.sender);
  }
}

contract UniswapV2ERC20 is IUniswapV2ERC20 {
    using SafeMath for uint;

    string public override constant name = 'Uniswap V2';
    string public override constant symbol = 'UNI-V2';
    uint8 public override constant decimals = 18;
    uint  public override totalSupply;
    mapping(address => uint) public override balanceOf;
    mapping(address => mapping(address => uint)) public override allowance;

    bytes32 public override DOMAIN_SEPARATOR;
    // keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");
    bytes32 public override constant PERMIT_TYPEHASH = 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9;
    mapping(address => uint) public override nonces;

    constructor() {
        uint chainId;
        assembly {
            chainId := chainid()
        }
        DOMAIN_SEPARATOR = keccak256(
            abi.encode(
                keccak256('EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)'),
                keccak256(bytes(name)),
                keccak256(bytes('1')),
                chainId,
                address(this)
            )
        );
    }

    function _mint(address to, uint value) internal {
        totalSupply = totalSupply.add(value);
        balanceOf[to] = balanceOf[to].add(value);
        emit Transfer(address(0), to, value);
    }

    function _burn(address from, uint value) internal {
        balanceOf[from] = balanceOf[from].sub(value);
        totalSupply = totalSupply.sub(value);
        emit Transfer(from, address(0), value);
    }

    function _approve(address owner, address spender, uint value) private {
        allowance[owner][spender] = value;
        emit Approval(owner, spender, value);
    }

    function _transfer(address from, address to, uint value) private {
        balanceOf[from] = balanceOf[from].sub(value);
        balanceOf[to] = balanceOf[to].add(value);
        emit Transfer(from, to, value);
    }

    function approve(address spender, uint value) external override returns (bool) {
        _approve(msg.sender, spender, value);
        return true;
    }

    function transfer(address to, uint value) external override returns (bool) {
        _transfer(msg.sender, to, value);
        return true;
    }

    function transferFrom(address from, address to, uint value) external override returns (bool) {
        if (allowance[from][msg.sender] != type(uint).max) {
            allowance[from][msg.sender] = allowance[from][msg.sender].sub(value);
        }
        _transfer(from, to, value);
        return true;
    }

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external override {
        require(deadline >= block.timestamp, 'UniswapV2: EXPIRED');
        bytes32 digest = keccak256(
            abi.encodePacked(
                '\x19\x01',
                DOMAIN_SEPARATOR,
                keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonces[owner]++, deadline))
            )
        );
        address recoveredAddress = ecrecover(digest, v, r, s);
        require(recoveredAddress != address(0) && recoveredAddress == owner, 'UniswapV2: INVALID_SIGNATURE');
        _approve(owner, spender, value);
    }
}


contract ScarcityLite is CommonIERC20 {
  event Mint(address sender, address recipient, uint256 value);
  event Burn(uint256 value);

  mapping(address => uint256) internal balances;
  mapping(address => mapping(address => uint256)) internal _allowances;
  uint256 internal _totalSupply;

  struct BurnConfig {
    uint256 transferFee; // percentage expressed as number betewen 1 and 1000
    uint256 burnFee; // percentage expressed as number betewen 1 and 1000
    address feeDestination;
  }

  BurnConfig public config;

  function configureScarcity(
    uint256 transferFee,
    uint256 burnFee,
    address feeDestination
  ) public {
    require(config.transferFee + config.burnFee < 1000);
    config.transferFee = transferFee;
    config.burnFee = burnFee;
    config.feeDestination = feeDestination;
  }

  function getConfiguration()
    public
    view
    returns (
      uint256,
      uint256,
      address
    )
  {
    return (config.transferFee, config.burnFee, config.feeDestination);
  }

  function name() public pure returns (string memory) {
    return "Scarcity";
  }

  function symbol() public pure returns (string memory) {
    return "SCX";
  }

  function decimals() public pure override returns (uint8) {
    return 18;
  }

  function totalSupply() external view override returns (uint256) {
    return _totalSupply;
  }

  function balanceOf(address account) external view override returns (uint256) {
    return balances[account];
  }

  function transfer(address recipient, uint256 amount) external override returns (bool) {
    _transfer(msg.sender, recipient, amount);
    return true;
  }

  function allowance(address owner, address spender) external view override returns (uint256) {
    return _allowances[owner][spender];
  }

  function approve(address spender, uint256 amount) external override returns (bool) {
    _approve(msg.sender, spender, amount);
    return true;
  }

  function transferFrom(
    address sender,
    address recipient,
    uint256 amount
  ) external override returns (bool) {
    _transfer(sender, recipient, amount);
    _approve(sender, msg.sender, _allowances[sender][msg.sender] - (amount));
    return true;
  }

  function burn(uint256 value) external returns (bool) {
    burn(msg.sender, value);
    return true;
  }

  function burn(address holder, uint256 value) internal {
    balances[holder] = balances[holder] - value;
    _totalSupply = _totalSupply - value;
    emit Burn(value);
  }

  function mint(address recipient, uint256 value) internal {
    balances[recipient] = balances[recipient] + (value);
    _totalSupply = _totalSupply + (value);
    emit Mint(msg.sender, recipient, value);
  }

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

  //outside of Behodler, Scarcity transfer incurs a fee.
  function _transfer(
    address sender,
    address recipient,
    uint256 amount
  ) internal virtual {
    require(sender != address(0), "Scarcity: transfer from the zero address");
    require(recipient != address(0), "Scarcity: transfer to the zero address");

    uint256 feeComponent = (config.transferFee * amount) / (1000);
    uint256 burnComponent = (config.burnFee * amount) / (1000);
    _totalSupply = _totalSupply - burnComponent;
    emit Burn(burnComponent);

    balances[config.feeDestination] = balances[config.feeDestination] + (feeComponent);

    balances[sender] = balances[sender] - (amount);

    balances[recipient] = balances[recipient] + (amount - (feeComponent + burnComponent));
    emit Transfer(sender, recipient, amount);
  }

  function applyBurnFee(
    address token,
    uint256 amount,
    bool proxyBurn
  ) internal returns (uint256) {
    uint256 burnAmount = (config.burnFee * amount) / (1000);
    Burnable bToken = Burnable(token);
    if (proxyBurn) {
      bToken.burn(burnAmount);
    } else {
      bToken.burn(burnAmount);
    }

    return burnAmount;
  }
}

library AddressBalanceCheck {
  function tokenBalance(address token) public view returns (uint256) {
    return CommonIERC20(token).balanceOf(address(this));
  }

  function shiftedBalance(address token, uint256 factor) public view returns (uint256) {
    return CommonIERC20(token).balanceOf(address(this)) / factor;
  }

  function transferIn(
    address token,
    address sender,
    uint256 value
  ) public {
    CommonIERC20(token).transferFrom(sender, address(this), value);
  }

  function transferOut(
    address token,
    address recipient,
    uint256 value
  ) public {
    CommonIERC20(token).transfer(recipient, value);
  }
}

library ABDK {
  /*
   * Minimum value signed 64.64-bit fixed point number may have.
   */
  int128 private constant MIN_64x64 = -0x80000000000000000000000000000000;

  /*
   * Maximum value signed 64.64-bit fixed point number may have.
   */
  int128 private constant MAX_64x64 = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

  /**
   * Convert unsigned 256-bit integer number into signed 64.64-bit fixed point
   * number.  Revert on overflow.
   *
   * @param x unsigned 256-bit integer number
   * @return signed 64.64-bit fixed point number
   */
  function fromUInt(uint256 x) internal pure returns (int128) {
    require(x <= 0x7FFFFFFFFFFFFFFF);
    return int128(uint128(x << 64));
  }

  /**
   * Calculate x + y.  Revert on overflow.
   *
   * @param x signed 64.64-bit fixed point number
   * @param y signed 64.64-bit fixed point number
   * @return signed 64.64-bit fixed point number
   */
  function add(int128 x, int128 y) internal pure returns (int128) {
    int256 result = int256(x) + y;
    require(result >= MIN_64x64 && result <= MAX_64x64);
    return int128(result);
  }

  /**
   * Calculate binary logarithm of x.  Revert if x <= 0.
   *
   * @param x signed 64.64-bit fixed point number
   * @return signed 64.64-bit fixed point number
   */
  function log_2(uint256 x) internal pure returns (uint256) {
    require(x > 0);

    uint256 msb = 0;
    uint256 xc = x;
    if (xc >= 0x10000000000000000) {
      xc >>= 64;
      msb += 64;
    }
    if (xc >= 0x100000000) {
      xc >>= 32;
      msb += 32;
    }
    if (xc >= 0x10000) {
      xc >>= 16;
      msb += 16;
    }
    if (xc >= 0x100) {
      xc >>= 8;
      msb += 8;
    }
    if (xc >= 0x10) {
      xc >>= 4;
      msb += 4;
    }
    if (xc >= 0x4) {
      xc >>= 2;
      msb += 2;
    }
    if (xc >= 0x2) msb += 1; // No need to shift xc anymore

    uint256 result = (msb - 64) << 64;
    uint256 ux = uint256(x) << uint256(127 - msb);
    for (uint256 bit = 0x8000000000000000; bit > 0; bit >>= 1) {
      ux *= ux;
      uint256 b = ux >> 255;
      ux >>= 127 + b;
      result += bit * b;
    }

    return result;
  }
}

contract StubLiquidityReceiver {}

contract LachesisLite {
  struct tokenConfig {
    bool valid;
    bool burnable;
  }
  address public behodler;
  mapping(address => tokenConfig) private config;

  function cut(address token) public view returns (bool, bool) {
    tokenConfig memory parameters = config[token];
    return (parameters.valid, parameters.burnable);
  }

  function measure(
    address token,
    bool valid,
    bool burnable
  ) public {
    _measure(token, valid, burnable);
  }

  function _measure(
    address token,
    bool valid,
    bool burnable
  ) internal {
    config[token] = tokenConfig({valid: valid, burnable: burnable});
  }

  function setBehodler(address b) public {
    behodler = b;
  }

  function updateBehodler(address token) public {
    (bool valid, bool burnable) = cut(token);

    BehodlerLite(behodler).setValidToken(token, valid, burnable);
    BehodlerLite(behodler).setTokenBurnable(token, burnable);
  }
}

contract BehodlerLite is ScarcityLite {
  using ABDK for int128;
  using ABDK for uint256;
  using AddressBalanceCheck for address;
  mapping(address => bool) validTokens;
  struct PrecisionFactors {
    uint8 swapPrecisionFactor;
    uint8 maxLiquidityExit; //percentage as number between 1 and 100
  }
  address receiver;
  address lachesis;
  PrecisionFactors safetyParameters;

  constructor() {
    receiver = address(new StubLiquidityReceiver());
    safetyParameters.swapPrecisionFactor = 30; //approximately a billion
    safetyParameters.maxLiquidityExit = 90;
  }

  function setLachesis(address l) public {
    lachesis = l;
  }

  function setValidToken(
    address token,
    bool valid,
    bool burnable
  ) public {
    require(msg.sender == lachesis);
    validTokens[token] = valid;
    tokenBurnable[token] = burnable;
  }

  modifier onlyValidToken(address token) {
    require(lachesis == address(0) || validTokens[token], "BehodlerLite: tokenInvalid");
    _;
  }

  function setReceiver(address newReceiver) public {
    receiver = newReceiver;
  }

  function setSafetParameters(uint8 swapPrecisionFactor, uint8 maxLiquidityExit) external {
    safetyParameters.swapPrecisionFactor = swapPrecisionFactor;
    safetyParameters.maxLiquidityExit = maxLiquidityExit;
  }

  //Logarithmic growth can get quite flat beyond the first chunk. We divide input amounts by
  uint256 public constant MIN_LIQUIDITY = 1e12;

  mapping(address => bool) public tokenBurnable;

  function setTokenBurnable(address token, bool burnable) public {
    tokenBurnable[token] = burnable;
  }

  mapping(address => bool) public whiteListUsers; // can trade on tokens that are disabled

  function swap(
    address inputToken,
    address outputToken,
    uint256 inputAmount,
    uint256 outputAmount
  ) external payable onlyValidToken(inputToken) returns (bool success) {
    uint256 initialInputBalance = inputToken.tokenBalance();

    inputToken.transferIn(msg.sender, inputAmount);

    uint256 netInputAmount = inputAmount - burnToken(inputToken, inputAmount);
    uint256 initialOutputBalance = outputToken.tokenBalance();
    require(
      (outputAmount * 100) / initialOutputBalance <= safetyParameters.maxLiquidityExit,
      "BEHODLER: liquidity withdrawal too large."
    );
    uint256 finalInputBalance = initialInputBalance + (netInputAmount);
    uint256 finalOutputBalance = initialOutputBalance - (outputAmount);

    //new scope to avoid stack too deep errors.
    {
      //if the input balance after adding input liquidity is 1073741824 bigger than the initial balance, we revert.
      uint256 inputRatio = (initialInputBalance << safetyParameters.swapPrecisionFactor) / finalInputBalance;
      uint256 outputRatio = (finalOutputBalance << safetyParameters.swapPrecisionFactor) / initialOutputBalance;

      require(inputRatio != 0 && inputRatio == outputRatio, "BEHODLER: swap invariant.");
    }

    require(finalOutputBalance >= MIN_LIQUIDITY, "BEHODLER: min liquidity.");
    outputToken.transferOut(msg.sender, outputAmount);
    success = true;
  }

  function addLiquidity(address inputToken, uint256 amount)
    external
    payable
    onlyValidToken(inputToken)
    returns (uint256 deltaSCX)
  {
    uint256 initialBalance = uint256(int256(inputToken.shiftedBalance(MIN_LIQUIDITY).fromUInt()));

    inputToken.transferIn(msg.sender, amount);

    uint256 netInputAmount = uint256(int256(((amount - burnToken(inputToken, amount)) / MIN_LIQUIDITY).fromUInt()));

    uint256 finalBalance = uint256(initialBalance + netInputAmount);
    require(uint256(finalBalance) >= MIN_LIQUIDITY, "BEHODLER: min liquidity.");
    deltaSCX = uint256(finalBalance.log_2() - (initialBalance > 1 ? initialBalance.log_2() : 0));
    mint(msg.sender, deltaSCX);
  }

  /*
        ΔSCX =  log(InitialBalance) - log(FinalBalance)
        tokensToRelease = InitialBalance -FinalBalance
        =>FinalBalance =  InitialBalance - tokensToRelease
        Then apply logs and deduct SCX from msg.sender

        The choice of base for the log isn't relevant from a mathematical point of view
        but from a computational point of view, base 2 is the cheapest for obvious reasons.
        "From my point of view, the Jedi are evil" - Darth Vader
     */
  function withdrawLiquidity(address outputToken, uint256 tokensToRelease)
    external
    payable
    onlyValidToken(outputToken)
    returns (uint256 deltaSCX)
  {
    uint256 initialBalance = outputToken.tokenBalance();
    uint256 finalBalance = initialBalance - tokensToRelease;
    require(finalBalance > MIN_LIQUIDITY, "BEHODLER: min liquidity");
    require(
      (tokensToRelease * 100) / initialBalance <= safetyParameters.maxLiquidityExit,
      "BEHODLER: liquidity withdrawal too large."
    );

    uint256 logInitial = initialBalance.log_2();
    uint256 logFinal = finalBalance.log_2();

    deltaSCX = logInitial - (finalBalance > 1 ? logFinal : 0);
    uint256 scxBalance = balances[msg.sender];

    if (deltaSCX > scxBalance) {
      //rounding errors in scx creation and destruction. Err on the side of holders
      uint256 difference = deltaSCX - scxBalance;
      if ((difference * 10000) / deltaSCX == 0) deltaSCX = scxBalance;
    }
    burn(msg.sender, deltaSCX);
    outputToken.transferOut(msg.sender, tokensToRelease);
  }

  /*
        ΔSCX =  log(InitialBalance) - log(FinalBalance)
        tokensToRelease = InitialBalance -FinalBalance
        =>FinalBalance =  InitialBalance - tokensToRelease
        Then apply logs and deduct SCX from msg.sender

        The choice of base for the log isn't relevant from a mathematical point of view
        but from a computational point of view, base 2 is the cheapest for obvious reasons.
        "From my point of view, the Jedi are evil" - Darth Vader
     */
  function withdrawLiquidityFindSCX(
    address outputToken,
    uint256 tokensToRelease,
    uint256 scx,
    uint256 passes
  ) external view returns (uint256) {
    uint256 upperBoundary = outputToken.tokenBalance();
    uint256 lowerBoundary = 0;

    for (uint256 i = 0; i < passes; i++) {
      uint256 initialBalance = outputToken.tokenBalance();
      uint256 finalBalance = initialBalance - tokensToRelease;

      uint256 logInitial = initialBalance.log_2();
      uint256 logFinal = finalBalance.log_2();

      int256 deltaSCX = int256(logInitial - (finalBalance > 1 ? logFinal : 0));
      int256 difference = int256(scx) - deltaSCX;
      // if (difference**2 < 1000000) return tokensToRelease;
      if (difference == 0) return tokensToRelease;
      if (difference < 0) {
        // too many tokens requested
        upperBoundary = tokensToRelease - 1;
      } else {
        //too few tokens requested
        lowerBoundary = tokensToRelease + 1;
      }
      tokensToRelease = ((upperBoundary - lowerBoundary) / 2) + lowerBoundary; //bitshift
      tokensToRelease = tokensToRelease > initialBalance ? initialBalance : tokensToRelease;
    }
    return tokensToRelease;
  }

  function burnToken(address token, uint256 amount) private returns (uint256 burnt) {
    if (tokenBurnable[token]) {
      burnt = applyBurnFee(token, amount, false);
    } else {
      burnt = (config.burnFee * amount) / (1000);
      token.transferOut(receiver, burnt);
    }
  }
}

contract TokenProxy is TokenProxyLike {
 string public override name;
 string public override symbol; 
 constructor (string memory _name, string memory  _symbol, address _baseToken) TokenProxyLike(_baseToken){
     name=_name;
        symbol=_symbol;
 }

    mapping(address => uint256) internal _balances;

    mapping(address => mapping(address => uint256)) internal _allowances;

    uint256 internal _totalSupply;


    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5,05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless this function is
     * overridden;
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view override returns (uint8) {
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
    function balanceOf(address account)
        public
        view
        virtual
        override
        returns (uint256)
    {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `recipient` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address recipient, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _transfer(msg.sender, recipient, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender)
        public
        view
        virtual
        override
        returns (uint256)
    {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _approve(msg.sender, spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * Requirements:
     *
     * - `sender` and `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     * - the caller must have allowance for ``sender``'s tokens of at least
     * `amount`.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);

        uint256 currentAllowance = _allowances[sender][msg.sender];
        require(
            currentAllowance >= amount,
            "ERC20: transfer amount exceeds allowance"
        );
        _approve(sender, msg.sender, currentAllowance - amount);

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
    function increaseAllowance(address spender, uint256 addedValue)
        public
        virtual
        returns (bool)
    {
        _approve(
            msg.sender,
            spender,
            _allowances[msg.sender][spender] + addedValue
        );
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
    function decreaseAllowance(address spender, uint256 subtractedValue)
        public
        virtual
        returns (bool)
    {
        uint256 currentAllowance = _allowances[msg.sender][spender];
        require(
            currentAllowance >= subtractedValue,
            "ERC20: decreased allowance below zero"
        );
        _approve(msg.sender, spender, currentAllowance - subtractedValue);

        return true;
    }

      function mint(address to, uint256 amount) public override returns (uint){
          IERC20(baseToken).transferFrom(msg.sender,address(this),amount);
          _mint(to,amount);
          return amount;
      }

    function redeem(address to, uint256 amount) public override returns (uint){
        _burn(msg.sender,amount);
        IERC20(baseToken).transfer(to, amount);
        return amount;
    }

    /**
     * @dev Moves tokens `amount` from `sender` to `recipient`.
     *
     * This is internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `sender` cannot be the zero address.
     * - `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     */
    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal virtual {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        uint256 senderBalance = _balances[sender];
        require(
            senderBalance >= amount,
            "ERC20: transfer amount exceeds balance"
        );
        _balances[sender] = senderBalance - amount;
        _balances[recipient] += amount;

        emit Transfer(sender, recipient, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");


        _totalSupply += amount;
        _balances[account] += amount;
        emit Transfer(address(0), account, amount);
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

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        _balances[account] = accountBalance - amount;
        _totalSupply -= amount;

        emit Transfer(account, address(0), amount);
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
}

/**@notice to C4 auditors: this part of Limbo intersects significantly with MorgothDAO and is beyond the scope of the audit.
* No prizes are offered for auditing MorgothDAO at this stage. While it's important that Flan be set up correctly, an incorrect setup
* is easy to detect and costless to discard (ignoring gas costs) and so may be attempted multiple times until perfected. 
* The migration to Behodler will require a surface level understanding of Morgoth the functionality employed by Morgoth has already withstood the test of multiple mainnet uses
*/
///@dev this contract combines multiple genesis operations into one transaction to protect against entereing into an invalid state
contract FlanGenesis{
    struct Dependencies {
        uint something;
    }    
}
/*
All tokens in Limbo comply with the ERC677 standard. In addition they are ownable, alow burning
and can whitelist addresses with finite or infinite minting power
*/

abstract contract ERC677 is ERC20Burnable, Ownable {
   
    constructor(string memory name, string memory symbol) ERC20() {

    }

    /**
     * @dev transfer token to a contract address with additional data if the recipient is a contact.
     * @param _to The address to transfer to.
     * @param _value The amount to be transferred.
     * @param _data The extra data to be passed to the receiving contract.
     */
    function transferAndCall(
        address _to,
        uint256 _value,
        bytes memory _data
    ) public returns (bool success) {
        // super.transfer(_to, _value);
        _transfer(msg.sender, _to, _value);
        if (isContract(_to)) {
            contractFallback(_to, _value, _data);
        }
        return true;
    }

    function contractFallback(
        address _to,
        uint256 _value,
        bytes memory _data
    ) private {
        IERC677Receiver receiver = IERC677Receiver(_to);
        receiver.onTokenTransfer(msg.sender, _value, _data);
    }

    function isContract(address _addr) private view returns (bool hasCode) {
        uint256 length;
        assembly {
            length := extcodesize(_addr)
        }
        return length > 0;
    }
}

abstract contract MockFOTToken is Context, IERC20, IERC20Metadata {

    uint transferFee = 0;//0-1000
    mapping(address => uint256) internal _balances;

    mapping(address => mapping(address => uint256)) internal _allowances;

    uint256 internal _totalSupply;

    string private _name;
    string private _symbol;

    /**
     * @dev Sets the values for {name} and {symbol}.
     *
     * The defaut value of {decimals} is 18. To select a different value for
     * {decimals} you should overload it.
     *
     * All two of these values are immutable: they can only be set once during
     * construction.
     */
    constructor(string memory name_, string memory symbol_, uint fee) {
        _name = name_;
        _symbol = symbol_;
        transferFee = fee;
        _mint(msg.sender,100 ether);
    }

    // /**
    //  * @dev Returns the name of the token.
    //  */
    // function name() public view virtual override returns (string memory) {
    //     return _name;
    // }

    // /**
    //  * @dev Returns the symbol of the token, usually a shorter version of the
    //  * name.
    //  */
    // function symbol() public view virtual override returns (string memory) {
    //     return _symbol;
    // }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5,05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless this function is
     * overridden;
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    // function decimals() public view virtual override returns (uint8) {
    //     return 18;
    // }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account)
        public
        view
        virtual
        override
        returns (uint256)
    {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `recipient` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address recipient, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender)
        public
        view
        virtual
        override
        returns (uint256)
    {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * Requirements:
     *
     * - `sender` and `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     * - the caller must have allowance for ``sender``'s tokens of at least
     * `amount`.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);

        uint256 currentAllowance = _allowances[sender][_msgSender()];
        require(
            currentAllowance >= amount,
            "ERC20: transfer amount exceeds allowance"
        );
        _approve(sender, _msgSender(), currentAllowance - amount);

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
    function increaseAllowance(address spender, uint256 addedValue)
        public
        virtual
        returns (bool)
    {
        _approve(
            _msgSender(),
            spender,
            _allowances[_msgSender()][spender] + addedValue
        );
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
    function decreaseAllowance(address spender, uint256 subtractedValue)
        public
        virtual
        returns (bool)
    {
        uint256 currentAllowance = _allowances[_msgSender()][spender];
        require(
            currentAllowance >= subtractedValue,
            "ERC20: decreased allowance below zero"
        );
        _approve(_msgSender(), spender, currentAllowance - subtractedValue);

        return true;
    }

    /**
     * @dev Moves tokens `amount` from `sender` to `recipient`.
     *
     * This is internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `sender` cannot be the zero address.
     * - `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     */
    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal virtual {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(sender, recipient, amount);

        uint256 senderBalance = _balances[sender];
        require(
            senderBalance >= amount,
            "ERC20: transfer amount exceeds balance"
        );
        uint fee = (amount * transferFee)/1000;
        _balances[sender] = senderBalance - amount;
        _balances[recipient] += amount-fee;
        _totalSupply -=fee;

        emit Transfer(sender, recipient, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply += amount;
        _balances[account] += amount;
        emit Transfer(address(0), account, amount);
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
        _balances[account] = accountBalance - amount;
        _totalSupply -= amount;

        emit Transfer(account, address(0), amount);
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
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be to transferred to `to`.
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
}

// File temp/@openzeppelin/contracts/token/ERC20/extensions/ERC20Burnable.sol

/**
 * @dev Extension of {ERC20} that allows token holders to destroy both their own
 * tokens and those that they have an allowance for, in a way that can be
 * recognized off-chain (via event analysis).
 */
abstract contract MockMigrationUniPair is ERC20Burnable {
    constructor(string memory name, string memory symbol) ERC20() {}

    function factory() public view returns (address) {
        return address(this);
    }

    uint112 reserve0;
    uint112 reserve1;

    function setReserves(uint112 r0, uint112 r1) public {
        reserve0 = r0;
        reserve1 = r1;
    }

    function getReserves()
        public
        view
        returns (
            uint112 _reserve0,
            uint112 _reserve1,
            uint32 _blockTimestampLast
        )
    {
        return (reserve0, reserve1, uint32(block.timestamp));
    }

    function mint(address to) external returns (uint256 liquidity) {
        uint256 val = (reserve0 * reserve1) / (reserve0 + reserve1);
        _mint(to, val);
        return val;
    }

    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external {}
}

/**
 * @notice Initially Flan's liquidity may be fairly low, limiting Limbo's ability to reward souls. Flan backstop accepts stablecoins in return for minting Pyroflan.
 *Under the hood a smaller quantity of Flan is minted and paired with the stablecoin in Uniswap in order to tilt the price of Flan higher while incresaing liquidity.
 * The same operation is performed with PyroFlan
 * The calling user then receives PyroFlan equal in value to the intial amount sent in but at the new price. A small premium is added.
 * The incentives facing the user: mint $X of PyroFlan with <$X of stablecoin, stake PyroFlan in Limbo for high APY, do not immediately dump because PyroFlan increases in value and because of 2% exit fee.
 * The incentives should be enough to encourage a gradual increase in pooled Flan and stablecoins, creating some minting runway for Limbo to accelerate.
 * In the future when Flan and Limbo are thriving and Flan is listed on Curve, we can create a version of this for Curve and Uniswap V3 in order to concentrate Flan liquidity and further cement stablecoin status.
 * Note: in this version, LP tokens generated are cast into the void. The argument of keeping them for fee revenue is negated by the impact on Flan. It would just be taking from Peter to give to Paul. 
 */
///@dev This contract uses Pyrotokens3. At the time of authoring, Pyrotokens3 implementation is incomplete and not fully tested but the interface (ABI) is locked.
contract FlanBackstop is Governable {
  /**
   *@param dao LimboDAO
   *@param flan Flan address
   *@param pyroFlan PyroFlan address
   */
  constructor(
    address dao,
    address flan,
    address pyroFlan
  ) Governable(dao) {
    config.pyroFlan = pyroFlan;
    config.flan = flan;
    IERC20(flan).approve(pyroFlan, 2**256 - 1);
  }

  struct ConfigVars {
    address flan;
    address pyroFlan;
    mapping(address => address) flanLPs;
    mapping(address => address) pyroFlanLPs;
    mapping(address => uint256) acceptableHighestPrice; //Highest tolerated Flan per stable
    mapping(address => uint8) decimalPlaces; //USDC and USDT have 6 decimal places because large stablecoin transfers are exactly where you'd like to find accidental bugs
  }

  ConfigVars public config;

  /**
   *@param stablecoin One of the popular stablecoins such as USDC, USDT, MIM, OUSD etc.
   *@param flanLP Uniswap V2 (or a fork such as Sushi) flan/Stablecoin LP
   *@param pyroFlanLP Uniswap V2 (or a fork such as Sushi) pyroFlan/Stablecoin LP
   *@param acceptableHighestPrice Since the prices are being read from balances, not oracles, the opportunity for price manipulation through flash loans exists. The community can put a circuit breaker in place to prevent such an exploit.
   *@param decimalPlaces USDT and USDC do not conform to common ERC20 practice. 
   */
  function setBacker(
    address stablecoin,
    address flanLP,
    address pyroFlanLP,
    uint256 acceptableHighestPrice,
    uint8 decimalPlaces
  ) external onlySuccessfulProposal {
    config.flanLPs[stablecoin] = flanLP;
    config.pyroFlanLPs[stablecoin] = pyroFlanLP;
    config.acceptableHighestPrice[stablecoin] = acceptableHighestPrice;
    config.decimalPlaces[stablecoin] = decimalPlaces;
  }

  /**
  *@notice takes in a stablecoin, mints flan and pyroFlan and pairs with stablecoin in a Uniswap Pair to generate liquidity
   *@param stablecoin Stablecoin with which to purchase
   *@param amount amount in stablecoin wei units.
   */
  function purchasePyroFlan(address stablecoin, uint256 amount) external {
    uint normalizedAmount = normalize(stablecoin, amount);
    address flanLP = config.flanLPs[stablecoin];
    address pyroFlanLP = config.pyroFlanLPs[stablecoin];
    require(flanLP != address(0) && pyroFlanLP != address(0), "BACKSTOP: configure stablecoin");

    uint256 balanceOfFlanBefore = IERC20(config.flan).balanceOf(flanLP);
    uint256 balanceOfStableBefore = IERC20(stablecoin).balanceOf(flanLP);
    uint256 priceBefore = (balanceOfFlanBefore * getMagnitude(stablecoin)) / balanceOfStableBefore;

    //Price tilt pairs and mint liquidity
    FlanLike(config.flan).mint(address(this), normalizedAmount / 2);
    IERC20(config.flan).transfer(flanLP, normalizedAmount / 4);
    IERC20(stablecoin).transferFrom(msg.sender, flanLP, amount / 2);

    UniPairLike(flanLP).mint(address(this));
    uint256 redeemRate = PyroTokenLike(config.pyroFlan).redeemRate();
    PyroTokenLike(config.pyroFlan).mint(pyroFlanLP, normalizedAmount / 4);
    redeemRate = PyroTokenLike(config.pyroFlan).redeemRate();
    redeemRate = PyroTokenLike(config.pyroFlan).redeemRate();
    IERC20(stablecoin).transferFrom(msg.sender, pyroFlanLP, amount / 2);
    UniPairLike(pyroFlanLP).mint(address(this));

    uint256 balanceOfFlan = IERC20(config.flan).balanceOf(flanLP);
    uint256 balanceOfStable = IERC20(stablecoin).balanceOf(flanLP);

    uint256 tiltedPrice = (balanceOfFlan * getMagnitude(stablecoin)) / balanceOfStable;
    require(tiltedPrice < config.acceptableHighestPrice[stablecoin], "BACKSTOP: potential price manipulation");
    uint256 growth = ((priceBefore - tiltedPrice) * 100) / priceBefore;

    uint256 flanToMint = (tiltedPrice * normalizedAmount) / (1 ether);

    //share some price tilting with the user to incentivize minting: The larger the purchase, the better the return
    uint256 premium = (flanToMint * (growth / 2)) / 100;

    FlanLike(config.flan).mint(address(this), flanToMint + premium);
    redeemRate = PyroTokenLike(config.pyroFlan).redeemRate();
    PyroTokenLike(config.pyroFlan).mint(msg.sender, flanToMint + premium);
    redeemRate = PyroTokenLike(config.pyroFlan).redeemRate();
  }

  function getMagnitude(address token) internal view returns (uint256) {
    uint256 places = config.decimalPlaces[token];
    return 10**places;
  }

  function normalize(address token, uint256 amount) internal view returns (uint256) {
    uint256 places = config.decimalPlaces[token];
    uint256 bump = 10**(18 - places);
    return amount * bump;
  }
}

/**@notice
Exotic tokens may cause Limbo to act unpredictably. The token type that inspired the writing of this class is the rebase token.
Since Limbo keeps track of balances, a token who's balance changes dynamically will fall our of sync with Limbo balances.
By using a proxy token, we can neutralize balance changes within limbo without changing Limbo code. If we were to force Limbo to dynamically account for changing 
balances then we might impose additional gas costs on all users. This scenario offloads additional gas consumption to stakers of rebase tokens only. From a security standpoint, arbitrary rebase logic
could open up unanticipated security holes. This proxy forces governance to neutralize such holes on a per token basis, allowing Limbo to adapt over time without requiring disruptive changes to the protocol.
*/
contract TokenProxyRegistry is Governable {
    struct TokenConfig{
        address baseToken;
        bool migrateBaseToBehodler;
    }
    mapping (address=>TokenConfig) public tokenProxy;

    constructor (address dao) Governable(dao){

    }

    function setProxy (address baseToken, address proxy, bool migrateBase) public onlySuccessfulProposal {
        tokenProxy[proxy] = TokenConfig(baseToken, migrateBase);
    }
}
/*
Contract: LIMBO is the main staking contract. It corresponds conceptually to Sushi's Masterchef and takes design inspiration from Masterchef.
Context: Limbo is a part of the Behodler ecosystem. All dapps within the Behodler ecosystem either support or are supported by the Behodler AMM.
Purpose: As a single contract store of liquidity, Behodler AMM requires new tokens be initiated with the a TVL equal to the average TVL of existing tokens. 
         In Behodler nomenclature, the total value of all tokens in the AMM is the total value bonded (TVB) and the value of individual tokens is the average value bonded (AVB). 
         The primary goal of Limbo is to raise capital for prospective AMM tokens in order to meet the AVB threshold. 
Secondary goals: since Limbo possesses staking mechanics, a secondary goal is to encourage lockup of protocol tokens.
Types of staking: Staked tokens are either for migration to Behodler or for lockup. The former pools are threshold and the latter are perpetual.
Primary incentive: users staking on Limbo receive the perpetually minted Flan token. 
Economics: When the staked value of a threshold token is migrated to Behodler, SCX is generated. The SCX is used via an external AMM such as Uniswap to prop up the liquidity and value of Flan. 
           Rather than being used to purchase Flan on the open market, the generated SCX is paired with newly minted Flan in a ratio that steers the price of Flan toward parity with Dai.
           This mechanism of pairing and steering the price through minting is known in Behodler as price tilting and effectively doubles the liquidity raised. For instance, suppose we list
           $10000 of a new token on Behodler. We then take $10000 worth of SCX and pair it with $10000 of newly minted Flan, adding $20000 of token liquidity to an external AMM. The extra 
           $10000 will form the price support for newly minted Flan which can be used to encourage future migrations.
           In addition to migration driven liquidity growth, Flan will be rewarded for token lockup. For lockup of Flan, the price support pressure of reduced circulating supply will provide additional 
           runway from which to mint more Flan. For external AMM pair contracts involving SCX or Pyrotokens, the lockup will raise liquidity for those pairs which will promote arbitrage trading of the pairs which will
           lead to additional burning of those tokens. For direct lockup of SCX, additional minting of SCX corresponds algorithmically to increased liquidity on Behodler and an increased SCX price. This raises the AVB of Behodler which creates 
           additional liquidity for Flan during the next migration. Flan therefore has 4 supporting vectors: SCX from migration, price support for SCX via lockup, price support via PyroFlan and indirect price support of Flan and SCX via trading on external pairs (automining).
Nomenclature: Since words like token are incredibly generic, we need to provide context through naming. Sticking to an overall metaphor, to paraphrase MakerDao documentation, reduces code smells.
          1. A token listed on Limbo is a Soul
          2. When a token lists on Behodler, we say the soul is crossing over. The event is a crossing.
          3. A token crosses over when the TVL on Limbo exceeds a threshold.
          4. Tokens which do not cross over such as existing tokens listed on Behodler or the protocol tokens are perpetual souls.

Security note: Since the migration steps generate value transfers between protocols, forced delays should be instituted to close any flash loan or dominant miner ttack vectors.

Basic staking incentives:
For both perpatual and threshold souls, a flan per second statistic is divided proportionately amongst the existing stakers.

Late stakers considerations:
Suppose you're the last person to stake on a threshold soul. That is, your stake takes the soul over the crossing threshold and the soul is locked.
In this instance, you would have earned no Flan, creating a declining incentive for stakers to arrive and in the extreme leading
to a situation of never crossing the threshold for any soul. This is a tragedy of the commons situation that leads to an overly 
inflated and essentially worthless Flan. We need a strategy to ameliorate this. The strategy needs to:
1. provide sufficient incentive for later arrivals.
2. Not punish early stakers and ideally reward them for being early.
3. Not disproportionately inflate the supply of flan.

Crossing incentives:
After a crossing, stakers are no longer able to withdraw their tokens as they'll now be sent to Behodler. They'll therefore need to be compensated for loss of tokens. 
Governance can calibrate two variables on a soul to encourage prospective stakers in threshold souls to breach the threshold:
1. Initial crossing bonus (ICB) is the Flan per token paid to all stakers and is a positive integer.
2. Crossing bonus delta (CBD) is the Flan per token for every second the soul is live. For instance suppose the CBD is 2. From the very first token staked to
the point at which the threshold was crossed, the soul records 10000 seconds passing. This amounts to 2*10000 = 20000 Flan per token.
The ICB and CBD are combined to forma Total Flan Per Token (TF) and the individual user balance is multiplied by TF. For instance, using the example above, suppose the ICB is 10 Flan per token.
This means the total Flan per token paid out is 10 + 20000 = 20010 Flan per token. If a user has 3 T staked, they receive 3*20010 = 60030 Flan as reward for having their T migrated to Behodler.
This is in addition to any Flan their received during the staking phase.
Note: CBD can be negative. This creates a situation where the initial bonus per token is at its highest when the staking round begins. 
For negative CBD, the intent is to create a sense of urgency amongst prospective stakers to push the pool over the threshold. For positive CBD, the intent is to draw marginal stakers into the soul in a desire to receive the crossing bonus while the opportunity still exists.
A negative CBD benefits from strong communal coordination. For instance, if the token listed has a large, active and well heeled community, a negative CBD might act as a rallying cry to ape in. A positive CBD benefits from individually uncoordinated motivations (classical market setting)
States of migration:
1. calibration
No staking/unstaking.
2. Staking
Staking/unstaking. If type is threshold, take threshold into account
3. WaitingToCross
Can claim rewards. Can't unstake.
4. CrossedOver
Injected into Behodler

Flash governance:
Since there might be many souls staking, we don't want to have to go through long-to-confirm proposals.
Instead, we want to have the opportunity to flash a governance action quickly. Flash governance happens in the span of 1 transaction.
To protect the community and the integrity of the DAO, all flash governance decisions must be accompanied by a large EYE deposit that presumably is more costly to give up
than the most profitable attack vector. The deposit is locked for a duration long enough for a long form burn proposal to be voted on.

The community can then decide if their governance action was in accord with the wellbeing of Limbo.
If it isn't, they can slash the deposit by betwen 1 and 100%. Flash gov can only move a variable some percentage per day.
Eg. suppose we vote on snapshot to raise the threshold for Sushi to 1200 Sushi from 1180, 1.69%. Some chosen community member flash sets the threshold to the new value.
A malicious flash staker then sets the threshold down to 1150. The community believes that the latter user was acting against the will of the community and a formal proposal is deployed onchain which slashes the user's staked EYE.
The community votes on the proposal and the EYE is slashed. After a fixed timeout, the EYE belonging to the original flash staker.

Rectangle of Fairness:
When new lquidity is added to Behodler, SCX is generated. The fully undiluted price of the new quantity of SCX far exceeds the value of the tokens migrated. Because of the dynamics of Behodler's bonding curve, the 
current value of the AVB is always equal to about 25 SCX. If the AVB increases, the increase shows up as in increase in the SCX price so that the 25 SCX metric still holds. For this reason, only 25 SCX is used to prop up
the liquidity of Flan. The surplus SCX generated is burnt. Because multiplying 25 SCX by the current market price gives us a value equal to the AVB and because we wish to strike a balance between boosting Flan and not over diluting the 
market with too much SCX, this value is known as the Rectangle of Fairness. While 25 SCX is the value of AVB, it's usually desirable to hold back a bit more than 25 for 2 reasons:
1. SCX burns on transfer so that after all open market operations are complete, we'd have less than 25 remaining. 
2. CPMMs such as Uniswap impose hyperbolic price slippage so that trying to withdraw the full balance of SCX results in paying an assymptotically high Flan price. As such we can deploy a bit more than 25 SCX per migrations without worrying about added dilution 
*/
enum SoulState {
  calibration,
  staking,
  waitingToCross,
  crossedOver
}
enum SoulType {
  uninitialized,
  threshold, //the default soul type is staked and when reaching a threshold, migrates to Behodler
  perpetual //the type of staking pool most people are familiar with.
}

/*
Error string legend:
token not recognized as valid soul.	           E1
invalid state	                                 E2
unstaking locked	                             E3
balance exceeded	                             E4
bonus already claimed.	                       E5
crossing bonus arithmetic invariant.	         E6
token accounted for.	                         E7
burning excess SCX failed.	                   E8
Invocation reward failed.	                     E9
only threshold souls can be migrated           EB
not enough time between crossing and migration EC
bonus must be positive                         ED
Unauthorized call                              EE
Protocol disabled                              EF
Reserve divergence tolerance exceeded          EG
not enough time between reserve stamps         EH
Minimum APY only applicable to threshold souls EI
Governance action failed.                      EJ
Access Denied                                  EK
ERC20 Transfer Failed                          EL
Incorrect SCX transfer to AMMHelper            EM
*/

struct Soul {
  uint256 lastRewardTimestamp;
  uint256 accumulatedFlanPerShare;
  uint256 crossingThreshold; //the value at which this soul is elligible to cross over to Behodler
  SoulType soulType;
  SoulState state;
  uint256 flanPerSecond; // fps: we use a helper function to convert min APY into fps
}

struct CrossingParameters {
  uint256 stakingBeginsTimestamp; //to calculate bonus
  uint256 stakingEndsTimestamp;
  int256 crossingBonusDelta; //change in teraFlanPerToken per second
  uint256 initialCrossingBonus; //measured in teraFlanPerToken
  bool burnable;
}

struct CrossingConfig {
  address behodler;
  uint256 SCX_fee;
  uint256 migrationInvocationReward; //calling migrate is expensive. The caller should be rewarded in Flan.
  uint256 crossingMigrationDelay; // this ensures that if Flan is successfully attacked, governance will have time to lock Limbo and prevent bogus migrations
  address morgothPower;
  address angband;
  address ammHelper;
  uint16 rectangleOfFairnessInflationFactor; //0-100: if the community finds the requirement to be too strict, they can inflate how much SCX to hold back
}

library SoulLib {
  function set(
    Soul storage soul,
    uint256 crossingThreshold,
    uint256 soulType,
    uint256 state,
    uint256 fps
  ) external {
    soul.crossingThreshold = crossingThreshold;
    soul.flanPerSecond = fps;
    soul.state = SoulState(state);
    soul.soulType = SoulType(soulType);
  }
}

library CrossingLib {
  function set(
    CrossingParameters storage params,
    FlashGovernanceArbiterLike flashGoverner,
    Soul storage soul,
    uint256 initialCrossingBonus,
    int256 crossingBonusDelta,
    bool burnable,
    uint256 crossingThreshold
  ) external {
    flashGoverner.enforceTolerance(initialCrossingBonus, params.initialCrossingBonus);
    flashGoverner.enforceToleranceInt(crossingBonusDelta, params.crossingBonusDelta);

    params.initialCrossingBonus = initialCrossingBonus;
    params.crossingBonusDelta = crossingBonusDelta;
    params.burnable = burnable;

    flashGoverner.enforceTolerance(crossingThreshold, soul.crossingThreshold);
    soul.crossingThreshold = crossingThreshold;
  }
}

library MigrationLib {
  function migrate(
    address token,
    LimboAddTokenToBehodlerPowerLike power,
    CrossingParameters memory crossingParams,
    CrossingConfig memory crossingConfig,
    FlanLike flan,
    uint256 RectangleOfFairness,
    Soul storage soul
  ) external returns (uint256, uint256) {
    power.parameterize(token, crossingParams.burnable);

    //invoke Angband execute on power that migrates token type to Behodler
    uint256 tokenBalance = IERC20(token).balanceOf(address(this));
    IERC20(token).transfer(address(crossingConfig.morgothPower), tokenBalance);
    AngbandLike(crossingConfig.angband).executePower(address(crossingConfig.morgothPower));

    uint256 scxMinted = IERC20(address(crossingConfig.behodler)).balanceOf(address(this));

    uint256 adjustedRectangle = ((crossingConfig.rectangleOfFairnessInflationFactor) * RectangleOfFairness) / 100;

    //for top up or exotic high value migrations.
    if (scxMinted <= adjustedRectangle) {
      adjustedRectangle = scxMinted / 2;
    }

    //burn SCX - rectangle
    uint256 excessSCX = scxMinted - adjustedRectangle;
    require(BehodlerLike(crossingConfig.behodler).burn(excessSCX), "E8");

    //use remaining scx to buy flan and pool it on an external AMM
    IERC20(crossingConfig.behodler).transfer(crossingConfig.ammHelper, adjustedRectangle);
    uint256 lpMinted = AMMHelper(crossingConfig.ammHelper).stabilizeFlan(adjustedRectangle);

    //reward caller and update soul state
    require(flan.mint(msg.sender, crossingConfig.migrationInvocationReward), "E9");
    soul.state = SoulState.crossedOver;
    return (tokenBalance, lpMinted);
  }
}

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
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
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
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: value }(data);
        return _verifyCallResult(success, returndata, errorMessage);
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
    function functionStaticCall(address target, bytes memory data, string memory errorMessage) internal view returns (bytes memory) {
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
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
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
library SafeERC20 {
    using Address for address;

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
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
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
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}
/// @title Limbo
/// @author Justin Goro
/// @notice Tokens are either staked for locking (perpetual) or for migration to the Behodler AMM (threshold).
/// @dev The governance functions are initially unguarded to allow the deploying dev to rapidly set up without having to endure governance imposed time limits on proposals. Ending the config period is a irreversible action.
contract Limbo is Governable {
  using SafeERC20 for IERC20;
  using SoulLib for Soul;
  using MigrationLib for address;
  using CrossingLib for CrossingParameters;

  event SoulUpdated(address soul, uint256 fps);
  event Staked(address staker, address soul, uint256 amount);
  event Unstaked(address staker, address soul, uint256 amount);
  event TokenListed(address token, uint256 amount, uint256 scxfln_LP_minted);

  event ClaimedReward(address staker, address soul, uint256 index, uint256 amount);

  event BonusPaid(address token, uint256 index, address recipient, uint256 bonus);

  struct User {
    uint256 stakedAmount;
    uint256 rewardDebt;
    bool bonusPaid;
  }

  uint256 constant TERA = 1E12;
  uint256 constant RectangleOfFairness = 30 ether; //MP = 1/t. Rect = tMP = t(1/t) = 1. 25 is the result of scaling factors on Behodler.
  bool protocolEnabled = true;

  ///@notice protocol settings for migrating threshold tokens to Behodler
  CrossingConfig public crossingConfig;

  ///@notice Since a token can be listed more than once on Behodler, we index each listing to separate the rewards from each staking event.
  ///@dev tokenAddress->index->stakingInfo
  mapping(address => mapping(uint256 => Soul)) public souls;

  ///@notice Each token maintains its own index to allow Limbo to keep rewards for each staking event separate
  mapping(address => uint256) public latestIndex;

  ///@dev tokenAddress->userAddress->soulIndex->Userinfo
  mapping(address => mapping(address => mapping(uint256 => User))) public userInfo;
  ///@dev token->index->data
  mapping(address => mapping(uint256 => CrossingParameters)) public tokenCrossingParameters;

  ///@dev soul->owner->unstaker->amount
  mapping(address => mapping(address => mapping(address => uint256))) unstakeApproval;
  FlanLike Flan;

  modifier enabled() {
    require(protocolEnabled, "EF");
    _;
  }

  ///@notice helper function for approximating a total dollar value APY for a threshold soul.
  ///@param token threshold soul
  ///@param desiredAPY because values may be out of sync with the market, this function can only ever approximate an APY
  ///@param daiThreshold user can select a Behodler AVB in Dai. 0 indicates the migration oracle value for AVB should be used.
  function attemptToTargetAPY(
    address token,
    uint256 desiredAPY,
    uint256 daiThreshold
  ) public governanceApproved(false) {
    Soul storage soul = currentSoul(token);
    require(soul.soulType == SoulType.threshold, "EI");
    uint256 fps = AMMHelper(crossingConfig.ammHelper).minAPY_to_FPS(desiredAPY, daiThreshold);
    flashGoverner.enforceTolerance(soul.flanPerSecond, fps);
    soul.flanPerSecond = fps;
  }

  ///@notice refreshes current state of soul.
  function updateSoul(address token) public {
    Soul storage s = currentSoul(token);
    updateSoul(token, s);
  }

  function updateSoul(address token, Soul storage soul) internal {
    require(soul.soulType != SoulType.uninitialized, "E1");
    uint256 finalTimeStamp = block.timestamp;
    if (soul.state != SoulState.staking) {
      finalTimeStamp = tokenCrossingParameters[token][latestIndex[token]].stakingEndsTimestamp;
    }
    uint256 balance = IERC20(token).balanceOf(address(this));

    if (balance > 0) {
      uint256 flanReward = (finalTimeStamp - soul.lastRewardTimestamp) * soul.flanPerSecond;

      soul.accumulatedFlanPerShare = soul.accumulatedFlanPerShare + ((flanReward * TERA) / balance);
    }
    soul.lastRewardTimestamp = finalTimeStamp;
  }

  constructor(address flan, address limboDAO) Governable(limboDAO) {
    Flan = FlanLike(flan);
  }

  ///@notice configure global migration settings such as the address of Behodler and the minumum delay between end of staking and migration
  function configureCrossingConfig(
    address behodler,
    address angband,
    address ammHelper,
    address morgothPower,
    uint256 migrationInvocationReward,
    uint256 crossingMigrationDelay,
    uint16 rectInflationFactor //0 to 100
  ) public onlySuccessfulProposal {
    crossingConfig.migrationInvocationReward = migrationInvocationReward * (1 ether);
    crossingConfig.behodler = behodler;
    crossingConfig.crossingMigrationDelay = crossingMigrationDelay;
    crossingConfig.angband = angband;
    crossingConfig.ammHelper = ammHelper;
    crossingConfig.morgothPower = morgothPower;
    require(rectInflationFactor <= 10000, "E6");
    crossingConfig.rectangleOfFairnessInflationFactor = rectInflationFactor;
  }

  ///@notice if an exploit in any part of Limbo or its souls is detected, anyone with sufficient EYE balance can disable the protocol instantly
  function disableProtocol() public governanceApproved(true) {
    protocolEnabled = false;
  }

  ///@notice Once disabled, the only way to reenable is via a formal proposal. This forces the community to deliberate on the legitimacy of the disabling that lead to this state. A malicious call to disable can have its EYE slashed.
  function enableProtocol() public onlySuccessfulProposal {
    protocolEnabled = true;
  }

  ///@notice Governance function for rapidly calibrating a soul. Useful for responding to large price movements quickly
  ///@param token Soul to calibrate
  ///@param initialCrossingBonus Of the crossing bonus flan payout, this represents the fixed Flan per token component
  ///@param crossingBonusDelta Of the crossing bonus flan payout, this represents the payout per flan per second that the soul is in staking state
  ///@param fps Flan Per Second staked.
  function adjustSoul(
    address token,
    uint256 initialCrossingBonus,
    int256 crossingBonusDelta,
    uint256 fps
  ) public governanceApproved(false) {
    Soul storage soul = currentSoul(token);
    flashGoverner.enforceTolerance(soul.flanPerSecond, fps);
    soul.flanPerSecond = fps;

    CrossingParameters storage params = tokenCrossingParameters[token][latestIndex[token]];

    flashGoverner.enforceTolerance(params.initialCrossingBonus, initialCrossingBonus);
    flashGoverner.enforceTolerance(
      uint256(params.crossingBonusDelta < 0 ? params.crossingBonusDelta * -1 : params.crossingBonusDelta),
      uint256(crossingBonusDelta < 0 ? crossingBonusDelta * -1 : crossingBonusDelta)
    );

    params.initialCrossingBonus = initialCrossingBonus;
    params.crossingBonusDelta = crossingBonusDelta;
  }

  ///@notice Configuration of soul through formal proposal. Should only be called infrequently.
  ///@dev Unlike with flash governance, variable movements are unguarded
  ///@param crossingThreshold The token balance on Behodler that triggers the soul to enter into waitingToCross state
  ///@param soulType Indicates whether the soul is perpetual or threshold
  ///@param state a threshold soul can be either staking, waitingToCross, or CrossedOver. Both soul types can be in calibration state.
  ///@param index a token could be initially liste as a threshold soul and then later added as perpetual. An index helps distinguish these two events so that user late to claim rewards have no artificial time constraints imposed on their behaviour
  function configureSoul(
    address token,
    uint256 crossingThreshold,
    uint256 soulType,
    uint256 state,
    uint256 index,
    uint256 fps
  ) public onlySoulUpdateProposal {
    {
      latestIndex[token] = index > latestIndex[token] ? latestIndex[token] + 1 : latestIndex[token];

      Soul storage soul = currentSoul(token);
      bool fallingBack = soul.state != SoulState.calibration && SoulState(state) == SoulState.calibration;
      soul.set(crossingThreshold, soulType, state, fps);
      if (SoulState(state) == SoulState.staking) {
        tokenCrossingParameters[token][latestIndex[token]].stakingBeginsTimestamp = block.timestamp;
      }
      if(fallingBack){
         tokenCrossingParameters[token][latestIndex[token]].stakingEndsTimestamp = block.timestamp;
      }
    }
    emit SoulUpdated(token, fps);
  }

  ///@notice We need to know how to handle threshold souls at the point of crossing
  ///@param token The soul to configure
  ///@param initialCrossingBonus Of the crossing bonus flan payout, this represents the fixed Flan per token component
  ///@param crossingBonusDelta Of the crossing bonus flan payout, this represents the payout per flan per second that the soul is in staking state
  ///@param burnable For listing on Behodler, is this token going to burn on trade or does it get its own Pyrotoken
  ///@param crossingThreshold The token balance on Behodler that triggers the soul to enter into waitingToCross state
  function configureCrossingParameters(
    address token,
    uint256 initialCrossingBonus,
    int256 crossingBonusDelta,
    bool burnable,
    uint256 crossingThreshold
  ) public governanceApproved(false) {
    CrossingParameters storage params = tokenCrossingParameters[token][latestIndex[token]];
    Soul storage soul = currentSoul(token);
    params.set(flashGoverner, soul, initialCrossingBonus, crossingBonusDelta, burnable, crossingThreshold);
  }

  ///@notice User facing stake function for handling both types of souls
  ///@param token The soul to stake
  ///@param amount The amount of tokens to stake
  /**@dev Can handle fee on transfer tokens but for more exotic tokens such as rebase tokens, use a proxy wrapper. See the TokenProxyRegistry for logistics.
   *The purpose of balance checking before and after transfer of tokens is to account for fee-on-transfer discrepencies so that tokens like SCX can be listed without inducing
   *broken states. The community is encouraged to use proxy wrappers for tokens which may open up Limbo or Beholer exploit vulnerabilities.
   *Security enforcement of tokens listed on Limbo is offloaded to governance so that Limbo isn't required to anticipate every attack vector.
   */
  function stake(address token, uint256 amount) public enabled {
    Soul storage soul = currentSoul(token);
    require(soul.state == SoulState.staking, "E2");
    updateSoul(token, soul);
    uint256 currentIndex = latestIndex[token];
    User storage user = userInfo[token][msg.sender][currentIndex];
    if (amount > 0) {
      //dish out accumulated rewards.
      uint256 pending = getPending(user, soul);
      if (pending > 0) {
        Flan.mint(msg.sender, pending);
      }

      //Balance checking accounts for FOT discrepencies
      uint256 oldBalance = IERC20(token).balanceOf(address(this));
      IERC20(token).safeTransferFrom(msg.sender, address(this), amount);
      uint256 newBalance = IERC20(token).balanceOf(address(this));

      user.stakedAmount = user.stakedAmount + newBalance - oldBalance; //adding true difference accounts for FOT tokens
      if (soul.soulType == SoulType.threshold && newBalance > soul.crossingThreshold) {
        soul.state = SoulState.waitingToCross;
        tokenCrossingParameters[token][latestIndex[token]].stakingEndsTimestamp = block.timestamp;
      }
    }

    user.rewardDebt = (user.stakedAmount * soul.accumulatedFlanPerShare) / TERA;
    emit Staked(msg.sender, token, user.stakedAmount);
  }

  ///@notice User facing unstake function for handling both types of souls. For threshold souls, can only be called during staking phase.
  ///@param token The soul to unstake
  ///@param amount The amount of tokens to unstake
  function unstake(address token, uint256 amount) public enabled {
    _unstake(token, amount, msg.sender, msg.sender);
  }

  ///@notice Allows for Limbo to be upgraded 1 user at a time without introducing a system wide security risk. Anticipates moving tokens to Limbo2 (wen Limbo2??)
  ///@dev similar to ERC20.transferFrom, this function allows a user to approve an upgrade contract migrate their staked tokens safely.
  function unstakeFor(
    address token,
    uint256 amount,
    address holder
  ) public {
    _unstake(token, amount, msg.sender, holder);
  }

  function _unstake(
    address token,
    uint256 amount,
    address unstaker,
    address holder
  ) internal {
    if (unstaker != holder) {
      unstakeApproval[token][holder][unstaker] -= amount;
    }
    Soul storage soul = currentSoul(token);
    require(soul.state == SoulState.calibration || soul.state == SoulState.staking, "E2");
    updateSoul(token, soul);
    User storage user = userInfo[token][holder][latestIndex[token]];
    require(user.stakedAmount >= amount, "E4");

    uint256 pending = getPending(user, soul);

    if (pending > 0 && amount > 0) {
      user.stakedAmount = user.stakedAmount - amount;
      IERC20(token).safeTransfer(address(unstaker), amount);
      rewardAdjustDebt(unstaker, pending, soul.accumulatedFlanPerShare, user);
      emit Unstaked(unstaker, token, amount);
    }
  }

  ///@notice accumulated flan rewards from staking can be claimed
  ///@param token The soul for which to claim rewards
  ///@param index souls no longer listed may still have unclaimed rewards.
  function claimReward(address token, uint256 index) public enabled {
    Soul storage soul = souls[token][index];
    updateSoul(token, soul);
    User storage user = userInfo[token][msg.sender][index];

    uint256 pending = getPending(user, soul);

    if (pending > 0) {
      rewardAdjustDebt(msg.sender, pending, soul.accumulatedFlanPerShare, user);
      emit ClaimedReward(msg.sender, token, index, pending);
    }
  }

  ///@notice for threshold souls only, claiming the compensation for migration tokens known as the Crossing Bonus
  ///@param token The soul for which to claim rewards
  ///@param index souls no longer listed may still have an unclaimed bonus.
  ///@dev The tera factor is to handle fixed point calculations without significant loss of precision.
  function claimBonus(address token, uint256 index) public enabled {
    Soul storage soul = souls[token][index];
    CrossingParameters storage crossing = tokenCrossingParameters[token][index];
    require(soul.state == SoulState.crossedOver || soul.state == SoulState.waitingToCross, "E2");

    User storage user = userInfo[token][msg.sender][index];
    require(!user.bonusPaid, "E5");
    user.bonusPaid = true;
    int256 accumulatedFlanPerTeraToken = crossing.crossingBonusDelta *
      int256(crossing.stakingEndsTimestamp - crossing.stakingBeginsTimestamp);

    //assert signs are the same
    require(accumulatedFlanPerTeraToken * crossing.crossingBonusDelta >= 0, "E6");

    int256 finalFlanPerTeraToken = int256(crossing.initialCrossingBonus) + accumulatedFlanPerTeraToken;

    uint256 flanBonus = 0;
    require(finalFlanPerTeraToken > 0, "ED");

    flanBonus = uint256((int256(user.stakedAmount) * finalFlanPerTeraToken)) / TERA;
    Flan.mint(msg.sender, flanBonus);

    emit BonusPaid(token, index, msg.sender, flanBonus);
  }

  /**@notice some tokens may be sent to Limbo by mistake or unhandled in some manner. For instance, if a Pooltogether token is listed and Limbo wins,
  the reward token may not have relevance on Limbo. If the token exists as a pair with Flan on the external AMM
  this function buys Flan from the AMM and burns it. A small percentage of the purchased Flan is sent to the caller to incentivize 
  flushing Limbo of stuck tokens. A secondary incentive exists to create new pairs for Flan.
  */
  function claimSecondaryRewards(address token) public {
    SoulState state = currentSoul(token).state;
    require(state == SoulState.calibration || state == SoulState.crossedOver, "E7");
    uint256 balance = IERC20(token).balanceOf(address(this));
    IERC20(token).safeTransfer(crossingConfig.ammHelper, balance);
    AMMHelper(crossingConfig.ammHelper).buyFlanAndBurn(token, balance, msg.sender);
  }

  ///@notice migrates threshold token from Limbo to Behodler and orchestrates Flan boosting mechanics. Callers of this function are rewared to compensate for gas expenditure
  /**@dev this function depends on a Morgoth Power. For those unfamiliar, a power is similar to a spell on other DAOs. Morgoth owns Behodler and so the only way to list
   * a token on Behodler is via a Morgoth Power. Permission mapping is handled on Morgoth side. Calling this function assumes that the power has been calibrated and than Limbo has been granted
   * permission on Morgoth to execute migrations to Behodler. The other big depenency is the AMM helper which contains the bulk of the migration logic.
   */
  function migrate(address token) public enabled {
    Soul storage soul = currentSoul(token);
    require(soul.soulType == SoulType.threshold, "EB");
    require(soul.state == SoulState.waitingToCross, "E2");
    require(
      block.timestamp - tokenCrossingParameters[token][latestIndex[token]].stakingEndsTimestamp >
        crossingConfig.crossingMigrationDelay,
      "EC"
    );
    (uint256 tokenBalance, uint256 lpMinted) = token.migrate(
      LimboAddTokenToBehodlerPowerLike(crossingConfig.morgothPower),
      tokenCrossingParameters[token][latestIndex[token]],
      crossingConfig,
      Flan,
      RectangleOfFairness,
      soul
    );
    emit TokenListed(token, tokenBalance, lpMinted);
  }

  ///@notice analogous to ERC20 approve, this function gives third party contracts permission to migrate token balances on Limbo. Useful for both upgrades and third party integrations into Limbo
  function approveUnstake(
    address soul,
    address unstaker,
    uint256 amount
  ) external {
    unstakeApproval[soul][msg.sender][unstaker] = amount; //soul->owner->unstaker->amount
  }

  function rewardAdjustDebt(
    address recipient,
    uint256 pending,
    uint256 accumulatedFlanPerShare,
    User storage user
  ) internal {
    Flan.mint(recipient, pending);
    user.rewardDebt = (user.stakedAmount * accumulatedFlanPerShare) / TERA;
  }

  function currentSoul(address token) internal view returns (Soul storage) {
    return souls[token][latestIndex[token]];
  }

  function getPending(User memory user, Soul memory soul) internal pure returns (uint256) {
    return ((user.stakedAmount * soul.accumulatedFlanPerShare) / TERA) - user.rewardDebt;
  }
}

contract BlackHole {}

///@Title Uniswap V2 helper for managing Flan liquidity on Uniswap V2, Sushiswap and any other compatible AMM
///@author Justin Goro
/**@notice Flan liquidity is boosted on Uniswap (or Sushiswap) via open market operations at the point of a token migration.
  * UniswapHelper handles all the mechanics as well managing a just-in-time (Justin Time?) oracle
 */
contract UniswapHelper is Governable, AMMHelper {
  address limbo;

  struct UniVARS {
    UniPairLike Flan_SCX_tokenPair;
    address behodler;
    address blackHole;
    address flan;
    uint256 divergenceTolerance;
    uint256 minQuoteWaitDuration;
    address DAI;
    uint8 precision; // behodler uses a binary search. The higher this number, the more precise
    IUniswapV2Factory factory;
    uint8 priceBoostOvershoot; //percentage (0-100) for which the price must be overcorrected when strengthened to account for other AMMs
  }

  struct FlanQuote {
    uint256 DaiScxSpotPrice;
    uint256 DaiBalanceOnBehodler;
    uint256 blockProduced;
  }

  /**@dev the Dai SCX price and the Dai balance on Behodler are both sampled twice before a migration can occur. 
  * The two samples have to be spaced a minimum duration and have to be the same values (within an error threshold). The objective here is to make price manipulation untenably expensive for an attacker
  * so that the mining power expended (or the opportunity cost of eth staked) far exceeds the benefit to manipulating Limbo.
  * The assumption of price stability isn't a bug because migrations aren't required to happen frequently. Instead if natural price drift occurs for non malicious reasons,
  * the migration can be reattempted until a period of sufficient calm allows for migration. If a malicious actor injects volatility in order to prevent migration, by the principle
  * of antifragility, they're doing the entire Ethereum ecosystem a service at their own expense.
  */
  FlanQuote[2] public latestFlanQuotes; //0 is latest

  UniVARS VARS;

  //not sure why codebases don't use keyword ether but I'm reluctant to entirely part with that tradition for now.
  uint256 constant EXA = 1e18;

  //needs to be updated for future Martian, Lunar and Venusian blockchains although I suspect Lunar colonies will be very Terracentric because of low time lag.
  uint256 constant year = (1 days * 365);

  /*
    instead of relying on oracles, we simply require snapshots of important 
    prices to be taken at intervals far enough apart.
    If an attacker wishes to overstate or understate a price through market manipulation,
    they'd have to keep it out of equilibrium over the span of the two snapshots or they'd
    have to time the manipulation to happen as the snapshots occur. As a miner,
    they could do this through transaction ordering but they'd have to win two blocks at precise moments
    which is statistically highly unlikely. 
    The snapshot enforcement can be hindered by false negatives. Natural price variation, for instance, but the cost
    of this is just having to snapshot again when the market is calmer. Since migration is not not time sensitive,
    this is a cost worth bearing.
    */
  modifier ensurePriceStability() {
    _ensurePriceStability();
    _;
  }

  modifier onlyLimbo() {
    require(msg.sender == limbo);
    _;
  }

  constructor(address _limbo, address limboDAO) Governable(limboDAO) {
    limbo = _limbo;
    VARS.blackHole = address(new BlackHole());
    VARS.factory = IUniswapV2Factory(address(0x5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f));
    VARS.DAI = 0x6B175474E89094C44Da98b954EedeAC495271d0F;
  }

  ///@notice LP tokens minted during migration are discarded.
  function blackHole() public view returns (address) {
    return VARS.blackHole;
  }

  ///@notice Uniswap factory contract
  function setFactory(address factory) public {
    require(block.chainid != 1, "Uniswap factory hardcoded on mainnet");
    VARS.factory = IUniswapV2Factory(factory);
  }

  ///@dev Only for testing: On mainnet Dai has a fixed address.
  function setDAI(address dai) public {
    require(block.chainid != 1, "DAI hardcoded on mainnet");
    VARS.DAI = dai;
  }

  ///@notice main configuration function.
  ///@dev We prefer to use configuration functions rather than a constructor for a number of reasons.
  ///@param _limbo Limbo contract
  ///@param FlanSCXPair The Uniswap flan/SCX pair
  ///@param behodler Behodler AMM
  ///@param flan The flan token
  ///@param divergenceTolerance The amount of price difference between the two quotes that is tolerated before a migration is attempted 
  ///@param minQuoteWaitDuration The minimum duration between the sampling of oracle data used for migration
  ///@param precision In order to query the tokens redeemed by a quantity of SCX, Behodler performs a binary search. Precision refers to the max iterations of the search.
  ///@param priceBoostOvershoot Flan targets parity with Dai. If we set Flan to equal Dai then between migrations, it will always be below Dai. Overshoot gives us some runway by intentionally "overshooting" the price
  function configure(
    address _limbo,
    address FlanSCXPair,
    address behodler,
    address flan,
    uint256 divergenceTolerance,
    uint256 minQuoteWaitDuration,
    uint8 precision,
    uint8 priceBoostOvershoot
  ) public onlySuccessfulProposal {
    limbo = _limbo;
    VARS.Flan_SCX_tokenPair = UniPairLike(FlanSCXPair);
    VARS.behodler = behodler;
    VARS.flan = flan;
    require(divergenceTolerance >= 100, "Divergence of 100 is parity");
    VARS.divergenceTolerance = divergenceTolerance;
    VARS.minQuoteWaitDuration = minQuoteWaitDuration;
    VARS.DAI = 0x6B175474E89094C44Da98b954EedeAC495271d0F;
    VARS.precision = precision == 0 ? precision : precision;
    require(priceBoostOvershoot < 100, "Set overshoot to number between 1 and 100.");
    VARS.priceBoostOvershoot = priceBoostOvershoot;
  }

  ///@notice Samples the two values required for migration. Must be called twice before migration can occur.
  function generateFLNQuote() public override {
    latestFlanQuotes[1] = latestFlanQuotes[0];
    (
      latestFlanQuotes[0].DaiScxSpotPrice,
      latestFlanQuotes[0].DaiBalanceOnBehodler
    ) = getLatestFLNQuote();
    latestFlanQuotes[0].blockProduced = block.number;
  }

  function getLatestFLNQuote() internal view returns (uint256 dai_scx, uint256 daiBalanceOnBehodler) {
    uint256 daiToRelease = BehodlerLike(VARS.behodler).withdrawLiquidityFindSCX(
      VARS.DAI,
      10000,
      1 ether,
      VARS.precision
    );
    dai_scx = (daiToRelease * EXA) / (1 ether);

    daiBalanceOnBehodler = IERC20(VARS.DAI).balanceOf(VARS.behodler);
  }

  ///@notice When tokens are migrated to Behodler, SCX is generated. This SCX is used to boost Flan liquidity and nudge the price of Flan back to parity with Dai
  ///@param rectangleOfFairness refers to the quantity of SCX held back to be used for open market Flan stabilizing operations
  ///@dev makes use of price tilting. Be sure to understand the concept of price tilting before trying to understand the final if statement.
  function stabilizeFlan(uint256 rectangleOfFairness) public override onlyLimbo ensurePriceStability returns (uint256 lpMinted) {
    uint256 localSCXBalance = IERC20(VARS.behodler).balanceOf(address(this));

    //SCX transfers incur a 2% fee. Checking that SCX balance === rectangleOfFairness must take this into account.
    //Note that for hardcoded values, this contract can be upgraded through governance so we're not ignoring potential Behodler configuration changes
    require((localSCXBalance * 100) / rectangleOfFairness == 98, "EM");
    rectangleOfFairness = localSCXBalance;

    //get DAI per scx
    uint256 existingSCXBalanceOnLP = IERC20(VARS.behodler).balanceOf(address(VARS.Flan_SCX_tokenPair));
    uint256 finalSCXBalanceOnLP = existingSCXBalanceOnLP + rectangleOfFairness;

    //the DAI value of SCX is the final quantity of Flan because we want Flan to hit parity with Dai.
    uint256 DesiredFinalFlanOnLP = ((finalSCXBalanceOnLP * latestFlanQuotes[0].DaiScxSpotPrice) / EXA);
    address pair = address(VARS.Flan_SCX_tokenPair);
    uint256 existingFlanOnLP = IERC20(VARS.flan).balanceOf(pair);

    if (existingFlanOnLP < DesiredFinalFlanOnLP) {
      uint256 flanToMint = ((DesiredFinalFlanOnLP - existingFlanOnLP) * (100 - VARS.priceBoostOvershoot)) / 100;

      flanToMint = flanToMint == 0 ? DesiredFinalFlanOnLP - existingFlanOnLP : flanToMint;
      FlanLike(VARS.flan).mint(pair, flanToMint);
      IERC20(VARS.behodler).transfer(pair, rectangleOfFairness);
      {
        lpMinted = VARS.Flan_SCX_tokenPair.mint(VARS.blackHole);
      }
    } else {
      uint256 minFlan = existingFlanOnLP / VARS.Flan_SCX_tokenPair.totalSupply();

      FlanLike(VARS.flan).mint(pair, minFlan + 2);
      IERC20(VARS.behodler).transfer(pair, rectangleOfFairness);
      lpMinted = VARS.Flan_SCX_tokenPair.mint(VARS.blackHole);
    }
    //Don't allow future migrations to piggy back off the data collected by recent migrations. Forces attackers to face the same cryptoeconomic barriers each time.
    _zeroOutQuotes();
  }

  ///@notice helper function for converting a desired APY into a flan per second (FPS) statistic
  ///@param minAPY Here APY refers to the dollar value of flan relative to the dollar value of the threshold
  ///@param daiThreshold The DAI value of the target threshold to list on Behodler. Threshold is an approximation of the AVB on Behodler
  function minAPY_to_FPS(
    uint256 minAPY, //divide by 10000 to get percentage
    uint256 daiThreshold
  ) public override view ensurePriceStability returns (uint256 fps) {
    daiThreshold = daiThreshold == 0 ? latestFlanQuotes[0].DaiBalanceOnBehodler : daiThreshold;
    // console.log("DAI threshold %s", daiThreshold);
    uint256 returnOnThreshold = (minAPY * daiThreshold) / 1e4;
    fps = returnOnThreshold / (year);
  }

  ///@notice Buys Flan with a specified token, apportions 1% of the purchased Flan to the caller and burns the rest.
  ///@param inputToken The token used to buy Flan
  ///@param amount amount of input token used to buy Flan
  ///@param recipient receives 1% of Flan purchased as an incentive to call this function regularly
  ///@dev Assumes a pair for Flan/InputToken exists on Uniswap
  function buyFlanAndBurn(
    address inputToken,
    uint256 amount,
    address recipient
  ) public override {
    address pair = VARS.factory.getPair(inputToken, VARS.flan);

    uint256 flanBalance = IERC20(VARS.flan).balanceOf(pair);
    uint256 inputBalance = IERC20(inputToken).balanceOf(pair);

    uint256 amountOut = getAmountOut(amount, inputBalance, flanBalance);
    uint256 amount0Out = inputToken < VARS.flan ? 0 : amountOut;
    uint256 amount1Out = inputToken < VARS.flan ? amountOut : 0;
    IERC20(inputToken).transfer(pair, amount);
    UniPairLike(pair).swap(amount0Out, amount1Out, address(this), "");
    uint256 reward = (amountOut / 100);
    ERC20Burnable(VARS.flan).transfer(recipient, reward);
    ERC20Burnable(VARS.flan).burn(amountOut - reward);
  }

  function getAmountOut(
    uint256 amountIn,
    uint256 reserveIn,
    uint256 reserveOut
  ) internal pure returns (uint256 amountOut) {
    uint256 amountInWithFee = amountIn * 997;
    uint256 numerator = amountInWithFee * reserveOut;
    uint256 denominator = reserveIn * 1000 + amountInWithFee;
    amountOut = numerator / denominator;
  }

  function getAmountIn(
    uint256 amountOut,
    uint256 reserveIn,
    uint256 reserveOut
  ) internal pure returns (uint256 amountIn) {
    uint256 numerator = reserveIn * amountOut * 1000;
    uint256 denominator = (reserveOut - amountOut) * 997;
    amountIn = (numerator / denominator) + 1;
  }

  function _zeroOutQuotes() internal {
    delete latestFlanQuotes[0];
    delete latestFlanQuotes[1];
  }

  //the purpose of the divergence code is to bring the robustness of a good oracle without requiring an oracle
  function _ensurePriceStability() internal view {
    FlanQuote[2] memory localFlanQuotes; //save gas
    localFlanQuotes[0] = latestFlanQuotes[0];
    localFlanQuotes[1] = latestFlanQuotes[1];

    uint256 daiSCXSpotPriceDivergence = localFlanQuotes[0].DaiScxSpotPrice > localFlanQuotes[1].DaiScxSpotPrice
      ? (localFlanQuotes[0].DaiScxSpotPrice * 100) / localFlanQuotes[1].DaiScxSpotPrice
      : (localFlanQuotes[1].DaiScxSpotPrice * 100) / localFlanQuotes[0].DaiScxSpotPrice;

    uint256 daiBalanceDivergence = localFlanQuotes[0].DaiBalanceOnBehodler > localFlanQuotes[1].DaiBalanceOnBehodler
      ? (localFlanQuotes[0].DaiBalanceOnBehodler * 100) / localFlanQuotes[1].DaiBalanceOnBehodler
      : (localFlanQuotes[1].DaiBalanceOnBehodler * 100) / localFlanQuotes[0].DaiBalanceOnBehodler;

    // console.log("dai balance divergence %s", daiBalanceDivergence);
    require(
      daiSCXSpotPriceDivergence < VARS.divergenceTolerance && daiBalanceDivergence < VARS.divergenceTolerance,
      "EG"
    );

    require(
      localFlanQuotes[0].blockProduced - localFlanQuotes[1].blockProduced > VARS.minQuoteWaitDuration &&
        localFlanQuotes[1].blockProduced > 0,
      "EH"
    );
  }
}

/**@notice LimboDAO offers two forms of governance: flash and proposal. Proposals are contracts that have authorization to execute guarded functions on contracts that implement the Governable abstract contract.
 * Proposals require Fate to be put forward for voting and Fate is the spendable voting token.
 * Flash governance occurs in the duration of one transaction and is more appropriate for variable tweaking such as changing the Flan per Second or Threshold of a pool.
 * Flash governance requires an asset be deposited into an adjudication contract. The community can then vote, through a proposal, whether the decision was legitimate. If not, the deposit can be slashed
 * By default, the asset is EYE.
 */
contract FlashGovernanceArbiter is Governable {
  /**
   * @param actor user making flash governance decision
   * @param deposit_asset is the asset type put up as decision collateral. Must be burnable.
   * @param amount is the amount of the deposit_asset to be put up as decision collateral.
   * @param target is the contract that will be affected by the flash governance decision.
   */
  event flashDecision(address actor, address deposit_asset, uint256 amount, address target);

  mapping(address => bool) enforceLimitsActive;

  constructor(address dao) Governable(dao) {}

  struct FlashGovernanceConfig {
    address asset;
    uint256 amount;
    uint256 unlockTime;
    bool assetBurnable;
  }

  //Note: epoch settings prevent DOS attacks. Change tolerance curtails the damage of bad flash governance.
  struct SecurityParameters {
    uint8 maxGovernanceChangePerEpoch; //prevents flash governance from wrecking the incentives.
    uint256 epochSize; //only one flash governance action can happen per epoch to prevent governance DOS
    uint256 lastFlashGovernanceAct;
    uint8 changeTolerance; //1-100 maximum percentage any numeric variable can be changed through flash gov
  }

  //the current parameters determining the rules of flash governance
  FlashGovernanceConfig public flashGovernanceConfig;
  SecurityParameters public security;

  /*For every decision, we record the config at the time of the decision. This allows governance to change the rules
   *without undermining the terms under which pending decisions were made.
   */
  mapping(address => mapping(address => FlashGovernanceConfig)) public pendingFlashDecision; //contract->user->config

  /**
   *@notice An attempt is made to withdraw the current deposit requirement.
   * For a given user, flash governance decisions can only happen one at a time
   *@param sender is the user making the flash governance decision
   *@param target is the contract that will be affected by the flash governance decision.
   *@param emergency flash governance decisions are restricted in frequency per epoch but some decisions are too important. These can be marked emergency.
   *@dev be very careful about setting emergency to true. Only decisions which preclude the execution of other flash governance decisions should be considered candidtes for emergency.
   */
  function assertGovernanceApproved(
    address sender,
    address target,
    bool emergency
  ) public {
    if (
      IERC20(flashGovernanceConfig.asset).transferFrom(sender, address(this), flashGovernanceConfig.amount) &&
      pendingFlashDecision[target][sender].unlockTime < block.timestamp
    ) {
      require(
        emergency || (block.timestamp - security.lastFlashGovernanceAct > security.epochSize),
        "Limbo: flash governance disabled for rest of epoch"
      );
      pendingFlashDecision[target][sender] = flashGovernanceConfig;
      pendingFlashDecision[target][sender].unlockTime += block.timestamp;

      security.lastFlashGovernanceAct = block.timestamp;
      emit flashDecision(sender, flashGovernanceConfig.asset, flashGovernanceConfig.amount, target);
    } else {
      revert("LIMBO: governance decision rejected.");
    }
  }

  /**
   *@param asset is the asset type put up as decision collateral. Must be burnable.
   *@param amount is the amount of the deposit_asset to be put up as decision collateral.
   *@param unlockTime is the duration for which the deposit collateral must be locked in order to give the community time to weigh up the decision
   *@param assetBurnable is a technical parameter to determined the manner in which burning should occur. Non burnable assets are just no longer accounted for and accumulate within this contract.
   */
  function configureFlashGovernance(
    address asset,
    uint256 amount,
    uint256 unlockTime,
    bool assetBurnable
  ) public virtual onlySuccessfulProposal {
    flashGovernanceConfig.asset = asset;
    flashGovernanceConfig.amount = amount;
    flashGovernanceConfig.unlockTime = unlockTime;
    flashGovernanceConfig.assetBurnable = assetBurnable;
  }

  /**
    @param maxGovernanceChangePerEpoch max number of flash governance decisions per epoch to prevent DOS
    @param epochSize is the duration of a flash governance epoch and reflects proposal deliberation durations
    @param changeTolerance is the amount by which a variable can be changed through flash governance.
    */
  function configureSecurityParameters(
    uint8 maxGovernanceChangePerEpoch,
    uint256 epochSize,
    uint8 changeTolerance
  ) public virtual onlySuccessfulProposal {
    security.maxGovernanceChangePerEpoch = maxGovernanceChangePerEpoch;
    security.epochSize = epochSize;
    require(security.changeTolerance < 100, "Limbo: % between 0 and 100");
    security.changeTolerance = changeTolerance;
  }

  /**
    @notice LimboDAO proposals for burning flash governance collateral act through this function
    @param targetContract is the contract that is affected by the flash governance decision.
    @param user is the user who made the flash governance decision
    @param asset is the collateral asset to be burnt
    @param amount is the amount of the collateral to be burnt
    */
  function burnFlashGovernanceAsset(
    address targetContract,
    address user,
    address asset,
    uint256 amount
  ) public virtual onlySuccessfulProposal {
    if (pendingFlashDecision[targetContract][user].assetBurnable) {
      Burnable(asset).burn(amount);
    }

    pendingFlashDecision[targetContract][user] = flashGovernanceConfig;
  }

  /**
   *@notice Assuming a flash governance decision was not rejected during the lock window, the user is free to withdraw their asset
   *@param targetContract is the contract that is affected by the flash governance decision.
   *@param asset is the collateral asset to be withdrawn
   */
  function withdrawGovernanceAsset(address targetContract, address asset) public virtual {
    require(
      pendingFlashDecision[targetContract][msg.sender].asset == asset &&
        pendingFlashDecision[targetContract][msg.sender].amount > 0 &&
        pendingFlashDecision[targetContract][msg.sender].unlockTime < block.timestamp,
      "Limbo: Flashgovernance decision pending."
    );
    IERC20(pendingFlashDecision[targetContract][msg.sender].asset).transfer(
      msg.sender,
      pendingFlashDecision[targetContract][msg.sender].amount
    );
    delete pendingFlashDecision[targetContract][msg.sender];
  }

  /**
   *@notice when a governance function is executed, it can enforce change limits on variables in the event that the execution is through flash governance
   * However, a proposal is subject to the full deliberation of the DAO and such limits may thwart good governance.
   * @param enforce for the given context, set whether variable movement limits are enforced or not.
   */
  function setEnforcement(bool enforce) public {
    enforceLimitsActive[msg.sender] = enforce;
  }

  ///@dev for negative values, relative comparisons need to be calculated correctly.
  function enforceToleranceInt(int256 v1, int256 v2) public view {
    if (!configured) return;
    uint256 uv1 = uint256(v1 > 0 ? v1 : -1 * v1);
    uint256 uv2 = uint256(v2 > 0 ? v2 : -1 * v2);
    enforceTolerance(uv1, uv2);
  }

  ///@notice Allows functions to enforce maximum limits on a per variable basis
  ///@dev the 100 factor is just to allow for simple percentage comparisons without worrying about enormous precision.
  function enforceTolerance(uint256 v1, uint256 v2) public view {
    if (!configured || !enforceLimitsActive[msg.sender]) return;
    //bonus points for readability
    if (v1 > v2) {
      if (v2 == 0) require(v1 <= 1, "FE1");
      else require(((v1 - v2) * 100) < security.changeTolerance * v1, "FE1");
    } else {
      if (v1 == 0) require(v2 <= 1, "FE1");
      else require(((v2 - v1) * 100) < security.changeTolerance * v1, "FE1");
    }
  }
}

abstract contract Proposal {
  string public description;
  LimboDAOLike DAO;

  constructor(address dao, string memory _description) {
    DAO = LimboDAOLike(dao);
    description = _description;
  }

  modifier onlyDAO() {
    address dao = address(DAO);
    require(dao != address(0), "PROPOSAL: DAO not set");
    require(msg.sender == dao, "PROPOSAL: only DAO can invoke");
    _;
  }

  //Use this modifier on a parameterize funtion. This allows the proposal to lock itself into a readonly state during voting.
  modifier notCurrent() {
    (, , , , address proposal) = DAO.currentProposalState();
    require(proposal != address(this), "LimboDAO: proposal locked");
    _;
  }

  function orchestrateExecute() public onlyDAO {
    require(execute(), "LimboDAO: execution of proposal failed");
  }

  //override this function with all proposal logic. Only instructions included in this function will be executed if the proposal is a success.
  function execute() internal virtual returns (bool);
}

///@title Proposal Factory
///@author Justin Goro
///@notice authenticates and gatekeeps proposals up for vote on LimboDAO.
///@dev constructors are prefered to initializers when an imporant base contract exists.
contract ProposalFactory is Governable, Ownable {
  mapping(address => bool) public whitelistedProposalContracts;
  address public soulUpdateProposal;

  constructor(
    address _dao,
    address whitelistingProposal,
    address _soulUpdateProposal
  ) Governable(_dao) {
    //in order for proposals to be white listed, an initial whitelisting proposal needs to be whitelisted at deployment
    whitelistedProposalContracts[whitelistingProposal] = true;
    whitelistedProposalContracts[_soulUpdateProposal] = true;
    soulUpdateProposal = _soulUpdateProposal;
  }

  ///@notice SoulUpdateProposal is one of the most important proposals and governs the creation of new staking souls.
  ///@dev onlyOwner denotes that this important function is overseen by MorgothDAO.
  ///@param newProposal new update soul
  function changeSoulUpdateProposal(address newProposal) public onlyOwner {
    soulUpdateProposal = newProposal;
  }

  ///@notice there is no formal onchain enforcement of proposal structure and compliance. Proposal contracts must first be white listed for usage
  function toggleWhitelistProposal(address proposal) public onlySuccessfulProposal {
    whitelistedProposalContracts[proposal] = !whitelistedProposalContracts[proposal];
  }

  ///@notice user facing function to vote on a new proposal. Note that the proposal contract must first be whitelisted for usage
  ///@param proposal whitelisted popular contract
  function lodgeProposal(address proposal) public {
    require(whitelistedProposalContracts[proposal], "LimboDAO: invalid proposal");
    LimboDAOLike(DAO).makeProposal(proposal, msg.sender);
  }
}

contract GovernableStub is Governable {
    constructor(address dao) Governable(dao) {}

    function userTokenBalance(address token) public view returns (uint256) {
        return 0;
    }
}

contract RealUniswapV2Pair is UniswapV2ERC20 {
    event Mint(address indexed sender, uint256 amount0, uint256 amount1);
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
    event Sync(uint112 reserve0, uint112 reserve1);

    using SafeMath for uint256;
    using UQ112x112 for uint224;

    uint256 public constant MINIMUM_LIQUIDITY = 10**3;
    bytes4 private constant SELECTOR =
        bytes4(keccak256(bytes("transfer(address,uint256)")));

    address public factory;
    address public token0;
    address public token1;

    uint112 private reserve0; // uses single storage slot, accessible via getReserves
    uint112 private reserve1; // uses single storage slot, accessible via getReserves
    uint32 private blockTimestampLast; // uses single storage slot, accessible via getReserves

    uint256 public price0CumulativeLast;
    uint256 public price1CumulativeLast;
    uint256 public kLast; // reserve0 * reserve1, as of immediately after the most recent liquidity event

    uint256 private unlocked = 1;
    modifier lock() {
        require(unlocked == 1, "UniswapV2: LOCKED");
        unlocked = 0;
        _;
        unlocked = 1;
    }

    function getReserves()
        public
        view
        returns (
            uint112 _reserve0,
            uint112 _reserve1,
            uint32 _blockTimestampLast
        )
    {
        _reserve0 = reserve0;
        _reserve1 = reserve1;
        _blockTimestampLast = blockTimestampLast;
    }

    function _safeTransfer(
        address token,
        address to,
        uint256 value
    ) private {
        (bool success, bytes memory data) = token.call(
            abi.encodeWithSelector(SELECTOR, to, value)
        );
        require(
            success && (data.length == 0 || abi.decode(data, (bool))),
            "UniswapV2: TRANSFER_FAILED"
        );
    }

    constructor() {
        factory = msg.sender;
    }

    // called once by the factory at time of deployment
    function initialize(address _token0, address _token1) external {
        require(msg.sender == factory, "UniswapV2: FORBIDDEN"); // sufficient check
        token0 = _token0;
        token1 = _token1;
    }

    // update reserves and, on the first call per block, price accumulators
    function _update(
        uint256 balance0,
        uint256 balance1,
        uint112 _reserve0,
        uint112 _reserve1
    ) private {
        require(
            balance0 <= type(uint112).max && balance1 <= type(uint112).max,
            "UniswapV2: OVERFLOW"
        );
        uint32 blockTimestamp = uint32(block.timestamp % 2**32);
        uint32 timeElapsed = blockTimestamp - blockTimestampLast; // overflow is desired
        if (timeElapsed > 0 && _reserve0 != 0 && _reserve1 != 0) {
            // * never overflows, and + overflow is desired
            price0CumulativeLast +=
                uint256(UQ112x112.encode(_reserve1).uqdiv(_reserve0)) *
                timeElapsed;
            price1CumulativeLast +=
                uint256(UQ112x112.encode(_reserve0).uqdiv(_reserve1)) *
                timeElapsed;
        }
        reserve0 = uint112(balance0);
        reserve1 = uint112(balance1);
        blockTimestampLast = blockTimestamp;
        emit Sync(reserve0, reserve1);
    }

    // if fee is on, mint liquidity equivalent to 1/6th of the growth in sqrt(k)
    function _mintFee(uint112 _reserve0, uint112 _reserve1)
        private
        returns (bool feeOn)
    {
        address feeTo = IUniswapV2Factory(factory).feeTo();
        feeOn = feeTo != address(0);
        uint256 _kLast = kLast; // gas savings
        if (feeOn) {
            if (_kLast != 0) {
                uint256 rootK = Math.sqrt(uint256(_reserve0).mul(_reserve1));
                uint256 rootKLast = Math.sqrt(_kLast);
                if (rootK > rootKLast) {
                    uint256 numerator = totalSupply.mul(rootK.sub(rootKLast));
                    uint256 denominator = rootK.mul(5).add(rootKLast);
                    uint256 liquidity = numerator / denominator;
                    if (liquidity > 0) _mint(feeTo, liquidity);
                }
            }
        } else if (_kLast != 0) {
            kLast = 0;
        }
    }

    // this low-level function should be called from a contract which performs important safety checks
    function mint(address to) external lock returns (uint256 liquidity) {
        (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
        uint256 balance0 = IERC20(token0).balanceOf(address(this));
        uint256 balance1 = IERC20(token1).balanceOf(address(this));
        uint256 amount0 = balance0.sub(_reserve0);
        uint256 amount1 = balance1.sub(_reserve1);

        bool feeOn = _mintFee(_reserve0, _reserve1);
        uint256 _totalSupply = totalSupply; // gas savings, must be defined here since totalSupply can update in _mintFee
        if (_totalSupply == 0) {
            liquidity = Math.sqrt(amount0.mul(amount1)).sub(MINIMUM_LIQUIDITY);
            _mint(address(0), MINIMUM_LIQUIDITY); // permanently lock the first MINIMUM_LIQUIDITY tokens
        } else {
            // console.log(
            //     "totalSupply %s, reserve0 %s, reserve1 %s",
            //     _totalSupply,
            //     _reserve0,
            //     _reserve1
            // );
            // console.log("amount0 %s, amount1 %s", amount0, amount1);
            liquidity = Math.min(
                amount0.mul(_totalSupply) / _reserve0,
                amount1.mul(_totalSupply) / _reserve1
            );
        }
        require(liquidity > 0, "UniswapV2: INSUFFICIENT_LIQUIDITY_MINTED");
        _mint(to, liquidity);

        _update(balance0, balance1, _reserve0, _reserve1);
        if (feeOn) kLast = uint256(reserve0).mul(reserve1); // reserve0 and reserve1 are up-to-date
        emit Mint(msg.sender, amount0, amount1);
    }

    // this low-level function should be called from a contract which performs important safety checks
    function burn(address to)
        external
        lock
        returns (uint256 amount0, uint256 amount1)
    {
        (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
        address _token0 = token0; // gas savings
        address _token1 = token1; // gas savings
        uint256 balance0 = IERC20(_token0).balanceOf(address(this));
        uint256 balance1 = IERC20(_token1).balanceOf(address(this));
        uint256 liquidity = balanceOf[address(this)];

        bool feeOn = _mintFee(_reserve0, _reserve1);
        uint256 _totalSupply = totalSupply; // gas savings, must be defined here since totalSupply can update in _mintFee
        amount0 = liquidity.mul(balance0) / _totalSupply; // using balances ensures pro-rata distribution
        amount1 = liquidity.mul(balance1) / _totalSupply; // using balances ensures pro-rata distribution
        require(
            amount0 > 0 && amount1 > 0,
            "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED"
        );
        _burn(address(this), liquidity);
        _safeTransfer(_token0, to, amount0);
        _safeTransfer(_token1, to, amount1);
        balance0 = IERC20(_token0).balanceOf(address(this));
        balance1 = IERC20(_token1).balanceOf(address(this));

        _update(balance0, balance1, _reserve0, _reserve1);
        if (feeOn) kLast = uint256(reserve0).mul(reserve1); // reserve0 and reserve1 are up-to-date
        emit Burn(msg.sender, amount0, amount1, to);
    }

    // this low-level function should be called from a contract which performs important safety checks
    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external lock {
        require(
            amount0Out > 0 || amount1Out > 0,
            "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT"
        );
        (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
        require(
            amount0Out < _reserve0 && amount1Out < _reserve1,
            "UniswapV2: INSUFFICIENT_LIQUIDITY"
        );

        uint256 balance0;
        uint256 balance1;
        {
            // scope for _token{0,1}, avoids stack too deep errors
            address _token0 = token0;
            address _token1 = token1;
            require(to != _token0 && to != _token1, "UniswapV2: INVALID_TO");
            if (amount0Out > 0) _safeTransfer(_token0, to, amount0Out); // optimistically transfer tokens
            if (amount1Out > 0) _safeTransfer(_token1, to, amount1Out); // optimistically transfer tokens
            if (data.length > 0)
                IUniswapV2Callee(to).uniswapV2Call(
                    msg.sender,
                    amount0Out,
                    amount1Out,
                    data
                );
            balance0 = IERC20(_token0).balanceOf(address(this));
            balance1 = IERC20(_token1).balanceOf(address(this));
        }
        uint256 amount0In = balance0 > _reserve0 - amount0Out
            ? balance0 - (_reserve0 - amount0Out)
            : 0;
        uint256 amount1In = balance1 > _reserve1 - amount1Out
            ? balance1 - (_reserve1 - amount1Out)
            : 0;
        require(
            amount0In > 0 || amount1In > 0,
            "UniswapV2: INSUFFICIENT_INPUT_AMOUNT"
        );
        {
            // scope for reserve{0,1}Adjusted, avoids stack too deep errors
            uint256 balance0Adjusted = balance0.mul(1000).sub(amount0In.mul(3));
            uint256 balance1Adjusted = balance1.mul(1000).sub(amount1In.mul(3));
            require(
                balance0Adjusted.mul(balance1Adjusted) >=
                    uint256(_reserve0).mul(_reserve1).mul(1000**2),
                "UniswapV2: K"
            );
        }

        _update(balance0, balance1, _reserve0, _reserve1);
        emit Swap(msg.sender, amount0In, amount1In, amount0Out, amount1Out, to);
    }

    // force balances to match reserves
    function skim(address to) external lock {
        address _token0 = token0; // gas savings
        address _token1 = token1; // gas savings
        _safeTransfer(
            _token0,
            to,
            IERC20(_token0).balanceOf(address(this)).sub(reserve0)
        );
        _safeTransfer(
            _token1,
            to,
            IERC20(_token1).balanceOf(address(this)).sub(reserve1)
        );
    }

    // force reserves to match balances
    function sync() external lock {
        _update(
            IERC20(token0).balanceOf(address(this)),
            IERC20(token1).balanceOf(address(this)),
            reserve0,
            reserve1
        );
    }
}



/**
 *@notice The reward token for Limbo. Flan can be minted without limit and is intended to converge on the price of DAI via various external incentives
 */
abstract contract Flan is ERC677("Flan", "FLN"), Governable {
    event burnOnTransferFeeAdjusted(uint8 oldFee, uint8 newFee);
    mapping(address => uint256) public mintAllowance; //type(uint).max == whitelist

    uint8 public burnOnTransferFee = 0; //% between 1 and 100, recipient pays

    constructor(address dao) Governable(dao) {}

    /**
    * @param fee - % between 1 and 100, recipient pays
     */
    function setBurnOnTransferFee(uint8 fee) public onlySuccessfulProposal {
        _setBurnOnTransferFee(fee);
    }

    ///@notice flash governance technique for FOT change.
    function incrementBurnOnTransferFee(int8 change)
        public
        governanceApproved(false)
    {
        uint8 newFee = uint8(int8(burnOnTransferFee) + change);
        flashGoverner.enforceTolerance(newFee, burnOnTransferFee);
        _setBurnOnTransferFee(newFee);
    }

    function _setBurnOnTransferFee(uint8 fee) internal {
        uint8 priorFee = burnOnTransferFee;
        burnOnTransferFee = fee > 100 ? 100 : fee;
        emit burnOnTransferFeeAdjusted(priorFee, burnOnTransferFee);
    }

    ///@notice grants unlimited minting power to a contract
    ///@param minter contract to be given unlimited minting power
    ///@param enabled minting power enabled or disabled
    function whiteListMinting(address minter, bool enabled)
        public
        onlySuccessfulProposal
    {
        mintAllowance[minter] = enabled ? type(uint256).max : 0;
    }

    ///@notice metered minting power. Useful for once off minting
    function increaseMintAllowance(address minter, uint256 _allowance)
        public
        onlySuccessfulProposal
    {
        mintAllowance[minter] = mintAllowance[minter] + _allowance;
    }

    ///@notice minting of flan open to approved minters and LimboDAO
    ///@param recipient address to receive flan
    ///@param amount amount of flan to be minted 
    function mint(address recipient, uint256 amount) public returns (bool) {
        uint256 allowance = mintAllowance[_msgSender()];
        require(
            _msgSender() == owner() || allowance >= amount,
            "Flan: Mint allowance exceeded"
        );
        approvedMint(recipient, amount, _msgSender(), allowance);
        return true;
    }

    function approvedMint(
        address recipient,
        uint256 amount,
        address minter,
        uint256 allowance
    ) internal {
        _mint(recipient, amount);
        if (allowance < type(uint256).max && minter != owner()) {
            mintAllowance[minter] = mintAllowance[minter] - amount;
        }
    }

    function safeTransfer(address _to, uint256 _amount) external {
        uint256 flanBal = balanceOf(address(this));
        uint256 flanToTransfer = _amount > flanBal ? flanBal : _amount;
        _transfer(_msgSender(), _to, flanToTransfer);
    }

    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal override {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        uint256 fee = (burnOnTransferFee * amount) / 100;

        _totalSupply = _totalSupply - fee;
        uint256 senderBalance = _balances[sender];
        require(
            senderBalance >= amount,
            "ERC20: transfer amount exceeds balance"
        );
        _balances[sender] = senderBalance - amount;
        _balances[recipient] += amount - fee;

        emit Transfer(sender, recipient, amount);
    }
}

abstract contract UniswapPair is ERC677 {
    address public factory;

    constructor(
        address _factory,
        string memory name,
        string memory symbol
    ) ERC677(name, symbol) {
        factory = _factory;
        _mint(_msgSender(), 10 ether);
    }
}

abstract contract MockToken is ERC677 {
    constructor(
        string memory name,
        string memory symbol,
        address[] memory LPs,
        uint256[] memory mintVal
    ) ERC677(name, symbol) {
        _mint(msg.sender, 100 ether);
        uint256 deceth = (1 ether) / 10;
        require(LPs.length == mintVal.length, "CONSTRUCTION MISMATCH");
        for (uint256 i = 0; i < LPs.length; i++) {
            _mint(LPs[i], mintVal[i] * deceth);
        }
    }

    function mint(uint amount) public {
        _mint(msg.sender,amount);
    }
}

abstract contract MockBehodler is ERC677 {
  address addTokenPower;
  uint256 priceMultiplier = 200;

  function setPriceMultiplier(uint256 _priceMultiplier) public {
    priceMultiplier = _priceMultiplier;
  }

  function withdrawLiquidityFindSCX(
    address outputToken,
    uint256 tokensToRelease,
    uint256 scx,
    uint256 passes
  ) external view returns (uint256) {
    return priceMultiplier * scx;
  }

  function mintTo(address recipient, uint256 amount) public {
    _mint(recipient, amount);
  }

  function mint(uint256 amount) public {
    require(msg.sender == addTokenPower, "Only Mock Power can mint on Mock Behodler.");
    _mint(msg.sender, amount);
  }

  constructor(
    string memory name,
    string memory symbol,
    address _addTokenPower
  ) ERC677(name, symbol) {
    _mint(msg.sender, 100 ether);
    addTokenPower = _addTokenPower;
  }

  address MickyMouseToken = 0xAa645185F79506175917Ae2Fdd3128E4711D4065;

  function config()
    public
    view
    returns (
      uint256 transferFee,
      uint256 burnFee,
      address feeDestination
    )
  {
    transferFee = 15;
    burnFee = 5;
    feeDestination = MickyMouseToken;
  }

  function _transfer(
    address sender,
    address recipient,
    uint256 amount
  ) internal override {
    require(sender != address(0), "Scarcity: transfer from the zero address");
    require(recipient != address(0), "Scarcity: transfer to the zero address");
    (uint256 tfee, uint256 bfee, address mouse) = config();
    uint256 feeComponent = (tfee * amount) / (1000);
    // console.log("transferFee %s, amount %s, feeComponent %s", config.transferFee, amount, feeComponent);
    uint256 burnComponent = (bfee * amount) / (1000);
    _totalSupply = _totalSupply - burnComponent;

    _balances[mouse] = _balances[mouse] + (feeComponent);

    _balances[sender] = _balances[sender] - (amount);

    _balances[recipient] = _balances[recipient] + (amount - (feeComponent + burnComponent));
    emit Transfer(sender, recipient, amount);
  }
}

contract AngbandLite is AngbandLike {
    function executePower(address powerInvoker) public override {
        IdempotentPowerInvoker(powerInvoker).invoke();
    }
}

abstract contract IdempotentPowerInvoker {
    AngbandLike public angband;

    constructor(address _angband) {
        angband = AngbandLike(_angband);
    }

    function orchestrate() internal virtual returns (bool);

    function invoke() public {
        require(msg.sender == address(angband), "MORGOTH: angband only");
        require(orchestrate(), "MORGOTH: Power invocation");
    }
}

abstract contract BehodlerLiteLike {
    function addLiquidity(address inputToken, uint256 amount)
        external
        payable
        virtual
        returns (uint256 deltaSCX);

    function setTokenBurnable(address token, bool burnable) public virtual;
}

contract LimboAddTokenToBehodler is IdempotentPowerInvoker {
    struct Parameters {
        address soul;
        bool burnable;
        address limbo;
        address tokenProxyRegistry;
    }

    Parameters public params;
    address behodler;

    constructor(
        address _angband,
        address limbo,
        address behodlerLite,
        address _proxyregistry
    ) IdempotentPowerInvoker(_angband) {
        params.limbo = limbo;
        behodler = behodlerLite;
        params.tokenProxyRegistry = _proxyregistry;
    }

    function parameterize(address soul, bool burnable) public {
        require(
            msg.sender == params.limbo,
            "MORGOTH: Only Limbo can migrate tokens from Limbo."
        );
        params.soul = soul;
        params.burnable = burnable;
    }

    function orchestrate() internal override returns (bool) {
        require(
            params.soul != address(0),
            "MORGOTH: PowerInvoker not parameterized."
        );

        uint256 balanceOfToken = CommonIERC20(params.soul).balanceOf(
            address(this)
        );
        require(balanceOfToken > 0, "MORGOTH: remember to seed contract");
        (address baseToken, bool migrate) = TokenProxyRegistry(
            params.tokenProxyRegistry
        ).tokenProxy(params.soul);

        address tokenToMigrate = params.soul;
        if (migrate && baseToken != address(0)) {
            tokenToMigrate = baseToken;
            TokenProxyLike(params.soul).redeem(address(this), balanceOfToken);
        }

        CommonIERC20(tokenToMigrate).approve(behodler, type(uint256).max);
        BehodlerLiteLike(behodler).setTokenBurnable(
            tokenToMigrate,
            params.burnable
        );
        BehodlerLiteLike(behodler).addLiquidity(tokenToMigrate, balanceOfToken);
        uint256 scxBal = CommonIERC20(behodler).balanceOf(address(this));
        CommonIERC20(behodler).transfer(params.limbo, scxBal);
        params.soul = address(0); // prevent non limbo from executing.
        return true;
    }
}

/**
* @author Justin Goro
* @notice Earning Fate precludes owners of EYE based assets from earning Flan on Limbo. This proposal makes Fate monetizable into Flan in order to compensate users for the opportunity cost.
*/
contract TurnOnFateMintingProposal is Proposal {
    constructor(address dao, string memory _description)
        Proposal(dao, description)
    {}

    uint256 rate;

    function parameterize(uint256 _rate) public notCurrent {
        rate = _rate;
    }

    function execute() internal override returns (bool) {
        DAO.setFateToFlan(rate);
        return true;
    }
}

/**
* @author Justin Goro
* @notice This is the only mandatory proposal and is whitelisted at deployment time for LimboDAO. All subsequent proposals are whitelisted by this proposal.
*/
contract ToggleWhitelistProposalProposal is Proposal {
    struct Parameters {
        address proposalFactory;
        address toggleContract;
    }

    Parameters params;

    constructor(address dao, string memory _description)
        Proposal(dao, description){
    }

    function parameterize(address proposalFactory, address toggleContract)
        public
        notCurrent
    {
        params.proposalFactory = proposalFactory;
        params.toggleContract = toggleContract;
    }

    function execute() internal override returns (bool) {
        ProposalFactoryLike(params.proposalFactory).toggleWhitelistProposal(
            params.toggleContract
        );
        return true;
    }
}

/**
* @author Justin Goro
* @notice Each proposal is subject to a fate cost and a duration of voting. These values are themselves subject to governance
*/
contract UpdateProposalConfigProposal is Proposal {
    struct Parameters {
        uint256 votingDuration;
        uint256 requiredFateStake;
        address proposalFactory;
    }

    Parameters public params;

    constructor(address dao, string memory _description)
        Proposal(dao, _description)
    {}

    function parameterize(
        uint256 votingDuration,
        uint256 requiredFateStake,
        address proposalFactory
    ) public notCurrent {
        params.proposalFactory = proposalFactory;
        params.requiredFateStake = requiredFateStake;
        params.votingDuration = votingDuration;
    }

    function execute() internal override returns (bool) {
        DAO.setProposalConfig(
            params.votingDuration,
            params.requiredFateStake,
            params.proposalFactory
        );
        return true;
    }
}

/**
* @author Justin Goro
* @notice The singular form of UpdateMultiplSoulConfig
*/
contract UpdateSoulConfigProposal is Proposal {
    struct Parameters {
        address token;
        uint256 crossingThreshold;
        uint256 soulType;
        uint256 state;
        uint256 index;
        uint256 fps;
    }
    Parameters params;
    LimboLike limbo;
    MorgothTokenApproverLike morgothApprover;

    constructor(
        address dao,
        string memory _description,
        address _limbo,
        address morgothTokenApprover
    ) Proposal(dao, _description) {
        limbo = LimboLike(_limbo);
        morgothApprover = MorgothTokenApproverLike(morgothTokenApprover);
    }

    function parameterize(
        address token,
        uint256 crossingThreshold,
        uint256 soulType,
        uint256 state,
        uint256 index,
        uint256 fps
    ) public notCurrent {
        require(
            morgothApprover.approved(token),
            "MORGOTH: token not approved for listing on Behodler"
        );
        params.token = token;
        params.crossingThreshold = crossingThreshold;
        params.soulType = soulType;
        params.state = state;
        params.index = index;
        params.fps = fps;
    }

    function execute() internal override returns (bool) {
        limbo.configureSoul(
            params.token,
            params.crossingThreshold,
            params.soulType,
            params.state,
            params.index,
            params.fps
        );

        return true;
    }
}

/**
* @author Justin Goro
* @notice Occasionally tokens are added to Limbo that are not elligible for staking. This can either happen by mistake or because tokens earn other tokens.
* This proposal allows the orderly withdrawal of such tokens. 
* If it is known in advance that a token earns tokens such as a rebase token, it's better to use a proxy wrapper token via the proxy registry.
*/
contract WithdrawERC20Proposal is Proposal {
    struct Parameters {
        address token;
        address destination;
    }
    Parameters params;
    LimboLike limbo;

    constructor(address _dao) Proposal(_dao, "Withdraw errant tokens") {
        (address _limbo, , , , , , ) = LimboDAOLike(_dao).domainConfig();
        limbo = LimboLike(_limbo);
    }

    function parameterize(address token, address destination)
        public
        notCurrent
    {
        params.token = token;
        params.destination = destination;
    }

    function execute() internal override returns (bool) {
        limbo.withdrawERC20(params.token, params.destination);
        return true;
    }
}

/**
* @author Justin Goro
* @notice EYE and EYE based assets can be used to earn fate. This proposal determines which tokens fall into the latter category.
*/
contract SetAssetApprovalProposal is Proposal {
    struct Parameters {
        address asset;
        bool approved;
    }

    Parameters public params;

    constructor(address dao, string memory _description)
        Proposal(dao, description)
    {}

    function parameterize(address asset, bool approved) public notCurrent {
        params.asset = asset;
        params.approved = approved;
    }

    function execute() internal override returns (bool) {
        DAO.setApprovedAsset(params.asset, params.approved);
        return true;
    }
}

/**
* @author Justin Goro
* @notice For adding a list of new souls to Limbo for staking 
*/
contract UpdateMultipleSoulConfigProposal is Proposal {
  struct Parameters {
    address token;
    uint256 crossingThreshold;
    uint256 soulType;
    uint256 state;
    uint256 index;
    uint256 targetAPY;
    uint256 daiThreshold;
  }

  Parameters[] params;
  LimboLike limbo;
  AMMHelper ammHelper;
  MorgothTokenApproverLike morgothApprover;

  constructor(
    address dao,
    string memory _description,
    address _limbo,
    address _ammHelper,
    address morgothTokenApprover
  ) Proposal(dao, _description) {
    limbo = LimboLike(_limbo);
    ammHelper = AMMHelper(_ammHelper);
    morgothApprover = MorgothTokenApproverLike(morgothTokenApprover);
  }

  function parameterize(
    address token,
    uint256 crossingThreshold,
    uint256 soulType,
    uint256 state,
    uint256 index,
    uint256 targetAPY,
    uint256 daiThreshold
  ) public notCurrent {
    require(morgothApprover.approved(token), "MORGOTH: token not approved for listing on Behodler");
    params.push(
      Parameters({
        token: token,
        crossingThreshold: crossingThreshold,
        soulType: soulType,
        state: state,
        index: index,
        targetAPY: targetAPY,
        daiThreshold: daiThreshold
      })
    );
  }

  function execute() internal override returns (bool) {
    for (uint256 i = 0; i < params.length; i++) {
      uint256 fps = ammHelper.minAPY_to_FPS(params[i].targetAPY, params[i].daiThreshold);
      limbo.configureSoul(
        params[i].token,
        params[i].crossingThreshold,
        params[i].soulType,
        params[i].state,
        params[i].index,
        fps
      );
    }

    return true;
  }
}

/**
* @author Justin Goro
* @notice Flash governance decisions are accompanied by staked collateral that can be slashed by LimboDAO. This proposal is responsible for slashing
*/
contract BurnFlashStakeDeposit is Proposal {
    struct Parameters {
        address user;
        address asset;
        uint256 amount;
        address flashGoverner;
        address targetContract;
    }

    Parameters public params;

    constructor(address dao, string memory _description)
        Proposal(dao, description)
    {}

    function parameterize(
        address user,
        address asset,
        uint256 amount,
        address flashGoverner,
        address targetContract
    ) public notCurrent {
        params.user = user;
        params.asset = asset;
        params.amount = amount;
        params.flashGoverner = flashGoverner;
        params.targetContract = targetContract;
    }

    function execute() internal override returns (bool) {
        FlashGovernanceArbiterLike(params.flashGoverner)
            .burnFlashGovernanceAsset(
            params.targetContract,
            params.user,
            params.asset,
            params.amount
        );
        return true;
    }
}

/**
* @author Justin Goro
* @notice Flan has an optional fee on transfer feature. This proposal determines what that fee should be. Zero == off
*/
contract AdjustFlanFeeOnTransferProposal is Proposal {
    struct Parameters {
        address flan;
        uint8 fee;
    }
    Parameters public params;

    constructor(address dao, string memory _description)
        Proposal(dao, description)
    {}

    function parameterize(
       address flan,
        uint8 fee
    ) public notCurrent {
        params.flan = flan;
        params.fee = fee;
    }

    function execute() internal override returns (bool) {
        FlanLike(params.flan).setBurnOnTransferFee(
          params.fee
        );
        return true;
    }
}

contract RealUniswapV2Factory is IUniswapV2Factory {
    address public override feeTo;
    address public override feeToSetter;

    mapping(address => mapping(address => address)) public override getPair;
    address[] public override allPairs;

    constructor(address _feeToSetter) {
        feeToSetter = _feeToSetter;
    }

    function allPairsLength() external override view returns (uint) {
        return allPairs.length;
    }

    function createPair(address tokenA, address tokenB) external override returns (address pair) {
        require(tokenA != tokenB, 'UniswapV2: IDENTICAL_ADDRESSES');
        (address token0, address token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        require(token0 != address(0), 'UniswapV2: ZERO_ADDRESS');
        require(getPair[token0][token1] == address(0), 'UniswapV2: PAIR_EXISTS'); // single check is sufficient
        bytes memory bytecode = type(RealUniswapV2Pair).creationCode;
        bytes32 salt = keccak256(abi.encodePacked(token0, token1));
        assembly {
            pair := create2(0, add(bytecode, 32), mload(bytecode), salt)
        }
        IUniswapV2Pair(pair).initialize(token0, token1);
        getPair[token0][token1] = pair;
        getPair[token1][token0] = pair; // populate mapping in the reverse direction
        allPairs.push(pair);
        emit PairCreated(token0, token1, pair, allPairs.length);
    }

    function setFeeTo(address _feeTo) external override {
        require(msg.sender == feeToSetter, 'UniswapV2: FORBIDDEN');
        feeTo = _feeTo;
    }

    function setFeeToSetter(address _feeToSetter) external override {
        require(msg.sender == feeToSetter, 'UniswapV2: FORBIDDEN');
        feeToSetter = _feeToSetter;
    }
}

/**@notice expresses the balance changes of a rebase token as a fluctuating redeem rate, allowing for balanceOf stability. Useful for dapps which maintain their own balance values
* Very large rebase down movement tokens are still discouraged as this could cause threshold instability.
*/
///@dev TokenProxyRegistry contract maps this token to a base token.
abstract contract RebaseProxy is ERC20, TokenProxyLike {
    constructor(
        address _baseToken,
        string memory name_,
        string memory symbol_
    ) TokenProxyLike(_baseToken) ERC20() {}

    function redeemRate() public view returns (uint256) {
        uint256 balanceOfBase = IERC20(baseToken).balanceOf(address(this));
        if (totalSupply() == 0 || balanceOfBase == 0) return ONE;

        return (balanceOfBase * ONE) / totalSupply();
    }

    function mint(address to, uint256 amount)
        public
        override
        returns (uint256)
    {
        uint256 _redeemRate = redeemRate();
        require(
            IERC20(baseToken).transferFrom(msg.sender, address(this), amount)
        );
        uint256 baseBalance = IERC20(baseToken).balanceOf(address(this));
        uint256 proxy = (baseBalance * ONE) / _redeemRate;
        _mint(to, proxy);
    }

    function redeem(address to, uint256 amount)
        public
        override
        returns (uint256)
    {
        uint256 _redeemRate = redeemRate();
        uint256 baseTokens = (_redeemRate * amount) / ONE;
        _burn(msg.sender, amount);
        IERC20(baseToken).transfer(to, baseTokens);
    }
}

library TransferHelper {
  function ERC20NetTransfer(
    address token,
    address from,
    address to,
    int256 amount
  ) public {
    if (amount > 0) {
      require(IERC20(token).transferFrom(from, to, uint256(amount)), "LimboDAO: ERC20 transfer from failed.");
    } else {
      require(IERC20(token).transfer(from, uint256(amount * (-1))), "LimboDAO: ERC20 transfer failed.");
    }
  }
}

enum FateGrowthStrategy {
  straight,
  directRoot,
  indirectTwoRootEye
}

enum ProposalDecision {
  voting,
  approved,
  rejected
}

///@title Limbo DAO
///@author Justin Goro
/**@notice
 *This is the first MicroDAO associated with MorgothDAO. A MicroDAO manages parameterization of running dapps without having
 *control over existential functionality. This is not to say that some of the decisions taken are not critical but that the domain
 *of influence is confined to the local Dapp - Limbo in this case.
 * LimboDAO has two forms of decision making: proposals and flash governance. For proposals, voting power is required. Voting power in LimboDAO is measured
 * by a points system called Fate. Staking EYE or an EYE based LP earns Fate at a quadratic rate. Fate can be used to list a proposal for voting or to vote.
 * Using Fate to make a governance decisions spens it out of existince. So Fate reflects the opportunity cost of staking.
 * Flash governance is for instant decision making that cannot wait for voting to occur. Best used for small tweaks to parameters or emergencies.
 * Flash governance requires a governance asset (EYE) be staked at the time of the execution. The asset cannot be withdrawn for a certain period of time,
 * allowing for Fate holders to vote on the legitimacy of the decision. If the decision is considered malicious, the staked EYE is burnt.
 */
///@dev Contracts subject to LimboDAO must inherit the Governable abstract contract.
contract LimboDAO is Ownable {
  event daoKilled(address newOwner);
  event proposalLodged(address proposal, address proposer);
  event voteCast(address voter, address proposal, int256 fateCast);
  event assetApproval(address asset, bool appoved);
  event proposalExecuted(address proposal, bool approved);
  event assetBurnt(address burner, address asset, uint256 fateCreated);

  using TransferHelper for address;
  uint256 constant ONE = 1 ether;
  uint256 precision = 1e9;

  struct DomainConfig {
    address limbo;
    address flan;
    address eye;
    address fate;
    bool live;
    address flashGoverner;
    address sushiFactory;
    address uniFactory;
  }

  struct ProposalConfig {
    uint256 votingDuration;
    uint256 requiredFateStake;
    address proposalFactory; //check this for creating proposals
  }

  struct ProposalState {
    int256 fate;
    ProposalDecision decision;
    address proposer;
    uint256 start;
    Proposal proposal;
  }

  //rateCrate
  struct FateState {
    uint256 fatePerDay;
    uint256 fateBalance;
    uint256 lastDamnAdjustment;
  }

  struct AssetClout {
    uint256 fateWeight;
    uint256 balance;
  }

  DomainConfig public domainConfig;
  ProposalConfig public proposalConfig;

  /**@notice for staking EYE, we simply take the square root of staked amount.
   * For LP tokens, only half the value of the token is EYE so it's tempting to take the square root for the EYE balance. However this punishes the holder by ignoring the cost incurred by supplying the other asset. Since the other asset at rest is equal in value to the EYE balance, we just multiply the calculation by 2.
   */
  mapping(address => FateGrowthStrategy) public fateGrowthStrategy;
  mapping(address => bool) public assetApproved;
  mapping(address => FateState) public fateState; //lateDate

  //Fate is earned per day. Keeping track of relative staked values, we can increment user balance
  mapping(address => mapping(address => AssetClout)) public stakedUserAssetWeight; //user->asset->weight

  ProposalState public currentProposalState;
  ProposalState public previousProposalState;

  // Since staking EYE precludes it from earning Flan on Limbo, fateToFlan can optionally be set to a non zero number to allow fat holders to spend their fate for Flan.
  uint256 public fateToFlan;

  modifier isLive() {
    require(domainConfig.live, "LimboDAO: DAO is not live.");
    _;
  }

  function nextProposal() internal {
    previousProposalState = currentProposalState;
    currentProposalState.proposal = Proposal(address(0));
    currentProposalState.fate = 0;
    currentProposalState.decision = ProposalDecision.voting;
    currentProposalState.proposer = address(0);
    currentProposalState.start = 0;
  }

  modifier onlySuccessfulProposal() {
    // console.log('onlySuccessfulProposal');
    require(successfulProposal(msg.sender), "LimboDAO: approve proposal");
    _;
    //nextProposal();
  }

  ///@notice has a proposal successfully been approved?
  function successfulProposal(address proposal) public view returns (bool) {
    return
      currentProposalState.decision == ProposalDecision.approved && proposal == address(currentProposalState.proposal);
  }

  modifier updateCurrentProposal() {
    incrementFateFor(msg.sender);
    if (address(currentProposalState.proposal) != address(0)) {
      uint256 durationSinceStart = block.timestamp - currentProposalState.start;
      if (
        durationSinceStart >= proposalConfig.votingDuration && currentProposalState.decision == ProposalDecision.voting
      ) {
        if (currentProposalState.fate > 0) {
          currentProposalState.decision = ProposalDecision.approved;
          currentProposalState.proposal.orchestrateExecute();
          fateState[currentProposalState.proposer].fateBalance += proposalConfig.requiredFateStake;
        } else {
          currentProposalState.decision = ProposalDecision.rejected;
        }
        emit proposalExecuted(
          address(currentProposalState.proposal),
          currentProposalState.decision == ProposalDecision.approved
        );
        nextProposal();
      }
    }
    _;
  }

  modifier incrementFate() {
    incrementFateFor(msg.sender);
    _;
  }

  function incrementFateFor(address user) public {
    FateState storage state = fateState[user];
    state.fateBalance += (state.fatePerDay * (block.timestamp - state.lastDamnAdjustment)) / (1 days);
    state.lastDamnAdjustment = block.timestamp;
  }

  ///@param limbo address of Limbo
  ///@param flan address of Flan
  ///@param eye address of EYE token
  ///@param proposalFactory authenticates and instantiates valid proposals for voting
  ///@param sushiFactory is the SushiSwap Factory contract
  ///@param uniFactory is the UniSwapV2 Factory contract
  ///@param flashGoverner oversees flash governance cryptoeconomics
  ///@param precisionOrderOfMagnitude when comparing fractional values, it's not necessary to get every last digit right
  ///@param sushiLPs valid EYE containing LP tokens elligible for earning Fate through staking
  ///@param uniLPs valid EYE containing LP tokens elligible for earning Fate through staking
  function seed(
    address limbo,
    address flan,
    address eye,
    address proposalFactory,
    address sushiFactory,
    address uniFactory,
    address flashGoverner,
    uint256 precisionOrderOfMagnitude,
    address[] memory sushiLPs,
    address[] memory uniLPs
  ) public onlyOwner {
    _seed(limbo, flan, eye, sushiFactory, uniFactory, flashGoverner);
    proposalConfig.votingDuration = 2 days;
    proposalConfig.requiredFateStake = 223 * ONE; //50000 EYE for 24 hours
    proposalConfig.proposalFactory = proposalFactory;
    precision = 10**precisionOrderOfMagnitude;
    for (uint256 i = 0; i < sushiLPs.length; i++) {
      require(UniPairLike(sushiLPs[i]).factory() == sushiFactory, "LimboDAO: invalid Sushi LP");
      if (IERC20(eye).balanceOf(sushiLPs[i]) > 1000) assetApproved[sushiLPs[i]] = true;
      fateGrowthStrategy[sushiLPs[i]] = FateGrowthStrategy.indirectTwoRootEye;
    }
    for (uint256 i = 0; i < uniLPs.length; i++) {
      require(UniPairLike(uniLPs[i]).factory() == uniFactory, "LimboDAO: invalid Sushi LP");
      if (IERC20(eye).balanceOf(uniLPs[i]) > 1000) assetApproved[uniLPs[i]] = true;
      fateGrowthStrategy[uniLPs[i]] = FateGrowthStrategy.indirectTwoRootEye;
    }
  }

  ///@notice allows Limbo to be governed by a new DAO
  ///@dev functions marked by onlyOwner are governed by MorgothDAO
  function killDAO(address newOwner) public onlyOwner isLive {
    domainConfig.live = false;
    Governable(domainConfig.flan).setDAO(newOwner);
    Governable(domainConfig.limbo).setDAO(newOwner);
    emit daoKilled(newOwner);
  }

  ///@notice optional conversion rate of Fate to Flan
  function setFateToFlan(uint256 rate) public onlySuccessfulProposal {
    fateToFlan = rate;
  }

  ///@notice caller spends their Fate to earn Flan
  function convertFateToFlan(uint256 fate) public returns (uint256 flan) {
    require(fateToFlan > 0, "LimboDAO: Fate conversion to Flan disabled.");
    fateState[msg.sender].fateBalance -= fate;
    flan = (fateToFlan * fate) / ONE;
    Flan(domainConfig.flan).mint(msg.sender, flan);
  }

  /**@notice handles proposal lodging logic. A deposit of Fate is removed from the user. If the decision is a success, half the fate is returned.
   *  This is to encourage only lodging of proposals that are likely to succeed.
   *  @dev not for external calling. Use the proposalFactory to lodge a proposal instead.
   */
  function makeProposal(address proposal, address proposer) public updateCurrentProposal {
    address sender = msg.sender;
    require(sender == proposalConfig.proposalFactory, "LimboDAO: only Proposal Factory");
    require(address(currentProposalState.proposal) == address(0), "LimboDAO: active proposal.");

    fateState[proposer].fateBalance = fateState[proposer].fateBalance - proposalConfig.requiredFateStake * 2;
    currentProposalState.proposal = Proposal(proposal);
    currentProposalState.decision = ProposalDecision.voting;
    currentProposalState.fate = 0;
    currentProposalState.proposer = proposer;
    currentProposalState.start = block.timestamp;
    emit proposalLodged(proposal, proposer);
  }

  ///@notice handles proposal voting logic.
  ///@param proposal contract to be voted on
  ///@param fate positive is YES, negative is NO. Absolute value is deducted from caller.
  function vote(address proposal, int256 fate) public incrementFate isLive {
    require(
      proposal == address(currentProposalState.proposal), //this is just to protect users with out of sync UIs
      "LimboDAO: stated proposal does not match current proposal"
    );
    require(currentProposalState.decision == ProposalDecision.voting, "LimboDAO: voting on proposal closed");
    if (block.timestamp - currentProposalState.start > proposalConfig.votingDuration - 1 hours) {
      int256 currentFate = currentProposalState.fate;
      //check if voting has ended
      if (block.timestamp - currentProposalState.start > proposalConfig.votingDuration) {
        revert("LimboDAO: voting for current proposal has ended.");
      } else if (
        //The following if statement checks if the vote is flipped by fate
        fate * currentFate < 0 && //sign different
        (fate + currentFate) * fate > 0 //fate flipped current fate onto the same side of zero as fate
      ) {
        //extend voting duration when vote flips decision. Suggestion made by community member
        currentProposalState.start = currentProposalState.start + 2 hours;
      }
    }
    uint256 cost = fate > 0 ? uint256(fate) : uint256(-fate);
    fateState[msg.sender].fateBalance = fateState[msg.sender].fateBalance - cost;

    currentProposalState.fate += fate;
    emit voteCast(msg.sender, proposal, fate);
  }

  ///@notice pushes the decision to execute a successful proposal. For convenience only
  function executeCurrentProposal() public updateCurrentProposal {}

  ///@notice parameterizes the voting
  ///@param requiredFateStake the amount of Fate required to lodge a proposal
  ///@param votingDuration the duration of voting in seconds
  ///@param proposalFactory the address of the proposal factory
  function setProposalConfig(
    uint256 votingDuration,
    uint256 requiredFateStake,
    address proposalFactory
  ) public onlySuccessfulProposal {
    proposalConfig.votingDuration = votingDuration;
    proposalConfig.requiredFateStake = requiredFateStake;
    proposalConfig.proposalFactory = proposalFactory;
  }

  ///@notice Assets approved for earning Fate
  function setApprovedAsset(address asset, bool approved) public onlySuccessfulProposal {
    assetApproved[asset] = approved;
    fateGrowthStrategy[asset] = FateGrowthStrategy.indirectTwoRootEye;
    emit assetApproval(asset, approved);
  }

  ///@notice handles staking logic for EYE and EYE based assets so that correct rate of fate is earned.
  ///@param finalAssetBalance after staking, what is the final user balance on LimboDAO of the asset in question
  ///@param finalEYEBalance if EYE is being staked, this value is the same as finalAssetBalance but for LPs it's about half
  ///@param rootEYE offload high gas arithmetic to the client. Cheap to verify. Square root in fixed point requires Babylonian algorithm
  ///@param asset the asset being staked
  function setEYEBasedAssetStake(
    uint256 finalAssetBalance,
    uint256 finalEYEBalance,
    uint256 rootEYE,
    address asset
  ) public isLive incrementFate {
    require(assetApproved[asset], "LimboDAO: illegal asset");
    address sender = msg.sender;
    FateGrowthStrategy strategy = fateGrowthStrategy[asset];

    //verifying that rootEYE value is accurate within precision.
    uint256 rootEYESquared = rootEYE * rootEYE;
    uint256 rootEYEPlusOneSquared = (rootEYE + 1) * (rootEYE + 1);
    require(
      rootEYESquared <= finalEYEBalance && rootEYEPlusOneSquared > finalEYEBalance,
      "LimboDAO: Stake EYE invariant."
    );
    AssetClout storage clout = stakedUserAssetWeight[sender][asset];
    fateState[sender].fatePerDay -= clout.fateWeight;
    uint256 initialBalance = clout.balance;
    //EYE
    if (strategy == FateGrowthStrategy.directRoot) {
      require(finalAssetBalance == finalEYEBalance, "LimboDAO: staking eye invariant.");
      require(asset == domainConfig.eye);

      clout.fateWeight = rootEYE;
      clout.balance = finalAssetBalance;
      fateState[sender].fatePerDay += rootEYE;
    } else if (strategy == FateGrowthStrategy.indirectTwoRootEye) {
      //LP
      clout.fateWeight = 2 * rootEYE;
      fateState[sender].fatePerDay += clout.fateWeight;

      uint256 actualEyeBalance = IERC20(domainConfig.eye).balanceOf(asset);
      require(actualEyeBalance > 0, "LimboDAO: No EYE");
      uint256 totalSupply = IERC20(asset).totalSupply();
      uint256 eyePerUnit = (actualEyeBalance * ONE) / totalSupply;
      uint256 impliedEye = (eyePerUnit * finalAssetBalance) / (ONE * precision);
      finalEYEBalance /= precision;
      require(
        finalEYEBalance == impliedEye, //precision cap
        "LimboDAO: stake invariant check 2."
      );
      clout.balance = finalAssetBalance;
    } else {
      revert("LimboDAO: asset growth strategy not accounted for");
    }
    int256 netBalance = int256(finalAssetBalance) - int256(initialBalance);
    asset.ERC20NetTransfer(sender, address(this), netBalance);
  }

  /**
   *@notice Acquiring enough fate to either influence a decision or to lodge a proposal can take very long.
   * If a very important decision has to be acted on via a proposal, the option exists to buy large quantities for fate instantly by burning an EYE based asset
   * This may be necessary if a vote is nearly complete by the looming outcome is considered unacceptable.
   * While Fate accumulation is quadratic for staking, burning is linear and subject to a factor of 10. This gives whales effective veto power but at the cost of a permanent
   * loss of EYE.
   *@param asset the asset to burn and can be EYE or EYE based assets
   *@param amount the amount of asset to burn
   */
  function burnAsset(address asset, uint256 amount) public isLive incrementFate {
    require(assetApproved[asset], "LimboDAO: illegal asset");
    address sender = msg.sender;
    require(ERC677(asset).transferFrom(sender, address(this), amount), "LimboDAO: transferFailed");
    uint256 fateCreated = fateState[msg.sender].fateBalance;
    if (asset == domainConfig.eye) {
      fateCreated = amount * 10;
      ERC677(domainConfig.eye).burn(amount);
    } else {
      uint256 actualEyeBalance = IERC20(domainConfig.eye).balanceOf(asset);
      require(actualEyeBalance > 0, "LimboDAO: No EYE");
      uint256 totalSupply = IERC20(asset).totalSupply();
      uint256 eyePerUnit = (actualEyeBalance * ONE) / totalSupply;
      uint256 impliedEye = (eyePerUnit * amount) / ONE;
      fateCreated = impliedEye * 20;
    }
    fateState[msg.sender].fateBalance += fateCreated;
    emit assetBurnt(msg.sender, asset, fateCreated);
  }

  ///@notice grants unlimited Flan minting power to an address.
  function approveFlanMintingPower(address minter, bool enabled) public onlySuccessfulProposal isLive {
    Flan(domainConfig.flan).increaseMintAllowance(minter, enabled ? type(uint256).max : 0);
  }

  ///@notice call this after initial config is complete.
  function makeLive() public onlyOwner {
    require(
      Governable(domainConfig.limbo).DAO() == address(this) && Governable(domainConfig.flan).DAO() == address(this),
      "LimboDAO: transfer ownership of limbo and flan."
    );
    domainConfig.live = true;
  }

  ///@notice if the DAO is being dismantled, it's necessary to transfer any owned items
  function transferOwnershipOfThing(address thing, address destination) public onlySuccessfulProposal {
    Ownable(thing).transferOwnership(destination);
  }

  function timeRemainingOnProposal() public view returns (uint256) {
    require(currentProposalState.decision == ProposalDecision.voting, "LimboDAO: proposal finished.");
    uint256 elapsed = block.timestamp - currentProposalState.start;
    if (elapsed > proposalConfig.votingDuration) return 0;
    return proposalConfig.votingDuration - elapsed;
  }

  /**@notice seed is a goro idiom for initialize that you tend to find in all the dapps I've written.
   * I prefer initialization funcitons to parameterized solidity constructors for reasons beyond the scope of this comment.
   */
  function _seed(
    address limbo,
    address flan,
    address eye,
    address sushiFactory,
    address uniFactory,
    address flashGoverner
  ) internal {
    domainConfig.limbo = limbo;
    domainConfig.flan = flan;
    domainConfig.eye = eye;
    domainConfig.uniFactory = uniFactory;
    domainConfig.sushiFactory = sushiFactory;
    domainConfig.flashGoverner = flashGoverner;
    assetApproved[eye] = true;
    fateGrowthStrategy[eye] = FateGrowthStrategy.directRoot;
  }

  function getFlashGoverner() external view returns (address) {
    return domainConfig.flashGoverner;
  }
}

contract MockAddTokenPower is LimboAddTokenToBehodlerPowerLike {
    address behodler;
    address limbo;
    uint256 scxToMint = 10000;

    function setScarcityToMint(uint256 _scarcity) public {
        scxToMint = _scarcity;
    }

    function seed(address _behodler, address _limbo) public {
        limbo = _limbo;
        behodler = _behodler;
    }

    function parameterize(address token, bool burnable) public override {}

    function invoke() public {
        MockBehodler(behodler).mint(scxToMint);
        MockBehodler(behodler).transfer(limbo, scxToMint);
    }
}

contract MockAngband {

    function executePower(address invoker) public {
        MockAddTokenPower(invoker).invoke();
    }
}
