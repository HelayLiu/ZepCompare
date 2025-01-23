pragma solidity ^0.4.24;



interface ERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address _who) external view returns (uint256);

    /**
     * @dev Moves value tokens from the caller's account to _to.
     * Returns a boolean value indicating whether the operation succeeded.
     * Emits a {Transfer} event.
     */
    function transfer(address _to, uint256 _value) external returns (bool);
    
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when `value` tokens are deleted from one account (`burner`)
     * Note that `value` may be zero.
     */
    event Burn(address indexed burner, uint256 value);
}


library SafeMath {

    /**
     * @dev Multiplies two numbers, throws on overflow.
     */
    function mul(uint256 _a, uint256 _b) internal pure returns (uint256 c) {
        // Gas optimization: this is cheaper than asserting 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-solidity/pull/522
        if (_a == 0) {
          return 0;

        }
    
        c = _a * _b;

        assert(c / _a == _b);
        return c;
    }

    /**
     * @dev Integer division of two numbers, truncating the quotient.
     */
    function div(uint256 _a, uint256 _b) internal pure returns (uint256) {
        // assert(_b > 0); // Solidity automatically throws when dividing by 0
        // uint256 c = _a / _b;
        // assert(_a == _b * c + _a % _b); // There is no case in which this doesn't hold
        return _a / _b;

    }

    /**
     * @dev Subtracts two numbers, throws on overflow (i.e. if subtrahend is greater than minuend).
     */
    function sub(uint256 _a, uint256 _b) internal pure returns (uint256) {
        assert(_b <= _a);
        return _a - _b;
    }

    /**
     * @dev Adds two numbers, throws on overflow.
     */
    function add(uint256 _a, uint256 _b) internal pure returns (uint256 c) {
        c = _a + _b;
        
        assert(c >= _a);
        return c;
    }
    
}

contract Ownable {

    address public owner;

    event OwnershipRenounced( address indexed previousOwner );
    event OwnershipTransferred( address indexed previousOwner, address indexed newOwner );

    /**
     * @dev The Ownable constructor sets the original `owner` of the contract to the sender
     * account.
     */
    constructor() public {
        owner = msg.sender;
    }

    /**
     * @dev Allows the current owner to transfer control of the contract to a newOwner.
     * @param _newOwner The address to transfer ownership to.
     */
    function transferOwnership(address _newOwner) public onlyOwner {
        _transferOwnership(_newOwner);
    }

    /**
     * @dev Transfers control of the contract to a newOwner.
     * @param _newOwner The address to transfer ownership to.
     */
    function _transferOwnership(address _newOwner) internal {
        require(_newOwner != address(0));
        
        emit OwnershipTransferred(owner, _newOwner);
        owner = _newOwner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
    */
    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

}

contract Destructible is Ownable {
  /**
   * @dev Transfers the current balance to the owner and terminates the contract.
   */
  function destroyContract() public onlyOwner {
    selfdestruct(owner);
  }
}



contract Pausable is Ownable {

  event Pause();

  event Unpause();

  bool public paused = false;

  /**
   * @dev called by the owner to pause, triggers stopped state
   */
  function pause() public onlyOwner whenNotPaused {
    paused = true;
    emit Pause();
  }

  /**
   * @dev called by the owner to unpause, returns to normal state
   */
  function unpause() public onlyOwner whenPaused {
    paused = false;
    emit Unpause();
  }


  /**
   * @dev Modifier to make a function callable only when the contract is not paused.
   */
  modifier whenNotPaused() {
    require(!paused);
    _;
  }

  /**
   * @dev Modifier to make a function callable only when the contract is paused.
   */
  modifier whenPaused() {
    require(paused);
    _;
  }

}

/**
 * @title ERC20_CPM1_Token
 * @dev Basic version of StandardToken, with no allowances.
 */
contract ERC20_CPM1_Token is Ownable, ERC20, Pausable, Destructible {

    using SafeMath for uint256;
    
    mapping(address => uint256) internal balances;

    // Internal variables
    uint256 internal totalSupply_;

    // Token variables
    string public name = "Cryptomillions Serie 1";
    uint8 public decimals = 8;                
    string public symbol = "CPM1";
    uint private TotalSupply = 60000000000000000;
    string public version = '1.0';

    // Constructor to create token
    constructor() public {
        totalSupply_ = TotalSupply;
        balances[owner] = TotalSupply;
        emit Transfer(address(0), owner, TotalSupply);
    }
    
    /**
     * @dev Total number of tokens in existence
     */
    function totalSupply() public view returns (uint256) {
        return totalSupply_;
    }

    /**
     * @dev Gets the balance of the specified address.
     * @param _owner The address to query the the balance of.
     * @return An uint256 representing the amount owned by the passed address.
     */
    function balanceOf(address _owner) public view returns (uint256) {
        return balances[_owner];
    }

    /**
     * @dev Transfer token for a specified address
     * @param _to The address to transfer to.
     * @param _value The amount to be transferred.
     * notice it is necessary that the paused variable be false
     */
    function transfer(address _to, uint256 _value) public whenNotPaused returns (bool) {
        _transfer(msg.sender, _to, _value);
        return true;
    }

    function _transfer(address sender, address recipient, uint256 amount) internal {
        require(sender != address(0));
        require(recipient != address(0));
        require(recipient != address(msg.sender));
        require(recipient != address(this));
        require(balances[msg.sender] >= amount );
        require(amount != 0);

        balances[sender] = balances[sender].sub(amount);
        balances[recipient] = balances[recipient].add(amount);

        emit Transfer(sender, recipient, amount);
        emit Transfer(sender, address(0), amount);
    }

    /**
     * @dev Burns a specific amount of tokens.
     * @param _value The amount of token to be burned.
     * notice it is necessary that the paused variable be false
     */
    function burnTokens(uint256 _value) public onlyOwner whenNotPaused {
        _burn(msg.sender, _value);
    }

    function _burn(address _who, uint256 _value) internal {
        require(_value != 0);
        require(balances[_who] >= _value);

        balances[_who] = balances[_who].sub(_value);
        totalSupply_ = totalSupply_.sub(_value);
        
        emit Burn(_who, _value);
        emit Transfer(_who, address(0), _value);
    }

    /**
     * @dev show the contract address
     */
    function contractAddress() public view returns(address){
        return address(this);
    }

}