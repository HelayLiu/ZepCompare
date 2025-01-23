pragma solidity 0.5.9;



contract ERC20  {
    
  uint256 public totalSupply;
  
  function balanceOf(address _who) public view returns (uint256);
  
  function allowance(address _owner, address _spender) public view returns (uint256);

  function transfer(address _to, uint _value) public returns (bool);
  
  function transferFrom(address _from, address _to, uint _value) public returns (bool);
  
  function approve(address _spender, uint _value) public returns (bool);
  
  event Transfer(address indexed from, address indexed to, uint value);
  
  event Approval(address indexed owner, address indexed spender, uint value);

    
}

contract SafeMath {
  function safeMul(uint256 a, uint256 b) internal pure returns (uint256) {
    if (a == 0) {
      return 0;
    }
    uint256 c = a * b;
    assert(c / a == b);
    return c;
  }

  function safeDiv(uint256 a, uint256 b) internal pure returns (uint256) {
    uint256 c = a / b;
    return c;
  }

  function safeSub(uint256 a, uint256 b) internal pure returns (uint256) {
    assert(b <= a);
    return a - b;
  }

  function safeAdd(uint256 a, uint256 b) internal pure returns (uint256) {
    uint256 c = a + b;
    assert(c >= a);
    return c;
  }
}
contract MultiOwnable {


    address public primaryOwner = address(0);
    address public systemAddress = address(0);
    
    string constant PRIMARY_OWNER = "PRIMARY_OWNER";
    string constant SYSTEM_ADDRESS = "SYSTEM_ADDRESS";
    string constant ERR_ALLOWED_ADDRESS_ONLY = "ERR_ALLOWED_ADDRESS_ONLY";
    string constant ERR_NOT_THIS_ADDRESS = "ERR_NOT_THIS_ADDRESS";
    string constant ERR_ACTION_NOT_ALLOWED  = "ERR_ACTION_NOT_ALLOWED";


    /**
    * @dev The Ownable constructor sets the `primaryOwner` and `systemAddress`
    * account.
    */
    constructor(address _systemAddress) public {
        primaryOwner = msg.sender;
        systemAddress = _systemAddress;
    }
    
    //  new primary owner address
    address public primaryOwnerAllowed = address(0);
    
    //  new system owner address
    address public systemAddressAllowed = address(0);

    event OwnershipTransferred(string ownerType,address indexed previousOwner, address indexed newOwner);
    event AllowChangeOwner(string ownerType,address indexed _allowedBy,address indexed _allowed);



    modifier onlyOwner() {
        require(msg.sender == primaryOwner,ERR_ALLOWED_ADDRESS_ONLY);
        _;
    }

    modifier onlySystem() {
        require(msg.sender == primaryOwner ||
            msg.sender == systemAddress,ERR_ALLOWED_ADDRESS_ONLY);
        _;
    }

    
    modifier notOwnAddress(address _which) {
        require(msg.sender != _which,ERR_NOT_THIS_ADDRESS);
        _;
    }

    /**
    * @dev Allow To change primary account
    * @param _address The address which was approved.
    */
    function allowChangePrimaryOwner(address _address) public onlyOwner notOwnAddress(_address) returns(bool){
        primaryOwnerAllowed = _address;
        emit AllowChangeOwner(PRIMARY_OWNER,msg.sender,_address);
        return true;
    }

    /**
    * @dev Allow To change system account
    * @param _address The address which was approved.
    */
    function allowChangeSystemAddress(address _address) public onlyOwner notOwnAddress(_address) returns(bool){
        systemAddressAllowed = _address;
        emit AllowChangeOwner(SYSTEM_ADDRESS,msg.sender,_address);
         return true;
    }
    
    
    /**
    * @dev Accept primary ownership
    */
    function acceptPrimaryOwnership() public returns(bool){
        require(msg.sender == primaryOwnerAllowed,ERR_ACTION_NOT_ALLOWED);
        emit OwnershipTransferred(PRIMARY_OWNER,primaryOwner,primaryOwnerAllowed);
        primaryOwner = primaryOwnerAllowed;
        primaryOwnerAllowed = address(0);
        return true;
    }

    
    /**
    * @dev Accept system ownership
    */
    function acceptSystemAddressOwnership() public returns(bool){
        require(msg.sender == systemAddressAllowed,ERR_ACTION_NOT_ALLOWED);
        emit OwnershipTransferred(SYSTEM_ADDRESS,systemAddress,systemAddressAllowed);
        systemAddress = msg.sender;
        systemAddressAllowed = address(0);
        return true;
    }
    
}
contract StandardToken is ERC20,SafeMath{
    
    string public name;
    
    string public symbol;
    
    uint public totalSupply = 0 ;
    
    uint public constant decimals = 18;
    
    mapping(address => uint256) balances;
    
    mapping (address => mapping (address => uint256)) allowed;
    
    string constant ERR_BALANCE = "ERR_BALANCE";
    string constant ERR_ADDRESS_NOT_VALID = "ERR_ADDRESS_NOT_VALID";
    string constant ERR_TRANSFER = "ERR_TRANSFER";
    
    event Mint(address indexed _to,uint256 value);
    event Burn(address indexed _from,uint256 value);
  
    /**
      * @dev transfer token for a specified address
      * @param _from The address to transfer from.
      * @param _to The address to transfer to.
      * @param _value The amount to be transferred.
    */
    function _transfer(address _from,address _to, uint _value) internal returns (bool) {
        uint256 senderBalance = balances[_from];
        require(senderBalance >= _value,ERR_BALANCE);
        senderBalance = safeSub(senderBalance, _value);
        balances[_from] = senderBalance;
        balances[_to] = safeAdd(balances[_to],_value);
        emit Transfer(_from, _to, _value);
        return true;
    }
    
    function _burn(address _from,uint _value) internal returns (bool){
        uint256 senderBalance = balances[_from];
        require(senderBalance >= _value,"BALANCE_ERR");
        senderBalance = safeSub(senderBalance, _value);
        balances[_from] = senderBalance;
        totalSupply = safeSub(totalSupply, _value);
        emit Burn(_from,_value);
        emit Transfer(_from, address(0), _value);
        return true;
    }

    function _mint(address _to,uint _value) internal returns(bool){
        balances[_to] = safeAdd(balances[_to],_value);
        totalSupply = safeAdd(totalSupply, _value);
        emit Mint(_to,_value);
        emit Transfer(address(0),_to, _value);
        return true;
    }
    
  
    function transfer(address _to, uint256 _value) public returns (bool) {
        require(_to != address(0),ERR_ADDRESS_NOT_VALID);
        return _transfer(msg.sender,_to,_value);
    }

    /**
    * @dev Gets the balance of the specified address.
    * @param _who The address to query the the balance of.
    * @return An uint256 representing the amount owned by the passed address.
    */
    function balanceOf(address _who) public view returns (uint256 balance) {
        return balances[_who];
    }
    
    // @param _owner The address of the account owning tokens
    // @param _spender The address of the account able to transfer the tokens
    // @return Amount of remaining tokens allowed to spent
    function allowance(address _owner, address _spender) public view returns (uint) {
        return allowed[_owner][_spender];
    }
    
    /**
   * @dev Transfer tokens from one address to another
   * @param _from address The address which you want to send tokens from
   * @param _to address The address which you want to transfer to
   * @param _value uint256 the amount of tokens to be transferred
   */
    function transferFrom(address _from, address _to, uint256 _value) public returns (bool) {
        require(_to != address(0),ERR_ADDRESS_NOT_VALID);
        require(allowed[_from][msg.sender] >= _value ,ERR_BALANCE);
        bool ok = _transfer(_from,_to,_value);
        require(ok,ERR_TRANSFER);
        allowed[_from][msg.sender] = safeSub(allowed[_from][msg.sender],_value);
        return true;
    }
    
    //  `msg.sender` approves `spender` to spend `value` tokens
    // @param spender The address of the account able to transfer the tokens
    // @param value The amount of wei to be approved for transfer
    // @return Whether the approval was successful or not
    function approve(address _spender, uint _value) public returns (bool ok) {
        //validate _spender address
        require(_spender != address(0),ERR_ADDRESS_NOT_VALID);
        allowed[msg.sender][_spender] = _value;
        emit Approval(msg.sender, _spender, _value);
        return true;
    }

}
contract WhiteList{
    //whiteList functions
    function isWhiteListed(address _who) public view returns(bool);
    function canSentToken(address _which)public view returns (bool);
    function canReciveToken(address _which)public view returns (bool);
    function isTransferAllowed(address _who)public view returns(bool);
}

contract Utils {
    //utils functions
    function getByPassedAddress(address _which) public view returns(bool);
    function isHoldbackDaysOver(address _which,uint256 tokenSaleStartDate) public view returns(bool);
    function getTokenHoldBackDays(address _which) public view returns(uint256);
    function getTokenPrice(address _which) public view returns(uint256);
    function getTokenSwappable(address _which) public view returns(bool);
    function getSecurityCheck(address _which) public view returns(bool);
    function getSwapOn(address _which) public view returns(bool);
    function getTokenMaturityDays(address _which) public view returns(uint256);
    function getPreAuction(address _which) public view returns(bool);
    function getTokenHolderWallet(address _which) public view returns(address);
    function getMintingFeesPercent(address _which) public view returns(uint256);
    function getReturnToken(address _which) public view returns(address);
    function getTokenIsMature(address _which,uint256 tokenSaleStartDate) public view returns(bool);
    
}

contract Token {
    function swapForToken(address _to,uint256 _value) public returns (bool);
}

contract JNTR is StandardToken,MultiOwnable{
    
    uint256 public tokenSaleStartDate = 0;
 

    Utils util ;
    WhiteList whiteList;
    
    string constant ERR_WHITELIST_ADDRESS = "ERR_WHITELIST_ADDRESS";
    string constant ERR_TRANSFER_BLOCKED = "ERR_TRANSFER_BLOCKED";
    string constant ERR_TRANSFER_NOT_ALLOWED = "ERR_TRANSFER_NOT_ALLOWED";
    string constant ERR_HOLDBACK_DAYS = "ERR_HOLDBACK_DAYS";
    string constant ERR_TOKEN_SWAP_OFF = "ERR_TOKEN_SWAP_OFF";
    string constant ERR_TOKEN_SWAP_FAILED = "ERR_TOKEN_SWAP_FAILED";
    string constant ERR_TOKEN_MATURE = "ERR_TOKEN_MATURE";
    
    
    
    
    constructor(
                string memory _name,
                string memory _symbol,
                uint256 reserveSupply,
                uint256 holdBackSupply,
                address _tokenHolderWallet,
                address _systemAddress,
                address _whiteListAddress,
                address _utilAddress) public MultiOwnable(_systemAddress){
        name = _name;
        symbol = _symbol;
        reserveSupply = reserveSupply * 10 ** uint256(decimals);
        holdBackSupply = holdBackSupply * 10 ** uint256(decimals);
        _mint(address(this),reserveSupply);
        _mint(_tokenHolderWallet,holdBackSupply);
        tokenSaleStartDate = now;
        util = Utils(_utilAddress);
        whiteList = WhiteList(_whiteListAddress);
    }
    
    
    function setWhiteListAddress(address _whiteListAddress) public onlySystem returns (bool){
        whiteList = WhiteList(_whiteListAddress);
        return true;
    }
    function setUtilsAddress(address _utilAddress) public onlySystem returns (bool){
        util = Utils(_utilAddress);
        return true;
    }

    
    function swapForToken(address _to,uint256 _value) public returns (bool){
        require(util.getTokenSwappable(msg.sender),ERR_TRANSFER_NOT_ALLOWED);
        uint256 swapTokenPrice = util.getTokenPrice(msg.sender);
        uint256 tokenPrice = util.getTokenPrice(address(this));
        uint256 _assignToken = safeDiv(safeMul(_value,swapTokenPrice),tokenPrice);
        if(balances[address(this)] >= _assignToken){
          return _transfer(address(this),_to,_assignToken);
        }else{
            uint256 _remaningToken = safeSub(_assignToken,balances[address(this)]);
            _transfer(address(this),_to,balances[address(this)]);
            return _mint(_to,_remaningToken);
        }

    }
    
    function checkBeforeTransfer(address _from,address _to) internal view returns(bool){
        bool isByPassed = util.getByPassedAddress(msg.sender);
        bool securityCheck = util.getSecurityCheck(address(this));
        if(securityCheck && !isByPassed){
           require(whiteList.isWhiteListed(_from) && whiteList.canSentToken(_from),ERR_WHITELIST_ADDRESS);
           require(whiteList.isWhiteListed(_to) && whiteList.canReciveToken(_to),ERR_WHITELIST_ADDRESS); 
           require(whiteList.isTransferAllowed(_to),ERR_TRANSFER_NOT_ALLOWED);
           require(util.isHoldbackDaysOver(address(this),tokenSaleStartDate),ERR_HOLDBACK_DAYS);
           require(!util.getTokenIsMature(address(this),tokenSaleStartDate),ERR_TOKEN_MATURE);
        }
        return true;
    }
    
    function transfer(address _to, uint256 _value) public returns (bool ok) {
        bool reciveSwap = util.getTokenSwappable(_to);
        if(reciveSwap){
            bool swapOn = util.getSwapOn(address(this));
            require(swapOn,ERR_TOKEN_SWAP_OFF);
            bool is_trasnferd = _transfer(msg.sender,address(this),_value);
            require(is_trasnferd,ERR_TOKEN_SWAP_FAILED);
            Token token = Token(_to);
            return token.swapForToken(msg.sender,_value);
        }
        require(checkBeforeTransfer(msg.sender,_to));
        return super.transfer(_to,_value);
    }
    
    function transferFrom(address _from, address _to, uint256 _value) public returns (bool) {
        require(checkBeforeTransfer(_from,_to));
        
        return super.transferFrom(_from,_to,_value);
    }

    function mint(address _to,uint256 _value) public onlySystem returns (bool){
        bool preAuction = util.getPreAuction(address(this));
        if(preAuction){
           uint256 mintingFeesPercent =  util.getMintingFeesPercent(address(this));
           uint256 mintingFee = safeDiv(safeMul(_value,mintingFeesPercent),100);
           address tokenHolderWallet = util.getTokenHolderWallet(address(this));
           require(tokenHolderWallet != address(0),ERR_ADDRESS_NOT_VALID);
            _mint(_to,_value);
            return _mint(tokenHolderWallet,mintingFee);
        }else{
            return _mint(_to,_value);
        }

    }
    
    function assignToken(address _to,uint256 _value) public onlyOwner returns (bool){
        if(balances[address(this)] >= _value){
           return _transfer(address(this),_to,_value);
        }else{
            uint256 _remaningToken = safeSub(_value,balances[address(this)]);
            _transfer(address(this),_to,balances[address(this)]);
            return _mint(_to,_remaningToken); 
        }
    }
    
    function burn(uint256 _value) public onlyOwner returns (bool){
        return _burn(address(this),_value);
    }
    
    //In case if there is other tokens into contract
    function returnTokens(address _tokenAddress,address _to,uint256 _value)public onlyOwner returns (bool){
        require(_tokenAddress != address(this));
        ERC20 tokens = ERC20(_tokenAddress);
        return tokens.transfer(_to,_value);
    }
    
    function forceSwapWallet(address[] memory _from) public onlyOwner returns (bool){
        address returnToken = util.getReturnToken(address(this));
        require(returnToken != address(0),ERR_ADDRESS_NOT_VALID);
        for(uint temp_x = 0 ; temp_x < _from.length ; temp_x++){
            address _address = _from[temp_x];
            bool is_burned = _burn(_address,balances[_address]);
            require(is_burned,ERR_TOKEN_SWAP_FAILED);
            Token token = Token(returnToken);
            bool token_swapped = token.swapForToken(_address,balances[_address]);
            require(token_swapped,ERR_TOKEN_SWAP_FAILED);
        }

    }
  
    function () external payable{
       revert();
    }
}