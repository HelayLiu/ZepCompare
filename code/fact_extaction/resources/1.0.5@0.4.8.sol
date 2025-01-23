// SPDX-License-Identifier: MIT
pragma solidity ^0.4.8;

contract ReentrancyGuard {

  /// @dev We use a single lock for the whole contract.
  bool private rentrancy_lock = false;

  /// Prevent contract from calling itself, directly or indirectly.
  /// @notice If you mark a function `nonReentrant`, you should also
  /// mark it `external`. Calling one nonReentrant function from
  /// another is not supported. Instead, you can implement a
  /// `private` function doing the actual work, and a `external`
  /// wrapper marked as `nonReentrant`.
  modifier nonReentrant() {
    if(rentrancy_lock == false) {
      rentrancy_lock = true;
      _;
      rentrancy_lock = false;
    } else {
      throw;
    }
  }

}

/*
 * Shareable
 *
 * Based on https://github.com/ethereum/dapp-bin/blob/master/wallet/wallet.sol
 *
 * inheritable "property" contract that enables methods to be protected by requiring the acquiescence of either a single, or, crucially, each of a number of, designated owners.
 *
 * usage:
 * use modifiers onlyowner (just own owned) or onlymanyowners(hash), whereby the same hash must be provided by some number (specified in constructor) of the set of owners (specified in the constructor) before the interior is executed.
 */
contract Shareable {
  // struct for the status of a pending operation.
  struct PendingState {
    uint yetNeeded;
    uint ownersDone;
    uint index;
  }

  // the number of owners that must confirm the same operation before it is run.
  uint public required;

  // list of owners
  address[256] owners;
  // index on the list of owners to allow reverse lookup
  mapping(address => uint) ownerIndex;
  // the ongoing operations.
  mapping(bytes32 => PendingState) pendings;
  bytes32[] pendingsIndex;


  // this contract only has six types of events: it can accept a confirmation, in which case
  // we record owner and operation (hash) alongside it.
  event Confirmation(address owner, bytes32 operation);
  event Revoke(address owner, bytes32 operation);


  // simple single-sig function modifier.
  modifier onlyOwner {
    if (!isOwner(msg.sender)) {
      throw;
    }
    _;
  }

  // multi-sig function modifier: the operation must have an intrinsic hash in order
  // that later attempts can be realised as the same underlying operation and
  // thus count as confirmations.
  modifier onlymanyowners(bytes32 _operation) {
    if (confirmAndCheck(_operation)) {
      _;
    }
  }

  // constructor is given number of sigs required to do protected "onlymanyowners" transactions
  // as well as the selection of addresses capable of confirming them.
  function Shareable(address[] _owners, uint _required) {
    owners[1] = msg.sender;
    ownerIndex[msg.sender] = 1;
    for (uint i = 0; i < _owners.length; ++i) {
      owners[2 + i] = _owners[i];
      ownerIndex[_owners[i]] = 2 + i;
    }
    required = _required;
    if (required > owners.length) {
      throw;
    }
  }

  // Revokes a prior confirmation of the given operation
  function revoke(bytes32 _operation) external {
    uint index = ownerIndex[msg.sender];
    // make sure they're an owner
    if (index == 0) {
      return;
    }
    uint ownerIndexBit = 2**index;
    var pending = pendings[_operation];
    if (pending.ownersDone & ownerIndexBit > 0) {
      pending.yetNeeded++;
      pending.ownersDone -= ownerIndexBit;
      Revoke(msg.sender, _operation);
    }
  }

  // Gets an owner by 0-indexed position (using numOwners as the count)
  function getOwner(uint ownerIndex) external constant returns (address) {
    return address(owners[ownerIndex + 1]);
  }

  function isOwner(address _addr) constant returns (bool) {
    return ownerIndex[_addr] > 0;
  }

  function hasConfirmed(bytes32 _operation, address _owner) constant returns (bool) {
    var pending = pendings[_operation];
    uint index = ownerIndex[_owner];

    // make sure they're an owner
    if (index == 0) {
      return false;
    }

    // determine the bit to set for this owner.
    uint ownerIndexBit = 2**index;
    return !(pending.ownersDone & ownerIndexBit == 0);
  }

  // returns true when operation can be executed
  function confirmAndCheck(bytes32 _operation) internal returns (bool) {
    // determine what index the present sender is:
    uint index = ownerIndex[msg.sender];
    // make sure they're an owner
    if (index == 0) {
      throw;
    }

    var pending = pendings[_operation];
    // if we're not yet working on this operation, switch over and reset the confirmation status.
    if (pending.yetNeeded == 0) {
      // reset count of confirmations needed.
      pending.yetNeeded = required;
      // reset which owners have confirmed (none) - set our bitmap to 0.
      pending.ownersDone = 0;
      pending.index = pendingsIndex.length++;
      pendingsIndex[pending.index] = _operation;
    }
    // determine the bit to set for this owner.
    uint ownerIndexBit = 2**index;
    // make sure we (the message sender) haven't confirmed this operation previously.
    if (pending.ownersDone & ownerIndexBit == 0) {
      Confirmation(msg.sender, _operation);
      // ok - check if count is enough to go ahead.
      if (pending.yetNeeded <= 1) {
        // enough confirmations: reset and run interior.
        delete pendingsIndex[pendings[_operation].index];
        delete pendings[_operation];
        return true;
      } else {
        // not enough: record that this owner in particular confirmed.
        pending.yetNeeded--;
        pending.ownersDone |= ownerIndexBit;
      }
    }
    return false;
  }

  function clearPending() internal {
    uint length = pendingsIndex.length;
    for (uint i = 0; i < length; ++i) {
      if (pendingsIndex[i] != 0) {
        delete pendings[pendingsIndex[i]];
      }
    }
    delete pendingsIndex;
  }

}

/*
 * DayLimit
 *
 * inheritable "property" contract that enables methods to be protected by placing a linear limit (specifiable)
 * on a particular resource per calendar day. is multiowned to allow the limit to be altered. resource that method
 * uses is specified in the modifier.
 */
contract DayLimit {

  uint public dailyLimit;
  uint public spentToday;
  uint public lastDay;


  function DayLimit(uint _limit) {
    dailyLimit = _limit;
    lastDay = today();
  }

  // sets the daily limit. doesn't alter the amount already spent today
  function _setDailyLimit(uint _newLimit) internal {
    dailyLimit = _newLimit;
  }

  // resets the amount already spent today.
  function _resetSpentToday() internal {
    spentToday = 0;
  }

  // checks to see if there is at least `_value` left from the daily limit today. if there is, subtracts it and
  // returns true. otherwise just returns false.
  function underLimit(uint _value) internal returns (bool) {
    // reset the spend limit if we're on a different day to last time.
    if (today() > lastDay) {
      spentToday = 0;
      lastDay = today();
    }
    // check to see if there's enough left - if so, subtract and return true.
    // overflow protection                    // dailyLimit check
    if (spentToday + _value >= spentToday && spentToday + _value <= dailyLimit) {
      spentToday += _value;
      return true;
    }
    return false;
  }

  // determines today's index.
  function today() private constant returns (uint) {
    return now / 1 days;
  }


  // simple modifier for daily limit.
  modifier limitedDaily(uint _value) {
    if (!underLimit(_value)) {
      throw;
    }
    _;
  }
}

/*
 * Multisig
 * Interface contract for multisig proxy contracts; see below for docs.
 */
contract Multisig {
  // EVENTS

  // logged events:
  // Funds has arrived into the wallet (record how much).
  event Deposit(address _from, uint value);
  // Single transaction going out of the wallet (record who signed for it, how much, and to whom it's going).
  event SingleTransact(address owner, uint value, address to, bytes data);
  // Multi-sig transaction going out of the wallet (record who signed for it last, the operation hash, how much, and to whom it's going).
  event MultiTransact(address owner, bytes32 operation, uint value, address to, bytes data);
  // Confirmation still needed for a transaction.
  event ConfirmationNeeded(bytes32 operation, address initiator, uint value, address to, bytes data);


  // FUNCTIONS

  // TODO: document
  function changeOwner(address _from, address _to) external;
  function execute(address _to, uint _value, bytes _data) external returns (bytes32);
  function confirm(bytes32 _h) returns (bool);
}


/**
 * LimitBalance
 * Simple contract to limit the balance of child contract.
 * Note this doesn't prevent other contracts to send funds 
 * by using selfdestruct(address);
 * See: https://github.com/ConsenSys/smart-contract-best-practices#remember-that-ether-can-be-forcibly-sent-to-an-account
 */
contract LimitBalance {

  uint public limit;

  function LimitBalance(uint _limit) {
    limit = _limit;
  }

  modifier limitedPayable() { 
    if (this.balance > limit) {
      throw;
    }
    _;
    
  }

}

/**
 * Math operations with safety checks
 */
library SafeMath {
  function mul(uint a, uint b) internal returns (uint) {
    uint c = a * b;
    assert(a == 0 || c / a == b);
    return c;
  }

  function div(uint a, uint b) internal returns (uint) {
    assert(b > 0);
    uint c = a / b;
    assert(a == b * c + a % b);
    return c;
  }

  function sub(uint a, uint b) internal returns (uint) {
    assert(b <= a);
    return a - b;
  }

  function add(uint a, uint b) internal returns (uint) {
    uint c = a + b;
    assert(c >= a);
    return c;
  }

  function max64(uint64 a, uint64 b) internal constant returns (uint64) {
    return a >= b ? a : b;
  }

  function min64(uint64 a, uint64 b) internal constant returns (uint64) {
    return a < b ? a : b;
  }

  function max256(uint256 a, uint256 b) internal constant returns (uint256) {
    return a >= b ? a : b;
  }

  function min256(uint256 a, uint256 b) internal constant returns (uint256) {
    return a < b ? a : b;
  }

  function assert(bool assertion) internal {
    if (!assertion) {
      throw;
    }
  }
}

/*
 * Ownable
 *
 * Base contract with an owner.
 * Provides onlyOwner modifier, which prevents function from running if it is called by anyone other than the owner.
 */
contract Ownable {
  address public owner;

  function Ownable() {
    owner = msg.sender;
  }

  modifier onlyOwner() {
    if (msg.sender != owner) {
      throw;
    }
    _;
  }

  function transferOwnership(address newOwner) onlyOwner {
    if (newOwner != address(0)) {
      owner = newOwner;
    }
  }

}

/*
 * ERC20Basic
 * Simpler version of ERC20 interface
 * see https://github.com/ethereum/EIPs/issues/20
 */
contract ERC20Basic {
  uint public totalSupply;
  function balanceOf(address who) constant returns (uint);
  function transfer(address to, uint value);
  event Transfer(address indexed from, address indexed to, uint value);
}

/*
 * MultisigWallet
 * usage:
 * bytes32 h = Wallet(w).from(oneOwner).execute(to, value, data);
 * Wallet(w).from(anotherOwner).confirm(h);
 */
contract MultisigWallet is Multisig, Shareable, DayLimit {

  struct Transaction {
    address to;
    uint value;
    bytes data;
  }

  function MultisigWallet(address[] _owners, uint _required, uint _daylimit)       
    Shareable(_owners, _required)        
    DayLimit(_daylimit) { }

  // destroys the contract sending everything to `_to`.
  function destroy(address _to) onlymanyowners(keccak256(msg.data)) external {
    selfdestruct(_to);
  }

  // gets called when no other function matches
  function() payable {
    // just being sent some cash?
    if (msg.value > 0)
      Deposit(msg.sender, msg.value);
  }

  // Outside-visible transact entry point. Executes transaction immediately if below daily spend limit.
  // If not, goes into multisig process. We provide a hash on return to allow the sender to provide
  // shortcuts for the other confirmations (allowing them to avoid replicating the _to, _value
  // and _data arguments). They still get the option of using them if they want, anyways.
  function execute(address _to, uint _value, bytes _data) external onlyOwner returns (bytes32 _r) {
    // first, take the opportunity to check that we're under the daily limit.
    if (underLimit(_value)) {
      SingleTransact(msg.sender, _value, _to, _data);
      // yes - just execute the call.
      if (!_to.call.value(_value)(_data)) {
        throw;
      }
      return 0;
    }
    // determine our operation hash.
    _r = keccak256(msg.data, block.number);
    if (!confirm(_r) && txs[_r].to == 0) {
      txs[_r].to = _to;
      txs[_r].value = _value;
      txs[_r].data = _data;
      ConfirmationNeeded(_r, msg.sender, _value, _to, _data);
    }
  }

  // confirm a transaction through just the hash. we use the previous transactions map, txs, in order
  // to determine the body of the transaction from the hash provided.
  function confirm(bytes32 _h) onlymanyowners(_h) returns (bool) {
    if (txs[_h].to != 0) {
      if (!txs[_h].to.call.value(txs[_h].value)(txs[_h].data)) {
        throw;
      }
      MultiTransact(msg.sender, _h, txs[_h].value, txs[_h].to, txs[_h].data);
      delete txs[_h];
      return true;
    }
  }

  function setDailyLimit(uint _newLimit) onlymanyowners(keccak256(msg.data)) external {
    _setDailyLimit(_newLimit);
  }

  function resetSpentToday() onlymanyowners(keccak256(msg.data)) external {
    _resetSpentToday();
  }


  // INTERNAL METHODS

  function clearPending() internal {
    uint length = pendingsIndex.length;
    for (uint i = 0; i < length; ++i) {
      delete txs[pendingsIndex[i]];
    }
    super.clearPending();
  }


  // FIELDS

  // pending transactions we have at present.
  mapping (bytes32 => Transaction) txs;
}

/*
 * PullPayment
 * Base contract supporting async send for pull payments.
 * Inherit from this contract and use asyncSend instead of send.
 */
contract PullPayment {
  using SafeMath for uint;

  mapping(address => uint) public payments;
  uint public totalPayments;

  // store sent amount as credit to be pulled, called by payer
  function asyncSend(address dest, uint amount) internal {
    payments[dest] = payments[dest].add(amount);
    totalPayments = totalPayments.add(amount);
  }

  // withdraw accumulated balance, called by payee
  function withdrawPayments() {
    address payee = msg.sender;
    uint payment = payments[payee];

    if (payment == 0) {
      throw;
    }

    if (this.balance < payment) {
      throw;
    }

    totalPayments = totalPayments.sub(payment);
    payments[payee] = 0;

    if (!payee.send(payment)) {
      throw;
    }
  }
}

contract HasNoEther is Ownable {

  /// Constructor that rejects incoming Ether
  /// @dev The flag `payable` is added so we can access `msg.value`
  ///      without compiler warning. If we leave out payable, then
  ///      Solidity will allow inheriting contracts to implement a
  ///      payable constructor. By doing it this way we prevent a
  ///      payable constructor from working.
  ///      Alternatively we could use assembly to access msg.value.
  function HasNoEther() payable {
    if(msg.value > 0) {
      throw;
    }
  }

  /// Disallow direct send by settings a default function without `payable`
  function() external {
  }

  /// Transfer all Ether owned by the contract to the owner
  /// @dev What if owner is itself a contract marked HasNoEther?
  function reclaimEther() external onlyOwner {
    if(!owner.send(this.balance)) {
      throw;
    }
  }
}

contract HasNoContracts is Ownable {

  /// Reclaim ownership of Ownable contracts
  function reclaimContract(address contractAddr) external onlyOwner {
    Ownable contractInst = Ownable(contractAddr);
    contractInst.transferOwnership(owner);
  }
}

/*
 * Contactable token
 * Basic version of a contactable contract
 */
contract Contactable is Ownable{

     string public contactInformation;

     function setContactInformation(string info) onlyOwner{
         contactInformation = info;
     }

}

/*
 * Claimable
 *
 * Extension for the Ownable contract, where the ownership needs to be claimed. This allows the new owner to accept the transfer.
 */
contract Claimable is Ownable {
  address public pendingOwner;

  modifier onlyPendingOwner() {
    if (msg.sender != pendingOwner) {
      throw;
    }
    _;
  }

  function transferOwnership(address newOwner) onlyOwner {
    pendingOwner = newOwner;
  }

  function claimOwnership() onlyPendingOwner {
    owner = pendingOwner;
    pendingOwner = 0x0;
  }

}

/*
 * Destructible
 * Base contract that can be destroyed by owner. All funds in contract will be sent to the owner.
 */
contract Destructible is Ownable {
  function destroy() onlyOwner {
    selfdestruct(owner);
  }
}

/*
 * Pausable
 * Abstract contract that allows children to implement a
 * pause mechanism.
 */
contract Pausable is Ownable {
  event Pause();
  event Unpause();

  bool public paused = false;

  modifier whenNotPaused() {
    if (paused) throw;
    _;
  }

  modifier whenPaused {
    if (!paused) throw;
    _;
  }

  // called by the owner to pause, triggers stopped state
  function pause() onlyOwner whenNotPaused returns (bool) {
    paused = true;
    Pause();
    return true;
  }

  // called by the owner to unpause, returns to normal state
  function unpause() onlyOwner whenPaused returns (bool) {
    paused = false;
    Unpause();
    return true;
  }
}

contract Migrations is Ownable {
  uint public lastCompletedMigration;

  function setCompleted(uint completed) onlyOwner {
    lastCompletedMigration = completed;
  }

  function upgrade(address newAddress) onlyOwner {
    Migrations upgraded = Migrations(newAddress);
    upgraded.setCompleted(lastCompletedMigration);
  }
}

contract HasNoTokens is Ownable {

  /// Reject all ERC23 compatible tokens
  function tokenFallback(address from_, uint value_, bytes data_) external {
    throw;
  }

  /// Reclaim all ERC20Basic compatible tokens
  function reclaimToken(address tokenAddr) external onlyOwner {
    ERC20Basic tokenInst = ERC20Basic(tokenAddr);
    uint256 balance = tokenInst.balanceOf(this);
    tokenInst.transfer(owner, balance);
  }
}

contract TokenDestructible is Ownable {

  /// @notice Terminate contract and refund to owner
  /// @param  tokens List of addresses of ERC20 or ERC20Basic token contracts to
  //          refund
  /// @notice The called token contracts could try to re-enter this contract.
  //          Only supply token contracts you
  function destroy(address[] tokens) onlyOwner {

    // Transfer tokens to owner
    for(uint i = 0; i < tokens.length; i++) {
      ERC20Basic token = ERC20Basic(tokens[i]);
      uint256 balance = token.balanceOf(this);
      token.transfer(owner, balance);
    }

    // Transfer Eth to owner and terminate contract
    selfdestruct(owner);
  }
}

/*
 * ERC20 interface
 * see https://github.com/ethereum/EIPs/issues/20
 */
contract ERC20 is ERC20Basic {
  function allowance(address owner, address spender) constant returns (uint);
  function transferFrom(address from, address to, uint value);
  function approve(address spender, uint value);
  event Approval(address indexed owner, address indexed spender, uint value);
}

/*
 * Basic token
 * Basic version of StandardToken, with no allowances
 */
contract BasicToken is ERC20Basic {
  using SafeMath for uint;

  mapping(address => uint) balances;

  /*
   * Fix for the ERC20 short address attack  
   */
  modifier onlyPayloadSize(uint size) {
     if(msg.data.length < size + 4) {
       throw;
     }
     _;
  }

  function transfer(address _to, uint _value) onlyPayloadSize(2 * 32) {
    balances[msg.sender] = balances[msg.sender].sub(_value);
    balances[_to] = balances[_to].add(_value);
    Transfer(msg.sender, _to, _value);
  }

  function balanceOf(address _owner) constant returns (uint balance) {
    return balances[_owner];
  }
  
}

/*
 * DelayedClaimable
 * Extension for the Claimable contract, where the ownership needs to be claimed before/after certain block number
 */
contract DelayedClaimable is Claimable {

  uint public end;
  uint public start;

  function setLimits(uint _start, uint _end) onlyOwner {
    if (_start > _end)
        throw;
    end = _end;
    start = _start;
  }

  function claimOwnership() onlyPendingOwner {
    if ((block.number > end) || (block.number < start))
        throw;
    owner = pendingOwner;
    pendingOwner = 0x0;
    end = 0;
  }

}

/*
 * Bounty
 * 
 * This bounty will pay out to a researcher if they break invariant logic of the contract.
 */
contract Bounty is PullPayment, Destructible {
  bool public claimed;
  mapping(address => address) public researchers;

  event TargetCreated(address createdAddress);

  function() payable {
    if (claimed) {
      throw;
    }
  }

  function createTarget() returns(Target) {
    Target target = Target(deployContract());
    researchers[target] = msg.sender;
    TargetCreated(target);
    return target;
  }

  function deployContract() internal returns(address);

  function claim(Target target) {
    address researcher = researchers[target];
    if (researcher == 0) {
      throw;
    }
    // Check Target contract invariants
    if (target.checkInvariant()) {
      throw;
    }
    asyncSend(researcher, this.balance);
    claimed = true;
  }

}


/*
 * Target
 * 
 * Your main contract should inherit from this class and implement the checkInvariant method. This is a function that should check everything your contract assumes to be true all the time. If this function returns false, it means your contract was broken in some way and is in an inconsistent state. This is what security researchers will try to acomplish when trying to get the bounty.
 */
contract Target {
  function checkInvariant() returns(bool);
}


contract NoOwner is HasNoEther, HasNoTokens, HasNoContracts {
}

/*

LimitedTransferToken defines the generic interface and the implementation
to limit token transferability for different events.

It is intended to be used as a base class for other token contracts.

Overwriting transferableTokens(address holder, uint64 time) is the way to provide
the specific logic for limiting token transferability for a holder over time.

LimitedTransferToken has been designed to allow for different limiting factors,
this can be achieved by recursively calling super.transferableTokens() until the
base class is hit. For example:

function transferableTokens(address holder, uint64 time) constant public returns (uint256) {
  return min256(unlockedTokens, super.transferableTokens(holder, time));
}

A working example is VestedToken.sol:
https://github.com/OpenZeppelin/zeppelin-solidity/blob/master/contracts/token/VestedToken.sol

*/

contract LimitedTransferToken is ERC20 {
  // Checks whether it can transfer or otherwise throws.
  modifier canTransfer(address _sender, uint _value) {
   if (_value > transferableTokens(_sender, uint64(now))) throw;
   _;
  }

  // Checks modifier and allows transfer if tokens are not locked.
  function transfer(address _to, uint _value) canTransfer(msg.sender, _value) {
   return super.transfer(_to, _value);
  }

  // Checks modifier and allows transfer if tokens are not locked.
  function transferFrom(address _from, address _to, uint _value) canTransfer(_from, _value) {
   return super.transferFrom(_from, _to, _value);
  }

  // Default transferable tokens function returns all tokens for a holder (no limit).
  function transferableTokens(address holder, uint64 time) constant public returns (uint256) {
    return balanceOf(holder);
  }
}

/**
 * Standard ERC20 token
 *
 * https://github.com/ethereum/EIPs/issues/20
 * Based on code by FirstBlood:
 * https://github.com/Firstbloodio/token/blob/master/smart_contract/FirstBloodToken.sol
 */
contract StandardToken is BasicToken, ERC20 {

  mapping (address => mapping (address => uint)) allowed;

  function transferFrom(address _from, address _to, uint _value) {
    var _allowance = allowed[_from][msg.sender];

    // Check is not needed because sub(_allowance, _value) will already throw if this condition is not met
    // if (_value > _allowance) throw;

    balances[_to] = balances[_to].add(_value);
    balances[_from] = balances[_from].sub(_value);
    allowed[_from][msg.sender] = _allowance.sub(_value);
    Transfer(_from, _to, _value);
  }

  function approve(address _spender, uint _value) {
    allowed[msg.sender][_spender] = _value;
    Approval(msg.sender, _spender, _value);
  }

  function allowance(address _owner, address _spender) constant returns (uint remaining) {
    return allowed[_owner][_spender];
  }

}

/*
 * CrowdsaleToken
 *
 * Simple ERC20 Token example, with crowdsale token creation
 * IMPORTANT NOTE: do not use or deploy this contract as-is.
 * It needs some changes to be production ready.
 */
contract CrowdsaleToken is StandardToken {

  string public constant name = "CrowdsaleToken";
  string public constant symbol = "CRW";
  uint public constant decimals = 18;
  // replace with your fund collection multisig address 
  address public constant multisig = 0x0; 


  // 1 ether = 500 example tokens 
  uint public constant PRICE = 500;

  function () payable {
    createTokens(msg.sender);
  }
  
  function createTokens(address recipient) payable {
    if (msg.value == 0) {
      throw;
    }

    uint tokens = msg.value.mul(getPrice());
    totalSupply = totalSupply.add(tokens);

    balances[recipient] = balances[recipient].add(tokens);

    if (!multisig.send(msg.value)) {
      throw;
    }
  }
  
  // replace this with any other price function
  function getPrice() constant returns (uint result) {
    return PRICE;
  }
}

/**
 * Pausable token
 *
 * Simple ERC20 Token example, with pausable token creation
 * Issue:
 * https://github.com/OpenZeppelin/zeppelin-solidity/issues/194
 * Based on code by BCAPtoken:
 * https://github.com/BCAPtoken/BCAPToken/blob/5cb5e76338cc47343ba9268663a915337c8b268e/sol/BCAPToken.sol#L27
 **/

contract PausableToken is Pausable, StandardToken {

  function transfer(address _to, uint _value) whenNotPaused {
    return super.transfer(_to, _value);
  }

  function transferFrom(address _from, address _to, uint _value) whenNotPaused {
    return super.transferFrom(_from, _to, _value);
  }
}
/**
 * Mintable token
 *
 * Simple ERC20 Token example, with mintable token creation
 * Issue:
 * https://github.com/OpenZeppelin/zeppelin-solidity/issues/120
 * Based on code by TokenMarketNet:
 * https://github.com/TokenMarketNet/ico/blob/master/contracts/MintableToken.sol
 */

contract MintableToken is StandardToken, Ownable {
  event Mint(address indexed to, uint value);
  event MintFinished();

  bool public mintingFinished = false;
  uint public totalSupply = 0;

  modifier canMint() {
    if(mintingFinished) throw;
    _;
  }

  function mint(address _to, uint _amount) onlyOwner canMint returns (bool) {
    totalSupply = totalSupply.add(_amount);
    balances[_to] = balances[_to].add(_amount);
    Mint(_to, _amount);
    return true;
  }

  function finishMinting() onlyOwner returns (bool) {
    mintingFinished = true;
    MintFinished();
    return true;
  }
}

/*
 * SimpleToken
 *
 * Very simple ERC20 Token example, where all tokens are pre-assigned
 * to the creator. Note they can later distribute these tokens
 * as they wish using `transfer` and other `StandardToken` functions.
 */
contract SimpleToken is StandardToken {

  string public name = "SimpleToken";
  string public symbol = "SIM";
  uint public decimals = 18;
  uint public INITIAL_SUPPLY = 10000;
  
  function SimpleToken() {
    totalSupply = INITIAL_SUPPLY;
    balances[msg.sender] = INITIAL_SUPPLY;
  }

}

contract VestedToken is StandardToken, LimitedTransferToken {
  struct TokenGrant {
    address granter;
    uint256 value;
    uint64 cliff;
    uint64 vesting;
    uint64 start;
  }

  mapping (address => TokenGrant[]) public grants;

  function grantVestedTokens(
    address _to,
    uint256 _value,
    uint64 _start,
    uint64 _cliff,
    uint64 _vesting) {

    if (_cliff < _start) {
      throw;
    }
    if (_vesting < _start) {
      throw;
    }
    if (_vesting < _cliff) {
      throw;
    }


    TokenGrant memory grant = TokenGrant(msg.sender, _value, _cliff, _vesting, _start);
    grants[_to].push(grant);

    transfer(_to, _value);
  }

  function revokeTokenGrant(address _holder, uint _grantId) {
    TokenGrant grant = grants[_holder][_grantId];

    if (grant.granter != msg.sender) {
      throw;
    }
    uint256 nonVested = nonVestedTokens(grant, uint64(now));

    // remove grant from array
    delete grants[_holder][_grantId];
    grants[_holder][_grantId] = grants[_holder][grants[_holder].length - 1];
    grants[_holder].length -= 1;

    balances[msg.sender] = balances[msg.sender].add(nonVested);
    balances[_holder] = balances[_holder].sub(nonVested);
    Transfer(_holder, msg.sender, nonVested);
  }

  function tokenGrantsCount(address _holder) constant returns (uint index) {
    return grants[_holder].length;
  }

  function tokenGrant(address _holder, uint _grantId) constant returns (address granter, uint256 value, uint256 vested, uint64 start, uint64 cliff, uint64 vesting) {
    TokenGrant grant = grants[_holder][_grantId];

    granter = grant.granter;
    value = grant.value;
    start = grant.start;
    cliff = grant.cliff;
    vesting = grant.vesting;

    vested = vestedTokens(grant, uint64(now));
  }

  function vestedTokens(TokenGrant grant, uint64 time) private constant returns (uint256) {
    return calculateVestedTokens(
      grant.value,
      uint256(time),
      uint256(grant.start),
      uint256(grant.cliff),
      uint256(grant.vesting)
    );
  }

  function calculateVestedTokens(
    uint256 tokens,
    uint256 time,
    uint256 start,
    uint256 cliff,
    uint256 vesting) constant returns (uint256 vestedTokens)
    {

    if (time < cliff) {
      return 0;
    }
    if (time >= vesting) {
      return tokens;
    }

    uint256 cliffTokens = tokens.mul(cliff.sub(start)).div(vesting.sub(start));
    vestedTokens = cliffTokens;

    uint256 vestingTokens = tokens.sub(cliffTokens);

    vestedTokens = vestedTokens.add(vestingTokens.mul(time.sub(cliff)).div(vesting.sub(cliff)));
  }

  function nonVestedTokens(TokenGrant grant, uint64 time) private constant returns (uint256) {
    return grant.value.sub(vestedTokens(grant, time));
  }

  function lastTokenIsTransferableDate(address holder) constant public returns (uint64 date) {
    date = uint64(now);
    uint256 grantIndex = grants[holder].length;
    for (uint256 i = 0; i < grantIndex; i++) {
      date = SafeMath.max64(grants[holder][i].vesting, date);
    }
  }

  function transferableTokens(address holder, uint64 time) constant public returns (uint256 nonVested) {
    uint256 grantIndex = grants[holder].length;
    for (uint256 i = 0; i < grantIndex; i++) {
      uint256 current = nonVestedTokens(grants[holder][i], time);
      nonVested = nonVested.add(current);
    }

    return SafeMath.min256(balances[holder].sub(nonVested), super.transferableTokens(holder, time));
  }
}

