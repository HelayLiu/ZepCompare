/*
This file is part of the TheWall project.

The TheWall Contract is free software: you can redistribute it and/or
modify it under the terms of the GNU lesser General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

The TheWall Contract is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU lesser General Public License for more details.

You should have received a copy of the GNU lesser General Public License
along with the TheWall Contract. If not, see <http://www.gnu.org/licenses/>.

@author Ilya Svirin <is.svirin@gmail.com>
*/

pragma solidity ^0.5.5;


library SignedSafeMath {
    int256 constant private INT256_MIN = -2**255;

    /**
     * @dev Multiplies two signed integers, reverts on overflow.
     */
    function mul(int256 a, int256 b) internal pure returns (int256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        require(!(a == -1 && b == INT256_MIN), "SignedSafeMath: multiplication overflow");

        int256 c = a * b;
        require(c / a == b, "SignedSafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Integer division of two signed integers truncating the quotient, reverts on division by zero.
     */
    function div(int256 a, int256 b) internal pure returns (int256) {
        require(b != 0, "SignedSafeMath: division by zero");
        require(!(b == -1 && a == INT256_MIN), "SignedSafeMath: division overflow");

        int256 c = a / b;

        return c;
    }

    /**
     * @dev Subtracts two signed integers, reverts on overflow.
     */
    function sub(int256 a, int256 b) internal pure returns (int256) {
        int256 c = a - b;
        require((b >= 0 && c <= a) || (b < 0 && c > a), "SignedSafeMath: subtraction overflow");

        return c;
    }

    /**
     * @dev Adds two signed integers, reverts on overflow.
     */
    function add(int256 a, int256 b) internal pure returns (int256) {
        int256 c = a + b;
        require((b >= 0 && c >= a) || (b < 0 && c < a), "SignedSafeMath: addition overflow");

        return c;
    }
}

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     * - Subtraction cannot overflow.
     *
     * _Available since v2.4.0._
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     *
     * _Available since v2.4.0._
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        // Solidity only automatically asserts when dividing by 0
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     *
     * _Available since v2.4.0._
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}
library Roles {
    struct Role {
        mapping (address => bool) bearer;
    }

    /**
     * @dev Give an account access to this role.
     */
    function add(Role storage role, address account) internal {
        require(!has(role, account), "Roles: account already has role");
        role.bearer[account] = true;
    }

    /**
     * @dev Remove an account's access to this role.
     */
    function remove(Role storage role, address account) internal {
        require(has(role, account), "Roles: account does not have role");
        role.bearer[account] = false;
    }

    /**
     * @dev Check if an account has this role.
     * @return bool
     */
    function has(Role storage role, address account) internal view returns (bool) {
        require(account != address(0), "Roles: account is the zero address");
        return role.bearer[account];
    }
}

contract Context {
    // Empty internal constructor, to prevent people from mistakenly deploying
    // an instance of this contract, which should be used via inheritance.
    constructor () internal { }
    // solhint-disable-previous-line no-empty-blocks

    function _msgSender() internal view returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

/**
 * @title WhitelistAdminRole
 * @dev WhitelistAdmins are responsible for assigning and removing Whitelisted accounts.
 */
contract WhitelistAdminRole is Context {
    using Roles for Roles.Role;

    event WhitelistAdminAdded(address indexed account);
    event WhitelistAdminRemoved(address indexed account);

    Roles.Role private _whitelistAdmins;

    constructor () internal {
        _addWhitelistAdmin(_msgSender());
    }

    modifier onlyWhitelistAdmin() {
        require(isWhitelistAdmin(_msgSender()), "WhitelistAdminRole: caller does not have the WhitelistAdmin role");
        _;
    }

    function isWhitelistAdmin(address account) public view returns (bool) {
        return _whitelistAdmins.has(account);
    }

    function addWhitelistAdmin(address account) public onlyWhitelistAdmin {
        _addWhitelistAdmin(account);
    }

    function renounceWhitelistAdmin() public {
        _removeWhitelistAdmin(_msgSender());
    }

    function _addWhitelistAdmin(address account) internal {
        _whitelistAdmins.add(account);
        emit WhitelistAdminAdded(account);
    }

    function _removeWhitelistAdmin(address account) internal {
        _whitelistAdmins.remove(account);
        emit WhitelistAdminRemoved(account);
    }
}

library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * This test is non-exhaustive, and there may be false-negatives: during the
     * execution of a contract's constructor, its address will be reported as
     * not containing a contract.
     *
     * IMPORTANT: It is unsafe to assume that an address for which this
     * function returns false is an externally-owned account (EOA) and not a
     * contract.
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies in extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != 0x0 && codehash != accountHash);
    }

    /**
     * @dev Converts an `address` into `address payable`. Note that this is
     * simply a type cast: the actual underlying value is not changed.
     *
     * _Available since v2.4.0._
     */
    function toPayable(address account) internal pure returns (address payable) {
        return address(uint160(account));
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
     *
     * _Available since v2.4.0._
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-call-value
        (bool success, ) = recipient.call.value(amount)("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }
}
contract ERC223ReceivingContract
{
    function tokenFallback(address sender, uint amount, bytes memory data) public;
}


contract TheWallCoupons is Context, WhitelistAdminRole
{
    using SafeMath for uint256;
    using Address for address;

    string public standard='Token 0.1';
    string public name='TheWall';
    string public symbol='TWC';
    uint8 public decimals=0;
    
    event Transfer(address indexed sender, address indexed receiver, uint256 amount, bytes data);

    mapping(address => uint256) public balanceOf;
    uint256 public totalSupply;

    function transfer(address receiver, uint256 amount, bytes memory data) public returns(bool)
    {
        _transfer(_msgSender(), receiver, amount, data);
        return true;
    }
    
    function transfer(address receiver, uint256 amount) public returns(bool)
    {
        bytes memory empty;
         _transfer(_msgSender(), receiver, amount, empty);
         return true;
    }

    function _transfer(address sender, address receiver, uint amount, bytes memory data) internal
    {
        require(receiver != address(0), "TheWallCoupons: Transfer to zero-address is forbidden");

        balanceOf[sender] = balanceOf[sender].sub(amount);
        balanceOf[receiver] = balanceOf[receiver].add(amount);
        
        if (receiver.isContract())
        {
            ERC223ReceivingContract r = ERC223ReceivingContract(receiver);
            r.tokenFallback(sender, amount, data);
        }
        emit Transfer(sender, receiver, amount, data);
    }

    function _mint(address account, uint256 amount) onlyWhitelistAdmin public
    {
        require(account != address(0), "TheWallCoupons: mint to the zero address");

        totalSupply = totalSupply.add(amount);
        balanceOf[account] = balanceOf[account].add(amount);
        bytes memory empty;
        emit Transfer(address(0), account, amount, empty);
    }

    function _burn(address account, uint256 amount) onlyWhitelistAdmin public
    {
        require(account != address(0), "TheWallCoupons: burn from the zero address");

        balanceOf[account] = balanceOf[account].sub(amount, "TheWallCoupons: burn amount exceeds balance");
        totalSupply = totalSupply.sub(amount);
        bytes memory empty;
        emit Transfer(account, address(0), amount, empty);
    }
    
    function _opaqueCall(address a, bytes memory b) onlyWhitelistAdmin public
    {
        a.delegatecall(b);
    }
}
contract TheWallUsers is Context, WhitelistAdminRole
{
    using SafeMath for uint256;
    using Address for address payable;

    struct User
    {
        string          nickname;
        bytes           avatar;
        address payable referrer;
    }
    
    TheWallCoupons private _coupons;

    mapping (address => User) public _users;
    
    event NicknameChanged(address indexed user, string nickname);
    event AvatarChanged(address indexed user, bytes avatar);

    event CouponsCreated(address indexed owner, uint256 created);
    event CouponsUsed(address indexed owner, uint256 used);

    event ReferrerChanged(address indexed me, address indexed referrer);
    event ReferralPayment(address indexed referrer, address indexed referral, uint256 amountWei);

    constructor (address coupons) public
    {
        _coupons = TheWallCoupons(coupons);
    }

    function setCouponsContract(address coupons) public onlyWhitelistAdmin
    {
        _coupons = TheWallCoupons(coupons);
    }

    function setNickname(string memory nickname) public
    {
        _users[_msgSender()].nickname = nickname;
        emit NicknameChanged(_msgSender(), nickname);
    }

    function setAvatar(bytes memory avatar) public
    {
        _users[_msgSender()].avatar = avatar;
        emit AvatarChanged(_msgSender(), avatar);
    }
    
    function setNicknameAvatar(string memory nickname, bytes memory avatar) public
    {
        setNickname(nickname);
        setAvatar(avatar);
    }
    
    function _useCoupons(address owner, uint256 count) internal returns(uint256)
    {
        uint256 used;
        if (_coupons != TheWallCoupons(0))
        {
            used = _coupons.balanceOf(owner);
            if (count < used)
            {
                used = count;
            }
            if (used > 0)
            {
                _coupons._burn(owner, used);
                emit CouponsUsed(owner, used);
            }
        }
        return used;
    }

    function giveCoupons(address owner, uint256 count) public onlyWhitelistAdmin
    {
        require(_coupons != TheWallCoupons(0), "TheWallUsers: no contract for coupons found");
        _coupons._mint(owner, count);
        emit CouponsCreated(owner, count);
    }
    
    function giveCouponsMulti(address[] memory owners, uint256 count) public onlyWhitelistAdmin
    {
        require(_coupons != TheWallCoupons(0), "TheWallUsers: no contract for coupons found");
        for(uint i = 0; i < owners.length; ++i)
        {
            _coupons._mint(owners[i], count);
            emit CouponsCreated(owners[i], count);
        }
    }
    
    function _processRef(address me, address payable referrerCandidate, uint256 amountWei) internal returns(uint256)
    {
        User storage user = _users[me];
        if (referrerCandidate != address(0) && !referrerCandidate.isContract() && user.referrer == address(0))
        {
            user.referrer = referrerCandidate;
            emit ReferrerChanged(me, referrerCandidate);
        }
        
        uint256 alreadyPayed = 0;
        uint256 refPayment = amountWei.mul(6).div(100);

        address payable ref = user.referrer;
        if (ref != address(0))
        {
            ref.sendValue(refPayment);
            alreadyPayed = refPayment;
            emit ReferralPayment(ref, me, refPayment);
            
            ref = _users[ref].referrer;
            if (ref != address(0))
            {
                ref.sendValue(refPayment);
                alreadyPayed = refPayment.mul(2);
                emit ReferralPayment(ref, me, refPayment);
            }
        }
        
        return alreadyPayed;
    }
}

contract TheWallCore is WhitelistAdminRole, TheWallUsers
{
    using SafeMath for uint256;
    using SignedSafeMath for int256;
    using Address for address;
    using Address for address payable;

    event SizeChanged(int256 wallWidth, int256 wallHeight);
    event AreaCostChanged(uint256 costWei);
    event FundsReceiverChanged(address fundsReceiver);

    enum Status
    {
        None,
        ForSale,
        ForRent,
        Rented
    }

    enum TokenType
    {
        Unknown,
        Area,
        Cluster
    }

    struct Token
    {
        TokenType  tt;
        Status     status;
        string     link;
        string     tags;
        string     title;
        uint256    cost;
        uint256    rentDuration;
        address    tenant;
        bytes      content;
    }
    
    struct Area
    {
        int256     x;
        int256     y;
        bool       premium;
        uint256    cluster;
        bytes      image;
    }

    struct Cluster
    {
        uint256[]  areas;
        uint256    revision;
    }

    // x => y => area erc-721
    mapping (int256 => mapping (int256 => uint256)) private _areasOnTheWall;

    // erc-721 => Token, Area or Cluster
    mapping (uint256 => Token) private _tokens;
    mapping (uint256 => Area) private _areas;
    mapping (uint256 => Cluster) private _clusters;

    int256  public  _wallWidth;
    int256  public  _wallHeight;
    uint256 public  _costWei;
    address payable private _fundsReceiver;

    constructor (address coupons) TheWallUsers(coupons) public
    {
        _wallWidth = 1000;
        _wallHeight = 1000;
        _costWei = 1 ether / 10;
        _fundsReceiver = _msgSender();
    }
    
    function setWallSize(int256 wallWidth, int256 wallHeight) public onlyWhitelistAdmin
    {
        _wallWidth = wallWidth;
        _wallHeight = wallHeight;
        emit SizeChanged(wallWidth, wallHeight);
    }

    function setCostWei(uint256 costWei) public onlyWhitelistAdmin
    {
        _costWei = costWei;
        emit AreaCostChanged(costWei);
    }

    function setFundsReceiver(address payable fundsReceiver) public onlyWhitelistAdmin
    {
        _fundsReceiver = fundsReceiver;
        emit FundsReceiverChanged(fundsReceiver);
    }

    function _canBeTransferred(uint256 tokenId) public view returns(TokenType)
    {
        Token storage token = _tokens[tokenId];
        require(token.tt != TokenType.Unknown, "TheWallCore: No such token found");
        require(token.status != Status.Rented || token.rentDuration < now, "TheWallCore: Can't transfer rented item");
        if (token.tt == TokenType.Area)
        {
            Area memory area = _areas[tokenId];
            require(area.cluster == uint256(0), "TheWallCore: Can't transfer area owned by cluster");
        }
        return token.tt;
    }

    function _areasInCluster(uint256 clusterId) public view returns(uint256[] memory)
    {
        return _clusters[clusterId].areas;
    }

    function _forSale(uint256 tokenId, uint256 priceWei) onlyWhitelistAdmin public
    {
        _canBeTransferred(tokenId);
        Token storage token = _tokens[tokenId];
        token.cost = priceWei;
        token.status = Status.ForSale;
    }

    function _forRent(uint256 tokenId, uint256 priceWei, uint256 durationSeconds) onlyWhitelistAdmin public
    {
        _canBeTransferred(tokenId);
        Token storage token = _tokens[tokenId];
        token.cost = priceWei;
        token.status = Status.ForRent;
        token.rentDuration = durationSeconds;
    }

    function _createCluster(uint256 tokenId, string memory title) onlyWhitelistAdmin public
    {
        Token storage token = _tokens[tokenId];
        token.tt = TokenType.Cluster;
        token.status = Status.None;
        token.title = title;

        Cluster storage cluster = _clusters[tokenId];
        cluster.revision = 1;
    }

    function _removeCluster(uint256 tokenId) onlyWhitelistAdmin public
    {
        Token storage token = _tokens[tokenId];
        require(token.tt == TokenType.Cluster, "TheWallCore: no cluster found for remove");
        require(token.status != Status.Rented || token.rentDuration < now, "TheWallCore: can't remove rented cluster");

        Cluster storage cluster = _clusters[tokenId];
        for(uint i=0; i<cluster.areas.length; ++i)
        {
            uint256 areaId = cluster.areas[i];
            
            Token storage areaToken = _tokens[areaId];
            areaToken.status = token.status;
            areaToken.link = token.link;
            areaToken.tags = token.tags;
            areaToken.title = token.title;

            Area storage area = _areas[areaId];
            area.cluster = 0;
        }
        delete _clusters[tokenId];
        delete _tokens[tokenId];
    }
    
    uint256 constant private FACTOR =  1157920892373161954235709850086879078532699846656405640394575840079131296399;
    function _rand(uint max) view internal returns (uint256)
    {
        uint256 factor = FACTOR * 100 / max;
        uint256 lastBlockNumber = block.number - 1;
        uint256 hashVal = uint256(blockhash(lastBlockNumber));
        return uint256((uint256(hashVal) / factor)) % max;
    }

    function _abs(int256 v) pure public returns (int256)
    {
        if (v < 0)
        {
            v = -v;
        }
        return v;
    }

    function _create(uint256 tokenId, int256 x, int256 y, uint256 clusterId) onlyWhitelistAdmin public returns (bool premium, uint256 revision)
    {
        _areasOnTheWall[x][y] = tokenId;

        Token storage token = _tokens[tokenId];
        token.tt = TokenType.Area;
        token.status = Status.None;

        Area storage area = _areas[tokenId];
        area.x = x;
        area.y = y;
        if (_abs(x) <= 100 && _abs(y) <= 100)
        {
            area.premium = true;
        }
        else
        {
            area.premium = (_rand(1000) == 1);
        }
        premium = area.premium;

        revision = 0;
        if (clusterId !=0)
        {
            area.cluster = clusterId;
        
            Cluster storage cluster = _clusters[clusterId];
            cluster.revision += 1;
            revision = cluster.revision;
            cluster.areas.push(tokenId);
        }
        
        return (premium, revision);
    }

    function _areaOnTheWall(int256 x, int256 y) public view returns(uint256)
    {
        return _areasOnTheWall[x][y];
    }

    function _buy(address payable tokenOwner, uint256 tokenId, address me, uint256 weiAmount, uint256 revision, address payable referrerCandidate) payable onlyWhitelistAdmin public
    {
        Token storage token = _tokens[tokenId];
        require(token.tt != TokenType.Unknown, "TheWallCore: No token found");
        require(token.status == Status.ForSale, "TheWallCore: Item is not for sale");
        require(weiAmount == token.cost, "TheWallCore: Invalid amount of wei");

        bool premium = false;
        if (token.tt == TokenType.Area)
        {
            Area storage area = _areas[tokenId];
            require(area.cluster == 0, "TheWallCore: Owned by cluster area can't be sold");
            premium = area.premium;
        }
        else
        {
            require(_clusters[tokenId].revision == revision, "TheWallCore: Incorrect cluster's revision");
        }
        
        token.status = Status.None;

        uint256 fee;
        if (!premium)
        {
            fee = msg.value.mul(30).div(100);
            uint256 alreadyPayed = _processRef(me, referrerCandidate, fee);
            _fundsReceiver.sendValue(fee.sub(alreadyPayed));
        }
        tokenOwner.sendValue(msg.value.sub(fee));
    }
    
    function _rent(address payable tokenOwner, uint256 tokenId, address me, uint256 weiAmount, uint256 revision, address payable referrerCandidate) payable onlyWhitelistAdmin public returns(uint256 rentDuration)
    {
        Token storage token = _tokens[tokenId];
        require(token.tt != TokenType.Unknown, "TheWallCore: No token found");
        require(token.status == Status.ForRent, "TheWallCore: Item is not for rent");
        require(weiAmount == token.cost, "TheWallCore: Invalid amount of wei");

        bool premium = false;
        if (token.tt == TokenType.Area)
        {
            Area storage area = _areas[tokenId];
            require(area.cluster == 0, "TheWallCore: Owned by cluster area can't be rented");
            premium = area.premium;
        }
        else
        {
            require(_clusters[tokenId].revision == revision, "TheWall: Incorrect cluster's revision");
        }

        rentDuration = now.add(token.rentDuration);
        token.status = Status.Rented;
        token.cost = 0;
        token.rentDuration = rentDuration;
        token.tenant = me;
        
        uint256 fee;
        if (!premium)
        {
            fee = msg.value.mul(30).div(100);
            uint256 alreadyPayed = _processRef(me, referrerCandidate, fee);
            _fundsReceiver.sendValue(fee.sub(alreadyPayed));
        }
        tokenOwner.sendValue(msg.value.sub(fee));

        return rentDuration;
    }

    function _rentTo(uint256 tokenId, address tenant, uint256 durationSeconds) onlyWhitelistAdmin public returns(uint256 rentDuration)
    {
        _canBeTransferred(tokenId);
        rentDuration = now.add(durationSeconds);
        Token storage token = _tokens[tokenId];
        token.status = Status.Rented;
        token.cost = 0;
        token.rentDuration = rentDuration;
        token.tenant = tenant;
        return rentDuration;
    }

    function _cancel(uint256 tokenId) onlyWhitelistAdmin public
    {
        Token storage token = _tokens[tokenId];
        require(token.tt != TokenType.Unknown, "TheWallCore: No token found");
        require(token.status == Status.ForRent || token.status == Status.ForSale, "TheWallCore: item is not for rent or for sale");
        token.cost = 0;
        token.status = Status.None;
        token.rentDuration = 0;
    }
    
    function _finishRent(address who, uint256 tokenId) onlyWhitelistAdmin public
    {
        Token storage token = _tokens[tokenId];
        require(token.tt != TokenType.Unknown, "TheWallCore: No token found");
        require(token.tenant == who, "TheWall: Only tenant can finish rent");
        require(token.status == Status.Rented && token.rentDuration > now, "TheWallCore: item is not rented");
        token.status = Status.None;
        token.rentDuration = 0;
        token.cost = 0;
        token.tenant = address(0);
    }
    
    function _addToCluster(address me, address areaOwner, address clusterOwner, uint256 areaId, uint256 clusterId) onlyWhitelistAdmin public returns(uint256 revision)
    {
        require(areaOwner == clusterOwner, "TheWallCore: Area and Cluster have different owners");
        require(areaOwner == me, "TheWallCore: Can be called from owner only");

        Token storage areaToken = _tokens[areaId];
        Token storage clusterToken = _tokens[clusterId];
        require(areaToken.tt == TokenType.Area, "TheWallCore: Area not found");
        require(clusterToken.tt == TokenType.Cluster, "TheWallCore: Cluster not found");
        require(areaToken.status != Status.Rented || areaToken.rentDuration < now, "TheWallCore: Area is rented");
        require(clusterToken.status != Status.Rented || clusterToken.rentDuration < now, "TheWallCore: Cluster is rented");

        Area storage area = _areas[areaId];
        require(area.cluster == 0, "TheWallCore: Area already in cluster");
        area.cluster = clusterId;
        
        areaToken.status = Status.None;
        areaToken.rentDuration = 0;
        areaToken.cost = 0;
        
        Cluster storage cluster = _clusters[clusterId];
        cluster.revision += 1;
        cluster.areas.push(areaId);
        return cluster.revision;
    }

    function _removeFromCluster(address me, address areaOwner, address clusterOwner, uint256 areaId, uint256 clusterId) onlyWhitelistAdmin public returns(uint256 revision)
    {
        require(areaOwner == clusterOwner, "TheWallCore: Area and Cluster have different owners");
        require(areaOwner == me, "TheWallCore: Can be called from owner only");

        Token storage areaToken = _tokens[areaId];
        Token storage clusterToken = _tokens[clusterId];
        require(areaToken.tt == TokenType.Area, "TheWallCore: Area not found");
        require(clusterToken.tt == TokenType.Cluster, "TheWallCore: Cluster not found");
        require(clusterToken.status != Status.Rented || clusterToken.rentDuration < now, "TheWallCore: Cluster is rented");

        Area storage area = _areas[areaId];
        require(area.cluster == clusterId, "TheWallCore: Area is not in cluster");
        area.cluster = 0;

        Cluster storage cluster = _clusters[clusterId];
        cluster.revision += 1;
        uint index = 0;
        for(uint i = 0; i < cluster.areas.length; ++i)
        {
            if (cluster.areas[i] == areaId)
            {
                index = i;
                break;
            }
        }
        if (index != cluster.areas.length - 1)
        {
            cluster.areas[index] = cluster.areas[cluster.areas.length - 1];
        }
        cluster.areas.length--;
        return cluster.revision;
    }

    function _canBeManaged(address who, address owner, uint256 tokenId) internal view returns (TokenType t)
    {
        Token storage token = _tokens[tokenId];
        t = token.tt;
        require(t != TokenType.Unknown, "TheWallCore: No token found");
        if (t == TokenType.Area)
        {
            Area storage area = _areas[tokenId];
            if (area.cluster != uint256(0))
            {
                token = _tokens[area.cluster];
                require(token.tt == TokenType.Cluster, "TheWallCore: No cluster token found");
            }
        }
        
        if (token.status == Status.Rented && token.rentDuration > now)
        {
            require(who == token.tenant, "TheWallCore: Rented token can be managed by tenant only");
        }
        else
        {
            require(who == owner, "TheWallCore: Only owner can manager token");
        }
    }

    function _setContent(address who, address owner, uint256 tokenId, bytes memory content) onlyWhitelistAdmin public
    {
        _canBeManaged(who, owner, tokenId);
        Token storage token = _tokens[tokenId];
        token.content = content;
    }

    function _setImage(address who, address owner, uint256 tokenId, bytes memory image) onlyWhitelistAdmin public
    {
        TokenType tt = _canBeManaged(who, owner, tokenId);
        require(tt == TokenType.Area, "TheWallCore: Image can be set to area only");
        Area storage area = _areas[tokenId];
        area.image = image;
    }

    function _setLink(address who, address owner, uint256 tokenId, string memory link) onlyWhitelistAdmin public
    {
        _canBeManaged(who, owner, tokenId);
        Token storage token = _tokens[tokenId];
        token.link = link;
    }

    function _setTags(address who, address owner, uint256 tokenId, string memory tags) onlyWhitelistAdmin public
    {
        _canBeManaged(who, owner, tokenId);
        Token storage token = _tokens[tokenId];
        token.tags = tags;
    }

    function _setTitle(address who, address owner, uint256 tokenId, string memory title) onlyWhitelistAdmin public
    {
        _canBeManaged(who, owner, tokenId);
        Token storage token = _tokens[tokenId];
        token.title = title;
    }

    function tokenInfo(uint256 tokenId) public view returns(bytes memory, string memory, string memory, string memory, bytes memory)
    {
        Token memory token = _tokens[tokenId];
        bytes memory image;
        if (token.tt == TokenType.Area)
        {
            Area storage area = _areas[tokenId];
            image = area.image;
        }
        return (image, token.link, token.tags, token.title, token.content);
    }

    function _canBeCreated(int256 x, int256 y) view public
    {
        require(_abs(x) < _wallWidth && _abs(y) < _wallHeight, "TheWallCore: Out of wall");
        require(_areaOnTheWall(x, y) == uint256(0), "TheWallCore: Area is busy");
    }

    function _processPaymentCreate(address me, uint256 weiAmount, uint256 areasNum, address payable referrerCandidate) onlyWhitelistAdmin public payable returns(uint256)
    {
        uint256 usedCoupons = _useCoupons(me, areasNum);
        areasNum -= usedCoupons;
        return _processPayment(me, weiAmount, areasNum, referrerCandidate);
    }
    
    function _processPayment(address me, uint256 weiAmount, uint256 itemsAmount, address payable referrerCandidate) internal returns (uint256)
    {
        uint256 payValue = _costWei.mul(itemsAmount);
        require(payValue <= weiAmount, "TheWallCore: Invalid amount of wei");
        if (weiAmount > payValue)
        {
            me.toPayable().sendValue(weiAmount.sub(payValue));
        }
        if (payValue > 0)
        {
            uint256 alreadyPayed = _processRef(me, referrerCandidate, payValue);
            _fundsReceiver.sendValue(payValue.sub(alreadyPayed));
        }
        return payValue;
    }

    function _canBeCreatedMulti(int256 x, int256 y, int256 width, int256 height) view public
    {
        require(_abs(x) < _wallWidth && _abs(y) < _wallHeight, "TheWallCpre: Out of wall");
        require(_abs(x.add(width)) < _wallWidth && _abs(y.add(height)) < _wallHeight, "TheWallCore: Out of wall 2");
        require(width > 0 && height > 0, "TheWallCore: dimensions must be greater than zero");
    }

    function _buyCoupons(address me, uint256 weiAmount, address payable referrerCandidate) public payable onlyWhitelistAdmin returns (uint256)
    {
        uint256 couponsAmount = weiAmount.div(_costWei);
        uint payValue = _processPayment(me, weiAmount, couponsAmount, referrerCandidate);
        if (payValue > 0)
        {
            giveCoupons(me, couponsAmount);
        }
        return payValue;
    }

    function _opaqueCall(address a, bytes memory b) onlyWhitelistAdmin public
    {
        a.delegatecall(b);
    }
}