pragma solidity ^0.5.8;

library Math {
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a >= b ? a : b;
    }

    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow, so we distribute
        return (a / 2) + (b / 2) + ((a % 2 + b % 2) / 2);
    }
}

library SafeMath {
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b);

        return c;
    }

    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        // Solidity only automatically asserts when dividing by 0
        require(b > 0);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a);
        uint256 c = a - b;

        return c;
    }

    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a);

        return c;
    }

    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b != 0);
        return a % b;
    }
}

interface IERC20 {
    function transfer(address to, uint256 value) external returns (bool);
    function approve(address spender, uint256 value) external returns (bool);
    function transferFrom(address from, address to, uint256 value) external returns (bool);
    function totalSupply() external view returns (uint256);
    function balanceOf(address who) external view returns (uint256);
    function allowance(address owner, address spender) external view returns (uint256);
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

contract Ownable {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    constructor () internal {
        _owner = msg.sender;
        emit OwnershipTransferred(address(0), _owner);
    }

    function owner() public view returns (address) {
        return _owner;
    }

    modifier onlyOwner() {
        require(isOwner());
        _;
    }

    function isOwner() public view returns (bool) {
        return msg.sender == _owner;
    }

    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    function transferOwnership(address newOwner) public onlyOwner {
        _transferOwnership(newOwner);
    }

    function _transferOwnership(address newOwner) internal {
        require(newOwner != address(0));
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

/*
 * Owner의 권한 중 일부를 대신 행사할 수 있도록 대행자를 지정/해제 할 수 있는 인터페이스
 */
contract Delegable is Ownable {
    address private _delegator;
    
    event DelegateAppointed(address indexed previousDelegator, address indexed newDelegator);
    
    constructor () internal {
        _delegator = address(0);
    }
    
    /*
     * deletator를 가져옴
     */
    function delegator() public view returns (address) {
        return _delegator;
    }
    
    /*
     * delegator만 실행 가능하도록 지정하는 접근 제한
     */
    modifier onlyDelegator() {
        require(isDelegator());
        _;
    }
    
    /*
     * owner 또는 delegator가 실행 가능하도록 지정하는 접근 제한
     */
    modifier ownerOrDelegator() {
        require(isOwner() || isDelegator());
        _;
    }
    
    function isDelegator() public view returns (bool) {
        return msg.sender == _delegator;
    }
    
    /*
     * delegator를 임명
     */
    function appointDelegator(address delegator) public onlyOwner returns (bool) {
        require(delegator != address(0));
        require(delegator != owner());
        return _appointDelegator(delegator);
    }
    
    /*
     * 지정된 delegator를 해임
     */
    function dissmiss() public onlyOwner returns (bool) {
        require(_delegator != address(0));
        return _appointDelegator(address(0));
    }
    
    /*
     * delegator를 변경하는 내부 함수
     */
    function _appointDelegator(address delegator) private returns (bool) {
        require(_delegator != delegator);
        emit DelegateAppointed(_delegator, delegator);
        _delegator = delegator;
        return true;
    }
}

contract ERC20Like is IERC20, Delegable {
    using SafeMath for uint256;

    uint256 internal _totalSupply;  // 총 발행량
    bool isLock = false;  // 계약 잠금 플래그

    /*
     * 토큰 정보(충전량, 해금량, 가용잔액) 및 Spender 정보를 저장하는 구조체
     */
    struct TokenContainer {
        uint256 chargeAmount; // 충전량
        uint256 unlockAmount; // 해금량
        uint256 balance;  // 가용잔액
        mapping (address => uint256) allowed; // Spender
    }

    mapping (address => TokenContainer) internal _tokenContainers;

    // 총 발행량
    function totalSupply() public view returns (uint256) {
        return _totalSupply;
    }

    // 가용잔액 가져오기
    function balanceOf(address holder) public view returns (uint256) {
        return _tokenContainers[holder].balance;
    }

    // Spender의 남은 잔액 가져오기
    function allowance(address holder, address spender) public view returns (uint256) {
        return _tokenContainers[holder].allowed[spender];
    }

    // 토큰송금
    function transfer(address to, uint256 value) public returns (bool) {
        _transfer(msg.sender, to, value);
        return true;
    }

    // Spender 지정 및 금액 지정
    function approve(address spender, uint256 value) public returns (bool) {
        _approve(msg.sender, spender, value);
        return true;
    }

    // Spender 토큰송금
    function transferFrom(address from, address to, uint256 value) public returns (bool) {
        _transfer(from, to, value);
        _approve(from, msg.sender, _tokenContainers[from].allowed[msg.sender].sub(value));
        return true;
    }

    // Spender가 할당 받은 양 증가
    function increaseAllowance(address spender, uint256 addedValue) public returns (bool) {
        require(!isLock);
        uint256 value = _tokenContainers[msg.sender].allowed[spender].add(addedValue);
        if (msg.sender == owner()) {  // Sender가 계약 소유자인 경우 전체 발행량 조절
            require(_tokenContainers[msg.sender].chargeAmount >= _tokenContainers[msg.sender].unlockAmount.add(addedValue));
            _tokenContainers[msg.sender].unlockAmount = _tokenContainers[msg.sender].unlockAmount.add(addedValue);
            _tokenContainers[msg.sender].balance = _tokenContainers[msg.sender].balance.add(addedValue);
        }
        _approve(msg.sender, spender, value);
        return true;
    }

    // Spender가 할당 받은 양 감소
    function decreaseAllowance(address spender, uint256 subtractedValue) public returns (bool) {
        require(!isLock);
        uint256 value = _tokenContainers[msg.sender].allowed[spender].sub(subtractedValue);
        if (msg.sender == owner()) {  // Sender가 계약 소유자인 경우 전체 발행량 조절
            _tokenContainers[msg.sender].unlockAmount = _tokenContainers[msg.sender].unlockAmount.sub(subtractedValue);
            _tokenContainers[msg.sender].balance = _tokenContainers[msg.sender].balance.sub(subtractedValue);
        }
        _approve(msg.sender, spender, value);
        return true;
    }

    // 토큰송금 내부 실행 함수
    function _transfer(address from, address to, uint256 value) private {
        require(!isLock);
        require(to != address(0));

        _tokenContainers[from].balance = _tokenContainers[from].balance.sub(value);
        _tokenContainers[to].balance = _tokenContainers[to].balance.add(value);
        emit Transfer(from, to, value);
    }

    // Spender 지정 내부 실행 함수
    function _approve(address holder, address spender, uint256 value) private {
        require(!isLock);
        require(spender != address(0));
        require(holder != address(0));

        _tokenContainers[holder].allowed[spender] = value;
        emit Approval(holder, spender, value);
    }

    /* extension */
    /**
     * 충전량
     */
    function chargeAmountOf(address holder) external view returns (uint256) {
        return _tokenContainers[holder].chargeAmount;
    }

    /**
     * 해금량
     */
    function unlockAmountOf(address holder) external view returns (uint256) {
        return _tokenContainers[holder].unlockAmount;
    }

    /**
     * 가용잔액
     */
    function availableBalanceOf(address holder) external view returns (uint256) {
        return _tokenContainers[holder].balance;
    }

    /**
     * Holder의 계정 잔액 요약 출력(JSON 포맷)
     */
    function receiptAccountOf(address holder) external view returns (string memory) {
        bytes memory blockStart = bytes("{");
        bytes memory chargeLabel = bytes("\"chargeAmount\" : \"");
        bytes memory charge = bytes(uint2str(_tokenContainers[holder].chargeAmount));
        bytes memory unlockLabel = bytes("\", \"unlockAmount\" : \"");
        bytes memory unlock = bytes(uint2str(_tokenContainers[holder].unlockAmount));
        bytes memory balanceLabel = bytes("\", \"availableBalance\" : \"");
        bytes memory balance = bytes(uint2str(_tokenContainers[holder].balance));
        bytes memory blockEnd = bytes("\"}");

        string memory receipt = new string(blockStart.length + chargeLabel.length + charge.length + unlockLabel.length + unlock.length + balanceLabel.length + balance.length + blockEnd.length);
        bytes memory receiptBytes = bytes(receipt);

        uint readIndex = 0;
        uint writeIndex = 0;

        for (readIndex = 0; readIndex < blockStart.length; readIndex++) {
            receiptBytes[writeIndex++] = blockStart[readIndex];
        }
        for (readIndex = 0; readIndex < chargeLabel.length; readIndex++) {
            receiptBytes[writeIndex++] = chargeLabel[readIndex];
        }
        for (readIndex = 0; readIndex < charge.length; readIndex++) {
            receiptBytes[writeIndex++] = charge[readIndex];
        }
        for (readIndex = 0; readIndex < unlockLabel.length; readIndex++) {
            receiptBytes[writeIndex++] = unlockLabel[readIndex];
        }
        for (readIndex = 0; readIndex < unlock.length; readIndex++) {
            receiptBytes[writeIndex++] = unlock[readIndex];
        }
        for (readIndex = 0; readIndex < balanceLabel.length; readIndex++) {
            receiptBytes[writeIndex++] = balanceLabel[readIndex];
        }
        for (readIndex = 0; readIndex < balance.length; readIndex++) {
            receiptBytes[writeIndex++] = balance[readIndex];
        }
        for (readIndex = 0; readIndex < blockEnd.length; readIndex++) {
            receiptBytes[writeIndex++] = blockEnd[readIndex];
        }

        return string(receiptBytes);
    }

    // uint 값을 string 으로 변환하는 내부 함수
    function uint2str(uint _i) internal pure returns (string memory _uintAsString) {
        if (_i == 0) {
            return "0";
        }
        uint j = _i;
        uint len;
        while (j != 0) {
            len++;
            j /= 10;
        }
        bytes memory bstr = new bytes(len);
        uint k = len - 1;
        while (_i != 0) {
            bstr[k--] = byte(uint8(48 + _i % 10));
            _i /= 10;
        }
        return string(bstr);
    }

    // 전체 유통량 - Owner의 unlockAmount
    function circulationAmount() external view returns (uint256) {
        return _tokenContainers[owner()].unlockAmount;
    }

    // 전체 유통량 증가
    function increaseCirculation(uint256 amount) external onlyOwner returns (uint256) {
        require(!isLock);
        require(_tokenContainers[msg.sender].chargeAmount >= _tokenContainers[msg.sender].unlockAmount.add(amount));
        _tokenContainers[msg.sender].unlockAmount = _tokenContainers[msg.sender].unlockAmount.add(amount);
        _tokenContainers[msg.sender].balance = _tokenContainers[msg.sender].balance.add(amount);
        return _tokenContainers[msg.sender].unlockAmount;
    }

    // 전체 유통량 감소
    function decreaseCirculation(uint256 amount) external onlyOwner returns (uint256) {
        require(!isLock);
        _tokenContainers[msg.sender].unlockAmount = _tokenContainers[msg.sender].unlockAmount.sub(amount);
        _tokenContainers[msg.sender].balance = _tokenContainers[msg.sender].balance.sub(amount);
        return _tokenContainers[msg.sender].unlockAmount;
    }

    /*
     * 특정 사용자(ICO, PreSale 구매자)가 구매한 금액 만큼의 충전량을 직접 입력할 때 사용함
     * IEO 구매자는 거래소가 Spender 권한으로 transferForm으로 나눠주기 때문에
     * 이 함수는 사전 구매자에 한해서만 사용
     */
    function charge(address holder, uint256 chargeAmount, uint256 unlockAmount) external ownerOrDelegator {
        require(!isLock);
        require(holder != address(0));
        require(holder != owner());
        require(chargeAmount > 0);
        require(chargeAmount >= unlockAmount);
        require(_tokenContainers[owner()].balance >= chargeAmount);

        _tokenContainers[owner()].balance = _tokenContainers[owner()].balance.sub(chargeAmount);

        _tokenContainers[holder].chargeAmount = _tokenContainers[holder].chargeAmount.add(chargeAmount);
        _tokenContainers[holder].unlockAmount = _tokenContainers[holder].unlockAmount.add(unlockAmount);
        _tokenContainers[holder].balance = _tokenContainers[holder].balance.add(unlockAmount);
    }
    
    /*
     * 특정 사용자(ICO, PreSale 구매자)가 구매한 금액 안에서 해금량을 변경할 때 사용함
     * unlockAmount는 chargeAmount보다 커질 수 없음
     */
    function increaseUnlockAmount(address holder, uint256 unlockAmount) external ownerOrDelegator {
        require(!isLock);
        require(holder != address(0));
        require(holder != owner());
        require(_tokenContainers[holder].chargeAmount >= _tokenContainers[holder].unlockAmount.add(unlockAmount));

        _tokenContainers[holder].unlockAmount = _tokenContainers[holder].unlockAmount.add(unlockAmount);
        _tokenContainers[holder].balance = _tokenContainers[holder].balance.add(unlockAmount);
    }
    
    /*
     * 특정 사용자(ICO, PreSale 구매자)가 구매한 금액 안에서 해금량을 변경할 때 사용함
     * balance가 lockAmount보다 큰 경우에만 허용
     */
    function decreaseUnlockAmount(address holder, uint256 lockAmount) external ownerOrDelegator {
        require(!isLock);
        require(holder != address(0));
        require(holder != owner());
        require(_tokenContainers[holder].balance >= lockAmount);

        _tokenContainers[holder].unlockAmount = _tokenContainers[holder].unlockAmount.sub(lockAmount);
        _tokenContainers[holder].balance = _tokenContainers[holder].balance.sub(lockAmount);
    }

    /*
     * 특정 사용자(ICO, PreSale 구매자)가 구매한 금액 안에서 전체를 해금할 때 사용함
     * 한번 지정한 해금량은 늘릴 수만 있고 줄일 수는 없음
     */
    function unlockAmountAll(address holder) external ownerOrDelegator {
        require(!isLock);
        require(holder != address(0));
        require(holder != owner());

        uint256 unlockAmount = _tokenContainers[holder].chargeAmount.sub(_tokenContainers[holder].unlockAmount);

        require(unlockAmount > 0);
        
        _tokenContainers[holder].unlockAmount = _tokenContainers[holder].unlockAmount.add(unlockAmount);
        _tokenContainers[holder].balance = _tokenContainers[holder].balance.add(unlockAmount);
    }

    // 계약 잠금
    function lock() external onlyOwner returns (bool) {
        isLock = true;
        return isLock;
    }

    // 계약 잠금 해제
    function unlock() external onlyOwner returns (bool) {
        isLock = false;
        return isLock;
    }
}

contract SymToken is ERC20Like {
    string public name = "SymToken";
    string public symbol = "SYM";
    uint256 public decimals = 18;

    constructor () public {
        _totalSupply = 900000000 * (10 ** decimals);
        _tokenContainers[msg.sender].chargeAmount = _totalSupply;
    }
}