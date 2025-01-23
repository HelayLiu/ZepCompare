pragma solidity ^0.8.0;

contract ERC20 {
    
    mapping(address => mapping(address => uint256)) private _allowances;
    event Approval(address indexed owner, address indexed spender, uint256 value);
    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) public virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }
}