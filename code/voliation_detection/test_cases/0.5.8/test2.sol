pragma solidity >=0.5.0 <0.6.0;


library AltBn128 {
    uint256 constant public G1x = uint256(0x01);
    uint256 constant public G1y = uint256(0x02);

    // Number of elements in the field (often called `q`)
    // n = n(u) = 36u^4 + 36u^3 + 18u^2 + 6u + 1
    uint256 constant public N = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001;

    // p = p(u) = 36u^4 + 36u^3 + 24u^2 + 6u + 1
    // Field Order
    uint256 constant public P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47;

    // (p+1) / 4
    uint256 constant public A = 0xc19139cb84c680a6e14116da060561765e05aa45a1c72a34f082305b61f3f52;

    /* ECC Functions */
    function ecAdd(uint256[2] memory p0, uint256[2] memory p1) public view
        returns (uint256[2] memory retP)
    {
        uint256[4] memory i = [p0[0], p0[1], p1[0], p1[1]];
        
        assembly {
            // call ecadd precompile
            // inputs are: x1, y1, x2, y2
            if iszero(staticcall(not(0), 0x06, i, 0x80, retP, 0x40)) {
                revert(0, 0)
            }
        }
    }

    function ecMul(uint256[2] memory p, uint256 s) public view
        returns (uint256[2] memory retP)
    {
        // With a public key (x, y), this computes p = scalar * (x, y).
        uint256[3] memory i = [p[0], p[1], s];
        
        assembly {
            // call ecmul precompile
            // inputs are: x, y, scalar
            if iszero(staticcall(not(0), 0x07, i, 0x60, retP, 0x40)) {
                revert(0, 0)
            }
        }
    }

    function ecMulG(uint256 s) public view
        returns (uint256[2] memory retP)
    {
        return ecMul([G1x, G1y], s);
    }

    function powmod(uint256 base, uint256 e, uint256 m) public view
        returns (uint256 o)
    {
        // returns pow(base, e) % m
        assembly {
            // define pointer
            let p := mload(0x40)

            // Store data assembly-favouring ways
            mstore(p, 0x20)             // Length of Base
            mstore(add(p, 0x20), 0x20)  // Length of Exponent
            mstore(add(p, 0x40), 0x20)  // Length of Modulus
            mstore(add(p, 0x60), base)  // Base
            mstore(add(p, 0x80), e)     // Exponent
            mstore(add(p, 0xa0), m)     // Modulus

            // call modexp precompile! -- old school gas handling
            let success := staticcall(sub(gas, 2000), 0x05, p, 0xc0, p, 0x20)

            // gas fiddling
            switch success case 0 {
                revert(0, 0)
            }

            // data
            o := mload(p)
        }
    }

    // Keep everything contained within this lib
    function addmodn(uint256 x, uint256 n) public pure
        returns (uint256)
    {
        return addmod(x, n, N);
    }

    function modn(uint256 x) public pure
        returns (uint256)
    {
        return x % N;
    }

    /*
       Checks if the points x, y exists on alt_bn_128 curve
    */
    function onCurve(uint256 x, uint256 y) public pure
        returns(bool)
    {
        uint256 beta = mulmod(x, x, P);
        beta = mulmod(beta, x, P);
        beta = addmod(beta, 3, P);

        return onCurveBeta(beta, y);
    }

    function onCurveBeta(uint256 beta, uint256 y) public pure
        returns(bool)
    {
        return beta == mulmod(y, y, P);
    }

    /*
    * Calculates point y value given x
    */
    function evalCurve(uint256 x) public view
        returns (uint256, uint256)
    {
        uint256 beta = mulmod(x, x, P);
        beta = mulmod(beta, x, P);
        beta = addmod(beta, 3, P);

        uint256 y = powmod(beta, A, P);

        // require(beta == mulmod(y, y, P), "Invalid x for evalCurve");
        return (beta, y);
    }
}

library LSAG {
    // abi.encodePacked is the "concat" or "serialization"
    // of all supplied arguments into one long bytes value
    // i.e. abi.encodePacked :: [a] -> bytes

    /**
    * Converts an integer to an elliptic curve point
    */
    function intToPoint(uint256 _x) public view
        returns (uint256[2] memory)
    {
        uint256 x = _x;
        uint256 y;
        uint256 beta;

        while (true) {
            (beta, y) = AltBn128.evalCurve(x);

            if (AltBn128.onCurveBeta(beta, y)) {
                return [x, y];
            }

            x = AltBn128.addmodn(x, 1);
        }
    }

    /**
    * Returns an integer representation of the hash
    * of the input
    */
    function H1(bytes memory b) public pure
        returns (uint256)
    {
        return AltBn128.modn(uint256(keccak256(b)));
    }

    /**
    * Returns elliptic curve point of the integer representation
    * of the hash of the input
    */
    function H2(bytes memory b) public view
        returns (uint256[2] memory)
    {
        return intToPoint(H1(b));
    }

    /**
    * Helper function to calculate Z1
    * Avoids stack too deep problem
    */
    function ringCalcZ1(
        uint256[2] memory pubKey,
        uint256 c,
        uint256 s
    ) public view
        returns (uint256[2] memory)
    {
        return AltBn128.ecAdd(
            AltBn128.ecMulG(s),
            AltBn128.ecMul(pubKey, c)
        );
    }

    /**
    * Helper function to calculate Z2
    * Avoids stack too deep problem
    */
    function ringCalcZ2(
        uint256[2] memory keyImage,
        uint256[2] memory h,
        uint256 s,
        uint256 c
    ) public view
        returns (uint256[2] memory)
    {
        return AltBn128.ecAdd(
            AltBn128.ecMul(h, s),
            AltBn128.ecMul(keyImage, c)
        );
    }


    /**
    * Verifies the ring signature
    * Section 4.2 of the paper https://eprint.iacr.org/2004/027.pdf
    */
    function verify(
        bytes memory message,
        uint256 c0,
        uint256[2] memory keyImage,
        uint256[] memory s,
        uint256[2][] memory publicKeys
    ) public view
        returns (bool)
    {
        require(publicKeys.length >= 2, "Signature size too small");
        require(publicKeys.length == s.length, "Signature sizes do not match!");

        uint256 c = c0;
        uint256 i = 0;

        // Step 1
        // Extract out public key bytes
        bytes memory hBytes = "";

        for (i = 0; i < publicKeys.length; i++) {
            hBytes = abi.encodePacked(
                hBytes,
                publicKeys[i]
            );
        }

        uint256[2] memory h = H2(hBytes);

        // Step 2
        uint256[2] memory z_1;
        uint256[2] memory z_2;


        for (i = 0; i < publicKeys.length; i++) {
            z_1 = ringCalcZ1(publicKeys[i], c, s[i]);
            z_2 = ringCalcZ2(keyImage, h, s[i], c);

            if (i != publicKeys.length - 1) {
                c = H1(
                    abi.encodePacked(
                        hBytes,
                        keyImage,
                        message,
                        z_1,
                        z_2
                    )
                );
            }
        }

        return c0 == H1(
            abi.encodePacked(
                hBytes,
                keyImage,
                message,
                z_1,
                z_2
            )
        );
    }
}
contract Heiswap {
    // Events
    event Deposited(address, uint256 etherAmount, uint256 idx);

    // Maximum number of participants in a ring
    uint256 constant ringMaxParticipants = 5;

    struct Ring {
        /* NOTE: Once someone signs a transaction
                 then no one else is able to deposit
                 money into the ring anymore
        */

        // When was thing block created
        uint256 createdBlockNumber;

        // Ring hash will be available once
        // there is 5 participants in the ring
        // TODO: Manually call the function "closeRing"
        bytes32 ringHash;

        // In a ring, everyone deposits
        // the same amount of ETH. Otherwise
        // the sender and receiver can be identified
        // which defeats the whole purpose of this
        // application
        uint256 amountDeposited;

        // Number of participants who've deposited
        uint8 dParticipantsNo;
        // The Public Key (stealth addresses)
        // These are in bytes because web3.js is
        // buggy with big int
        mapping (uint256 => uint256[2]) publicKeys;

        // Number of participants who've withdrawn
        uint8 wParticipantsNo;
        // Key Images of participants who have withdrawn
        // Used to determine if a participant is trying to
        // double withdraw
        mapping (uint256 => uint256[2]) keyImages;
    }

    // Fixed amounts allowed to be inserted into the rings
    uint256[10] allowedAmounts = [ 1 ether, 2 ether, 4 ether, 8 ether, 16 ether, 32 ether ];

    // Mimics dynamic 'lists'
    // allowedAmount => numberOfRings (in the current amount)
    mapping(uint256 => uint256) ringsNo;

    // allowedAmount => ringIndex => Ring
    mapping (uint256 => mapping(uint256 => Ring)) rings;


    function deposit(uint256[2] memory publicKey) public payable
    {
        // Get amount sent
        uint256 receivedEther = floorEtherAndCheck(msg.value);

        // Gets the current ring for the amounts
        uint256 curIndex = ringsNo[receivedEther];
        Ring storage ring = rings[receivedEther][curIndex];

        if (!AltBn128.onCurve(uint256(publicKey[0]), uint256(publicKey[1]))) {
            revert("Public Key no on Curve");
        }

        // Make sure that public key (stealth address)
        // isn't already in there
        for (uint8 i = 0; i < ring.dParticipantsNo; i++) {
            if (ring.publicKeys[i][0] == publicKey[0] &&
                ring.publicKeys[i][1] == publicKey[1]) {
                revert("Address already in current Ring");
            }
        }

        // If its a new ring
        // set createdBlockNum size
        if (ring.dParticipantsNo == 0) {
            ring.createdBlockNumber = block.number - 1;
        }

        // Update ring params
        ring.publicKeys[ring.dParticipantsNo] = publicKey;
        ring.dParticipantsNo++;
        ring.amountDeposited += receivedEther;

        // Create new ring if current ring has exceeded number of participants
        if (ring.dParticipantsNo >= ringMaxParticipants) {
            // Set ringHash
            ring.ringHash = createRingHash(receivedEther / (1 ether), curIndex);

            // Add new Ring pool
            ringsNo[receivedEther] += 1;
        }

        // Broadcast Event
        emit Deposited(msg.sender, receivedEther, curIndex);
    }

    // User can only withdraw if the ring is closed
    // NOTE: Convert to ether
    // i.e. there is a ringHash
    function withdraw(
        address payable receiver, uint256 amountEther, uint256 index,
        uint256 c0, uint256[2] memory keyImage, uint256[] memory s
    ) public
    {
        uint i;
        uint256 startGas = gasleft();

        // Get amount sent in whole number
        uint256 withdrawEther = floorEtherAndCheck(amountEther * 1 ether);

        // Gets the current ring, given the amount and idx
        Ring storage ring = rings[withdrawEther][index];

        // If everyone has withdrawn
        if (ring.wParticipantsNo >= ringMaxParticipants) {
            revert("All funds from current Ring has been withdrawn");
        }

        // Ring needs to be closed first
        if (ring.ringHash == bytes32(0x00)) {
            revert("Ring isn't closed");
        }

        // Convert public key to dynamic array
        // Based on number of people who have
        // deposited
        uint256[2][] memory publicKeys = new uint256[2][](ring.dParticipantsNo);

        for (i = 0; i < ring.dParticipantsNo; i++) {
            publicKeys[i] = [
                uint256(ring.publicKeys[uint8(i)][0]),
                uint256(ring.publicKeys[uint8(i)][1])
            ];
        }

        // Attempts to verify ring signature
        bool signatureVerified = LSAG.verify(
            abi.encodePacked(ring.ringHash, receiver), // Convert to bytes
            c0,
            keyImage,
            s,
            publicKeys
        );

        if (!signatureVerified) {
            revert("Invalid signature");
        }

        // Checks if Key Image has been used
        // AKA No double withdraw
        for (i = 0; i < ring.wParticipantsNo; i++) {
            if (ring.keyImages[uint8(i)][0] == keyImage[0] &&
                ring.keyImages[uint8(i)][1] == keyImage[1]) {
                revert("Signature has been used!");
            }
        }

        // Otherwise adds key image to the current key image
        // And adjusts params accordingly
        ring.keyImages[ring.wParticipantsNo] = keyImage;
        ring.wParticipantsNo += 1;

        // Send ETH to receiver
        // Calculate fees (1.33%) + gasUsage fees
        uint256 gasUsed = startGas - gasleft();
        uint256 fees = (withdrawEther / 75) + gasUsed + startGas;

        // Relayer gets (1%) of the xferred value + compensated for gas usage
        msg.sender.transfer(fees);

        // Reciever then gets the remaining ETH
        receiver.transfer(withdrawEther - fees);
    }


    // If enough blocks has passed, user can manually close the ring.
    // To force fully close the ring
    function forceCloseRing(
        uint256 amount, uint256 index,
        uint256 c0, uint256[2] memory keyImage, uint256[] memory s
    ) public
    {
        // Get amount sent
        uint256 receivedEther = floorEtherAndCheck(amount * 1 ether);

        // Gets the current ring for the amounts
        uint256 curIndex = ringsNo[receivedEther];
        Ring storage ring = rings[receivedEther][curIndex];
        
        // How many blocks have passed
        uint256 blocksPassed = (block.number - 1 - ring.createdBlockNumber);

        if (ring.dParticipantsNo < 2) {
            revert("Not enough participants!");
        }

        if (ring.ringHash != bytes32(0x00)) {
            revert("Ring is already closed!");
        }

        // Convert public key to dynamic array
        uint256[2][] memory publicKeys = new uint256[2][](ring.dParticipantsNo);

        for (uint8 i = 0; i < ring.dParticipantsNo; i++) {
            publicKeys[i] = [
                uint256(ring.publicKeys[uint8(i)][0]),
                uint256(ring.publicKeys[uint8(i)][1])
            ];
        }

        // Attempts to verify ring signature
        // for user to close ring
        bool signatureVerified = LSAG.verify(
            abi.encodePacked("closeRing", receivedEther, curIndex),
            c0,
            keyImage,
            s,
            publicKeys
        );

        if (!signatureVerified) {
            revert("Invalid signature");
        }

        // Close the ring
        // (Once ring hash is there, it means ring is closed)
        ring.ringHash = createRingHash(receivedEther / (1 ether), index);

        // Create new ring
        ringsNo[receivedEther] += 1;
    }

    /* Helper functions */
    // TODO: Use safemath library

    // Creates ring hash (used for signing)
    function createRingHash(uint256 amountEther, uint256 index) internal view
        returns (bytes32)
    {
        uint256[2][ringMaxParticipants] memory publicKeys;
        uint256 receivedEther = floorEtherAndCheck(amountEther * 1 ether);

        Ring storage r = rings[receivedEther][index];

        for (uint8 i = 0; i < ringMaxParticipants; i++) {
            publicKeys[i] = r.publicKeys[i];
        }

        bytes memory b = abi.encodePacked(
            blockhash(block.number - 1),
            r.createdBlockNumber,
            r.amountDeposited,
            r.dParticipantsNo,
            publicKeys
        );

        return keccak256(b);
    }

    // Gets ring hash needed to generate signature
    function getRingHash(uint256 amountEther, uint256 index) public view
        returns (bytes memory)
    {
        uint256 receivedEther = floorEtherAndCheck(amountEther * 1 ether);
        Ring memory r = rings[receivedEther][index];

        // If the ringhash hasn't been closed
        // return the hash needed to close the
        // ring
        if (r.ringHash == bytes32(0x00)) {
            return abi.encodePacked("closeRing", receivedEther, index);
        }

        return abi.encodePacked(r.ringHash);
    }

    // Gets all addresses in a Ring
    // Converting to Bytes32 cause web3.js has a bug that doesn't convert
    // Big Num correctly....
    function getPublicKeys(uint256 amountEther, uint256 index) public view
        returns (bytes32[2][ringMaxParticipants] memory)
    {
        uint256 receivedEther = floorEtherAndCheck(amountEther * 1 ether);

        bytes32[2][ringMaxParticipants] memory publicKeys;

        for (uint i = 0; i < ringMaxParticipants; i++) {
            publicKeys[i][0] = bytes32(rings[receivedEther][index].publicKeys[i][0]);
            publicKeys[i][1] = bytes32(rings[receivedEther][index].publicKeys[i][1]);
        }

        return publicKeys;
    }

    // Gets number of participants who
    // have deposited and withdrawn
    // ret: (dParticipants, wParticipants)
    function getParticipants(uint256 amountEther, uint256 index) public view
        returns (uint8, uint8)
    {
        uint256 receivedEther = floorEtherAndCheck(amountEther * 1 ether);
        Ring memory r = rings[receivedEther][index];

        return (r.dParticipantsNo, r.wParticipantsNo);
    }

    // Gets the max nunmber of ring participants
    function getRingMaxParticipants() public pure
        returns (uint256)
    {
        return ringMaxParticipants;
    }

    // Gets the current ring index
    // for the given amount of ether
    // Used to estimate the current idx for better UX
    function getCurrentRingIdx(uint256 amountEther) public view
        returns (uint256)
    {
        uint256 receivedEther = floorEtherAndCheck(amountEther * 1 ether);
        return ringsNo[receivedEther];
    }

    // Floors the current ether values
    // Makes sure the values needs to in `allowedAmounts`
    function floorEtherAndCheck(uint256 receivedAmount) internal view
        returns (uint256)
    {
        uint256 i;
        bool allowed = false;

        // Floors received ether
        uint256 receivedEther = (receivedAmount / 1 ether) * 1 ether;

        for (i = 0; i < 10; i ++) {
            if (allowedAmounts[i] == receivedEther) {
                allowed = true;
            }
            if (allowed) {
                break;
            }
        }

        // Revert if ETH sent isn't in the allowed fixed amounts
        require(allowed, "Only ETH values of 1, 2, 4, 6, 8 ... 32 are allowed");

        return receivedEther;
    }
}