// SPDX-License-Identifier: MIT
pragma solidity 0.8.1;




interface ITimeswapLendCallback {
    /// @notice Called to `msg.sender` after initiating a lend from ITimeswapPair#lend.
    /// @dev In the implementation you must pay the asset token owed for the lend transaction.
    /// The caller of this method must be checked to be a TimeswapPair deployed by the canonical TimeswapFactory.
    /// @param assetIn The amount of asset tokens owed due to the pool for the lend transaction
    /// @param data Any data passed through by the caller via the ITimeswapPair#lend call
    function timeswapLendCallback(
        uint112 assetIn,
        bytes calldata data
    ) external;
}
interface ITimeswapBorrowCallback {
    /// @notice Called to `msg.sender` after initiating a borrow from ITimeswapPair#borrow.
    /// @dev In the implementation you must pay the collateral token owed for the borrow transaction.
    /// The caller of this method must be checked to be a TimeswapPair deployed by the canonical TimeswapFactory.
    /// @param collateralIn The amount of asset tokens owed due to the pool for the borrow transaction
    /// @param data Any data passed through by the caller via the ITimeswapPair#borrow call
    function timeswapBorrowCallback(
        uint112 collateralIn,
        bytes calldata data
    ) external;
}
interface ITimeswapMintCallback {
    /// @notice Called to `msg.sender` after initiating a mint from ITimeswapPair#mint.
    /// @dev In the implementation you must pay the asset token and collateral token owed for the mint transaction.
    /// The caller of this method must be checked to be a TimeswapPair deployed by the canonical TimeswapFactory.
    /// @param assetIn The amount of asset tokens owed due to the pool for the mint transaction.
    /// @param collateralIn The amount of collateral tokens owed due to the pool for the min transaction.
    /// @param data Any data passed through by the caller via the ITimeswapPair#mint call
    function timeswapMintCallback(
        uint112 assetIn,
        uint112 collateralIn,
        bytes calldata data
    ) external;
}
library ETH {
    function transfer(address payable to, uint256 amount) internal {
        (bool success, ) = to.call{value: amount}('');
        require(success, 'E521');
    }
}

library SquareRoot {
    // babylonian method (https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method)
    function sqrt(uint256 y) internal pure returns (uint256 z) {
        if (y > 3) {
            z = y;
            uint256 x = y / 2 + 1;
            while (x < z) {
                z = x;
                x = (y / x + x) / 2;
            }
        } else if (y != 0) {
            z = 1;
        }
    }

    function sqrtUp(uint256 y) internal pure returns (uint256 z) {
        z = sqrt(y);
        if (z % y > 0) z++;
    }
}

library Math {
    function divUp(uint256 x, uint256 y) internal pure returns (uint256 z) {
        z = x / y;
        if (x % y > 0) z++;
    }

    function shiftRightUp(uint256 x, uint8 y) internal pure returns (uint256 z) {
        z = x >> y;
        if (x != z << y) z++;
    }

}

library SafeCast {
    function modUint32(uint256 x) internal pure returns (uint32 y) {
        y = uint32(x % 0x100000000);
    }
    
    function toUint112(uint256 x) internal pure returns (uint112 y) {
        require((y = uint112(x)) == x);
    }

    function toUint128(uint256 x) internal pure returns (uint128 y) {
        require((y = uint128(x)) == x);
    }

    function truncateUint112(uint256 x) internal pure returns (uint112 y) {
        if (x > type(uint112).max) return y = type(uint112).max;
        y = uint112(x);
    }
}

library NFTSVG {

    struct SVGParams {
        string tokenId;
        string svgTitle;
        string assetInfo;
        string collateralInfo;
        string debtRequired;
        string collateralLocked;
        string maturityDate;
        string maturityTimestampString;
        string tokenColors;
        bool isMatured;
    }

    function constructSVG(SVGParams memory params) public pure returns (string memory) {


        string memory colorScheme = params.isMatured ? ".G{stop-color:#3C3C3C}.H{fill:#959595}.I{stop-color:#000000}.J{stop-color:#FFFFFF}" : ".G{stop-color:#20087E}.H{fill:#5457D7}.I{stop-color:#61F6FF}.J{stop-color:#3C43FF}";

        string memory svg = string(abi.encodePacked('<svg width="290" height="500" xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink"><style type="text/css" ><![CDATA[.B{fill-rule:evenodd}', params.tokenColors, colorScheme, ']]></style><g clip-path="url(#mainclip)"><rect width="290" height="500" fill="url(\'#background\')"/><rect y="409" width="290" height="90" fill="#141330" fill-opacity="0.4"/><rect y="408" width="290" height="2" fill="url(#divider)"/></g><text y="70px" x="145" fill="white" font-family="arial" font-weight="500" font-size="24px" text-anchor="middle">'));

        svg = string(abi.encodePacked(svg, params.svgTitle, '</text><text y="95px" x="145" fill="white" font-family="arial" font-weight="400" font-size="12px" text-anchor="middle">', params.maturityDate, '</text>'));

        
        if (!params.isMatured) {
            string memory maturityInfo = string(abi.encodePacked('MATURITY: ', params.maturityTimestampString));
            svg = string(abi.encodePacked(svg, '<text y="115px" x="145" fill="white" font-family="arial" font-weight="300" font-size="10px" text-anchor="middle" opacity="50%">', maturityInfo, '</text>'));
        } else {
            svg = string(abi.encodePacked(svg, '<rect width="74" height="22" rx="13" y="110" x="107" text-anchor="middle" fill="#FFFFFF" /><text y="125px" x="145" fill="black" font-family="arial" font-weight="600" font-size="10px" letter-spacing="1" text-anchor="middle">MATURED</text>'));
        }

        svg = string(abi.encodePacked(svg, '<text text-rendering="optimizeSpeed"><textPath startOffset="-100%" fill="white" font-family="\'Courier New\', monospace" font-size="10px" xlink:href="#text-path-a">', params.assetInfo, '<animate additive="sum" attributeName="startOffset" from="0%" to="100%" begin="0s" dur="30s" repeatCount="indefinite" /></textPath><textPath startOffset="0%" fill="white" font-family="\'Courier New\', monospace" font-size="10px" xlink:href="#text-path-a">', params.assetInfo, '<animate additive="sum" attributeName="startOffset" from="0%" to="100%" begin="0s" dur="30s" repeatCount="indefinite" /></textPath><textPath startOffset="50%" fill="white" font-family="\'Courier New\', monospace" font-size="10px" xlink:href="#text-path-a">'));
        svg = string(abi.encodePacked(svg, params.collateralInfo, '<animate additive="sum" attributeName="startOffset" from="0%" to="100%" begin="0s" dur="30s" repeatCount="indefinite" /></textPath><textPath startOffset="-50%" fill="white" font-family="\'Courier New\', monospace" font-size="10px" xlink:href="#text-path-a">', params.collateralInfo, '<animate additive="sum" attributeName="startOffset" from="0%" to="100%" begin="0s" dur="30s" repeatCount="indefinite" /></textPath></text><text y="435px" x="12" fill="white" font-family="arial" font-weight="400" font-size="13px" opacity="60%">ID:</text><text y="435px" x="278" fill="white" font-family="arial" font-weight="500" font-size="13px" text-anchor="end">'));
        svg = string(abi.encodePacked(svg, params.tokenId, '</text><text y="460px" x="12" fill="white" font-family="arial" font-weight="400" font-size="13px" opacity="60%">Debt required:</text><text y="460px" x="278" fill="white" font-family="arial" font-weight="500" font-size="13px" text-anchor="end">', params.debtRequired, '</text><text y="484px" x="12" fill="white" font-family="arial" font-weight="400" font-size="13px" opacity="60%">Collateral locked:</text><text y="484px" x="278" fill="white" font-family="arial" font-weight="500" font-size="13px" text-anchor="end">', params.collateralLocked, '</text><g filter="url(#filter0_f)"><path d="M253 319.5C253 346.838 204.871 369 145.5 369C86.1294 369 38 346.838 38 319.5C38 292.162 86.1294 270 145.5 270C204.871 270 253 292.162 253 319.5Z" class="H"/></g>'));
        svg = string(abi.encodePacked(svg, '<path d="M144.235 272.663h4.147v11.255h-4.147zm62.092 19.456l2.074 2.089-16.76 5.627-2.074-2.089zm-26.564-14.565l3.591 1.206-9.676 9.747-3.591-1.206zm37.046 34.903v2.412h-19.353v-2.412zm-33.454 36.11l-3.591 1.206-9.676-9.747 3.591-1.206zm25.046-15.448l-2.074 2.089-16.76-5.627 2.074-2.089zm-64.165 10.289h4.147v11.255h-4.147zm-43.258-15.916l2.074 2.089-16.76 5.627-2.074-2.089zm17.962 11.328l3.591 1.206-9.676 9.747-3.591-1.206zm-25.778-26.157v2.412H73.809v-2.412zm28.915-26.253l-3.591 1.206-9.676-9.747 3.591-1.206zm-20.434 10.881l-2.074 2.089-16.76-5.627 2.074-2.089z" fill="#6fa4d4"/><path d="M198.383 344.249C211.892 336.376 220 325.646 220 314s-8.108-22.376-21.617-30.249C184.898 275.893 166.204 271 145.5 271s-39.398 4.893-52.883 12.751C79.108 291.624 71 302.354 71 314s8.108 22.376 21.617 30.249C106.102 352.107 124.796 357 145.5 357s39.398-4.893 52.883-12.751zM145.5 358c41.698 0 75.5-19.699 75.5-44s-33.802-44-75.5-44S70 289.699 70 314s33.803 44 75.5 44zm56.402-10.206C216.307 339.026 225 327.049 225 314s-8.693-25.026-23.098-33.794C187.516 271.449 167.577 266 145.5 266s-42.016 5.449-56.402 14.206C74.694 288.974 66 300.951 66 314s8.694 25.026 23.098 33.794C103.484 356.551 123.423 362 145.5 362s42.016-5.449 56.402-14.206zM145.5 363c44.459 0 80.5-21.938 80.5-49s-36.041-49-80.5-49S65 286.938 65 314s36.041 49 80.5 49z" fill-rule="evenodd" fill="#6fa4d5"/><path d="M189.764 303.604c0 14.364-19.951 26.008-44.562 26.008-24.343 0-44.127-11.392-44.555-25.54v6.92.363c0 14.38 19.951 26.022 44.562 26.022s44.562-11.642 44.562-26.022v-.363-7.574h-.008l.001.186z" fill="#7fc2e2"/><path d="M145.202 326.408c21.834 0 39.533-10.256 39.533-22.906s-17.699-22.906-39.533-22.906-39.533 10.255-39.533 22.906 17.7 22.906 39.533 22.906z" fill="#020136"/><path d="M189.764 303.604c0 14.364-19.951 26.008-44.562 26.008s-44.562-11.644-44.562-26.008 19.951-26.008 44.562-26.008 44.562 11.644 44.562 26.008zm-5.029-.102c0 12.65-17.699 22.906-39.533 22.906s-39.533-10.255-39.533-22.906 17.699-22.906 39.533-22.906 39.533 10.256 39.533 22.906z" fill="#4f95b8" class="B"/><path d="M184.753 303.84v-5.406c0-18.859-10.806-36.185-28.114-45.047l-3.987-2.053a2.31 2.31 0 0 1-.975-.848 2.46 2.46 0 0 1-.39-1.259 2.47 2.47 0 0 1 .316-1.282c.216-.384.536-.699.924-.908l6.693-3.887c15.85-9.252 25.533-25.798 25.533-43.637V184h-78.996v15.095c0 18.065 9.925 34.782 26.098 43.959l6.772 3.846a2.34 2.34 0 0 1 .937.911c.223.39.334.839.321 1.293s-.15.894-.395 1.27-.588.671-.988.851l-4.105 2.053c-17.598 8.772-28.64 26.249-28.64 45.32v4.948c-.624 6.062 3.212 12.255 11.581 16.901 15.515 8.616 40.595 8.664 56.011.096 8.238-4.584 12.008-10.688 11.404-16.703h0z" fill="#fff" fill-opacity=".3"/><path d="M154.382 238.266c3.037-5.261 3.007-10.965-.062-12.737l2.734 1.579c3.069 1.772 3.098 7.476.061 12.737s-7.992 8.088-11.061 6.316l-2.734-1.579c3.069 1.772 8.025-1.055 11.062-6.315v-.001z" class="D"/><path d="M154.382 238.266c3.037-5.261 3.007-10.965-.062-12.737s-8.024 1.055-11.061 6.316-3.008 10.965.061 12.737 8.025-1.055 11.062-6.315v-.001zm-1.402-.809c2.27-3.932 2.252-8.2-.045-9.526s-6.004.792-8.274 4.724-2.247 8.192.051 9.519 5.998-.784 8.268-4.716v-.001z" class="B C"/><path d="M152.935 227.929c2.297 1.326 2.315 5.595.045 9.526s-5.971 6.042-8.268 4.716-2.321-5.587-.051-9.519 5.975-6.051 8.273-4.724l.001.001z" class="D"/><path d="M148.854 232.173l1.827-2.157c.303-.364.664-.269.607.154l-.349 2.545c-.021.163.023.302.121.349l1.488.806c.241.139.107.695-.237.951l-2.028 1.534a.91.91 0 0 0-.316.438l-.91 2.656c-.155.449-.597.692-.75.437l-.938-1.578c-.031-.052-.08-.09-.139-.107s-.121-.01-.174.019l-2.043.841c-.35.139-.475-.274-.238-.686l1.458-2.525a.81.81 0 0 0 .118-.492l-.345-2.136a.8.8 0 0 1 .142-.539.81.81 0 0 1 .457-.318l1.85.033a.56.56 0 0 0 .223-.071.57.57 0 0 0 .176-.155v.001z" class="C"/><path d="M166.548 230.55c4.318-4.272 5.796-9.782 3.303-12.302l2.221 2.245c2.492 2.519 1.014 8.029-3.304 12.301s-9.844 5.691-12.336 3.171l-2.221-2.245c2.492 2.52 8.018 1.102 12.337-3.17z" class="D"/><path d="M166.548 230.549c4.318-4.272 5.796-9.782 3.303-12.302s-8.017-1.101-12.336 3.171-5.797 9.782-3.304 12.301 8.018 1.102 12.337-3.17zm-1.139-1.151c3.228-3.193 4.338-7.314 2.472-9.2s-6-.821-9.227 2.371-4.33 7.308-2.464 9.194 5.993.827 9.22-2.366l-.001.001z" class="B C"/><path d="M167.881 220.199c1.866 1.886.755 6.008-2.472 9.2s-7.354 4.252-9.22 2.366-.763-6.002 2.464-9.194 7.36-4.258 9.227-2.371l.001-.001z" class="D"/><path d="M162.824 223.215l2.332-1.599c.388-.271.711-.084.545.308l-1.008 2.363c-.064.152-.057.298.024.369l1.222 1.17c.196.198-.08.699-.48.854l-2.361.944c-.172.067-.318.186-.421.339l-1.579 2.321c-.268.392-.758.51-.839.224l-.488-1.77c-.015-.059-.052-.109-.104-.141s-.115-.04-.174-.026l-2.193.271c-.375.042-.386-.39-.048-.725l2.072-2.05a.81.81 0 0 0 .244-.443l.231-2.151a.81.81 0 0 1 .28-.483c.148-.123.333-.188.524-.186l1.776.52c.078.013.158.01.234-.009a.56.56 0 0 0 .211-.103v.003z" class="C"/><path d="M131.352 236.907c4.692 3.858 10.325 4.762 12.576 2.024l-2.005 2.439c-2.251 2.738-7.883 1.832-12.575-2.025s-6.67-9.208-4.419-11.946l2.005-2.439c-2.251 2.738-.274 8.089 4.419 11.947h-.001z" class="D"/><path d="M131.352 236.907c4.692 3.858 10.325 4.762 12.576 2.024s.273-8.088-4.419-11.946-10.324-4.763-12.575-2.025-.274 8.089 4.419 11.947h-.001zm1.028-1.251c3.507 2.883 7.721 3.564 9.405 1.515s.202-6.052-3.305-8.935-7.714-3.558-9.399-1.508-.208 6.046 3.299 8.929v-.001z" class="B C"/><path d="M141.785 237.172c-1.685 2.049-5.898 1.368-9.405-1.515s-4.983-6.879-3.299-8.929 5.892-1.374 9.399 1.509 4.991 6.885 3.305 8.935z" class="D"/><path d="M138.267 232.451l1.829 2.156c.309.359.156.699-.251.574l-2.454-.76c-.157-.048-.302-.026-.364.062l-1.039 1.335c-.177.215-.703-.008-.899-.39l-1.181-2.252c-.084-.164-.217-.298-.381-.384l-2.471-1.333c-.417-.227-.585-.702-.309-.812l1.71-.667c.057-.021.103-.064.128-.12s.03-.117.009-.174l-.495-2.153c-.08-.368.349-.424.716-.122l2.252 1.851a.81.81 0 0 0 .466.197l2.164.009a.81.81 0 0 1 .509.228c.138.134.221.312.239.503l-.336 1.82a.59.59 0 0 0 .033.232c.026.074.069.142.124.2h.001z" class="C"/><path d="M119.071 225.508c3.876 4.677 9.235 6.633 11.964 4.372l-2.431 2.015c-2.729 2.261-8.087.305-11.963-4.373s-4.803-10.306-2.074-12.567l2.431-2.015c-2.729 2.261-1.802 7.89 2.073 12.568z" class="D"/><path d="M119.071 225.508c3.876 4.677 9.235 6.633 11.964 4.372s1.802-7.89-2.074-12.567-9.234-6.634-11.963-4.373-1.802 7.89 2.073 12.568zm1.247-1.033c2.897 3.496 6.905 4.964 8.947 3.271s1.346-5.904-1.551-9.4-6.9-4.956-8.942-3.263-1.351 5.896 1.546 9.392h0z" class="B C"/><path d="M129.265 227.745c-2.043 1.693-6.051.225-8.947-3.271s-3.589-7.699-1.546-9.392 6.045-.233 8.942 3.263 3.595 7.707 1.551 9.4h0z" class="D"/><path d="M126.705 222.444l1.387 2.463c.235.411.021.716-.355.516l-2.265-1.212c-.145-.077-.292-.083-.369-.008l-1.273 1.114c-.214.177-.689-.141-.809-.553l-.733-2.435a.9.9 0 0 0-.301-.449l-2.173-1.777c-.367-.302-.441-.8-.149-.856l1.806-.331c.06-.01.114-.043.15-.092s.05-.111.041-.171l-.078-2.208c-.009-.377.423-.35.726.016l1.86 2.245a.81.81 0 0 0 .42.282l2.123.419c.186.049.347.163.456.32s.158.349.139.539l-.674 1.723c-.02.077-.023.156-.012.234s.041.152.084.219l-.001.002z" class="C"/><path d="M140.196 225.21c5.607 2.338 11.261 1.576 12.624-1.695l-1.215 2.914c-1.364 3.271-7.017 4.031-12.624 1.694s-9.046-6.888-7.682-10.16l1.215-2.914c-1.364 3.271 2.075 7.823 7.682 10.161h0z" class="D"/><path d="M140.196 225.211c5.607 2.337 11.261 1.576 12.624-1.695s-2.075-7.822-7.682-10.16-11.26-1.577-12.624 1.694 2.075 7.823 7.682 10.161h0zm.623-1.494c4.19 1.747 8.421 1.182 9.442-1.266s-1.555-5.853-5.746-7.599-8.413-1.178-9.434 1.271 1.547 5.848 5.737 7.595l.001-.001z" class="B C"/><path d="M150.261 222.449c-1.021 2.449-5.252 3.013-9.442 1.266s-6.758-5.146-5.737-7.595 5.243-3.018 9.434-1.271 6.767 5.15 5.746 7.6h-.001z" class="D"/><path d="M145.528 218.948l2.374 1.535c.4.254.352.624-.074.622l-2.569-.019c-.165 0-.297.062-.331.164l-.609 1.579c-.107.257-.675.196-.973-.114l-1.781-1.815a.9.9 0 0 0-.475-.257l-2.751-.562c-.465-.097-.763-.503-.53-.688l1.445-1.133c.048-.037.079-.091.088-.151s-.006-.121-.041-.17l-1.096-1.919c-.183-.329.211-.507.65-.324l2.691 1.122c.157.071.334.09.503.054l2.074-.616c.187-.043.383-.017.553.072a.81.81 0 0 1 .374.412l.205 1.839c.018.077.052.149.099.213a.57.57 0 0 0 .176.155h0l-.002.001z" class="C"/><path d="M147.623 266.948c3.037-5.26 3.007-10.965-.062-12.737l2.734 1.579c3.069 1.772 3.098 7.476.061 12.737s-7.992 8.087-11.061 6.315l-2.734-1.579c3.069 1.772 8.025-1.054 11.062-6.315h0z" class="F"/><path d="M147.623 266.948c3.037-5.26 3.007-10.965-.062-12.737s-8.024 1.055-11.061 6.315-3.008 10.965.061 12.737 8.025-1.054 11.062-6.315zm-1.402-.809c2.27-3.932 2.252-8.2-.045-9.526s-6.004.791-8.274 4.723-2.247 8.192.051 9.519 5.998-.785 8.268-4.716h0z" class="B E"/><path d="M146.176 256.612c2.297 1.327 2.315 5.595.045 9.527s-5.971 6.042-8.268 4.716-2.321-5.587-.051-9.519 5.975-6.051 8.273-4.724h.001z" class="F"/><path d="M142.095 260.856l1.827-2.157c.303-.364.664-.269.607.153l-.349 2.546c-.021.163.023.302.121.349l1.488.806c.241.139.107.695-.237.951l-2.028 1.534c-.148.11-.258.263-.316.438l-.91 2.656c-.155.449-.597.692-.75.437l-.938-1.578c-.031-.052-.08-.091-.139-.107a.23.23 0 0 0-.174.02l-2.043.84c-.35.14-.475-.274-.238-.686l1.458-2.525a.81.81 0 0 0 .118-.492l-.345-2.136c-.019-.191.032-.381.142-.539a.81.81 0 0 1 .457-.318l1.85.034c.078-.009.154-.033.223-.071s.129-.091.176-.155h0z" class="E"/><use xlink:href="#B" class="F"/><path d="M124 306.844c6.075 0 11-2.879 11-6.423S130.075 294 124 294s-11 2.877-11 6.421 4.926 6.423 11 6.423zm0-1.619c4.54 0 8.228-2.15 8.228-4.803s-3.688-4.803-8.228-4.803-8.218 2.151-8.218 4.803 3.678 4.803 8.218 4.803z" class="B E"/><use xlink:href="#C" class="F"/><use xlink:href="#D" class="E"/><use xlink:href="#B" x="6" y="9" class="F"/><path d="M130 315.844c6.075 0 11-2.879 11-6.423S136.075 303 130 303s-11 2.877-11 6.421 4.926 6.423 11 6.423zm0-1.619c4.54 0 8.228-2.15 8.228-4.803s-3.688-4.803-8.228-4.803-8.218 2.151-8.218 4.803 3.678 4.803 8.218 4.803z" class="B E"/><use xlink:href="#C" x="6" y="9" class="F"/><use xlink:href="#D" x="6" y="9" class="E"/><use xlink:href="#B" x="29" y="12" class="F"/><path d="M153 318.844c6.075 0 11-2.879 11-6.423S159.075 306 153 306s-11 2.877-11 6.421 4.926 6.423 11 6.423zm0-1.619c4.54 0 8.228-2.15 8.228-4.803s-3.688-4.803-8.228-4.803-8.218 2.151-8.218 4.803 3.678 4.803 8.218 4.803z" class="B E"/><use xlink:href="#C" x="29" y="12" class="F"/><use xlink:href="#D" x="29" y="12" class="E"/><use xlink:href="#E" class="F"/><path d="M165 304.844c6.074 0 11-2.879 11-6.423S171.074 292 165 292s-11 2.877-11 6.421 4.926 6.423 11 6.423zm0-1.619c4.54 0 8.227-2.15 8.227-4.803s-3.687-4.803-8.227-4.803-8.218 2.151-8.218 4.803 3.678 4.803 8.218 4.803z" class="B E"/><use xlink:href="#F" class="F"/><path d="M167.512 297.01l2.781.504c.467.081.565.44.171.603l-2.378.97c-.152.064-.251.172-.242.28l.045 1.691c0 .278-.548.44-.942.27l-2.342-.99c-.17-.073-.357-.092-.538-.054l-2.755.539c-.466.09-.898-.17-.754-.431l.898-1.601c.03-.053.038-.115.023-.174a.23.23 0 0 0-.104-.141l-1.75-1.349c-.295-.233 0-.549.476-.549h2.915c.173.005.343-.045.485-.143l1.678-1.367a.8.8 0 0 1 .537-.147.81.81 0 0 1 .504.237l.897 1.619c.046.064.105.118.172.158a.56.56 0 0 0 .223.075h0z" class="E"/><use xlink:href="#E" x="-6" y="7" class="F"/><path d="M159 311.844c6.074 0 11-2.879 11-6.423S165.074 299 159 299s-11 2.877-11 6.421 4.926 6.423 11 6.423zm0-1.619c4.54 0 8.227-2.15 8.227-4.803s-3.687-4.803-8.227-4.803-8.218 2.151-8.218 4.803 3.678 4.803 8.218 4.803z" class="B E"/><use xlink:href="#F" x="-6" y="7" class="F"/><path d="M161.512 304.01l2.781.504c.467.081.565.44.171.603l-2.378.97c-.152.064-.251.172-.242.28l.045 1.691c0 .278-.548.44-.942.27l-2.342-.99c-.17-.073-.357-.092-.538-.054l-2.755.539c-.466.09-.898-.17-.754-.431l.898-1.601c.03-.053.038-.115.023-.174s-.052-.11-.103-.141l-1.75-1.349c-.296-.233 0-.549.476-.549h2.915c.173.005.343-.045.485-.143l1.678-1.367a.8.8 0 0 1 .537-.147.81.81 0 0 1 .504.237l.897 1.619c.046.064.105.118.172.158a.56.56 0 0 0 .223.075h-.001z" class="E"/><path d="M189.764 174.008c0 14.364-19.951 26.008-44.562 26.008-24.343 0-44.127-11.392-44.555-25.54v6.928.356c0 14.38 19.951 26.022 44.562 26.022s44.562-11.641 44.562-26.022v-.356-7.581h-.008l.001.185z" fill="#2f2be1" class="B"/><path d="M144.5 194c19.054 0 34.5-8.954 34.5-20s-15.446-20-34.5-20-34.5 8.954-34.5 20 15.446 20 34.5 20z" fill="#232277"/><path d="M189.764 174.008c0 14.364-19.951 26.008-44.562 26.008s-44.562-11.644-44.562-26.008S120.591 148 145.202 148s44.562 11.644 44.562 26.008zM179 174c0 11.046-15.446 20-34.5 20s-34.5-8.954-34.5-20 15.446-20 34.5-20 34.5 8.954 34.5 20z" fill="#504df7" class="B"/><path d="M155.683 172.788l-12.188 3.486c-1.635.467-3.657-.207-3.774-1.258l-.864-7.836c-.103-.91.257-1.804 1.034-2.582l.602-.601c.55-.55 1.813-.725 2.816-.39l15.507 5.168c1.007.336 1.373 1.053.823 1.604l-.601.601c-.778.777-1.939 1.404-3.355 1.808z" fill="#7b78ff"/><path d="M133.955 172.081l12.187-3.485c1.635-.467 3.657.207 3.774 1.258l.865 7.835c.103.91-.258 1.805-1.036 2.583l-.601.601c-.55.55-1.813.725-2.817.39l-15.507-5.168c-1.006-.336-1.373-1.054-.823-1.604l.602-.601c.777-.777 1.939-1.404 3.356-1.809z" fill="#9fd2eb"/><path d="M149.915 169.853c-.116-1.051-2.138-1.725-3.773-1.258l-6.91 1.977.492 4.444c.117 1.051 2.139 1.725 3.774 1.258l6.91-1.977-.493-4.444z" fill="#11429f"/><defs><filter id="filter0_f" x="-32" y="200" width="355" height="239" filterUnits="userSpaceOnUse" color-interpolation-filters="sRGB"><feFlood flood-opacity="0" result="BackgroundImageFix"/><feBlend mode="normal" in="SourceGraphic" in2="BackgroundImageFix" result="shape"/><feGaussianBlur stdDeviation="35" result="effect1_foregroundBlur"/></filter><linearGradient id="background" x1="273.47" y1="-13.2813" x2="415.619" y2="339.655" gradientUnits="userSpaceOnUse"><stop stop-color="#0B0B16"/><stop offset="1" class="G"/></linearGradient><linearGradient id="divider" x1="1.47345e-06" y1="409" x2="298.995" y2="410.864" gradientUnits="userSpaceOnUse"><stop class="I"/><stop offset="0.5" class="J"/><stop offset="1" class="I"/></linearGradient><clipPath id="mainclip"><rect width="290" height="500" rx="20" fill="white"/></clipPath><path id="text-path-a" d="M40 10 h228 a12,12 0 0 1 12 12 v364 a12,12 0 0 1 -12 12 h-246 a12 12 0 0 1 -12 -12 v-364 a12 12 0 0 1 12 -12 z" /><path id="B" d="M124 306.844c6.075 0 11-2.879 11-6.423v3.158c0 3.544-4.925 6.421-11 6.421s-11-2.877-11-6.421v-3.158c0 3.544 4.926 6.423 11 6.423z"/><path id="C" d="M132.227 300.422c0 2.653-3.688 4.803-8.228 4.803s-8.218-2.15-8.218-4.803 3.678-4.803 8.218-4.803 8.228 2.15 8.228 4.803z"/><path id="D" d="M126.512 299.01l2.782.504c.466.081.565.44.171.603l-2.379.97c-.152.064-.25.172-.242.28l.046 1.691c0 .278-.548.44-.942.27l-2.342-.99c-.169-.073-.357-.092-.538-.054l-2.755.539c-.466.09-.898-.17-.754-.431l.898-1.601c.03-.053.038-.115.023-.174s-.052-.11-.103-.141l-1.75-1.349c-.296-.233 0-.549.476-.549h2.915c.173.005.342-.045.485-.143l1.677-1.367a.8.8 0 0 1 .538-.147.81.81 0 0 1 .504.237l.897 1.619a.57.57 0 0 0 .395.233h-.002z"/><path id="E" d="M165 304.844c6.074 0 11-2.879 11-6.423v3.158c0 3.544-4.926 6.421-11 6.421s-11-2.877-11-6.421v-3.158c0 3.544 4.926 6.423 11 6.423z"/><path id="F" d="M173.227 298.422c0 2.653-3.687 4.803-8.227 4.803s-8.218-2.15-8.218-4.803 3.678-4.803 8.218-4.803 8.227 2.15 8.227 4.803z"/></defs></svg>'));

        return svg;        
    }
}
library DateTime {

    uint constant SECONDS_PER_DAY = 24 * 60 * 60;
    uint constant SECONDS_PER_HOUR = 60 * 60;
    uint constant SECONDS_PER_MINUTE = 60;
    int constant OFFSET19700101 = 2440588;

    uint constant DOW_MON = 1;
    uint constant DOW_TUE = 2;
    uint constant DOW_WED = 3;
    uint constant DOW_THU = 4;
    uint constant DOW_FRI = 5;
    uint constant DOW_SAT = 6;
    uint constant DOW_SUN = 7;

    // ------------------------------------------------------------------------
    // Calculate the number of days from 1970/01/01 to year/month/day using
    // the date conversion algorithm from
    //   http://aa.usno.navy.mil/faq/docs/JD_Formula.php
    // and subtracting the offset 2440588 so that 1970/01/01 is day 0
    //
    // days = day
    //      - 32075
    //      + 1461 * (year + 4800 + (month - 14) / 12) / 4
    //      + 367 * (month - 2 - (month - 14) / 12 * 12) / 12
    //      - 3 * ((year + 4900 + (month - 14) / 12) / 100) / 4
    //      - offset
    // ------------------------------------------------------------------------
    function _daysFromDate(uint year, uint month, uint day) internal pure returns (uint _days) {
        require(year >= 1970);
        int _year = int(year);
        int _month = int(month);
        int _day = int(day);

        int __days = _day
          - 32075
          + 1461 * (_year + 4800 + (_month - 14) / 12) / 4
          + 367 * (_month - 2 - (_month - 14) / 12 * 12) / 12
          - 3 * ((_year + 4900 + (_month - 14) / 12) / 100) / 4
          - OFFSET19700101;

        _days = uint(__days);
    }

    // ------------------------------------------------------------------------
    // Calculate year/month/day from the number of days since 1970/01/01 using
    // the date conversion algorithm from
    //   http://aa.usno.navy.mil/faq/docs/JD_Formula.php
    // and adding the offset 2440588 so that 1970/01/01 is day 0
    //
    // int L = days + 68569 + offset
    // int N = 4 * L / 146097
    // L = L - (146097 * N + 3) / 4
    // year = 4000 * (L + 1) / 1461001
    // L = L - 1461 * year / 4 + 31
    // month = 80 * L / 2447
    // dd = L - 2447 * month / 80
    // L = month / 11
    // month = month + 2 - 12 * L
    // year = 100 * (N - 49) + year + L
    // ------------------------------------------------------------------------
    function _daysToDate(uint _days) internal pure returns (uint year, uint month, uint day) {
        int __days = int(_days);

        int L = __days + 68569 + OFFSET19700101;
        int N = 4 * L / 146097;
        L = L - (146097 * N + 3) / 4;
        int _year = 4000 * (L + 1) / 1461001;
        L = L - 1461 * _year / 4 + 31;
        int _month = 80 * L / 2447;
        int _day = L - 2447 * _month / 80;
        L = _month / 11;
        _month = _month + 2 - 12 * L;
        _year = 100 * (N - 49) + _year + L;

        year = uint(_year);
        month = uint(_month);
        day = uint(_day);
    }

    function timestampFromDate(uint year, uint month, uint day) internal pure returns (uint timestamp) {
        timestamp = _daysFromDate(year, month, day) * SECONDS_PER_DAY;
    }
    function timestampFromDateTime(uint year, uint month, uint day, uint hour, uint minute, uint second) internal pure returns (uint timestamp) {
        timestamp = _daysFromDate(year, month, day) * SECONDS_PER_DAY + hour * SECONDS_PER_HOUR + minute * SECONDS_PER_MINUTE + second;
    }
    function timestampToDate(uint timestamp) internal pure returns (uint year, uint month, uint day) {
        (year, month, day) = _daysToDate(timestamp / SECONDS_PER_DAY);
    }
    function timestampToDateTime(uint timestamp) internal pure returns (uint year, uint month, uint day, uint hour, uint minute, uint second) {
        (year, month, day) = _daysToDate(timestamp / SECONDS_PER_DAY);
        uint secs = timestamp % SECONDS_PER_DAY;
        hour = secs / SECONDS_PER_HOUR;
        secs = secs % SECONDS_PER_HOUR;
        minute = secs / SECONDS_PER_MINUTE;
        second = secs % SECONDS_PER_MINUTE;
    }

    function isValidDate(uint year, uint month, uint day) internal pure returns (bool valid) {
        if (year >= 1970 && month > 0 && month <= 12) {
            uint daysInMonth = _getDaysInMonth(year, month);
            if (day > 0 && day <= daysInMonth) {
                valid = true;
            }
        }
    }
    function isValidDateTime(uint year, uint month, uint day, uint hour, uint minute, uint second) internal pure returns (bool valid) {
        if (isValidDate(year, month, day)) {
            if (hour < 24 && minute < 60 && second < 60) {
                valid = true;
            }
        }
    }
    function isLeapYear(uint timestamp) internal pure returns (bool leapYear) {
        (uint year,,) = _daysToDate(timestamp / SECONDS_PER_DAY);
        leapYear = _isLeapYear(year);
    }
    function _isLeapYear(uint year) internal pure returns (bool leapYear) {
        leapYear = ((year % 4 == 0) && (year % 100 != 0)) || (year % 400 == 0);
    }
    function isWeekDay(uint timestamp) internal pure returns (bool weekDay) {
        weekDay = getDayOfWeek(timestamp) <= DOW_FRI;
    }
    function isWeekEnd(uint timestamp) internal pure returns (bool weekEnd) {
        weekEnd = getDayOfWeek(timestamp) >= DOW_SAT;
    }
    function getDaysInMonth(uint timestamp) internal pure returns (uint daysInMonth) {
        (uint year, uint month,) = _daysToDate(timestamp / SECONDS_PER_DAY);
        daysInMonth = _getDaysInMonth(year, month);
    }
    function _getDaysInMonth(uint year, uint month) internal pure returns (uint daysInMonth) {
        if (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12) {
            daysInMonth = 31;
        } else if (month != 2) {
            daysInMonth = 30;
        } else {
            daysInMonth = _isLeapYear(year) ? 29 : 28;
        }
    }
    // 1 = Monday, 7 = Sunday
    function getDayOfWeek(uint timestamp) internal pure returns (uint dayOfWeek) {
        uint _days = timestamp / SECONDS_PER_DAY;
        dayOfWeek = (_days + 3) % 7 + 1;
    }

    function getYear(uint timestamp) internal pure returns (uint year) {
        (year,,) = _daysToDate(timestamp / SECONDS_PER_DAY);
    }
    function getMonth(uint timestamp) internal pure returns (uint month) {
        (,month,) = _daysToDate(timestamp / SECONDS_PER_DAY);
    }
    function getDay(uint timestamp) internal pure returns (uint day) {
        (,,day) = _daysToDate(timestamp / SECONDS_PER_DAY);
    }
    function getHour(uint timestamp) internal pure returns (uint hour) {
        uint secs = timestamp % SECONDS_PER_DAY;
        hour = secs / SECONDS_PER_HOUR;
    }
    function getMinute(uint timestamp) internal pure returns (uint minute) {
        uint secs = timestamp % SECONDS_PER_HOUR;
        minute = secs / SECONDS_PER_MINUTE;
    }
    function getSecond(uint timestamp) internal pure returns (uint second) {
        second = timestamp % SECONDS_PER_MINUTE;
    }

    function addYears(uint timestamp, uint _years) internal pure returns (uint newTimestamp) {
        (uint year, uint month, uint day) = _daysToDate(timestamp / SECONDS_PER_DAY);
        year += _years;
        uint daysInMonth = _getDaysInMonth(year, month);
        if (day > daysInMonth) {
            day = daysInMonth;
        }
        newTimestamp = _daysFromDate(year, month, day) * SECONDS_PER_DAY + timestamp % SECONDS_PER_DAY;
        require(newTimestamp >= timestamp);
    }
    function addMonths(uint timestamp, uint _months) internal pure returns (uint newTimestamp) {
        (uint year, uint month, uint day) = _daysToDate(timestamp / SECONDS_PER_DAY);
        month += _months;
        year += (month - 1) / 12;
        month = (month - 1) % 12 + 1;
        uint daysInMonth = _getDaysInMonth(year, month);
        if (day > daysInMonth) {
            day = daysInMonth;
        }
        newTimestamp = _daysFromDate(year, month, day) * SECONDS_PER_DAY + timestamp % SECONDS_PER_DAY;
        require(newTimestamp >= timestamp);
    }
    function addDays(uint timestamp, uint _days) internal pure returns (uint newTimestamp) {
        newTimestamp = timestamp + _days * SECONDS_PER_DAY;
        require(newTimestamp >= timestamp);
    }
    function addHours(uint timestamp, uint _hours) internal pure returns (uint newTimestamp) {
        newTimestamp = timestamp + _hours * SECONDS_PER_HOUR;
        require(newTimestamp >= timestamp);
    }
    function addMinutes(uint timestamp, uint _minutes) internal pure returns (uint newTimestamp) {
        newTimestamp = timestamp + _minutes * SECONDS_PER_MINUTE;
        require(newTimestamp >= timestamp);
    }
    function addSeconds(uint timestamp, uint _seconds) internal pure returns (uint newTimestamp) {
        newTimestamp = timestamp + _seconds;
        require(newTimestamp >= timestamp);
    }

    function subYears(uint timestamp, uint _years) internal pure returns (uint newTimestamp) {
        (uint year, uint month, uint day) = _daysToDate(timestamp / SECONDS_PER_DAY);
        year -= _years;
        uint daysInMonth = _getDaysInMonth(year, month);
        if (day > daysInMonth) {
            day = daysInMonth;
        }
        newTimestamp = _daysFromDate(year, month, day) * SECONDS_PER_DAY + timestamp % SECONDS_PER_DAY;
        require(newTimestamp <= timestamp);
    }
    function subMonths(uint timestamp, uint _months) internal pure returns (uint newTimestamp) {
        (uint year, uint month, uint day) = _daysToDate(timestamp / SECONDS_PER_DAY);
        uint yearMonth = year * 12 + (month - 1) - _months;
        year = yearMonth / 12;
        month = yearMonth % 12 + 1;
        uint daysInMonth = _getDaysInMonth(year, month);
        if (day > daysInMonth) {
            day = daysInMonth;
        }
        newTimestamp = _daysFromDate(year, month, day) * SECONDS_PER_DAY + timestamp % SECONDS_PER_DAY;
        require(newTimestamp <= timestamp);
    }
    function subDays(uint timestamp, uint _days) internal pure returns (uint newTimestamp) {
        newTimestamp = timestamp - _days * SECONDS_PER_DAY;
        require(newTimestamp <= timestamp);
    }
    function subHours(uint timestamp, uint _hours) internal pure returns (uint newTimestamp) {
        newTimestamp = timestamp - _hours * SECONDS_PER_HOUR;
        require(newTimestamp <= timestamp);
    }
    function subMinutes(uint timestamp, uint _minutes) internal pure returns (uint newTimestamp) {
        newTimestamp = timestamp - _minutes * SECONDS_PER_MINUTE;
        require(newTimestamp <= timestamp);
    }
    function subSeconds(uint timestamp, uint _seconds) internal pure returns (uint newTimestamp) {
        newTimestamp = timestamp - _seconds;
        require(newTimestamp <= timestamp);
    }

    function diffYears(uint fromTimestamp, uint toTimestamp) internal pure returns (uint _years) {
        require(fromTimestamp <= toTimestamp);
        (uint fromYear,,) = _daysToDate(fromTimestamp / SECONDS_PER_DAY);
        (uint toYear,,) = _daysToDate(toTimestamp / SECONDS_PER_DAY);
        _years = toYear - fromYear;
    }
    function diffMonths(uint fromTimestamp, uint toTimestamp) internal pure returns (uint _months) {
        require(fromTimestamp <= toTimestamp);
        (uint fromYear, uint fromMonth,) = _daysToDate(fromTimestamp / SECONDS_PER_DAY);
        (uint toYear, uint toMonth,) = _daysToDate(toTimestamp / SECONDS_PER_DAY);
        _months = toYear * 12 + toMonth - fromYear * 12 - fromMonth;
    }
    function diffDays(uint fromTimestamp, uint toTimestamp) internal pure returns (uint _days) {
        require(fromTimestamp <= toTimestamp);
        _days = (toTimestamp - fromTimestamp) / SECONDS_PER_DAY;
    }
    function diffHours(uint fromTimestamp, uint toTimestamp) internal pure returns (uint _hours) {
        require(fromTimestamp <= toTimestamp);
        _hours = (toTimestamp - fromTimestamp) / SECONDS_PER_HOUR;
    }
    function diffMinutes(uint fromTimestamp, uint toTimestamp) internal pure returns (uint _minutes) {
        require(fromTimestamp <= toTimestamp);
        _minutes = (toTimestamp - fromTimestamp) / SECONDS_PER_MINUTE;
    }
    function diffSeconds(uint fromTimestamp, uint toTimestamp) internal pure returns (uint _seconds) {
        require(fromTimestamp <= toTimestamp);
        _seconds = toTimestamp - fromTimestamp;
    }
}
library Base64 {
    string internal constant TABLE = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';

    function encode(bytes memory data) internal pure returns (string memory) {
        if (data.length == 0) return '';
        
        // load the table into memory
        string memory table = TABLE;

        // multiply by 4/3 rounded up
        uint256 encodedLen = 4 * ((data.length + 2) / 3);

        // add some extra buffer at the end required for the writing
        string memory result = new string(encodedLen + 32);

        assembly {
            // set the actual output length
            mstore(result, encodedLen)
            
            // prepare the lookup table
            let tablePtr := add(table, 1)
            
            // input ptr
            let dataPtr := data
            let endPtr := add(dataPtr, mload(data))
            
            // result ptr, jump over length
            let resultPtr := add(result, 32)
            
            // run over the input, 3 bytes at a time
            for {} lt(dataPtr, endPtr) {}
            {
               dataPtr := add(dataPtr, 3)
               
               // read 3 bytes
               let input := mload(dataPtr)
               
               // write 4 characters
               mstore(resultPtr, shl(248, mload(add(tablePtr, and(shr(18, input), 0x3F)))))
               resultPtr := add(resultPtr, 1)
               mstore(resultPtr, shl(248, mload(add(tablePtr, and(shr(12, input), 0x3F)))))
               resultPtr := add(resultPtr, 1)
               mstore(resultPtr, shl(248, mload(add(tablePtr, and(shr( 6, input), 0x3F)))))
               resultPtr := add(resultPtr, 1)
               mstore(resultPtr, shl(248, mload(add(tablePtr, and(        input,  0x3F)))))
               resultPtr := add(resultPtr, 1)
            }
            
            // padding with '='
            switch mod(mload(data), 3)
            case 1 { mstore(sub(resultPtr, 2), shl(240, 0x3d3d)) }
            case 2 { mstore(sub(resultPtr, 1), shl(248, 0x3d)) }
        }
        
        return result;
    }
}


library FullMath {
    function mul512(uint256 a, uint256 b) internal pure returns (uint256 prod0, uint256 prod1) {
        // 512-bit multiply [prod1 prod0] = a * b
        // Compute the product mod 2**256 and mod 2**256 - 1
        // then use the Chinese Remainder Theorem to reconstruct
        // the 512 bit result. The result is stored in two 256
        // variables such that product = prod1 * 2**256 + prod0
        assembly {
            let mm := mulmod(a, b, not(0))
            prod0 := mul(a, b)
            prod1 := sub(sub(mm, prod0), lt(mm, prod0))
        }
    }
    
    /// @notice Calculates floor(a×b÷denominator) with full precision. Throws if result overflows a uint256 or denominator == 0
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @return result The 256-bit result
    /// @dev Credit to Remco Bloemen under MIT license https://xn--2-umb.com/21/muldiv
    function mulDiv(
        uint256 a,
        uint256 b,
        uint256 denominator
    ) internal pure returns (uint256 result) {
        unchecked {
            (uint256 prod0, uint256 prod1) = mul512(a, b);

            // Handle non-overflow cases, 256 by 256 division
            if (prod1 == 0) {
                require(denominator > 0);
                assembly {
                    result := div(prod0, denominator)
                }
                return result;
            }

            // Make sure the result is less than 2**256.
            // Also prevents denominator == 0
            require(denominator > prod1);

            ///////////////////////////////////////////////
            // 512 by 256 division.
            ///////////////////////////////////////////////

            // Make division exact by subtracting the remainder from [prod1 prod0]
            // Compute remainder using mulmod
            uint256 remainder;
            assembly {
                remainder := mulmod(a, b, denominator)
            }
            // Subtract 256 bit number from 512 bit number
            assembly {
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }

            // Factor powers of two out of denominator
            // Compute largest power of two divisor of denominator.
            // Always >= 1.
            uint256 twos;
            twos = (0 - denominator) & denominator;
            // Divide denominator by power of two
            assembly {
                denominator := div(denominator, twos)
            }

            // Divide [prod1 prod0] by the factors of two
            assembly {
                prod0 := div(prod0, twos)
            }
            // Shift in bits from prod1 into prod0. For this we need
            // to flip `twos` such that it is 2**256 / twos.
            // If twos is zero, then it becomes one
            assembly {
                twos := add(div(sub(0, twos), twos), 1)
            }
            prod0 |= prod1 * twos;    

            // Invert denominator mod 2**256
            // Now that denominator is an odd number, it has an inverse
            // modulo 2**256 such that denominator * inv = 1 mod 2**256.
            // Compute the inverse by starting with a seed that is correct
            // correct for four bits. That is, denominator * inv = 1 mod 2**4
            uint256 inv;
            inv = (3 * denominator) ^ 2;

            // Now use Newton-Raphson iteration to improve the precision.
            // Thanks to Hensel's lifting lemma, this also works in modular
            // arithmetic, doubling the correct bits in each step.
            inv *= 2 - denominator * inv; // inverse mod 2**8
            inv *= 2 - denominator * inv; // inverse mod 2**16
            inv *= 2 - denominator * inv; // inverse mod 2**32
            inv *= 2 - denominator * inv; // inverse mod 2**64
            inv *= 2 - denominator * inv; // inverse mod 2**128
            inv *= 2 - denominator * inv; // inverse mod 2**256

            // Because the division is now exact we can divide by multiplying
            // with the modular inverse of denominator. This will give us the
            // correct result modulo 2**256. Since the precoditions guarantee
            // that the outcome is less than 2**256, this is the final result.
            // We don't need to compute the high bits of the result and prod1
            // is no longer required.
            result = prod0 * inv;

            return result;
        }
    }

    /// @notice Calculates ceil(a×b÷denominator) with full precision. Throws if result overflows a uint256 or denominator == 0
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @return result The 256-bit result
    function mulDivUp(
        uint256 a,
        uint256 b,
        uint256 denominator
    ) internal pure returns (uint256 result) {
        result = mulDiv(a, b, denominator);
        if (mulmod(a, b, denominator) > 0) result++;
    }
}

interface ITimeswapPayCallback {
    /// @notice Called to `msg.sender` after initiating a pay from ITimeswapPair#pay.
    /// @dev In the implementation you must pay the asset token owed for the pay transaction.
    /// The caller of this method must be checked to be a TimeswapPair deployed by the canonical TimeswapFactory.
    /// @param assetIn The amount of asset tokens owed due to the pool for the pay transaction
    /// @param data Any data passed through by the caller via the ITimeswapPair#pay call
    function timeswapPayCallback(
        uint128 assetIn,
        bytes calldata data
    ) external;
}
contract WETH9 {
    string public name     = "Wrapped Ether";
    string public symbol   = "WETH";
    uint8  public decimals = 18;

    event  Approval(address indexed src, address indexed guy, uint wad);
    event  Transfer(address indexed src, address indexed dst, uint wad);
    event  Deposit(address indexed dst, uint wad);
    event  Withdrawal(address indexed src, uint wad);

    mapping (address => uint)                       public  balanceOf;
    mapping (address => mapping (address => uint))  public  allowance;

    receive() external payable {
        deposit();
    }
    fallback() external payable {
        deposit();
    }
    function deposit() public payable {
        balanceOf[msg.sender] += msg.value;
        emit Deposit(msg.sender, msg.value);
    }
    function withdraw(uint wad) public {
        require(balanceOf[msg.sender] >= wad);
        balanceOf[msg.sender] -= wad;
        payable(msg.sender).transfer(wad);
        emit Withdrawal(msg.sender, wad);
    }

    function totalSupply() public view returns (uint) {
        return address(this).balance;
    }

    function approve(address guy, uint wad) public returns (bool) {
        allowance[msg.sender][guy] = wad;
        emit Approval(msg.sender, guy, wad);
        return true;
    }

    function transfer(address dst, uint wad) public returns (bool) {
        return transferFrom(msg.sender, dst, wad);
    }

    function transferFrom(address src, address dst, uint wad)
        public
        returns (bool)
    {
        require(balanceOf[src] >= wad);

        if (src != msg.sender && allowance[src][msg.sender] != type(uint256).max) {
            require(allowance[src][msg.sender] >= wad);
            allowance[src][msg.sender] -= wad;
        }

        balanceOf[src] -= wad;
        balanceOf[dst] += wad;

        emit Transfer(src, dst, wad);

        return true;
    }
}
contract MaticTestToken {
    // MODEL

    string public constant name = 'Matic TEST TOKEN';
    string public constant symbol = 'MATIC';
    uint8 public immutable decimals = 18;

    address private constant ZERO = address(type(uint160).min);

    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    // EVENT

    event Approval(address indexed _owner, address indexed _spender, uint256 _value);

    event Transfer(address indexed _from, address indexed _to, uint256 _value);

    // UPDATE

    function approve(address _spender, uint256 _value) external returns (bool) {
        _approve(msg.sender, _spender, _value);
        return true;
    }

    function transfer(address _to, uint256 _value) external returns (bool) {
        _transfer(msg.sender, _to, _value);
        return true;
    }

    function transferFrom(
        address _from,
        address _to,
        uint256 _value
    ) external returns (bool) {
        if (msg.sender != _from && allowance[_from][msg.sender] != type(uint256).max) {
            allowance[_from][msg.sender] -= _value;

            emit Approval(_from, msg.sender, allowance[_from][msg.sender]);
        }
        _transfer(_from, _to, _value);
        return true;
    }

    function mint(address _to, uint256 _value) external {
        totalSupply += _value;
        balanceOf[_to] += _value;
        emit Transfer(ZERO, _to, _value);
    }

    // HELPER

    function _approve(
        address _owner,
        address _spender,
        uint256 _value
    ) private {
        allowance[_owner][_spender] = _value;
        emit Approval(_owner, _spender, _value);
    }

    function _transfer(
        address _from,
        address _to,
        uint256 _value
    ) private {
        balanceOf[_from] -= _value;
        balanceOf[_to] += _value;
        emit Transfer(_from, _to, _value);
    }
}

contract DaiTestToken {
    // MODEL

    string public constant name = 'DAI TEST TOKEN';
    string public constant symbol = 'DAI';
    uint8 public immutable decimals = 18;

    address private constant ZERO = address(type(uint160).min);

    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    // EVENT

    event Approval(address indexed _owner, address indexed _spender, uint256 _value);

    event Transfer(address indexed _from, address indexed _to, uint256 _value);

    // UPDATE

    function approve(address _spender, uint256 _value) external returns (bool) {
        _approve(msg.sender, _spender, _value);
        return true;
    }

    function transfer(address _to, uint256 _value) external returns (bool) {
        _transfer(msg.sender, _to, _value);
        return true;
    }

    function transferFrom(
        address _from,
        address _to,
        uint256 _value
    ) external returns (bool) {
        if (msg.sender != _from && allowance[_from][msg.sender] != type(uint256).max) {
            allowance[_from][msg.sender] -= _value;

            emit Approval(_from, msg.sender, allowance[_from][msg.sender]);
        }
        _transfer(_from, _to, _value);
        return true;
    }

    function mint(address _to, uint256 _value) external {
        totalSupply += _value;
        balanceOf[_to] += _value;
        emit Transfer(ZERO, _to, _value);
    }

    // HELPER

    function _approve(
        address _owner,
        address _spender,
        uint256 _value
    ) private {
        allowance[_owner][_spender] = _value;
        emit Approval(_owner, _spender, _value);
    }

    function _transfer(
        address _from,
        address _to,
        uint256 _value
    ) private {
        balanceOf[_from] -= _value;
        balanceOf[_to] += _value;
        emit Transfer(_from, _to, _value);
    }
}



interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}


interface IDeployNative {
    struct Deploy {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        uint256 deadline;
    }
}

interface ILend {
    struct LendGivenBond {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address bondTo;
        address insuranceTo;
        uint112 assetIn;
        uint128 bondOut;
        uint128 minInsurance;
        uint256 deadline;
    }

    struct LendGivenBondETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address bondTo;
        address insuranceTo;
        uint128 bondOut;
        uint128 minInsurance;
        uint256 deadline;
    }

    struct LendGivenBondETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address bondTo;
        address insuranceTo;
        uint112 assetIn;
        uint128 bondOut;
        uint128 minInsurance;
        uint256 deadline;
    }

    struct _LendGivenBond {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address from;
        address bondTo;
        address insuranceTo;
        uint112 assetIn;
        uint128 bondOut;
        uint128 minInsurance;
        uint256 deadline;
    }

    struct LendGivenInsurance {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address bondTo;
        address insuranceTo;
        uint112 assetIn;
        uint128 insuranceOut;
        uint128 minBond;
        uint256 deadline;
    }

    struct LendGivenInsuranceETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address bondTo;
        address insuranceTo;
        uint128 insuranceOut;
        uint128 minBond;
        uint256 deadline;
    }

    struct LendGivenInsuranceETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address bondTo;
        address insuranceTo;
        uint112 assetIn;
        uint128 insuranceOut;
        uint128 minBond;
        uint256 deadline;
    }

    struct _LendGivenInsurance {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address from;
        address bondTo;
        address insuranceTo;
        uint112 assetIn;
        uint128 insuranceOut;
        uint128 minBond;
        uint256 deadline;
    }

    struct LendGivenPercent {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address bondTo;
        address insuranceTo;
        uint112 assetIn;
        uint40 percent;
        uint128 minBond;
        uint128 minInsurance;
        uint256 deadline;
    }

    struct LendGivenPercentETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address bondTo;
        address insuranceTo;
        uint40 percent;
        uint128 minBond;
        uint128 minInsurance;
        uint256 deadline;
    }

    struct LendGivenPercentETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address bondTo;
        address insuranceTo;
        uint112 assetIn;
        uint40 percent;
        uint128 minBond;
        uint128 minInsurance;
        uint256 deadline;
    }

    struct _LendGivenPercent {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address from;
        address bondTo;
        address insuranceTo;
        uint112 assetIn;
        uint40 percent;
        uint128 minBond;
        uint128 minInsurance;
        uint256 deadline;
    }

    struct _Lend {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address from;
        address bondTo;
        address insuranceTo;
        uint112 xIncrease;
        uint112 yDecrease;
        uint112 zDecrease;
        uint256 deadline;
    }
}

interface IPay {
    struct Repay {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address collateralTo;
        uint256[] ids;
        uint112[] maxAssetsIn;
        uint256 deadline;
    }

    struct RepayETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address collateralTo;
        uint256[] ids;
        uint112[] maxAssetsIn;
        uint256 deadline;
    }

    struct RepayETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address payable collateralTo;
        uint256[] ids;
        uint112[] maxAssetsIn;
        uint256 deadline;
    }

    struct _Repay {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address from;
        address collateralTo;
        uint256[] ids;
        uint112[] maxAssetsIn;
        uint256 deadline;
    }
}

interface IMint {
    struct NewLiquidity {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint112 assetIn;
        uint112 debtIn;
        uint112 collateralIn;
        uint256 deadline;
    }

    struct NewLiquidityETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint112 debtIn;
        uint112 collateralIn;
        uint256 deadline;
    }

    struct NewLiquidityETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint112 assetIn;
        uint112 debtIn;
        uint256 deadline;
    }

    struct _NewLiquidity {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address assetFrom;
        address collateralFrom;
        address liquidityTo;
        address dueTo;
        uint112 assetIn;
        uint112 debtIn;
        uint112 collateralIn;
        uint256 deadline;
    }

    struct LiquidityGivenAsset {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint112 assetIn;
        uint256 minLiquidity;
        uint112 maxDebt;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct LiquidityGivenAssetETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint256 minLiquidity;
        uint112 maxDebt;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct LiquidityGivenAssetETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint112 assetIn;
        uint256 minLiquidity;
        uint112 maxDebt;
        uint256 deadline;
    }

    struct _LiquidityGivenAsset {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address assetFrom;
        address collateralFrom;
        address liquidityTo;
        address dueTo;
        uint112 assetIn;
        uint256 minLiquidity;
        uint112 maxDebt;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct LiquidityGivenDebt {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint112 debtIn;
        uint256 minLiquidity;
        uint112 maxAsset;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct LiquidityGivenDebtETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint112 debtIn;
        uint256 minLiquidity;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct LiquidityGivenDebtETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint112 debtIn;
        uint256 minLiquidity;
        uint112 maxAsset;
        uint256 deadline;
    }

    struct _LiquidityGivenDebt {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address assetFrom;
        address collateralFrom;
        address liquidityTo;
        address dueTo;
        uint112 debtIn;
        uint256 minLiquidity;
        uint112 maxAsset;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct LiquidityGivenCollateral {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint112 collateralIn;
        uint256 minLiquidity;
        uint112 maxAsset;
        uint112 maxDebt;
        uint256 deadline;
    }

    struct LiquidityGivenCollateralETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint112 collateralIn;
        uint256 minLiquidity;
        uint112 maxDebt;
        uint256 deadline;
    }

    struct LiquidityGivenCollateralETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address liquidityTo;
        address dueTo;
        uint256 minLiquidity;
        uint112 maxAsset;
        uint112 maxDebt;
        uint256 deadline;
    }

    struct _LiquidityGivenCollateral {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address assetFrom;
        address collateralFrom;
        address liquidityTo;
        address dueTo;
        uint112 collateralIn;
        uint256 minLiquidity;
        uint112 maxAsset;
        uint112 maxDebt;
        uint256 deadline;
    }

    struct _Mint {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address assetFrom;
        address collateralFrom;
        address liquidityTo;
        address dueTo;
        uint112 xIncrease;
        uint112 yIncrease;
        uint112 zIncrease;
        uint256 deadline;
    }
}

interface IBorrow {
    struct BorrowGivenDebt {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address assetTo;
        address dueTo;
        uint112 assetOut;
        uint112 debtIn;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct BorrowGivenDebtETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address payable assetTo;
        address dueTo;
        uint112 assetOut;
        uint112 debtIn;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct BorrowGivenDebtETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address assetTo;
        address dueTo;
        uint112 assetOut;
        uint112 debtIn;
        uint256 deadline;
    }

    struct _BorrowGivenDebt {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address from;
        address assetTo;
        address dueTo;
        uint112 assetOut;
        uint112 debtIn;
        uint112 maxCollateral;
        uint256 deadline;
    }
    struct BorrowGivenCollateral {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address assetTo;
        address dueTo;
        uint112 assetOut;
        uint112 collateralIn;
        uint112 maxDebt;
        uint256 deadline;
    }

    struct BorrowGivenCollateralETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address payable assetTo;
        address dueTo;
        uint112 assetOut;
        uint112 collateralIn;
        uint112 maxDebt;
        uint256 deadline;
    }

    struct BorrowGivenCollateralETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address assetTo;
        address dueTo;
        uint112 assetOut;
        uint112 maxDebt;
        uint256 deadline;
    }

    struct _BorrowGivenCollateral {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address from;
        address assetTo;
        address dueTo;
        uint112 assetOut;
        uint112 collateralIn;
        uint112 maxDebt;
        uint256 deadline;
    }

    struct BorrowGivenPercent {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address assetTo;
        address dueTo;
        uint112 assetOut;
        uint40 percent;
        uint112 maxDebt;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct BorrowGivenPercentETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address payable assetTo;
        address dueTo;
        uint112 assetOut;
        uint40 percent;
        uint112 maxDebt;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct BorrowGivenPercentETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address assetTo;
        address dueTo;
        uint112 assetOut;
        uint40 percent;
        uint112 maxDebt;
        uint256 deadline;
    }

    struct _BorrowGivenPercent {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address from;
        address assetTo;
        address dueTo;
        uint112 assetOut;
        uint40 percent;
        uint112 maxDebt;
        uint112 maxCollateral;
        uint256 deadline;
    }

    struct _Borrow {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address from;
        address assetTo;
        address dueTo;
        uint112 xDecrease;
        uint112 yIncrease;
        uint112 zIncrease;
        uint256 deadline;
    }
}

interface IBurn {
    struct RemoveLiquidity {
        IERC20 asset;
        IERC20 collateral;
        uint256 maturity;
        address assetTo;
        address collateralTo;
        uint256 liquidityIn;
    }

    struct RemoveLiquidityETHAsset {
        IERC20 collateral;
        uint256 maturity;
        address payable assetTo;
        address collateralTo;
        uint256 liquidityIn;
    }

    struct RemoveLiquidityETHCollateral {
        IERC20 asset;
        uint256 maturity;
        address assetTo;
        address payable collateralTo;
        uint256 liquidityIn;
    }
}

interface IWETH is IERC20 {
    /* ===== UPDATE ===== */

    function deposit() external payable;

    function withdraw(uint256 amount) external;
}

contract MathTest {
    function divUp(uint256 x, uint256 y) external pure returns (uint256 z) {
        return Math.divUp(x, y);
    }

    function shiftRightUp(uint256 x, uint8 y) external pure returns (uint256 z) {
        return Math.shiftRightUp(x, y);
    }
}
library MsgValue {
    using SafeCast for uint256;

    function getUint112() internal returns (uint112 value) {
        value = msg.value.truncateUint112();
        if (msg.value > value) ETH.transfer(payable(msg.sender), msg.value - value);
    }
}

library BlockNumber {
    using SafeCast for uint256;

    function get() internal view returns (uint32 blockNumber) {
        blockNumber = block.number.modUint32();
    }
}
contract SafeCastTest {
    function modUint32(uint256 x) external pure returns (uint32 y) {
        return SafeCast.modUint32(x);
    }
    
    function toUint112(uint256 x) external pure returns (uint112 y) {
        return SafeCast.toUint112(x);
    }

    function toUint128(uint256 x) external pure returns (uint128 y) {
        return SafeCast.toUint128(x);
    }

    function truncateUint112(uint256 x) external pure returns (uint112 y) {
        return SafeCast.truncateUint112(x);
    }
}
contract DateTimeCallee {
    function timestampToDateTime(uint256 timestamp)
        public
        pure
        returns (
            uint256 year,
            uint256 month,
            uint256 day,
            uint256 hour,
            uint256 minute,
            uint256 second
        )
    {
        return DateTime.timestampToDateTime(timestamp);
    }
}
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}
library SafeMetadata {
    function safeName(IERC20 token) internal view returns (string memory) {
        (bool success, bytes memory data) = address(token).staticcall(
            abi.encodeWithSelector(IERC20Metadata.name.selector)
        );
        if (success) return abi.decode(data, (string));
        return 'Token';
    }

    function safeSymbol(IERC20 token) internal view returns (string memory) {
        (bool success, bytes memory data) = address(token).staticcall(
            abi.encodeWithSelector(IERC20Metadata.symbol.selector)
        );
        if (success) return abi.decode(data, (string));
        return 'TKN';
    }

    function safeDecimals(IERC20 token) internal view returns (uint8) {
        (bool success, bytes memory data) = address(token).staticcall(
            abi.encodeWithSelector(IERC20Metadata.decimals.selector)
        );
        if (success && data.length >= 32) return abi.decode(data, (uint8));
        return 18;
    }
}

interface IERC20Permit is IERC20Metadata {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
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
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
    }

abstract contract ERC20 is IERC20Metadata {
    mapping(address => uint256) public override balanceOf;
    mapping(address => mapping(address => uint256)) public override allowance;

    function transfer(address to, uint256 amount) external override returns (bool) {
        _transfer(msg.sender, to, amount);

        return true;
    }

    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external override returns (bool) {
        _approve(from, msg.sender, allowance[from][msg.sender] - amount);
        _transfer(from, to, amount);

        return true;
    }

    function approve(address spender, uint256 amount) external override returns (bool) {
        _approve(msg.sender, spender, amount);

        return true;
    }

    function increaseAllowance(address spender, uint256 amount) external returns (bool) {
        _approve(msg.sender, spender, allowance[msg.sender][spender] + amount);

        return true;
    }

    function decreaseAllowance(address spender, uint256 amount) external returns (bool) {
        _approve(msg.sender, spender, allowance[msg.sender][spender] - amount);

        return true;
    }

    function _transfer(
        address from,
        address to,
        uint256 amount
    ) private {
        require(to != address(0), 'E601');

        balanceOf[from] -= amount;
        balanceOf[to] += amount;

        emit Transfer(from, to, amount);
    }

    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal {
        allowance[owner][spender] = amount;

        emit Approval(owner, spender, amount);
    }

    function _mint(address to, uint256 amount) internal {
        require(to != address(0), 'E601');

        balanceOf[to] += amount;

        emit Transfer(address(0), to, amount);
    }

    function _burn(address from, uint256 amount) internal {
        balanceOf[from] -= amount;

        emit Transfer(from, address(0), amount);
    }
}

contract FullMathTest {
    function mul512(uint256 a, uint256 b) external pure returns (uint256 prod0, uint256 prod1) {
        return FullMath.mul512(a, b);
    }

    function mulDiv(
        uint256 a,
        uint256 b,
        uint256 denominator
    ) external pure returns (uint256 result) {
        return FullMath.mulDiv(a, b, denominator);
    }

    function mulDivUp(
        uint256 a,
        uint256 b,
        uint256 denominator
    ) external pure returns (uint256 result) {
        return FullMath.mulDivUp(a, b, denominator);
    }
}
interface IERC165 {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[EIP section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}
interface IERC721 is IERC165 {
    /**
     * @dev Emitted when `tokenId` token is transferred from `from` to `to`.
     */
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);

    /**
     * @dev Emitted when `owner` enables `approved` to manage the `tokenId` token.
     */
    event Approval(address indexed owner, address indexed approved, uint256 indexed tokenId);

    /**
     * @dev Emitted when `owner` enables or disables (`approved`) `operator` to manage all of its assets.
     */
    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);

    /**
     * @dev Returns the number of tokens in ``owner``'s account.
     */
    function balanceOf(address owner) external view returns (uint256 balance);

    /**
     * @dev Returns the owner of the `tokenId` token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function ownerOf(uint256 tokenId) external view returns (address owner);

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`, checking first that contract recipients
     * are aware of the ERC721 protocol to prevent tokens from being forever locked.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If the caller is not `from`, it must be have been allowed to move this token by either {approve} or {setApprovalForAll}.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;

    /**
     * @dev Transfers `tokenId` token from `from` to `to`.
     *
     * WARNING: Usage of this method is discouraged, use {safeTransferFrom} whenever possible.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must be owned by `from`.
     * - If the caller is not `from`, it must be approved to move this token by either {approve} or {setApprovalForAll}.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 tokenId
    ) external;

    /**
     * @dev Gives permission to `to` to transfer `tokenId` token to another account.
     * The approval is cleared when the token is transferred.
     *
     * Only a single account can be approved at a time, so approving the zero address clears previous approvals.
     *
     * Requirements:
     *
     * - The caller must own the token or be an approved operator.
     * - `tokenId` must exist.
     *
     * Emits an {Approval} event.
     */
    function approve(address to, uint256 tokenId) external;

    /**
     * @dev Returns the account approved for `tokenId` token.
     *
     * Requirements:
     *
     * - `tokenId` must exist.
     */
    function getApproved(uint256 tokenId) external view returns (address operator);

    /**
     * @dev Approve or remove `operator` as an operator for the caller.
     * Operators can call {transferFrom} or {safeTransferFrom} for any token owned by the caller.
     *
     * Requirements:
     *
     * - The `operator` cannot be the caller.
     *
     * Emits an {ApprovalForAll} event.
     */
    function setApprovalForAll(address operator, bool _approved) external;

    /**
     * @dev Returns if the `operator` is allowed to manage all of the assets of `owner`.
     *
     * See {setApprovalForAll}
     */
    function isApprovedForAll(address owner, address operator) external view returns (bool);

    /**
     * @dev Safely transfers `tokenId` token from `from` to `to`.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `tokenId` token must exist and be owned by `from`.
     * - If the caller is not `from`, it must be approved to move this token by either {approve} or {setApprovalForAll}.
     * - If `to` refers to a smart contract, it must implement {IERC721Receiver-onERC721Received}, which is called upon a safe transfer.
     *
     * Emits a {Transfer} event.
     */
    function safeTransferFrom(
        address from,
        address to,
        uint256 tokenId,
        bytes calldata data
    ) external;
}
interface IERC721Metadata is IERC721 {
    /**
     * @dev Returns the token collection name.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the token collection symbol.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the Uniform Resource Identifier (URI) for `tokenId` token.
     */
    function tokenURI(uint256 tokenId) external view returns (string memory);
}
interface IERC721Extended is IERC721Metadata {
    function assetDecimals() external view returns (uint8);

    function collateralDecimals() external view returns (uint8);
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
        assembly {
            size := extcodesize(account)
        }
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

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
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
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
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
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
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
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

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
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) private pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

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
library SafeBalance {
    using Address for address;

    function safeBalance(
        IERC20 token
    ) internal view returns (uint256) {
        bytes memory data =
            address(token).functionStaticCall(
                abi.encodeWithSelector(IERC20.balanceOf.selector, address(this)),
                "balanceOf Call to IERC20 token not successful"
            );
        return abi.decode(data, (uint256));
    }
}
contract MsgValueCallee{
    function getUint112() payable public{
        MsgValue.getUint112();
    }
}
library BlockNumberTest {
    function get() external view returns (uint32 blockNumber) {
        return BlockNumber.get();
    }
}




library ECDSA {
    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature`. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM opcode allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {toEthSignedMessageHash} on it.
     *
     * Documentation for signature generation:
     * - with https://web3js.readthedocs.io/en/v1.3.4/web3-eth-accounts.html#sign[Web3.js]
     * - with https://docs.ethers.io/v5/api/signer/#Signer-signMessage[ethers]
     */
    function recover(bytes32 hash, bytes memory signature) internal pure returns (address) {
        // Check the signature length
        // - case 65: r,s,v signature (standard)
        // - case 64: r,vs signature (cf https://eips.ethereum.org/EIPS/eip-2098) _Available since v4.1._
        if (signature.length == 65) {
            bytes32 r;
            bytes32 s;
            uint8 v;
            // ecrecover takes the signature parameters, and the only way to get them
            // currently is to use assembly.
            assembly {
                r := mload(add(signature, 0x20))
                s := mload(add(signature, 0x40))
                v := byte(0, mload(add(signature, 0x60)))
            }
            return recover(hash, v, r, s);
        } else if (signature.length == 64) {
            bytes32 r;
            bytes32 vs;
            // ecrecover takes the signature parameters, and the only way to get them
            // currently is to use assembly.
            assembly {
                r := mload(add(signature, 0x20))
                vs := mload(add(signature, 0x40))
            }
            return recover(hash, r, vs);
        } else {
            revert("ECDSA: invalid signature length");
        }
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `r` and `vs` short-signature fields separately.
     *
     * See https://eips.ethereum.org/EIPS/eip-2098[EIP-2098 short signatures]
     *
     * _Available since v4.2._
     */
    function recover(
        bytes32 hash,
        bytes32 r,
        bytes32 vs
    ) internal pure returns (address) {
        bytes32 s;
        uint8 v;
        assembly {
            s := and(vs, 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            v := add(shr(255, vs), 27)
        }
        return recover(hash, v, r, s);
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `v`, `r` and `s` signature fields separately.
     */
    function recover(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal pure returns (address) {
        // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
        // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
        // the valid range for s in (281): 0 < s < secp256k1n ÷ 2 + 1, and for v in (282): v ∈ {27, 28}. Most
        // signatures from current libraries generate a unique signature with an s-value in the lower half order.
        //
        // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
        // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
        // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
        // these malleable signatures as well.
        require(
            uint256(s) <= 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0,
            "ECDSA: invalid signature 's' value"
        );
        require(v == 27 || v == 28, "ECDSA: invalid signature 'v' value");

        // If the signature is valid (and not malleable), return the signer address
        address signer = ecrecover(hash, v, r, s);
        require(signer != address(0), "ECDSA: invalid signature");

        return signer;
    }

    /**
     * @dev Returns an Ethereum Signed Message, created from a `hash`. This
     * produces hash corresponding to the one signed with the
     * https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`]
     * JSON-RPC method as part of EIP-191.
     *
     * See {recover}.
     */
    function toEthSignedMessageHash(bytes32 hash) internal pure returns (bytes32) {
        // 32 is the length in bytes of hash,
        // enforced by the type signature above
        return keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n32", hash));
    }

    /**
     * @dev Returns an Ethereum Signed Typed Data, created from a
     * `domainSeparator` and a `structHash`. This produces hash corresponding
     * to the one signed with the
     * https://eips.ethereum.org/EIPS/eip-712[`eth_signTypedData`]
     * JSON-RPC method as part of EIP-712.
     *
     * See {recover}.
     */
    function toTypedDataHash(bytes32 domainSeparator, bytes32 structHash) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));
    }
}
abstract contract EIP712 {
    /* solhint-disable var-name-mixedcase */
    // Cache the domain separator as an immutable value, but also store the chain id that it corresponds to, in order to
    // invalidate the cached domain separator if the chain id changes.
    bytes32 private immutable _CACHED_DOMAIN_SEPARATOR;
    uint256 private immutable _CACHED_CHAIN_ID;

    bytes32 private immutable _HASHED_NAME;
    bytes32 private immutable _HASHED_VERSION;
    bytes32 private immutable _TYPE_HASH;

    /* solhint-enable var-name-mixedcase */

    /**
     * @dev Initializes the domain separator and parameter caches.
     *
     * The meaning of `name` and `version` is specified in
     * https://eips.ethereum.org/EIPS/eip-712#definition-of-domainseparator[EIP 712]:
     *
     * - `name`: the user readable name of the signing domain, i.e. the name of the DApp or the protocol.
     * - `version`: the current major version of the signing domain.
     *
     * NOTE: These parameters cannot be changed except through a xref:learn::upgrading-smart-contracts.adoc[smart
     * contract upgrade].
     */
    constructor(string memory name, string memory version) {
        bytes32 hashedName = keccak256(bytes(name));
        bytes32 hashedVersion = keccak256(bytes(version));
        bytes32 typeHash = keccak256(
            "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"
        );
        _HASHED_NAME = hashedName;
        _HASHED_VERSION = hashedVersion;
        _CACHED_CHAIN_ID = block.chainid;
        _CACHED_DOMAIN_SEPARATOR = _buildDomainSeparator(typeHash, hashedName, hashedVersion);
        _TYPE_HASH = typeHash;
    }

    /**
     * @dev Returns the domain separator for the current chain.
     */
    function _domainSeparatorV4() internal view returns (bytes32) {
        if (block.chainid == _CACHED_CHAIN_ID) {
            return _CACHED_DOMAIN_SEPARATOR;
        } else {
            return _buildDomainSeparator(_TYPE_HASH, _HASHED_NAME, _HASHED_VERSION);
        }
    }

    function _buildDomainSeparator(
        bytes32 typeHash,
        bytes32 nameHash,
        bytes32 versionHash
    ) private view returns (bytes32) {
        return keccak256(abi.encode(typeHash, nameHash, versionHash, block.chainid, address(this)));
    }

    /**
     * @dev Given an already https://eips.ethereum.org/EIPS/eip-712#definition-of-hashstruct[hashed struct], this
     * function returns the hash of the fully encoded EIP712 message for this domain.
     *
     * This hash can be used together with {ECDSA-recover} to obtain the signer of a message. For example:
     *
     * ```solidity
     * bytes32 digest = _hashTypedDataV4(keccak256(abi.encode(
     *     keccak256("Mail(address to,string contents)"),
     *     mailTo,
     *     keccak256(bytes(mailContents))
     * )));
     * address signer = ECDSA.recover(digest, signature);
     * ```
     */
    function _hashTypedDataV4(bytes32 structHash) internal view virtual returns (bytes32) {
        return ECDSA.toTypedDataHash(_domainSeparatorV4(), structHash);
    }
}

library Counters {
    struct Counter {
        // This variable should never be directly accessed by users of the library: interactions must be restricted to
        // the library's function. As of Solidity v0.5.2, this cannot be enforced, though there is a proposal to add
        // this feature: see https://github.com/ethereum/solidity/issues/4637
        uint256 _value; // default: 0
    }

    function current(Counter storage counter) internal view returns (uint256) {
        return counter._value;
    }

    function increment(Counter storage counter) internal {
        unchecked {
            counter._value += 1;
        }
    }

    function decrement(Counter storage counter) internal {
        uint256 value = counter._value;
        require(value > 0, "Counter: decrement overflow");
        unchecked {
            counter._value = value - 1;
        }
    }

    function reset(Counter storage counter) internal {
        counter._value = 0;
    }
}
abstract contract ERC20Permit is IERC20Permit, ERC20, EIP712 {
    using Counters for Counters.Counter;

    mapping(address => Counters.Counter) private _nonces;

    // solhint-disable-next-line var-name-mixedcase
    bytes32 private immutable _PERMIT_TYPEHASH =
        keccak256('Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)');

    /**
     * @dev Initializes the {EIP712} domain separator using the `name` parameter, and setting `version` to `"1"`.
     *
     * It's a good idea to use the same `name` that is defined as the ERC20 token name.
     */
    constructor(string memory name) EIP712(name, '1') {}

    /**
     * @dev See {IERC20Permit-permit}.
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) public virtual override {
        require(block.timestamp <= deadline, 'E602');

        bytes32 structHash = keccak256(abi.encode(_PERMIT_TYPEHASH, owner, spender, value, _useNonce(owner), deadline));

        bytes32 hash = _hashTypedDataV4(structHash);

        address signer = ECDSA.recover(hash, v, r, s);
        require(signer == owner, 'E603');

        _approve(owner, spender, value);
    }

    /**
     * @dev See {IERC20Permit-nonces}.
     */
    function nonces(address owner) public view virtual override returns (uint256) {
        return _nonces[owner].current();
    }

    /**
     * @dev See {IERC20Permit-DOMAIN_SEPARATOR}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view override returns (bytes32) {
        return _domainSeparatorV4();
    }

    /**
     * @dev "Consume a nonce": return the current value and increment.
     *
     * _Available since v4.1._
     */
    function _useNonce(address owner) internal virtual returns (uint256 current) {
        Counters.Counter storage nonce = _nonces[owner];
        current = nonce.current();
        nonce.increment();
    }
}

interface IERC721Permit is IERC721Extended {
    // /// @notice The permit typehash used in the permit signature
    // /// @return The typehash for the permit
    // function PERMIT_TYPEHASH() external pure returns (bytes32);

    /// @notice The domain separator used in the permit signature
    /// @return The domain seperator used in encoding of permit signature
    function DOMAIN_SEPARATOR() external view returns (bytes32);

    /// @notice Approve of a specific token ID for spending by spender via signature
    /// @param spender The account that is being approved
    /// @param tokenId The ID of the token that is being approved for spending
    /// @param deadline The deadline timestamp by which the call must be mined for the approve to work
    /// @param v Must produce valid secp256k1 signature from the holder along with `r` and `s`
    /// @param r Must produce valid secp256k1 signature from the holder along with `v` and `s`
    /// @param s Must produce valid secp256k1 signature from the holder along with `r` and `v`
    function permit(
        address spender,
        uint256 tokenId,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;
}
interface IERC721Receiver {
    /**
     * @dev Whenever an {IERC721} `tokenId` token is transferred to this contract via {IERC721-safeTransferFrom}
     * by `operator` from `from`, this function is called.
     *
     * It must return its Solidity selector to confirm the token transfer.
     * If any other value is returned or the interface is not implemented by the recipient, the transfer will be reverted.
     *
     * The selector can be obtained in Solidity with `IERC721.onERC721Received.selector`.
     */
    function onERC721Received(
        address operator,
        address from,
        uint256 tokenId,
        bytes calldata data
    ) external returns (bytes4);
}
abstract contract ERC721 is IERC721Extended {
    bytes4 private constant _INTERFACE_ID_ERC165 = 0x01ffc9a7;
    bytes4 private constant _INTERFACE_ID_ERC721 = 0x80ac58cd;

    mapping(address => uint256) public override balanceOf;
    mapping(uint256 => address) public override ownerOf;
    mapping(uint256 => address) public override getApproved;
    mapping(address => mapping(address => bool)) public override isApprovedForAll;

    function supportsInterface(bytes4 interfaceID) external pure override returns (bool) {
        return interfaceID == _INTERFACE_ID_ERC165 || interfaceID == _INTERFACE_ID_ERC721;
    }

    modifier isApproved(address owner, uint256 id) {
        require(
            owner == msg.sender || getApproved[id] == msg.sender || isApprovedForAll[owner][msg.sender],
            'Forrbidden'
        );
        _;
    }

    function safeTransferFrom(
        address from,
        address to,
        uint256 id
    ) external override isApproved(from, id) {
        _safeTransfer(from, to, id, '');
    }

    function safeTransferFrom(
        address from,
        address to,
        uint256 id,
        bytes memory data
    ) external override isApproved(from, id) {
        _safeTransfer(from, to, id, data);
    }

    function transferFrom(
        address from,
        address to,
        uint256 id
    ) external override isApproved(from, id) {
        _transfer(from, to, id);
    }

    function approve(address to, uint256 id) external override {
        address owner = ownerOf[id];
        require(
            owner == msg.sender || isApprovedForAll[owner][msg.sender],
            'ERC721 :: approve : Approve caller is not owner nor approved for all'
        );
        require(to != owner, 'E605');

        _approve(to, id);
    }

    function setApprovalForAll(address operator, bool approved) external override {
        require(operator != msg.sender, 'E607');

        _setApprovalForAll(operator, approved);
    }

    function _safeTransfer(
        address from,
        address to,
        uint256 id,
        bytes memory data
    ) private {
        _transfer(from, to, id);

        require(_checkOnERC721Received(from, to, id, data), 'E608');
    }

    function _approve(address to, uint256 id) internal {
        getApproved[id] = to;

        emit Approval(ownerOf[id], to, id);
    }

    function _setApprovalForAll(address operator, bool approved) private {
        isApprovedForAll[msg.sender][operator] = approved;

        emit ApprovalForAll(msg.sender, operator, approved);
    }

    function _safeMint(address to, uint256 id) internal {
        _mint(to, id);

        require(
            _checkOnERC721Received(address(0), to, id, ''),
            'ERC721 :: _safeMint : Transfer to non ERC721Receiver implementer'
        );
    }

    function _mint(address to, uint256 id) private {
        require(to != address(0), 'E601');
        require(ownerOf[id] == address(0), 'E604');

        balanceOf[to]++;
        ownerOf[id] = to;

        emit Transfer(address(0), to, id);
    }

    function _transfer(
        address from,
        address to,
        uint256 id
    ) private {
        require(to != address(0), 'E601');

        ownerOf[id] = to;
        balanceOf[from]--;
        balanceOf[to]++;

        _approve(address(0), id);

        emit Transfer(from, to, id);
    }

    function _checkOnERC721Received(
        address from,
        address to,
        uint256 id,
        bytes memory data
    ) private returns (bool) {
        uint256 size;
        assembly {
            size := extcodesize(to)
        }
        if (size == 0) {
            return true;
        } else {
            bytes memory returnData;
            (bool success, bytes memory _return) = to.call(
                abi.encodeWithSelector(IERC721Receiver(to).onERC721Received.selector, msg.sender, from, id, data)
            );
            if (success) {
                returnData = _return;
            } else if (_return.length > 0) {
                assembly {
                    let returnDataSize := mload(_return)
                    revert(add(32, _return), returnDataSize)
                }
            } else {
                revert('ERC721 :: _checkOnERC721Received : Transfer to non ERC721Receiver implementer');
            }
            bytes4 retval = abi.decode(returnData, (bytes4));
            return (retval == 0x150b7a02);
        }
    }
}

contract SafeBalanceTest {
    function safeBalance(
        IERC20 token
    ) external view returns (uint256) {
        return SafeBalance.safeBalance(token);
    }
}
abstract contract ERC721Permit is IERC721Permit, ERC721, EIP712 {
    using Counters for Counters.Counter;

    mapping(uint256 => Counters.Counter) private _nonces;

    bytes32 public immutable _PERMIT_TYPEHASH =
        keccak256('Permit(address spender,uint256 tokenId,uint256 nonce,uint256 deadline)');

    constructor(string memory name) EIP712(name, '1') {}

    /// @inheritdoc IERC721Permit
    function permit(
        address spender,
        uint256 tokenId,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external override {
        address owner = ownerOf[tokenId];

        require(block.timestamp <= deadline, 'E602');

        bytes32 structHash = keccak256(abi.encode(_PERMIT_TYPEHASH, spender, tokenId, _useNonce(tokenId), deadline));

        bytes32 hash = _hashTypedDataV4(structHash);

        address signer = ECDSA.recover(hash, v, r, s);
        require(signer != address(0), 'E606');
        require(signer == owner, 'E603');
        require(spender != owner, 'E605');

        _approve(spender, tokenId);
    }

    function nonces(uint256 tokenId) public view virtual returns (uint256) {
        return _nonces[tokenId].current();
    }

    function DOMAIN_SEPARATOR() external view override returns (bytes32) {
        return _domainSeparatorV4();
    }

    function _useNonce(uint256 tokenId) internal virtual returns (uint256 current) {
        Counters.Counter storage nonce = _nonces[tokenId];
        current = nonce.current();
        nonce.increment();
    }
}

