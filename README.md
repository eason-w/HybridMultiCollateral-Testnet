# Hybrid Multi Collateral (Testnet)

### HMC is a native hybrid model stablecoin on Harmony
### This project is still underdevelopment with it only being able to mint HMC using ONE and HMCS as collateral

Improvements to be made:
 * Setup Sushi pairs
 * Switch from ONE<>HMCS to MAI<>HMCS
 * Add ONE as a collateral type instead of HMCS
 * Add JEWEL as a collateral type instead of HMCS
 * Deploy on mainnet + get an audit
 
Order of Contracts Included in main contract
 * Context.sol
 * SafeMath.sol
 * IERC20.sol
 * Address.sol
 * ERC20Custom.sol
 * ERC20.sol
 * Owned.sol
 * EnumerableSet.sol
 * AccessControl.sol
 * HMCS.sol
 * HMC.sol
 * ISushiswapV2Factory.sol
 * ISushiswapV2Pair.sol
 * Babylonian.sol
 * FixedPoint.sol
 * SushiswapV2OracleLibrary.sol
 * SushiswapV2Library.sol
 * SushiswapPairOracle.sol
 * AggregatorV3Interface.sol
 * ChainlinkONEUSDPriceConsumer.sol
 * HMCPoolLibrary.sol
 * TransferHelper.sol
 * HMCPool.sol
