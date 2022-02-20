# Hybrid Multi Collateral (Testnet)

### HMC is a native hybrid model stablecoin on Harmony
### This project is still under development with it only being able to mint HMC using ONE and HMCS as collateral

HMC_V0.42.sol is the main contract that is deployed on Harmony's Testnet:

HMC address: 0xb8c9300d2e77cde5a94e781417bc1412c9d752ba

HMCS address: 0x42e31a89100e32c0f912c6df2521b8ec7c576600
<br/>
<br/>

Roadmap & Improvements to be made:
 * Setup Sushi pairs
 * Switch from ONE<>HMCS to MAI<>HMCS
 * Add ONE as a collateral type instead of HMCS
 * Add JEWEL as a collateral type instead of HMCS
 * Deploy on mainnet + get an audit
<br/>
<br/>

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
