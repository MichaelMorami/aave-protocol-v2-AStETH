import hre from 'hardhat';
import ethers from 'ethers';
import {
  AStETH,
  AStETHFactory,
  StableDebtStETH,
  StableDebtStETHFactory,
  StETHMocked,
  VariableDebtStETH,
  VariableDebtStETHFactory,
  ChainlinkAggregatorMockFactory,
  ChainlinkAggregatorMock,
  WETH9Factory,
  WETH9,
  LendingPool,
} from '../../types';
import {
  deployAStETH,
  deployStableDebtStETH,
  deployStEthInterestRateStrategy,
  deployStEthMock,
  deployVariableDebtStETH,
} from '../../helpers/lido/deployment';
import { AaveContracts, Addresses } from '../../helpers/lido/aave-mainnet-contracts';
import { SignerWithAddress } from '@nomiclabs/hardhat-ethers/dist/src/signer-with-address';
import { strategyStETH } from '../../markets/aave/reservesConfigs';
import { wei } from './helpers';

export class AstEthSetup {
  public static readonly INITIAL_BALANCE = wei('1000');
  private constructor(
    public readonly deployer: SignerWithAddress,
    public readonly aave: AaveContracts,
    public readonly weth: WETH9,
    public readonly stETH: StETHMocked,
    public readonly astETH: AStETH,
    public readonly stableDebtStETH: StableDebtStETH,
    public readonly variableDebtStETH: VariableDebtStETH,
    public readonly priceFeed: ChainlinkAggregatorMock,
    public readonly lenders: { lenderA: Lender; lenderB: Lender; lenderC: Lender }
  ) {}

  static async deploy(): Promise<AstEthSetup> {
    const [deployer] = await hre.ethers.getSigners();

    await hre.network.provider.request({
      method: 'hardhat_impersonateAccount',
      params: [Addresses.Owner],
    });
    const aaveOwner = hre.ethers.provider.getSigner(Addresses.Owner);
    const aaveContracts = await AaveContracts.connect(aaveOwner);

    const stETH = await deployStEthMock(deployer);
    const { lendingPool } = aaveContracts;
    const [
      astETHImpl,
      variableDebtStETHImpl,
      stableDebtStETHImpl,
      interesetRateStrategy,
      chainlinkAggregatorMock,
      weth,
    ] = await Promise.all([
      deployAStETH(lendingPool.address, stETH.address, Addresses.Treasury, deployer),
      deployVariableDebtStETH(lendingPool.address, stETH.address, deployer),
      deployStableDebtStETH(lendingPool.address, stETH.address, deployer),
      deployStEthInterestRateStrategy(deployer),
      new ChainlinkAggregatorMockFactory(deployer).deploy(),
      WETH9Factory.connect('0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2', deployer),
    ]);

    // top up aave owner balance to send transactions
    await deployer.sendTransaction({
      to: aaveOwner._address,
      value: hre.ethers.utils.parseEther('10.0'),
    });

    await aaveContracts.lendingPoolConfigurator.initReserve(
      astETHImpl.address,
      stableDebtStETHImpl.address,
      variableDebtStETHImpl.address,
      18,
      interesetRateStrategy.address
    );
    const [reserveData] = await Promise.all([
      lendingPool.getReserveData(stETH.address),
      aaveContracts.lendingPoolConfigurator.setReserveFactor(
        stETH.address,
        strategyStETH.reserveFactor
      ),
      aaveContracts.lendingPoolConfigurator.configureReserveAsCollateral(
        stETH.address,
        strategyStETH.baseLTVAsCollateral,
        strategyStETH.liquidationThreshold,
        strategyStETH.liquidationBonus
      ),
      aaveContracts.priceOracle
        .connect(aaveOwner)
        .setAssetSources([stETH.address], [chainlinkAggregatorMock.address]),
    ]);

    const astETH = AStETHFactory.connect(reserveData.aTokenAddress, deployer);

    const [_, signerA, signerB, signerC] = await hre.ethers.getSigners();
    const lenders = {
      lenderA: new Lender(weth, stETH, lendingPool, astETH, signerA),
      lenderB: new Lender(weth, stETH, lendingPool, astETH, signerB),
      lenderC: new Lender(weth, stETH, lendingPool, astETH, signerC),
    };
    await Promise.all([
      stETH.mint(signerA.address, this.INITIAL_BALANCE),
      stETH.mint(signerB.address, this.INITIAL_BALANCE),
      stETH.mint(signerC.address, this.INITIAL_BALANCE),
    ]);

    return new AstEthSetup(
      deployer,
      aaveContracts,
      weth,
      stETH,
      AStETHFactory.connect(reserveData.aTokenAddress, deployer),
      StableDebtStETHFactory.connect(reserveData.stableDebtTokenAddress, deployer),
      VariableDebtStETHFactory.connect(reserveData.variableDebtTokenAddress, deployer),
      chainlinkAggregatorMock,
      lenders
    );
  }

  async rebaseStETH(perc) {
    const currentTotalSupply = await this.stETH.totalSupply();
    const currentSupply = hre.ethers.BigNumber.from(currentTotalSupply.toString());
    const supplyDelta = currentSupply.mul(Number(perc * 10000).toFixed(0)).div(10000);
    await this.stETH.rebase(supplyDelta.toString());
  }
}

export class Lender {
  public readonly weth: WETH9;
  public readonly stETH: StETHMocked;
  public readonly lendingPool: LendingPool;
  public readonly astETH: AStETH;
  public readonly signer: SignerWithAddress;
  constructor(
    weth: WETH9,
    stETH: StETHMocked,
    lendingPool: LendingPool,
    astETH: AStETH,
    signer: SignerWithAddress
  ) {
    this.signer = signer;
    this.weth = weth.connect(signer);
    this.stETH = stETH.connect(signer);
    this.lendingPool = lendingPool.connect(signer);
    this.astETH = astETH.connect(signer);
  }

  get address(): string {
    return this.signer.address;
  }

  async depositStEth(amount: ethers.BigNumberish) {
    await this.stETH.approve(this.lendingPool.address, amount);
    return this.lendingPool.deposit(this.stETH.address, amount, this.signer.address, 0);
  }
  withdrawStEth(amount: ethers.BigNumberish) {
    return this.lendingPool.withdraw(this.stETH.address, amount, this.signer.address);
  }

  wethBalance() {
    return this.weth.balanceOf(this.address).then(wei);
  }
  stEthBalance() {
    return this.stETH.balanceOf(this.address).then(wei);
  }
  astEthBalance() {
    return this.astETH.balanceOf(this.address).then(wei);
  }
  async depositWeth(amount: ethers.BigNumberish) {
    await this.weth.deposit({ value: amount });
    await this.weth.approve(this.lendingPool.address, amount);
    return this.lendingPool.deposit(this.weth.address, amount, this.signer.address, 0);
  }
  transferAstEth(recipient: string, amount: ethers.BigNumberish) {
    return this.astETH.transfer(recipient, amount);
  }
}
