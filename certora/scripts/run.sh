# certoraRun certora/harness/AStETHHarness.sol \
#     certora/harness/SymbolicLendingPool.sol \
#     certora/harness/DummyERC20A.sol \
#     certora/harness/DummyERC20B.sol \
#     --verify AStETHHarness:certora/specs/AStETH.spec \
#     --link AStETHHarness:POOL=SymbolicLendingPool AStETHHarness:UNDERLYING_ASSET_ADDRESS=DummyERC20A AStETHHarness:RESERVE_TREASURY_ADDRESS=DummyERC20B \
#     --solc solc6.12 \
#     --optimistic_loop \
#     --staging  \
#     --msg "AStETH rule sanity" \
#     --rule integrityOfMint




# certoraRun certora/harness/AStETHHarness.sol certora/harness/SymbolicLendingPool.sol certora/harness/DummyERC20A.sol certora/harness/DummyERC20B.sol --verify AStETHHarness:certora/specs/AStETH.spec --link AStETHHarness:POOL=SymbolicLendingPool AStETHHarness:UNDERLYING_ASSET_ADDRESS=DummyERC20A AStETHHarness:RESERVE_TREASURY_ADDRESS=DummyERC20B --solc solc6.12 --optimistic_loop --staging --msg "AStETH rule sanity" --rule integrityOfMint




# certoraRun contracts/protocol/tokenization/lido/AStETH.sol \
#     certora/harness/SymbolicLendingPool.sol \
#     certora/harness/DummyERC20A.sol \
#     certora/harness/DummyERC20B.sol \
#     --verify AStETH:certora/specs/AStETH.spec \
#     --link AStETH:POOL=SymbolicLendingPool AStETH:UNDERLYING_ASSET_ADDRESS=DummyERC20A AStETH:RESERVE_TREASURY_ADDRESS=DummyERC20B \
#     --solc solc6.12 \
#     --optimistic_loop \
#     --staging  \
#     --msg "AStETH rule sanity" \
#     --rule integrityOfMint


# certoraRun contracts/protocol/tokenization/lido/AStETH.sol certora/harness/SymbolicLendingPool.sol certora/harness/DummyERC20A.sol certora/harness/DummyERC20B.sol --verify AStETH:certora/specs/AStETH.spec --link AStETH:POOL=SymbolicLendingPool AStETH:UNDERLYING_ASSET_ADDRESS=DummyERC20A AStETH:RESERVE_TREASURY_ADDRESS=DummyERC20B --solc solc6.12 --optimistic_loop --staging  --msg "AStETH rule sanity" --rule integrityOfMint


# RUN THIS
certoraRun certora/harness/AStETHHarness.sol certora/harness/IncentivesControllerMock.sol certora/harness/SymbolicLendingPool.sol certora/harness/DummyERC20A.sol certora/harness/DummyERC20B.sol \
           --verify AStETHHarness:certora/specs/AStETH.spec \
           --link AStETHHarness:UNDERLYING_ASSET_ADDRESS=DummyERC20A AStETHHarness:POOL=SymbolicLendingPool AStETHHarness:_incentivesController=IncentivesControllerMock AStETHHarness:RESERVE_TREASURY_ADDRESS=DummyERC20B \
           --solc solc6.12 \
           --optimistic_loop \
           --settings -smt_nonLinearArithmetic=true \
           --cloud \           
           --msg "AStETH rule sanity"
           
#--rule integrityOfMint \