if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun certora/harness/AStETHHarness.sol certora/harness/IncentivesControllerMock.sol certora/harness/SymbolicLendingPool.sol certora/harness/DummyERC20A.sol certora/harness/DummyERC20B.sol \
           --verify AStETHHarness:certora/specs/AStETH.spec \
           --link AStETHHarness:UNDERLYING_ASSET_ADDRESS=DummyERC20A AStETHHarness:POOL=SymbolicLendingPool AStETHHarness:_incentivesController=IncentivesControllerMock AStETHHarness:RESERVE_TREASURY_ADDRESS=DummyERC20B SymbolicLendingPool:aToken=AStETHHarness SymbolicLendingPool:Asset=DummyERC20A \
           --solc solc6.12 \
           --optimistic_loop \
           --settings -smt_nonLinearArithmetic=true \
           --cloud \
           --msg "AStETH rule sanity"
        #    --rule_sanity \

#    --rule IntegrityOfBurn \         
#--rule integrityOfMint \
