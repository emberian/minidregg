/- Pure source-owned after-core execution identities. Actual consumers import
these constants; the runtime profile commits them without importing receivers. -/
import Init
namespace Minidregg.Compiler.WorldExecutionContract
def methodTableMeaning : String := "dregg/world/method-table/v1"
def methodTableFrame : List UInt8 := "DREGG/WORLD/METHODS".toUTF8.toList ++ [1]
def freeStepsPerDay : Nat := 1000000
def freshActivationCustomization : List UInt8 := "DREGG.COMPUTE.FRESH-GENESIS/v1".toUTF8.toList
def resourceViewFrame : List UInt8 := "DREGG/NATIVE-HOST/RESOURCE-VIEW/v6".toUTF8.toList
def receivingContract : List UInt8 :=
  "DREGG.WORLD-EXECUTION/v1:rom-method-table;unique-program-output-semantic-address;numeric-non-rom;immutable-instance-layout;current-cap-and-composed-law;validated-final-funding-leg-excluded-from-sample-and-output-only;claim-step-bounded-oracle;subject-clockday-quota;1000000-free-then-1-credit-per-step;source-pay-activation-history;atomic-usage-book-burn-effects;exact-payer-cap-law-book-root-balance-consent;no-failure-charge;exact-replay-before-reprice;neutral-lift-inactive;fresh-genesis-zero-history-only;anonymous-assist-actual-abi-fuel-bounded".toUTF8.toList
end Minidregg.Compiler.WorldExecutionContract
