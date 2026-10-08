/- Pure source-owned after-core execution identities. Actual consumers import
these constants; the runtime profile commits them without importing receivers. -/
import Theory.PersistedCodecTags
import Init
namespace Minidregg.Compiler.WorldExecutionContract
def methodTableMeaning : String := "dregg/world/method-table/v1"
def methodTableFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.world_methods_byte_v1
def freeStepsPerDay : Nat := 1000000
def freshActivationCustomization : List UInt8 := Minidregg.Theory.PersistedCodecTags.compute_fresh_genesis_v1.toUTF8.toList
def resourceViewFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.native_host_resource_view_v6.toUTF8.toList
def receivingContract : List UInt8 :=
  Minidregg.Theory.PersistedCodecTags.world_execution_v2_authenticated_whole_kind_observer_exact_canoni_d7a19b856fe5e7f5.toUTF8.toList
end Minidregg.Compiler.WorldExecutionContract
