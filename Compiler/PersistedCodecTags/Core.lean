/- The persisted receiving identities other modules name: the owner leaf of the codec
corpus. Every other identity is a census entry in `Compiler.PersistedCodecTags`, which
only the Store epoch reads; editing it never rebuilds the importers of this leaf. Both
files tag into one namespace, so the epoch's manifest collects them together. -/
module

public import Compiler.PersistedCodecTagRegistry

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
meta import Compiler.PersistedCodecTagRegistry

@[expose] public section

namespace Minidregg.Compiler.PersistedCodecTags

@[persisted_codec_tag] abbrev clockWireVersion : Nat := 6
@[persisted_codec_tag] abbrev world_root_v2 : String := "DREGG.WORLD-ROOT/v3"
@[persisted_codec_tag] abbrev registry_loaded_and_final_store_cells_v17 : String := "DREGG.REGISTRY.LOADED-AND-FINAL.STORE-CELLS/v18"
@[persisted_codec_tag] abbrev durable_checkpoint_byte_v4 : List UInt8 := "DREGG.DURABLE.CHECKPOINT".toUTF8.toList ++ [5]
@[persisted_codec_tag] abbrev clock_v4 : String := s!"DREGG/CLOCK/v{clockWireVersion}"
@[persisted_codec_tag] abbrev native_host_system_v1 : String := "DREGG.NATIVE-HOST.SYSTEM/v2"
@[persisted_codec_tag] abbrev durable_log_byte_v4 : List UInt8 := "DREGG.DURABLE.LOG".toUTF8.toList ++ [4]
@[persisted_codec_tag] abbrev native_host_log_tag_v4 : String := "DREGG/NATIVE-HOST/LOG-TAG/v5"
@[persisted_codec_tag] abbrev prefix_native_host_log_tag : String := "DREGG/NATIVE-HOST/LOG-TAG"
@[persisted_codec_tag] abbrev durable_seed : String := "DREGG.DURABLE.SEED"
@[persisted_codec_tag] abbrev seedWireVersion : Nat := 6
@[persisted_codec_tag] abbrev objectivebendfrontendidentity_manifestheader_a8a75167 : String := "DREGG/OBJECTIVE-BEND/FRONT-END/v2"

check_persisted_codec_tags
end Minidregg.Compiler.PersistedCodecTags
