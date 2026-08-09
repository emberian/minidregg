/-
# Compiler.NativeGlueGen — deterministic data-only Rust glue

This generator consumes only `ArtifactBundle.canonicalEncoding`, including its
closed Lean-owned native work catalog.  It emits a mechanical Rust integration
surface: canonical data constants, private work tags, pinned constructors, and
one byte/error dispatch function.  It emits no
validation routine, transcript implementation, statement construction,
verifier Boolean, policy procedure, or proof/acceptance token.

The complete artifact encoding is rendered through the bundle's existing bounded
JSON projections and embedded as an escaped string.  In particular, this module
never materializes `Encodable.encode` of a bundle.  Selected manifest identifiers
and shape counts are also projected as data constants for convenient glue
integration.  Rust is therefore generated plumbing or unverified compute only;
all semantic checking remains in Lean-owned controllers.
-/
import Compiler.SemanticArtifactBundle
import Compiler.NativeWorkProfiles

namespace Minidregg.Compiler.NativeGlueGen

open Minidregg.Compiler.SemanticArtifactBundle
open Minidregg.Compiler.NativeWorkProfiles

set_option autoImplicit false

/-! ## Deterministic source text from the canonical encoding -/

private def rustDecimal (value : Nat) : String :=
  "\"" ++ toString value ++ "\""

private def rustDecimalSlice (values : List Nat) : String :=
  let entries := values.map rustDecimal
  "&[" ++ String.intercalate ", " entries ++ "]"

private def rustByteSlice (values : List UInt8) : String :=
  let entries := values.map fun value => toString value.toNat
  "&[" ++ String.intercalate ", " entries ++ "]"

private def rustBenchmarkSchedule
    (cases : List DispatchBenchmarkCase) : String :=
  let entries := cases.map fun benchmark =>
    "(" ++ toString benchmark.vectorLength ++ ", " ++
      toString benchmark.batchRepetitions ++ ", " ++
      toString benchmark.samples ++ ")"
  "&[" ++ String.intercalate ", " entries ++ "]"

private def rustEscapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | character => character.toString

private def rustStringLiteral (value : String) : String :=
  "\"" ++ String.intercalate "" (value.toList.map rustEscapeChar) ++ "\""

private def workName (ordinal : Nat) : String :=
  "WORK_" ++ toString ordinal

private def workTag (ordinal : Nat) : String :=
  "Work" ++ toString ordinal

private def responseWidth : ByteCodecShape → Nat
  | .tower256PairVectorsU32LE => 0
  | .tower256CoordinateLE => 32

private def requestShapeConstants (stem : String) : ByteCodecShape → List String
  | .tower256PairVectorsU32LE =>
      ["pub const " ++ stem ++ "_REQUEST_COUNT_WIDTH: usize = 4;",
       "pub const " ++ stem ++ "_REQUEST_COORDINATE_WIDTH: usize = 32;",
       "pub const " ++ stem ++ "_REQUEST_VECTOR_ARITY: usize = 2;"]
  | .tower256CoordinateLE =>
      ["pub const " ++ stem ++ "_REQUEST_COORDINATE_WIDTH: usize = 32;"]

private def kernelFunction : KernelTag → String
  | .tower256DotProduct => "crate::native_dispatch::tower256_dot_product_bytes"

private def kernelConstructor : KernelTag → String
  | .tower256DotProduct => "tower256_dot_product"

private def benchmarkConstants (stem : String) : KernelTag → List String
  | .tower256DotProduct =>
      ["pub const " ++ stem ++ "_BENCHMARK_SCHEMA: &str = \"minidregg/native-dispatch-benchmark/v1\";",
       "pub const " ++ stem ++ "_BENCHMARK_PATTERN: &str = " ++
         rustStringLiteral tower256DotProductBenchmarkPattern ++ ";",
       "pub const " ++ stem ++ "_BENCHMARK_SEED: u64 = " ++
         toString tower256DotProductBenchmarkSeed ++ ";",
       "pub const " ++ stem ++ "_BENCHMARK_SCHEDULE: &[(usize, usize, usize)] = " ++
         rustBenchmarkSchedule tower256DotProductBenchmarkSchedule ++ ";",
       "pub const " ++ stem ++ "_BENCHMARK_SENTINEL_REQUEST: &[u8] = " ++
         rustByteSlice tower256DotProductBenchmarkSentinelRequestBytes ++ ";",
       "pub const " ++ stem ++ "_BENCHMARK_SENTINEL_RESPONSE: &[u8] = " ++
         rustByteSlice tower256DotProductBenchmarkSentinelResponseBytes ++ ";"]

private def workConstants (ordinal : Nat) (profile : WorkProfile) : List String :=
  let stem := workName ordinal
  ["pub const " ++ stem ++ "_ID_DECIMAL: &str = " ++ rustDecimal profile.workId ++ ";",
   "pub const " ++ stem ++ "_CARRIER_PROFILE_ID_DECIMAL: &str = " ++
     rustDecimal profile.carrierProfileId ++ ";",
   "pub const " ++ stem ++ "_REQUEST_CODEC_ID_DECIMAL: &str = " ++
     rustDecimal profile.requestCodec.codecId ++ ";",
   "pub const " ++ stem ++ "_RESPONSE_CODEC_ID_DECIMAL: &str = " ++
     rustDecimal profile.responseCodec.codecId ++ ";",
   "pub const " ++ stem ++ "_RESPONSE_WIDTH: usize = " ++
     toString (responseWidth profile.responseCodec.shape) ++ ";"] ++
    requestShapeConstants stem profile.requestCodec.shape ++
    benchmarkConstants stem profile.kernel

private def requestConstructor (ordinal : Nat) (profile : WorkProfile) : List String :=
  ["    pub fn " ++ kernelConstructor profile.kernel ++ "(request_bytes: Box<[u8]>) -> Self {",
   "        Self { work: NativeWorkTag::" ++ workTag ordinal ++ ", request_bytes }",
   "    }"]

private def accessorArm (suffix : String) (ordinal : Nat) : String :=
  "            NativeWorkTag::" ++ workTag ordinal ++ " => " ++ workName ordinal ++ suffix

private def enumerateFrom {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | ordinal, head :: tail => (ordinal, head) :: enumerateFrom (ordinal + 1) tail

private def fromIdsBranch (ordinal : Nat) (profile : WorkProfile) : List String :=
  let stem := workName ordinal
  ["        if work_id_decimal == " ++ stem ++ "_ID_DECIMAL {",
   "            if carrier_profile_id_decimal != " ++ stem ++ "_CARRIER_PROFILE_ID_DECIMAL",
   "                || request_codec_id_decimal != " ++ stem ++ "_REQUEST_CODEC_ID_DECIMAL",
   "                || response_codec_id_decimal != " ++ stem ++ "_RESPONSE_CODEC_ID_DECIMAL",
   "            {",
   "                return Err(NativeErrorDto {",
   "                    kind: NativeErrorKind::MalformedRequest,",
   "                    detail: \"work identifier supplied with noncanonical profile or codec pins\".into(),",
   "                });",
   "            }",
   "            return Ok(Self::" ++ kernelConstructor profile.kernel ++ "(request_bytes));",
   "        }"]

private def dispatchArm (ordinal : Nat) (profile : WorkProfile) : List String :=
  let stem := workName ordinal
  ["        NativeWorkTag::" ++ workTag ordinal ++ " => {",
   "            let response = " ++ kernelFunction profile.kernel ++
     "(&request.request_bytes).map_err(|error| NativeErrorDto {",
   "                kind: NativeErrorKind::ExecutionFailure,",
   "                detail: error.to_string(),",
   "            })?;",
   "            if response.len() != " ++ stem ++ "_RESPONSE_WIDTH {",
   "                return Err(NativeErrorDto {",
   "                    kind: NativeErrorKind::ExecutionFailure,",
   "                    detail: format!(\"native response has {} bytes, expected {}\", response.len(), " ++
     stem ++ "_RESPONSE_WIDTH),",
   "                });",
   "            }",
   "            Ok(NativeReplyDto { response_bytes: response.into_boxed_slice() })",
   "        }"]

/-- Complete bounded JSON projection of the canonical encoding.  This mirrors
`SemanticArtifactBundle`'s shared field projections but deliberately omits its
Gödel-number content-address field, whose concrete evaluation is not a viable
source-generation representation. -/
def canonicalPayloadJson (wire : ArtifactBundleEncoding) : Lean.Json :=
  canonicalPayloadToJson wire

/-- Exact payload embedded by the generated Rust source. -/
def canonicalPayloadText (wire : ArtifactBundleEncoding) : String :=
  (canonicalPayloadJson wire).pretty ++ "\n"

/-- Rust source generated from the closed first-order artifact encoding and work
catalog, rather than from higher-order declaration or runtime callback objects. -/
def rustSourceFromEncoding (wire : ArtifactBundleEncoding) : String :=
  let manifest := wire.manifest
  let clauseIds := manifest.dialectClauses.map (·.clauseId)
  let codecIds := manifest.codecs.map (·.codecId)
  let indexed := enumerateFrom 0 wire.nativeWorkCatalog
  let constants := indexed.flatMap fun item => workConstants item.1 item.2
  let tags := indexed.map fun item => "    " ++ workTag item.1 ++ ","
  let constructors := indexed.flatMap fun item =>
    requestConstructor item.1 item.2 ++ [""]
  let workIdArms := indexed.map fun item =>
    accessorArm "_ID_DECIMAL," item.1
  let profileIdArms := indexed.map fun item =>
    accessorArm "_CARRIER_PROFILE_ID_DECIMAL," item.1
  let requestCodecArms := indexed.map fun item =>
    accessorArm "_REQUEST_CODEC_ID_DECIMAL," item.1
  let responseCodecArms := indexed.map fun item =>
    accessorArm "_RESPONSE_CODEC_ID_DECIMAL," item.1
  let idBranches := indexed.flatMap fun item => fromIdsBranch item.1 item.2
  let dispatchArms := indexed.flatMap fun item => dispatchArm item.1 item.2
  String.intercalate "\n" <|
    ["// @generated by Minidregg.Compiler.NativeGlueGen; do not edit.",
     "// Lean-selected data transport and fallible opaque work dispatch only.",
     "",
     "pub const ARTIFACT_SCHEMA: &str = \"minidregg/semantic-artifact-bundle/v1\";",
     "pub const ARTIFACT_CANONICAL_PAYLOAD_JSON: &str = " ++
       rustStringLiteral (canonicalPayloadText wire) ++ ";",
     "pub const MANIFEST_VERSION_DECIMAL: &str = " ++
       rustDecimal manifest.manifestVersion ++ ";",
     "pub const ABI_ID_DECIMAL: &str = " ++ rustDecimal manifest.abiId ++ ";",
     "pub const SEMANTIC_PROGRAM_ID_DECIMAL: &str = " ++
       rustDecimal manifest.semanticProgramId ++ ";",
     "pub const SEMANTIC_RELATION_ID_DECIMAL: &str = " ++
       rustDecimal manifest.semanticRelationId ++ ";",
     "pub const RECEIPT_CODEC_ID_DECIMAL: &str = " ++
       rustDecimal manifest.receiptCodecId ++ ";",
     "pub const DIALECT_CLAUSE_IDS_DECIMAL: &[&str] = " ++
       rustDecimalSlice clauseIds ++ ";",
     "pub const CODEC_IDS_DECIMAL: &[&str] = " ++
       rustDecimalSlice codecIds ++ ";",
     "pub const EFFECT_DECLARATION_COUNT: usize = " ++
       toString wire.effects.length ++ ";",
     "pub const OUTER_PHASE_COUNT: usize = " ++
       toString wire.phasePlan.length ++ ";",
     ""] ++ constants ++
    ["",
     "#[derive(Clone, Debug, PartialEq, Eq)]",
     "pub struct CanonicalArtifactDto {",
     "    pub schema: &'static str,",
     "    pub canonical_payload_json: &'static str,",
     "}",
     "",
     "pub const CANONICAL_ARTIFACT: CanonicalArtifactDto = CanonicalArtifactDto {",
     "    schema: ARTIFACT_SCHEMA,",
     "    canonical_payload_json: ARTIFACT_CANONICAL_PAYLOAD_JSON,",
     "};",
     "",
     "#[derive(Clone, Debug, PartialEq, Eq)]",
     "enum NativeWorkTag {"] ++ tags ++
    ["}",
     "",
     "#[derive(Clone, Debug, PartialEq, Eq)]",
     "pub struct NativeWorkRequestDto {",
     "    work: NativeWorkTag,",
     "    request_bytes: Box<[u8]>,",
     "}",
     "",
     "#[derive(Clone, Debug, PartialEq, Eq)]",
     "pub struct NativeReplyDto {",
     "    response_bytes: Box<[u8]>,",
     "}",
     "",
     "#[derive(Clone, Debug, PartialEq, Eq)]",
     "pub enum NativeErrorKind {",
     "    UnsupportedWork,",
     "    MalformedRequest,",
     "    ExecutionFailure,",
     "}",
     "",
     "#[derive(Clone, Debug, PartialEq, Eq)]",
     "pub struct NativeErrorDto {",
     "    pub kind: NativeErrorKind,",
     "    pub detail: String,",
     "}",
     "",
     "impl NativeWorkRequestDto {"] ++ constructors ++
    ["    pub fn from_ids(",
     "        work_id_decimal: &str,",
     "        carrier_profile_id_decimal: &str,",
     "        request_codec_id_decimal: &str,",
     "        response_codec_id_decimal: &str,",
     "        request_bytes: Box<[u8]>,",
     "    ) -> Result<Self, NativeErrorDto> {"] ++ idBranches ++
    ["        Err(NativeErrorDto {",
     "            kind: NativeErrorKind::UnsupportedWork,",
     "            detail: format!(\"unsupported Lean work id {work_id_decimal}\"),",
     "        })",
     "    }",
     "",
     "    pub fn work_id_decimal(&self) -> &'static str {",
     "        match self.work {"] ++ workIdArms ++
    ["        }",
     "    }",
     "",
     "    pub fn carrier_profile_id_decimal(&self) -> &'static str {",
     "        match self.work {"] ++ profileIdArms ++
    ["        }",
     "    }",
     "",
     "    pub fn request_codec_id_decimal(&self) -> &'static str {",
     "        match self.work {"] ++ requestCodecArms ++
    ["        }",
     "    }",
     "",
     "    pub fn response_codec_id_decimal(&self) -> &'static str {",
     "        match self.work {"] ++ responseCodecArms ++
    ["        }",
     "    }",
     "",
     "    pub fn request_bytes(&self) -> &[u8] { &self.request_bytes }",
     "}",
     "",
     "impl NativeReplyDto {",
     "    pub fn response_bytes(&self) -> &[u8] { &self.response_bytes }",
     "    pub fn into_response_bytes(self) -> Box<[u8]> { self.response_bytes }",
     "}",
     "",
     "pub fn dispatch_native(",
     "    request: NativeWorkRequestDto,",
     ") -> Result<NativeReplyDto, NativeErrorDto> {",
     "    match request.work {"] ++ dispatchArms ++
    ["    }",
     "}",
     ""]

/-- Public generator entry point.  Its inputs are reduced to first-order
artifact and native-work data before source generation. -/
def rustSource (bundle : ArtifactBundle)
    (_closed : NativeCatalogWellFormed bundle.manifest bundle.nativeAbiCodecs
      bundle.nativeWorkCatalog) : String :=
  rustSourceFromEncoding bundle.canonicalEncoding

@[simp] theorem rustSource_def (bundle : ArtifactBundle)
    (closed : NativeCatalogWellFormed bundle.manifest bundle.nativeAbiCodecs
      bundle.nativeWorkCatalog) :
    rustSource bundle closed = rustSourceFromEncoding bundle.canonicalEncoding :=
  rfl

/-- Equal canonical artifact encodings generate byte-for-byte equal Rust source
text.  No ambient state, target path, clock, or native implementation is read. -/
theorem rustSource_eq_of_canonicalEncoding_eq
    {left right : ArtifactBundle}
    (leftClosed : NativeCatalogWellFormed left.manifest left.nativeAbiCodecs
      left.nativeWorkCatalog)
    (rightClosed : NativeCatalogWellFormed right.manifest right.nativeAbiCodecs
      right.nativeWorkCatalog)
    (sameEncoding : left.canonicalEncoding = right.canonicalEncoding) :
    rustSource left leftClosed = rustSource right rightClosed := by
  exact congrArg rustSourceFromEncoding sameEncoding

/-- Determinism stated directly at the closed encoding boundary. -/
theorem rustSourceFromEncoding_deterministic
    {left right : ArtifactBundleEncoding} (same : left = right) :
    rustSourceFromEncoding left = rustSourceFromEncoding right := by
  exact congrArg rustSourceFromEncoding same

/-! ## Writer and reusable build target -/

/-- Write generated source only when explicitly run by a build target.  Defining
this function performs no filesystem or Rust mutation. -/
def writeRustSource (path : System.FilePath) (bundle : ArtifactBundle)
    (closed : NativeCatalogWellFormed bundle.manifest bundle.nativeAbiCodecs
      bundle.nativeWorkCatalog) : IO Unit := do
  if let some directory := path.parent then IO.FS.createDirAll directory
  IO.FS.writeFile path (rustSource bundle closed)

structure BuildTarget where
  path : System.FilePath
  bundle : ArtifactBundle
  nativeCatalogWellFormed : NativeCatalogWellFormed bundle.manifest
    bundle.nativeAbiCodecs bundle.nativeWorkCatalog

def BuildTarget.run (target : BuildTarget) : IO Unit :=
  writeRustSource target.path target.bundle target.nativeCatalogWellFormed

#print axioms rustSource_eq_of_canonicalEncoding_eq
#print axioms rustSourceFromEncoding_deterministic

end Minidregg.Compiler.NativeGlueGen
