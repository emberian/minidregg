import Host.Json

namespace Minidregg.Host.ApplicationManagedPolicyAuthoringCheck

private def request (kind : String) : Lean.Json := .mkObj [
  ("kind", .str kind), ("app", .str "101"), ("packageManifest", .str "102"),
  ("snapshotManifest", .str "103"), ("owner", .str "17"), ("manager", .str "8")]

theorem exact_app_bytes :
    Json.author "application-managed-policy" (request "app") =
      .ok (Minidregg.Kernel.NativeHostGenesis.predicateStream.encode
        (Minidregg.Kernel.ApplicationGrain.managedPolicy 102 103 17 8)) := by decide

theorem authored_predicate_has_inspectable_ast :
    ((Json.author "application-managed-policy" (request "app")).toOption.bind
      (fun bytes => (Json.inspect "predicate" bytes).toOption)).isSome = true := by decide

theorem unknown_kind_refused :
    (Json.author "application-managed-policy" (request "global")).toOption = none := by decide

theorem unknown_field_refused :
    (Json.author "application-managed-policy"
      (.mkObj [("kind", .str "app"), ("app", .str "101"),
        ("packageManifest", .str "102"), ("snapshotManifest", .str "103"),
        ("owner", .str "17"), ("manager", .str "8"), ("override", .bool true)])).toOption = none := by decide

theorem colliding_resource_refused :
    (Json.author "application-managed-policy"
      (.mkObj [("kind", .str "app"), ("app", .str "101"),
        ("packageManifest", .str "101"), ("snapshotManifest", .str "103"),
        ("owner", .str "17"), ("manager", .str "8")])).toOption = none := by decide

end Minidregg.Host.ApplicationManagedPolicyAuthoringCheck
