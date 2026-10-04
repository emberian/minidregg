//! The room cell's declared fields (ROOM-SCHEMA v2). Native closed-schema
//! admission remains authoritative: the Host refuses a write to any field the
//! room did not declare at birth (K-FIELD-CLOSURE).
//!
//! A room declares its fixed fields (the tariff, the names index, the open
//! flag, the Hermes assignment: 1001..1012) and one unbounded tail, every
//! field from `ROSTER_FROM` up (`fieldsFrom`, `state-key/tagged-v4`). The
//! roster lives in the tail: field `ROSTER_FROM` is the founder; member `k`
//! (from 1) is field `ROSTER_FROM + 2k - 1` (subject) and `ROSTER_FROM + 2k`
//! (the member's stream). A member's rows are allocated when they join; a kick
//! revokes grants and keeps the rows (the history of who was here), and a
//! re-invite reuses them. Nothing is reserved for members who never come, so a
//! room's store, its opening and every read of it are as wide as the roster it
//! has, not the roster it might have.
//!
//! v1 pre-declared every roster slot (fields 2..1000, 499 historical members)
//! and so carried a 1,016-entry declaration in every read and every write of
//! the room. A v1 room cannot be read under v2: the declared-effect key codec
//! changed (`state-key/tagged-v4`), so a v1 world's cells refuse to decode at
//! the Host, and a client shown a room without the v2 tail refuses it by name
//! (`check_room_view`). v1 worlds are re-genesised, not migrated.
use std::collections::BTreeSet;

use serde_json::Value;

/// The schema epoch this client reads; `check_room_view` names it.
pub(crate) const ROOM_SCHEMA_EPOCH: u64 = 2;
pub(crate) const ROOM_FIELDS_START: u64 = 1001;
/// The first roster field: the founder's row; members' rows follow it.
pub(crate) const ROSTER_FROM: u64 = 2000;
pub(crate) const NAMES_FIELD: &str = "1010";
pub(crate) const OPEN_FIELD: &str = "1011";
pub(crate) const ASSIGNMENT_FIELD: &str = "1012";
pub(crate) const TARIFF_FIELDS: &[(&str, &str)] = &[
    ("week", "1001"),
    ("birth", "1002"),
    ("hermes/turn", "1003"),
    ("till", "1004"),
    ("period", "1005"),
    ("runner", "1006"),
    ("concierge", "1007"),
    ("hermes", "1008"),
    ("hermes/account", "1009"),
    ("open", OPEN_FIELD),
    ("hermes/assignment", ASSIGNMENT_FIELD),
];

/// The founder's roster row.
pub(crate) const FOUNDER_FIELD: u64 = ROSTER_FROM;

/// Member `k`'s (from 1) subject and stream rows.
pub(crate) fn member_fields(k: u64) -> (u64, u64) {
    assert!(k >= 1, "roster members count from 1");
    (ROSTER_FROM + 2 * k - 1, ROSTER_FROM + 2 * k)
}

/// The `--fields` of a room's birth: its fixed fields, then the roster tail.
pub(crate) fn declared_fields() -> String {
    assert!(
        unique_fields(TARIFF_FIELDS),
        "room schema contains duplicate or roster fields"
    );
    TARIFF_FIELDS
        .iter()
        .map(|(_, k)| k.to_string())
        .chain(std::iter::once(NAMES_FIELD.to_string()))
        .chain(std::iter::once(format!("{ROSTER_FROM}-")))
        .collect::<Vec<_>>()
        .join(",")
}

fn unique_fields(table: &[(&str, &str)]) -> bool {
    let mut keys = BTreeSet::from([NAMES_FIELD]);
    let mut names = BTreeSet::new();
    table.iter().all(|(name, key)| {
        names.insert(*name)
            && keys.insert(*key)
            && key
                .parse::<u64>()
                .is_ok_and(|k| (ROOM_FIELDS_START..ROSTER_FROM).contains(&k))
    })
}

/// Refuse a resource view of a cell that is not a v2 room: its declaration
/// must hold the roster tail from `ROSTER_FROM` and every fixed field. A narrowed
/// view (a K-FIELDS reader) sees only its own fields' declaration and is not
/// judged here; such a reader never reads the roster.
pub(crate) fn check_room_view(view: &Value) -> Result<(), String> {
    let cell = view.get("cell").ok_or("the room view carries no cell")?;
    let declared: BTreeSet<&str> = cell
        .get("declaration")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .collect();
    let tail = cell.get("declaredFrom").and_then(Value::as_str);
    if tail == Some(ROSTER_FROM.to_string().as_str())
        && TARIFF_FIELDS.iter().all(|(_, k)| declared.contains(k))
        && declared.contains(NAMES_FIELD)
    {
        return Ok(());
    }
    if declared.contains("2") && declared.contains("1000") {
        return Err(format!(
            "this room was born under room schema v1 (its roster pre-declared in fields 2..1000, \
             499 member slots); this client reads room schema v{ROOM_SCHEMA_EPOCH} (a roster tail \
             from field {ROSTER_FROM}). A v1 world is re-genesised, not migrated."
        ));
    }
    Err(format!(
        "this cell is not a room of schema v{ROOM_SCHEMA_EPOCH}: its declaration has no roster \
         tail from field {ROSTER_FROM} beside the room's fields {ROOM_FIELDS_START}..{}",
        ASSIGNMENT_FIELD
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn names_paid_open_and_assignment_are_distinct() {
        assert!(unique_fields(TARIFF_FIELDS));
        assert!(!unique_fields(&[("open", NAMES_FIELD)]));
        assert!(!unique_fields(&[("a", "1011"), ("b", "1011")]));
        // A fixed field inside the roster tail is refused.
        assert!(!unique_fields(&[("a", "2000")]));
        let fields = declared_fields();
        for k in [NAMES_FIELD, OPEN_FIELD, ASSIGNMENT_FIELD] {
            assert_eq!(fields.split(',').filter(|f| *f == k).count(), 1);
        }
        assert!(fields.ends_with(",2000-"));
    }

    /// The declaration is as wide as the room's own fields: twelve fields and
    /// one tail, where v1 declared 1,011.
    #[test]
    fn the_room_declares_twelve_fields_and_one_tail() {
        let fields = crate::workspace::parse_fields(&declared_fields()).unwrap();
        assert_eq!(fields["fields"].as_array().unwrap().len(), 12);
        assert_eq!(fields["from"], json!("2000"));
    }

    #[test]
    fn roster_rows_follow_the_founder_without_a_ceiling() {
        assert_eq!(FOUNDER_FIELD, 2000);
        assert_eq!(member_fields(1), (2001, 2002));
        assert_eq!(member_fields(2), (2003, 2004));
        // The 500th member, past v1's 499 slots, has rows like any other.
        assert_eq!(member_fields(500), (2999, 3000));
    }

    #[test]
    fn a_v1_room_is_refused_by_name_and_a_v2_room_is_read() {
        let mut v1: Vec<String> = (2..=1000).map(|f| f.to_string()).collect();
        v1.extend((1001..=1012).map(|f| f.to_string()));
        let old = json!({"cell":{"declaration":v1,"entries":[]}});
        assert!(check_room_view(&old).unwrap_err().contains("room schema v1"));
        let v2: Vec<String> = (1001..=1012).map(|f| f.to_string()).collect();
        let new = json!({"cell":{"declaration":v2,"declaredFrom":"2000","entries":[]}});
        assert!(check_room_view(&new).is_ok());
        let plain = json!({"cell":{"declaration":["1","2"],"entries":[]}});
        assert!(check_room_view(&plain).unwrap_err().contains("not a room"));
        let open = json!({"cell":{"declaration":"open","entries":[]}});
        assert!(check_room_view(&open).is_err());
    }
}
