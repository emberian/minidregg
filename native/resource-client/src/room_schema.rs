//! Fresh room declared fields. Native closed-schema admission remains authoritative.
use std::collections::BTreeSet;
pub(crate) const ROOM_FIELDS_START: u64 = 1001;
pub(crate) const ROSTER_MEMBER_CAPACITY: usize = 499;
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
pub(crate) fn declared_fields() -> String {
    assert!(
        unique_fields(TARIFF_FIELDS),
        "room schema contains duplicate or roster fields"
    );
    std::iter::once(format!("2-{}", ROOM_FIELDS_START - 1))
        .chain(TARIFF_FIELDS.iter().map(|(_, k)| k.to_string()))
        .chain(std::iter::once(NAMES_FIELD.to_string()))
        .collect::<Vec<_>>()
        .join(",")
}
fn unique_fields(table: &[(&str, &str)]) -> bool {
    let mut keys = BTreeSet::from([NAMES_FIELD]);
    let mut names = BTreeSet::new();
    table.iter().all(|(name, key)| {
        names.insert(*name)
            && keys.insert(*key)
            && key.parse::<u64>().is_ok_and(|k| k >= ROOM_FIELDS_START)
    })
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn names_paid_open_and_assignment_are_distinct() {
        assert!(unique_fields(TARIFF_FIELDS));
        assert!(!unique_fields(&[("open", NAMES_FIELD)]));
        assert!(!unique_fields(&[("a", "1011"), ("b", "1011")]));
        let fields = declared_fields();
        for k in [NAMES_FIELD, OPEN_FIELD, ASSIGNMENT_FIELD] {
            assert_eq!(fields.split(',').filter(|f| *f == k).count(), 1);
        }
        assert_eq!(ROSTER_MEMBER_CAPACITY, (ROOM_FIELDS_START as usize - 3) / 2);
    }
}
