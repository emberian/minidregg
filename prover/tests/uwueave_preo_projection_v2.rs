//! Consumer teeth for the checked Preoscript Projection V2 manifest.
//!
//! These tests intentionally inspect only the generated data contract.  The
//! projection is useful to host code for identifiers, obligations, plans, and
//! budgets, but its presence never stands in for Minidregg authorization or a
//! semantic controller verdict.

use minidregg_prover::uwueave_preo_projection_v2::{
    UwueavePreoCurrencyV2, UwueavePreoEvidenceKeyV2, UwueavePreoOriginV2,
    UWUEAVE_PREO_PROJECTION_V2, UWUEAVE_PREO_PROJECTION_V2_SCHEMA,
};

#[test]
fn schema_and_stable_ids_are_exact() {
    let projection = &UWUEAVE_PREO_PROJECTION_V2;

    assert_eq!(UWUEAVE_PREO_PROJECTION_V2_SCHEMA, "uwueave/preo-projection/v2");
    assert_eq!(projection.schema, UWUEAVE_PREO_PROJECTION_V2_SCHEMA);
    assert_eq!(projection.declaration.id_decimal, "400");
    assert_eq!(projection.declaration.state_type_id_decimal, "401");
    assert_eq!(projection.declaration.schema_version_decimal, "1");

    assert_eq!(projection.fields.len(), 1);
    assert_eq!(projection.fields[0].id_decimal, "402");
    assert_eq!(projection.fields[0].declaration_id_decimal, "400");
    assert_eq!(projection.fields[0].carrier_type_id_decimal, "401");
    assert_eq!(projection.invariants.len(), 1);
    assert_eq!(projection.invariants[0].id_decimal, "403");
    assert_eq!(projection.futures.len(), 1);
    assert_eq!(projection.futures[0].id_decimal, "404");
}

#[test]
fn sessions_plans_and_budget_references_are_exact() {
    let projection = &UWUEAVE_PREO_PROJECTION_V2;

    let sessions: Vec<_> = projection
        .sessions
        .iter()
        .map(|row| (row.id_decimal, row.declaration_id_decimal))
        .collect();
    let plans: Vec<_> = projection
        .plans
        .iter()
        .map(|row| (row.id_decimal, row.session_id_decimal))
        .collect();
    let budgets: Vec<_> = projection
        .budgets
        .iter()
        .map(|row| (row.id_decimal, row.session_id_decimal, row.plan_id_decimal))
        .collect();

    assert_eq!(sessions, [("407", "400")]);
    assert_eq!(plans, [("408", "407")]);
    assert_eq!(budgets, [("411", "407", "408")]);
}

#[test]
fn obligations_and_five_currency_profiles_survive_generation() {
    let projection = &UWUEAVE_PREO_PROJECTION_V2;
    assert_eq!(projection.sessions[0].obligations.len(), 2);
    assert_eq!(projection.plans[0].actions.len(), 2);

    let first_obligation = &projection.sessions[0].obligations[0];
    assert!(matches!(
        first_obligation.origin,
        UwueavePreoOriginV2::Crossing { index_decimal: "0" }
    ));
    assert_eq!(first_obligation.demand.currency, UwueavePreoCurrencyV2::PeerBarrier);
    assert_eq!(first_obligation.demand.participants_decimal, ["0", "1"]);
    assert!(matches!(
        first_obligation.demand.evidence,
        UwueavePreoEvidenceKeyV2::Named("11")
    ));

    let expected = [
        (UwueavePreoCurrencyV2::PeerBarrier, "2"),
        (UwueavePreoCurrencyV2::ArbiterCut, "0"),
        (UwueavePreoCurrencyV2::NetworkRound, "0"),
        (UwueavePreoCurrencyV2::UserPrompt, "0"),
        (UwueavePreoCurrencyV2::Rollback, "0"),
    ];
    for plan in projection.plans {
        let profile: Vec<_> = plan
            .profile
            .iter()
            .map(|entry| (entry.currency, entry.value_decimal))
            .collect();
        assert_eq!(profile, expected);
    }

    let budget = &projection.budgets[0];
    let limits: Vec<_> = budget
        .limits
        .iter()
        .map(|entry| (entry.currency, entry.value_decimal))
        .collect();
    let realized: Vec<_> = budget
        .realized_profile
        .iter()
        .map(|entry| (entry.currency, entry.value_decimal))
        .collect();
    assert_eq!(limits, expected);
    assert_eq!(realized, expected);
}

#[test]
fn generated_surface_is_static_data_not_a_permit_api() {
    let source = include_str!("../generated/uwueave_preo_projection_v2.rs");

    assert!(!source.contains("pub fn "));
    assert!(!source.contains("impl "));
    assert!(!source.contains("unsafe "));
    assert!(!source.contains("extern "));
    assert!(!source.contains("Verified"));
    assert!(!source.contains("Accepted"));
}
