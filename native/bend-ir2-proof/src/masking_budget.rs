//! Trace-opening dimension budget for this exact local-row, no-lookup profile.
//! This is one necessary protocol qualification, NOT a whole-transcript ZK proof.
//! Actual BatchSTARK opens main at zeta and g*zeta (the AIR default requests all
//! next columns). Each extension opening costs at most extension_degree base
//! coordinates. FRI open_input exposes one base row per query, not one per fold.
use dregg_circuit::descriptor_ir2::{IR2_EXT_DEGREE, IR2_FRI_NUM_QUERIES, IR2_FRI_LOG_BLOWUP};
use p3_field::TwoAdicField;

pub const MAIN_EXTENSION_OPENINGS: usize = 2;
pub const REQUIRED_TRACE_MASKS: usize =
    IR2_EXT_DEGREE * MAIN_EXTENSION_OPENINGS + IR2_FRI_NUM_QUERIES;
pub const MIN_TRACE_ROWS: usize = REQUIRED_TRACE_MASKS.next_power_of_two();

#[derive(Clone, Copy, Debug)]
pub struct TraceCapacity { rows: usize }
impl TraceCapacity {
    pub fn checked(rows: usize) -> Result<Self, &'static str> {
        if !rows.is_power_of_two() { return Err("trace capacity must be a power of two"); }
        if rows < REQUIRED_TRACE_MASKS {
            return Err("insufficient trace masks for actual extension/FRI opening budget");
        }
        if rows.ilog2() as usize + 1 + IR2_FRI_LOG_BLOWUP > p3_baby_bear::BabyBear::TWO_ADICITY {
            return Err("trace capacity exceeds BabyBear shifted LDE domain");
        }
        // BabyBear domain / FRI maximum degree is checked by the backend too;
        // reject arithmetic overflow before forming doubled hiding domains.
        if rows.checked_mul(2).is_none() { return Err("hiding domain size overflow"); }
        Ok(Self { rows })
    }
    pub fn rows(self) -> usize { self.rows }
    pub fn extended_log_height(self) -> usize { self.rows.ilog2() as usize + 1 }
}
