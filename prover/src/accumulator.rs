//! `[PROVER-accumulator-algebra]` — an executable mirror of Loom's proved
//! linear accumulator layer.
//!
//! `Loom/Accumulator.lean` deliberately folds only the post-reduction linear
//! channel: an opaque root plus rows `(weight, target)`, where a word satisfies
//! a row when `dot(weight, word) = target`.  This module implements exactly that
//! algebra over canonical `u64` field representatives:
//!
//! * same-word batching uses powers `1, gamma, gamma^2, ...` in both weights
//!   and targets;
//! * cross-word folding requires the two claims to have the same weights, keeps
//!   those weights, and folds targets as `a + gamma * b`;
//! * witness words fold coordinatewise as `f + gamma * g`;
//! * chain helpers iterate those same two operations without a second path.
//!
//! The runtime `word_len` field is the Rust replacement for Lean's ambient
//! index type.  All public operations reject malformed widths and non-canonical
//! field elements.  Arithmetic is field arithmetic when the caller supplies a
//! prime modulus; this unverified Rust does not prove primality.
//!
//! The boundary is strict.  `root` is generic and opaque, and a folded root is
//! caller-supplied just as `foldRoot` is an argument in Lean.  This module does
//! **not** claim the root commits the word, check Reed--Solomon membership,
//! construct Merkle openings, run Fiat--Shamir, or implement the proximity/RBR
//! extractor.  Those are `[PROVER-acc-root-link]`,
//! `[PROVER-acc-code-membership]`, and `[PROVER-acc-rbr]`.  There is likewise no
//! descriptor bridge yet: emitted multiplication gates are nonlinear until the
//! selector/sumcheck reduction produces this linear channel; silently dropping
//! them would be fail-open.

use std::fmt;

use crate::descriptor::Fp;

/// One post-reduction linear constraint `dot(weights, word) = target`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearConstraint {
    pub weights: Vec<Fp>,
    pub target: Fp,
}

/// Loom's `AccClaim` at runtime: an opaque commitment root and a finite linear
/// channel.  `word_len` makes the ambient word shape explicit even when the
/// channel is empty.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccClaim<Root = Fp> {
    pub root: Root,
    pub word_len: usize,
    pub channel: Vec<LinearConstraint>,
}

/// Conservative rejection reasons for malformed accumulator objects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccError {
    InvalidModulus(u64),
    NonCanonical {
        what: &'static str,
        value: Fp,
        modulus: u64,
    },
    ConstraintWidth {
        row: usize,
        expected: usize,
        actual: usize,
    },
    WordWidth {
        expected: usize,
        actual: usize,
    },
    ChannelLength {
        left: usize,
        right: usize,
    },
    UnsharedWeights {
        row: usize,
    },
    ScheduleLength {
        links: usize,
        challenges: usize,
        roots: Option<usize>,
    },
}

impl fmt::Display for AccError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AccError::InvalidModulus(p) => write!(f, "modulus {p} is smaller than 2"),
            AccError::NonCanonical {
                what,
                value,
                modulus,
            } => write!(f, "{what} value {value} is not canonical modulo {modulus}"),
            AccError::ConstraintWidth {
                row,
                expected,
                actual,
            } => write!(
                f,
                "constraint row {row} has width {actual}, expected {expected}"
            ),
            AccError::WordWidth { expected, actual } => {
                write!(f, "word has width {actual}, expected {expected}")
            }
            AccError::ChannelLength { left, right } => {
                write!(f, "claim channels have lengths {left} and {right}")
            }
            AccError::UnsharedWeights { row } => {
                write!(f, "claim channels do not share weights at row {row}")
            }
            AccError::ScheduleLength {
                links,
                challenges,
                roots,
            } => match roots {
                Some(roots) => write!(
                    f,
                    "fold schedule has {links} links, {challenges} challenges, and {roots} roots"
                ),
                None => write!(
                    f,
                    "word fold schedule has {links} links and {challenges} challenges"
                ),
            },
        }
    }
}

impl std::error::Error for AccError {}

fn validate_modulus(p: u64) -> Result<(), AccError> {
    if p < 2 {
        Err(AccError::InvalidModulus(p))
    } else {
        Ok(())
    }
}

fn canonical(what: &'static str, value: Fp, p: u64) -> Result<(), AccError> {
    if value < p {
        Ok(())
    } else {
        Err(AccError::NonCanonical {
            what,
            value,
            modulus: p,
        })
    }
}

#[inline]
fn add_mod(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 + b as u128) % p as u128) as u64
}

#[inline]
fn mul_mod(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 * b as u128) % p as u128) as u64
}

fn validate_word(word: &[Fp], expected: usize, p: u64) -> Result<(), AccError> {
    validate_modulus(p)?;
    if word.len() != expected {
        return Err(AccError::WordWidth {
            expected,
            actual: word.len(),
        });
    }
    for &value in word {
        canonical("word", value, p)?;
    }
    Ok(())
}

impl<Root> AccClaim<Root> {
    /// Validate the runtime mirror of Lean's typed channel shape and canonical
    /// representatives.  The opaque root is intentionally outside this check.
    pub fn validate(&self, p: u64) -> Result<(), AccError> {
        validate_modulus(p)?;
        for (row, constraint) in self.channel.iter().enumerate() {
            if constraint.weights.len() != self.word_len {
                return Err(AccError::ConstraintWidth {
                    row,
                    expected: self.word_len,
                    actual: constraint.weights.len(),
                });
            }
            for &weight in &constraint.weights {
                canonical("weight", weight, p)?;
            }
            canonical("target", constraint.target, p)?;
        }
        Ok(())
    }

    /// The channel-only satisfaction relation.  Unlike Lean's full
    /// `AccClaim.Satisfies`, this does not assert membership in a code; that
    /// absent conjunct is named `[PROVER-acc-code-membership]` above.
    pub fn channel_satisfied_by(&self, word: &[Fp], p: u64) -> Result<bool, AccError> {
        self.validate(p)?;
        validate_word(word, self.word_len, p)?;
        Ok(self
            .channel
            .iter()
            .all(|constraint| dot_unchecked(&constraint.weights, word, p) == constraint.target))
    }
}

fn dot_unchecked(weights: &[Fp], word: &[Fp], p: u64) -> Fp {
    weights.iter().zip(word).fold(0, |sum, (&weight, &value)| {
        add_mod(sum, mul_mod(weight, value, p), p)
    })
}

/// Evaluate one well-shaped linear constraint.  This is exposed separately for
/// conformance and residual-polynomial tests.
pub fn evaluate_constraint(
    constraint: &LinearConstraint,
    word: &[Fp],
    p: u64,
) -> Result<Fp, AccError> {
    validate_modulus(p)?;
    if constraint.weights.len() != word.len() {
        return Err(AccError::WordWidth {
            expected: constraint.weights.len(),
            actual: word.len(),
        });
    }
    for &weight in &constraint.weights {
        canonical("weight", weight, p)?;
    }
    canonical("target", constraint.target, p)?;
    validate_word(word, constraint.weights.len(), p)?;
    Ok(dot_unchecked(&constraint.weights, word, p))
}

/// WHIR same-word batching: combine every row with powers of `gamma`, leaving
/// the root and word shape unchanged and producing one row.  An empty channel
/// batches to the zero functional with target zero, matching the empty sum in
/// Lean.
pub fn batch_claim<Root: Clone>(
    claim: &AccClaim<Root>,
    gamma: Fp,
    p: u64,
) -> Result<AccClaim<Root>, AccError> {
    claim.validate(p)?;
    canonical("batch challenge", gamma, p)?;
    let mut weights = vec![0; claim.word_len];
    let mut target = 0;
    let mut power = 1 % p;
    for constraint in &claim.channel {
        for (out, &weight) in weights.iter_mut().zip(&constraint.weights) {
            *out = add_mod(*out, mul_mod(power, weight, p), p);
        }
        target = add_mod(target, mul_mod(power, constraint.target, p), p);
        power = mul_mod(power, gamma, p);
    }
    Ok(AccClaim {
        root: claim.root.clone(),
        word_len: claim.word_len,
        channel: vec![LinearConstraint { weights, target }],
    })
}

/// Loom's cross-word `foldClaims`.  Both claims must already be aligned to the
/// same functional channel.  Only the targets fold; `folded_root` is opaque
/// prover-supplied data whose binding is `[PROVER-acc-root-link]`.
pub fn fold_claims<Root, LeftRoot, RightRoot>(
    folded_root: Root,
    left: &AccClaim<LeftRoot>,
    right: &AccClaim<RightRoot>,
    gamma: Fp,
    p: u64,
) -> Result<AccClaim<Root>, AccError> {
    left.validate(p)?;
    right.validate(p)?;
    canonical("fold challenge", gamma, p)?;
    if left.word_len != right.word_len {
        return Err(AccError::WordWidth {
            expected: left.word_len,
            actual: right.word_len,
        });
    }
    if left.channel.len() != right.channel.len() {
        return Err(AccError::ChannelLength {
            left: left.channel.len(),
            right: right.channel.len(),
        });
    }
    let mut channel = Vec::with_capacity(left.channel.len());
    for (row, (a, b)) in left.channel.iter().zip(&right.channel).enumerate() {
        if a.weights != b.weights {
            return Err(AccError::UnsharedWeights { row });
        }
        channel.push(LinearConstraint {
            weights: a.weights.clone(),
            target: add_mod(a.target, mul_mod(gamma, b.target, p), p),
        });
    }
    Ok(AccClaim {
        root: folded_root,
        word_len: left.word_len,
        channel,
    })
}

/// Fold two witness words coordinatewise as `left + gamma * right`.
pub fn fold_words(left: &[Fp], right: &[Fp], gamma: Fp, p: u64) -> Result<Vec<Fp>, AccError> {
    validate_word(left, left.len(), p)?;
    validate_word(right, left.len(), p)?;
    canonical("fold challenge", gamma, p)?;
    Ok(left
        .iter()
        .zip(right)
        .map(|(&a, &b)| add_mod(a, mul_mod(gamma, b, p), p))
        .collect())
}

/// Iterate the one `fold_claims` operation over a chain.  Each output root is
/// explicit because the linear algebra imposes no root recurrence.
pub fn fold_claim_chain<Root: Clone>(
    base: &AccClaim<Root>,
    links: &[AccClaim<Root>],
    challenges: &[Fp],
    folded_roots: &[Root],
    p: u64,
) -> Result<AccClaim<Root>, AccError> {
    if links.len() != challenges.len() || links.len() != folded_roots.len() {
        return Err(AccError::ScheduleLength {
            links: links.len(),
            challenges: challenges.len(),
            roots: Some(folded_roots.len()),
        });
    }
    let mut acc = base.clone();
    for ((link, &gamma), root) in links.iter().zip(challenges).zip(folded_roots) {
        acc = fold_claims(root.clone(), &acc, link, gamma, p)?;
    }
    Ok(acc)
}

/// Iterate the one `fold_words` operation over witness words at the same
/// challenge schedule as a claim chain.
pub fn fold_word_chain(
    base: &[Fp],
    links: &[Vec<Fp>],
    challenges: &[Fp],
    p: u64,
) -> Result<Vec<Fp>, AccError> {
    if links.len() != challenges.len() {
        return Err(AccError::ScheduleLength {
            links: links.len(),
            challenges: challenges.len(),
            roots: None,
        });
    }
    let mut acc = base.to_vec();
    validate_word(&acc, base.len(), p)?;
    for (link, &gamma) in links.iter().zip(challenges) {
        acc = fold_words(&acc, link, gamma, p)?;
    }
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field4::P;

    const P5: u64 = 5;
    const X_WORD: [Fp; 4] = [0, 1, 2, 3];
    const ONE_WORD: [Fp; 4] = [1, 1, 1, 1];
    const ZERO_WORD: [Fp; 4] = [0, 0, 0, 0];
    const Q2: [Fp; 4] = [0, 0, 1, 0];
    const CONSV: [Fp; 4] = [1, 1, 1, 1];

    fn row(weights: &[Fp], target: Fp) -> LinearConstraint {
        LinearConstraint {
            weights: weights.to_vec(),
            target,
        }
    }

    fn good_claim(p: u64) -> AccClaim<&'static str> {
        let sum = X_WORD.iter().fold(0, |a, &b| add_mod(a, b, p));
        AccClaim {
            root: "good",
            word_len: 4,
            channel: vec![row(&Q2, 2), row(&CONSV, sum)],
        }
    }

    fn bad_pair(p: u64) -> AccClaim<&'static str> {
        // Residuals on X_WORD are -1 and +1, so the batch residual is gamma-1.
        let sum = X_WORD.iter().fold(0, |a, &b| add_mod(a, b, p));
        AccClaim {
            root: "bad",
            word_len: 4,
            channel: vec![row(&Q2, 3), row(&CONSV, add_mod(sum, p - 1, p))],
        }
    }

    fn eval_claim(target: Fp) -> AccClaim<&'static str> {
        AccClaim {
            root: "eval",
            word_len: 4,
            channel: vec![row(&Q2, target)],
        }
    }

    #[test]
    fn f5_good_claim_and_every_batch_are_satisfied() {
        let claim = good_claim(P5);
        assert_eq!(claim.channel_satisfied_by(&X_WORD, P5), Ok(true));
        for gamma in 0..P5 {
            assert_eq!(
                batch_claim(&claim, gamma, P5)
                    .unwrap()
                    .channel_satisfied_by(&X_WORD, P5),
                Ok(true)
            );
        }
    }

    #[test]
    fn f5_false_pair_has_exactly_one_bad_batch_challenge() {
        let claim = bad_pair(P5);
        assert_eq!(claim.channel_satisfied_by(&X_WORD, P5), Ok(false));
        let bad: Vec<Fp> = (0..P5)
            .filter(|&gamma| {
                batch_claim(&claim, gamma, P5)
                    .unwrap()
                    .channel_satisfied_by(&X_WORD, P5)
                    .unwrap()
            })
            .collect();
        assert_eq!(bad, vec![1]);
    }

    #[test]
    fn babybear_bad_batch_residual_is_gamma_minus_one() {
        let claim = bad_pair(P);
        for gamma in [0, 1, 2, 17, 1_000_000, P - 1] {
            let batched = batch_claim(&claim, gamma, P).unwrap();
            let actual = evaluate_constraint(&batched.channel[0], &X_WORD, P).unwrap();
            let residual = add_mod(actual, P - batched.channel[0].target, P);
            assert_eq!(residual, add_mod(gamma, P - 1, P));
            assert_eq!(
                batched.channel_satisfied_by(&X_WORD, P).unwrap(),
                gamma == 1
            );
        }
    }

    #[test]
    fn honest_cross_word_fold_closes_and_false_link_has_singleton_escape() {
        let a = eval_claim(2);
        let honest_b = eval_claim(1);
        for gamma in 0..P5 {
            let claim = fold_claims("fold", &a, &honest_b, gamma, P5).unwrap();
            let word = fold_words(&X_WORD, &ONE_WORD, gamma, P5).unwrap();
            assert!(claim.channel_satisfied_by(&word, P5).unwrap());
        }

        // The same target-1 link is false for ZERO_WORD.  The folded word stays
        // X_WORD while the target becomes 2+gamma, hence only gamma=0 escapes.
        let escapes: Vec<Fp> = (0..P5)
            .filter(|&gamma| {
                let claim = fold_claims("fold", &a, &honest_b, gamma, P5).unwrap();
                let word = fold_words(&X_WORD, &ZERO_WORD, gamma, P5).unwrap();
                claim.channel_satisfied_by(&word, P5).unwrap()
            })
            .collect();
        assert_eq!(escapes, vec![0]);
    }

    #[test]
    fn gamma_power_associativity_holds_on_channel_and_word() {
        let a = eval_claim(2);
        let b = eval_claim(1);
        let c = eval_claim(4);
        let gamma = 3;
        let gamma2 = mul_mod(gamma, gamma, P5);

        let ab = fold_claims("ab", &a, &b, gamma, P5).unwrap();
        let left = fold_claims("left-root", &ab, &c, gamma2, P5).unwrap();
        let bc = fold_claims("bc", &b, &c, gamma, P5).unwrap();
        let right = fold_claims("right-root", &a, &bc, gamma, P5).unwrap();
        assert_eq!(
            left.channel, right.channel,
            "roots are intentionally opaque"
        );

        let fg = fold_words(&X_WORD, &ONE_WORD, gamma, P5).unwrap();
        let left_word = fold_words(&fg, &ZERO_WORD, gamma2, P5).unwrap();
        let gh = fold_words(&ONE_WORD, &ZERO_WORD, gamma, P5).unwrap();
        let right_word = fold_words(&X_WORD, &gh, gamma, P5).unwrap();
        assert_eq!(left_word, right_word);
    }

    #[test]
    fn chain_helpers_match_manual_target_recurrence() {
        let a = eval_claim(2);
        let links = [eval_claim(1), eval_claim(4)];
        let challenges = [3, 4];
        let roots = ["r1", "r2"];
        let chain = fold_claim_chain(&a, &links, &challenges, &roots, P5).unwrap();
        let first = fold_claims("r1", &a, &links[0], 3, P5).unwrap();
        let manual = fold_claims("r2", &first, &links[1], 4, P5).unwrap();
        assert_eq!(chain, manual);

        let words = [ONE_WORD.to_vec(), ZERO_WORD.to_vec()];
        let chain_word = fold_word_chain(&X_WORD, &words, &challenges, P5).unwrap();
        let first_word = fold_words(&X_WORD, &ONE_WORD, 3, P5).unwrap();
        let manual_word = fold_words(&first_word, &ZERO_WORD, 4, P5).unwrap();
        assert_eq!(chain_word, manual_word);
    }

    #[test]
    fn malformed_shapes_and_unshared_channels_reject() {
        let malformed = AccClaim {
            root: (),
            word_len: 4,
            channel: vec![row(&[1, 2, 3], 0)],
        };
        assert!(matches!(
            malformed.validate(P5),
            Err(AccError::ConstraintWidth { row: 0, .. })
        ));

        let a = eval_claim(2);
        assert_eq!(
            a.channel_satisfied_by(&X_WORD[..3], P5),
            Err(AccError::WordWidth {
                expected: 4,
                actual: 3
            })
        );
        let different = AccClaim {
            root: "different",
            word_len: 4,
            channel: vec![row(&CONSV, 1)],
        };
        assert_eq!(
            fold_claims("fold", &a, &different, 2, P5),
            Err(AccError::UnsharedWeights { row: 0 })
        );
        assert!(matches!(
            fold_claims("fold", &a, &good_claim(P5), 2, P5),
            Err(AccError::ChannelLength { left: 1, right: 2 })
        ));
        assert!(matches!(
            fold_claim_chain(&a, &[], &[1], &[], P5),
            Err(AccError::ScheduleLength { .. })
        ));
    }

    #[test]
    fn noncanonical_values_and_challenges_reject() {
        let mut claim = eval_claim(2);
        claim.channel[0].weights[0] = P5;
        assert!(matches!(
            claim.validate(P5),
            Err(AccError::NonCanonical { what: "weight", .. })
        ));

        let a = eval_claim(2);
        assert!(matches!(
            batch_claim(&a, P5, P5),
            Err(AccError::NonCanonical {
                what: "batch challenge",
                ..
            })
        ));
        let mut bad_word = X_WORD;
        bad_word[0] = P5;
        assert!(matches!(
            a.channel_satisfied_by(&bad_word, P5),
            Err(AccError::NonCanonical { what: "word", .. })
        ));
        assert_eq!(a.validate(1), Err(AccError::InvalidModulus(1)));
    }

    #[test]
    fn empty_channel_batches_to_zero_constraint() {
        let empty = AccClaim {
            root: "empty",
            word_len: 3,
            channel: vec![],
        };
        let batched = batch_claim(&empty, 4, P5).unwrap();
        assert_eq!(batched.channel, vec![row(&[0, 0, 0], 0)]);
        assert!(batched.channel_satisfied_by(&[3, 2, 1], P5).unwrap());
    }
}
