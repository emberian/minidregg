//! Reproducible append-depth benchmark for the committed accumulator reference.
//!
//! This measures the implementation that exists, not the intended succinct
//! protocol: every accumulator proof carries all word values and all Merkle
//! paths, every append verifies both complete inputs, and RS membership is an
//! exhaustive inverse DFT.  Consequently the reported proof footprint is
//! `Theta(n log n)` field words and append work is at least linear in history
//! depth and quadratic in the word length.  These numbers are a reference-floor
//! baseline, never an RBR/folding-PCS performance claim.
//!
//! Examples:
//!
//! ```text
//! cargo run --release --bin committed_accumulator_bench
//! cargo run --release --bin committed_accumulator_bench -- \
//!   --log-domain 6 --depths 0,1,2,4,8,16,32,64 --csv
//! cargo run --release --bin committed_accumulator_bench -- \
//!   --log-domain 6 --depths 0,8,32 --retain-history --markdown
//! ```
//!
//! The driver launches one child process per depth so Linux `VmHWM` is a
//! per-case high-water mark rather than a cumulative artifact.  `--case` is an
//! internal/reproducibility mode that runs one case without spawning.

use std::env;
use std::fmt;
use std::fs;
use std::hint::black_box;
use std::process::Command;
use std::time::{Duration, Instant};

use minidregg_prover::accumulator::{AccClaim, LinearConstraint};
use minidregg_prover::committed_accumulator::{
    commit_claim, commit_fold_fs, verify_committed_claim, CommittedAccProof, CommittedAccRef,
    ReferenceRsCode,
};
use minidregg_prover::field4::{badd, bmul, two_adic_generator, P};
use minidregg_prover::poseidon::demo_spec;
use minidregg_prover::wide::{Digest, DIGEST_LIMBS};

const DEFAULT_DEPTHS: &[usize] = &[0, 1, 2, 4, 8, 16, 32, 64];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OutputFormat {
    Csv,
    Markdown,
    Row,
}

#[derive(Debug, Clone)]
struct Options {
    log_domain: u32,
    degree_bound: usize,
    depths: Vec<usize>,
    retain_history: bool,
    format: OutputFormat,
    case: Option<usize>,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            log_domain: 6,
            degree_bound: 2,
            depths: DEFAULT_DEPTHS.to_vec(),
            retain_history: false,
            format: OutputFormat::Markdown,
            case: None,
        }
    }
}

#[derive(Debug)]
struct CliError(String);

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Debug, Clone)]
struct ResultRow {
    host: String,
    depth: usize,
    word_len: usize,
    degree_bound: usize,
    retain_history: bool,
    setup: Duration,
    link_commit: Duration,
    fold: Duration,
    final_verify: Duration,
    max_rss_kib: Option<u64>,
    final_proof_field_words: usize,
    final_claim_field_words: usize,
    retained_history_field_words: usize,
}

fn usage() -> &'static str {
    "usage: committed_accumulator_bench [--log-domain N] [--degree-bound D] \
     [--depths D0,D1,...] [--retain-history] [--csv|--markdown]\n\
     internal: --case DEPTH --row"
}

fn parse_usize(flag: &str, value: Option<String>) -> Result<usize, CliError> {
    let value = value.ok_or_else(|| CliError(format!("{flag} needs a value")))?;
    value
        .parse()
        .map_err(|_| CliError(format!("invalid {flag} value {value:?}")))
}

fn parse_options() -> Result<Options, CliError> {
    let mut options = Options::default();
    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--log-domain" => {
                options.log_domain = parse_usize(&arg, args.next())?
                    .try_into()
                    .map_err(|_| CliError("log-domain does not fit u32".into()))?;
            }
            "--degree-bound" => options.degree_bound = parse_usize(&arg, args.next())?,
            "--depths" => {
                let raw = args
                    .next()
                    .ok_or_else(|| CliError("--depths needs a comma-separated value".into()))?;
                options.depths = raw
                    .split(',')
                    .map(|piece| {
                        piece
                            .parse()
                            .map_err(|_| CliError(format!("invalid depth {piece:?}")))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if options.depths.is_empty() {
                    return Err(CliError("--depths cannot be empty".into()));
                }
            }
            "--retain-history" => options.retain_history = true,
            "--csv" => options.format = OutputFormat::Csv,
            "--markdown" => options.format = OutputFormat::Markdown,
            "--row" => options.format = OutputFormat::Row,
            "--case" => options.case = Some(parse_usize(&arg, args.next())?),
            "--help" | "-h" => return Err(CliError(usage().into())),
            _ => return Err(CliError(format!("unknown argument {arg:?}\n{}", usage()))),
        }
    }
    if options.log_domain >= usize::BITS {
        return Err(CliError(format!(
            "log-domain {} exceeds this host's usize width",
            options.log_domain
        )));
    }
    let word_len = 1usize << options.log_domain;
    if options.degree_bound > word_len {
        return Err(CliError(format!(
            "degree-bound {} exceeds word length {word_len}",
            options.degree_bound
        )));
    }
    Ok(options)
}

fn hostname() -> String {
    env::var("HOSTNAME")
        .ok()
        .filter(|name| !name.is_empty())
        .or_else(|| {
            Command::new("hostname")
                .output()
                .ok()
                .filter(|output| output.status.success())
                .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
        })
        .unwrap_or_else(|| "unknown".into())
}

fn proc_status_kib(key: &str) -> Option<u64> {
    let status = fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|line| line.starts_with(key))?;
    line.split_whitespace().nth(1)?.parse().ok()
}

fn rs_word(log_domain: u32, constant: u64, linear: u64) -> Vec<u64> {
    let n = 1usize << log_domain;
    let generator = two_adic_generator(log_domain);
    let mut x = 1;
    let mut word = Vec::with_capacity(n);
    for _ in 0..n {
        word.push(badd(constant, bmul(linear, x)));
        x = bmul(x, generator);
    }
    word
}

fn eval_claim(word: &[u64], index: usize) -> AccClaim<()> {
    let mut weights = vec![0; word.len()];
    weights[index] = 1;
    AccClaim {
        root: (),
        word_len: word.len(),
        channel: vec![LinearConstraint {
            weights,
            target: word[index],
        }],
    }
}

fn make_committed(serial: usize, code: ReferenceRsCode) -> (AccClaim<Digest>, CommittedAccProof) {
    // Deterministic, distinct degree-1 words.  Mod reduction happens before
    // calling the canonical field operations.
    let constant = (3 + 17 * serial as u128) % P as u128;
    let linear = (5 + 29 * serial as u128) % P as u128;
    let word = rs_word(code.log_domain, constant as u64, linear as u64);
    let index = word.len() / 3;
    commit_claim(&eval_claim(&word, index), &word, code, &demo_spec(), P)
        .expect("deterministic degree-1 word must commit")
}

fn proof_field_words(proof: &CommittedAccProof) -> usize {
    proof
        .openings
        .iter()
        .map(|opening| 1 + opening.path.len() * DIGEST_LIMBS)
        .sum()
}

fn claim_field_words(claim: &AccClaim<Digest>) -> usize {
    DIGEST_LIMBS
        + claim
            .channel
            .iter()
            .map(|constraint| constraint.weights.len() + 1)
            .sum::<usize>()
}

fn run_case(options: &Options, depth: usize) -> ResultRow {
    let code = ReferenceRsCode {
        log_domain: options.log_domain,
        degree_bound: options.degree_bound,
    };
    let setup_start = Instant::now();
    let base = make_committed(0, code);
    let setup = setup_start.elapsed();
    let mut history = vec![base];
    let mut link_commit = Duration::ZERO;
    let mut fold = Duration::ZERO;

    for serial in 1..=depth {
        let start = Instant::now();
        let link = make_committed(serial, code);
        link_commit += start.elapsed();

        let current = history.last().expect("base accumulator exists");
        let start = Instant::now();
        let (_, claim, proof) = commit_fold_fs(
            CommittedAccRef {
                claim: &current.0,
                proof: &current.1,
            },
            CommittedAccRef {
                claim: &link.0,
                proof: &link.1,
            },
            code,
            &demo_spec(),
            P,
        )
        .expect("honest committed append must fold");
        fold += start.elapsed();

        if !options.retain_history {
            history.clear();
        }
        history.push((claim, proof));
    }

    let final_acc = history.last().expect("final accumulator exists");
    let verify_start = Instant::now();
    let accepted = verify_committed_claim(&final_acc.0, &final_acc.1, code, &demo_spec(), P);
    let final_verify = verify_start.elapsed();
    assert!(
        black_box(accepted),
        "final committed accumulator must verify"
    );

    let final_proof_field_words = proof_field_words(&final_acc.1);
    let final_claim_field_words = claim_field_words(&final_acc.0);
    let retained_history_field_words = history
        .iter()
        .map(|(claim, proof)| claim_field_words(claim) + proof_field_words(proof))
        .sum();
    ResultRow {
        host: hostname(),
        depth,
        word_len: 1usize << options.log_domain,
        degree_bound: options.degree_bound,
        retain_history: options.retain_history,
        setup,
        link_commit,
        fold,
        final_verify,
        max_rss_kib: proc_status_kib("VmHWM:"),
        final_proof_field_words,
        final_claim_field_words,
        retained_history_field_words,
    }
}

fn micros(duration: Duration) -> u128 {
    duration.as_micros()
}

fn csv_header() -> &'static str {
    "host,depth,word_len,degree_bound,retain_history,setup_us,link_commit_us,fold_us,final_verify_us,max_rss_kib,final_proof_field_words,final_claim_field_words,retained_history_field_words"
}

fn csv_row(row: &ResultRow) -> String {
    format!(
        "{},{},{},{},{},{},{},{},{},{},{},{},{}",
        row.host,
        row.depth,
        row.word_len,
        row.degree_bound,
        row.retain_history,
        micros(row.setup),
        micros(row.link_commit),
        micros(row.fold),
        micros(row.final_verify),
        row.max_rss_kib
            .map(|value| value.to_string())
            .unwrap_or_default(),
        row.final_proof_field_words,
        row.final_claim_field_words,
        row.retained_history_field_words,
    )
}

fn parse_row(line: &str) -> Result<ResultRow, CliError> {
    let fields: Vec<&str> = line.trim().split(',').collect();
    if fields.len() != 13 {
        return Err(CliError(format!("child emitted malformed row {line:?}")));
    }
    let number = |index: usize| -> Result<usize, CliError> {
        fields[index]
            .parse()
            .map_err(|_| CliError(format!("invalid numeric field in child row {line:?}")))
    };
    let duration = |index| number(index).map(|value| Duration::from_micros(value as u64));
    Ok(ResultRow {
        host: fields[0].to_owned(),
        depth: number(1)?,
        word_len: number(2)?,
        degree_bound: number(3)?,
        retain_history: fields[4] == "true",
        setup: duration(5)?,
        link_commit: duration(6)?,
        fold: duration(7)?,
        final_verify: duration(8)?,
        max_rss_kib: if fields[9].is_empty() {
            None
        } else {
            Some(number(9)? as u64)
        },
        final_proof_field_words: number(10)?,
        final_claim_field_words: number(11)?,
        retained_history_field_words: number(12)?,
    })
}

fn child_case(options: &Options, depth: usize) -> Result<ResultRow, CliError> {
    let executable = env::current_exe()
        .map_err(|error| CliError(format!("cannot locate benchmark executable: {error}")))?;
    let mut command = Command::new(executable);
    command
        .arg("--case")
        .arg(depth.to_string())
        .arg("--log-domain")
        .arg(options.log_domain.to_string())
        .arg("--degree-bound")
        .arg(options.degree_bound.to_string())
        .arg("--row");
    if options.retain_history {
        command.arg("--retain-history");
    }
    let output = command
        .output()
        .map_err(|error| CliError(format!("cannot run depth {depth}: {error}")))?;
    if !output.status.success() {
        return Err(CliError(format!(
            "depth {depth} failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    parse_row(&String::from_utf8_lossy(&output.stdout))
}

fn markdown(rows: &[ResultRow]) {
    println!("# Committed accumulator append-depth reference benchmark\n");
    println!(
        "> Exhaustive, non-succinct baseline: every proof contains every word value and every Merkle path; every append verifies both inputs and uses direct inverse-DFT RS membership. This is not an RBR/folding-PCS benchmark.\n"
    );
    println!(
        "| host | depth | n | d | retain history | setup ms | link commit ms | folds ms | final verify ms | max RSS KiB | final proof F-words | final claim F-words | retained F-words |"
    );
    println!("|---|---:|---:|---:|:---:|---:|---:|---:|---:|---:|---:|---:|---:|");
    for row in rows {
        println!(
            "| {} | {} | {} | {} | {} | {:.3} | {:.3} | {:.3} | {:.3} | {} | {} | {} | {} |",
            row.host,
            row.depth,
            row.word_len,
            row.degree_bound,
            row.retain_history,
            row.setup.as_secs_f64() * 1_000.0,
            row.link_commit.as_secs_f64() * 1_000.0,
            row.fold.as_secs_f64() * 1_000.0,
            row.final_verify.as_secs_f64() * 1_000.0,
            row.max_rss_kib
                .map(|value| value.to_string())
                .unwrap_or_else(|| "n/a".into()),
            row.final_proof_field_words,
            row.final_claim_field_words,
            row.retained_history_field_words,
        );
    }
    println!(
        "\n`F-word` counts canonical base-field elements only. Index/length metadata, allocator overhead, and Rust object headers are excluded; `max RSS` is Linux `/proc/self/status` `VmHWM` from a fresh child process per row."
    );
}

fn run() -> Result<(), CliError> {
    let options = parse_options()?;
    if let Some(depth) = options.case {
        println!("{}", csv_row(&run_case(&options, depth)));
        return Ok(());
    }

    let rows = options
        .depths
        .iter()
        .map(|&depth| child_case(&options, depth))
        .collect::<Result<Vec<_>, _>>()?;
    match options.format {
        OutputFormat::Csv | OutputFormat::Row => {
            println!("{}", csv_header());
            for row in &rows {
                println!("{}", csv_row(row));
            }
        }
        OutputFormat::Markdown => markdown(&rows),
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(2);
    }
}
