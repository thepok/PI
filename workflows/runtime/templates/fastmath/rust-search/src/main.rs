// Copy with: workflows/runtime/fastmath.sh new rust work/my_search
// Run with:  workflows/runtime/fastmath.sh rust work/my_search/Cargo.toml -- --self-test

use std::env;
use std::time::Instant;

#[derive(Debug, PartialEq, Eq)]
struct ResultRow {
    processed: u64,
    checksum: u64,
}

fn run_search(limit: u64) -> ResultRow {
    let mut result = ResultRow {
        processed: 0,
        checksum: 0,
    };
    for state in 0..limit {
        // Deliberately simple known-answer kernel. Replace this expression.
        result.checksum = result.checksum.wrapping_add(state.wrapping_mul(state));
        result.processed += 1;
    }
    result
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let self_test = args.iter().any(|arg| arg == "--self-test");
    let limit = args
        .windows(2)
        .find(|pair| pair[0] == "--limit")
        .map(|pair| pair[1].parse::<u64>().expect("invalid --limit"))
        .unwrap_or(10_000_000);

    if self_test {
        let tiny = run_search(10);
        assert_eq!(
            tiny,
            ResultRow {
                processed: 10,
                checksum: 285
            }
        );
        println!(r#"{{"self_test":true,"processed":10,"checksum":285}}"#);
        return;
    }

    let started = Instant::now();
    let result = run_search(limit);
    println!(
        r#"{{"claim_label":"experiment","processed":{},"checksum":{},"seconds":{:.6}}}"#,
        result.processed,
        result.checksum,
        started.elapsed().as_secs_f64()
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_tiny_sum_of_squares() {
        assert_eq!(
            run_search(10),
            ResultRow {
                processed: 10,
                checksum: 285
            }
        );
    }
}
