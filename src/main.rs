//! Benchmark Dijkstra vs. BMSSP (Duan et al. 2025) on random directed graphs.
//!
//! For each `n` we time both algorithms on `seeds × trials` total runs and take
//! the median. We also show the "speedup gap" `(BMSSP/Dijkstra) · log^{1/3}(n)`:
//! if the predicted asymptotic is tight (Dijkstra `Θ(m log n)`, BMSSP
//! `Θ(m log^{2/3} n)`) and both share the same per-edge cache pattern, this
//! number should stay roughly constant — it equals the ratio of the two
//! algorithms' hidden constants. A *decrease* with `n` means BMSSP's
//! asymptotic edge is overtaking the constant.

use std::time::Instant;

use graphs_bench::bmssp::sssp_bmssp;
use graphs_bench::dijkstra::dijkstra;
use graphs_bench::graph::Graph;
use graphs_bench::random_graph::random_directed;

fn fmt_time(us: f64) -> String {
    if us < 1_000.0 {
        format!("{:>9.1} µs", us)
    } else if us < 1_000_000.0 {
        format!("{:>9.2} ms", us / 1_000.0)
    } else {
        format!("{:>9.3} s ", us / 1_000_000.0)
    }
}

fn compare_distances(a: &[f64], b: &[f64]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    for (x, y) in a.iter().zip(b.iter()) {
        if x.is_infinite() && y.is_infinite() {
            continue;
        }
        let diff = (x - y).abs();
        let tol = 1e-7 * x.abs().max(y.abs()).max(1.0);
        if diff > tol {
            return false;
        }
    }
    true
}

fn median(mut xs: Vec<f64>) -> f64 {
    xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    xs[xs.len() / 2]
}

fn time_us<F: FnMut()>(mut f: F, trials: usize) -> Vec<f64> {
    let mut us: Vec<f64> = Vec::with_capacity(trials);
    for _ in 0..trials {
        let t = Instant::now();
        f();
        us.push(t.elapsed().as_secs_f64() * 1.0e6);
    }
    us
}

struct Row {
    n: usize,
    m: usize,
    dij_us: f64,
    bmssp_us: f64,
    ok: bool,
}

fn bench_size(n: usize, m: usize, seeds: usize, trials: usize) -> Row {
    let mut all_dij = Vec::with_capacity(seeds * trials);
    let mut all_bm = Vec::with_capacity(seeds * trials);
    let mut all_ok = true;
    let mut real_m = m;

    for s in 0..seeds {
        let g: Graph = random_directed(n, m, 100_000 + s as u64);
        real_m = g.m;

        // Warmup + correctness check on this seed.
        let dij_dist = dijkstra(&g, 0);
        let bmssp_dist = sssp_bmssp(&g, 0);
        if !compare_distances(&dij_dist, &bmssp_dist) {
            all_ok = false;
        }

        all_dij.extend(time_us(
            || {
                let _ = dijkstra(&g, 0);
            },
            trials,
        ));
        all_bm.extend(time_us(
            || {
                let _ = sssp_bmssp(&g, 0);
            },
            trials,
        ));
    }

    Row {
        n,
        m: real_m,
        dij_us: median(all_dij),
        bmssp_us: median(all_bm),
        ok: all_ok,
    }
}

fn bmssp_levels(n: usize) -> usize {
    // Same parameter choice as `sssp_bmssp`.
    let log2_n = ((n as f64).max(2.0)).log2();
    let t = (log2_n.powf(2.0 / 3.0)).floor().max(1.0) as usize;
    ((log2_n / t as f64).ceil() as usize).max(1)
}

fn print_header() {
    // For each row we show raw times, the BMSSP/Dijkstra ratio, the
    // ratio rescaled by `log^{1/3}(n)` (= ratio of hidden constants if the
    // predicted asymptotic is tight), and a per-edge time for Dijkstra.
    println!(
        "{:>9}  {:>10}  {:>3}  {:>11}  {:>11}  {:>7}  {:>11}  {:>11}  match",
        "n",
        "m",
        "L",
        "Dijkstra",
        "BMSSP",
        "ratio",
        "ratio·log^⅓",
        "Dij ns/edge",
    );
    println!("{}", "-".repeat(102));
}

fn print_row(r: &Row) {
    let log2_n = (r.n.max(2) as f64).log2();
    let ratio = r.bmssp_us / r.dij_us;
    let asym_const = ratio * log2_n.powf(1.0 / 3.0);
    let dij_per_edge_ns = r.dij_us * 1_000.0 / r.m as f64;
    let levels = bmssp_levels(r.n);
    println!(
        "{:>9}  {:>10}  {:>3}  {}  {}  {:>5.2}x  {:>10.2}  {:>8.2} ns  {}",
        r.n,
        r.m,
        levels,
        fmt_time(r.dij_us),
        fmt_time(r.bmssp_us),
        ratio,
        asym_const,
        dij_per_edge_ns,
        if r.ok { "yes" } else { "NO" },
    );
}

fn run_sweep(name: &str, sizes: &[usize], degree: usize, seeds: usize, trials: usize) {
    println!("\n## {name}");
    print_header();
    for &n in sizes {
        let m = degree * n;
        let row = bench_size(n, m, seeds, trials);
        print_row(&row);
    }
}

fn main() {
    println!("Benchmark: Dijkstra vs. BMSSP (Duan/Mao/Mao/Shu/Yin 2025)");
    println!("Random directed graphs; weights uniform in (0, 1]; source = vertex 0.");
    println!("Each row: median over `seeds × trials` runs of (graph, algorithm).");
    println!("`ratio·log^⅓` is the BMSSP/Dijkstra ratio rescaled by the predicted");
    println!("asymptotic gap log^{{1/3}}(n); flat means we are in the asymptotic");
    println!("regime, decreasing means BMSSP is catching up faster than predicted.");

    // Sparse only: BMSSP's asymptotic edge over Dijkstra (a factor of
    // log^{1/3} n on n log n) is most visible when m = O(n).
    let sparse_sizes = [
        1_000usize,
        3_000,
        10_000,
        30_000,
        100_000,
        300_000,
        1_000_000,
        1_500_000,
        2_000_000,
        2_500_000,
        3_000_000,
        4_000_000,
    ];
    run_sweep(
        "Sparse  (avg out-degree = 4,  m = 4n)",
        &sparse_sizes,
        4,
        2,
        3,
    );
}
