//! Partial-sorting data structure `D` from Lemma 3.3 of Duan et al.
//!
//! Supports three operations on `(key, value)` pairs where `key: u32` is a
//! vertex id and `value: f64` is a tentative distance:
//!
//!   * `insert(key, value)` — `O(max{1, log(N/M)})` amortised
//!   * `batch_prepend(items)` — `O(|items| · max{1, log(|items|/M)})` amortised,
//!     pre-condition that every value being prepended is strictly less than
//!     any value currently in the data structure.
//!   * `pull()` — returns up to `M` keys with the smallest values and a
//!     separator `x` such that every remaining value is `≥ x`. `O(|S'|)`
//!     amortised.
//!
//! The data lives in two block sequences:
//!   * `d0` for batch-prepended items (smaller values, at the front);
//!   * `d1` for inserted items, kept sorted by a block-level upper bound.
//!
//! We use a `best` map for lazy deletion: when a key is re-inserted with a
//! smaller value the old physical entry stays in its block but is skipped on
//! pull because its value no longer matches `best[key]`.

use std::collections::HashMap;

#[derive(Debug, Clone)]
struct Block {
    items: Vec<(u32, f64)>,
    /// Upper bound on values that may live in this block. Used by `d1` to
    /// binary-search the right block on insertion. For `d0` we just track the
    /// max value of the block.
    upper: f64,
}

#[derive(Debug)]
pub struct DStruct {
    m: usize,
    b: f64,
    d0: Vec<Block>,
    d1: Vec<Block>,
    /// Current best (smallest) value for each live key. `best.len()` is the
    /// number of logical entries in the structure.
    best: HashMap<u32, f64>,
}

impl DStruct {
    pub fn new(m: usize, b: f64) -> Self {
        let m = m.max(1);
        Self {
            m,
            b,
            d0: Vec::new(),
            d1: vec![Block {
                items: Vec::new(),
                upper: b,
            }],
            best: HashMap::new(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.best.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.best.is_empty()
    }

    pub fn insert(&mut self, key: u32, value: f64) {
        if let Some(&cur) = self.best.get(&key) {
            if cur <= value {
                return;
            }
        }
        self.best.insert(key, value);

        if self.d1.is_empty() {
            self.d1.push(Block {
                items: vec![(key, value)],
                upper: self.b,
            });
            return;
        }

        // Find the first d1 block whose upper bound is ≥ value (binary search).
        let mut lo = 0usize;
        let mut hi = self.d1.len();
        while lo < hi {
            let mid = (lo + hi) / 2;
            if self.d1[mid].upper >= value {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        // If value exceeds every block's upper (shouldn't happen for value < B),
        // pick the last block.
        let idx = if lo == self.d1.len() {
            self.d1.len() - 1
        } else {
            lo
        };
        self.d1[idx].items.push((key, value));
        if self.d1[idx].items.len() > self.m {
            self.split_d1_block(idx);
        }
    }

    fn split_d1_block(&mut self, idx: usize) {
        let original_upper = self.d1[idx].upper;
        let mut items = std::mem::take(&mut self.d1[idx].items);
        // Median split. We sort and slice in half; this is `O(M log M)` instead
        // of the `O(M)` median-of-medians used in the paper. It does not affect
        // correctness and keeps the constants small.
        items.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));
        let mid = items.len() / 2;
        let upper_half: Vec<(u32, f64)> = items.split_off(mid);
        let lower_half = items;
        let lower_upper = lower_half.last().map(|x| x.1).unwrap_or(f64::NEG_INFINITY);
        self.d1[idx] = Block {
            items: lower_half,
            upper: lower_upper,
        };
        self.d1.insert(
            idx + 1,
            Block {
                items: upper_half,
                upper: original_upper,
            },
        );
    }

    /// Insert a batch where every value is `<` everything currently in `D`.
    pub fn batch_prepend(&mut self, items: Vec<(u32, f64)>) {
        if items.is_empty() {
            return;
        }
        // 1) Deduplicate within the batch by keeping the smallest value per key.
        let mut dedup: HashMap<u32, f64> = HashMap::new();
        for (k, v) in items {
            let entry = dedup.entry(k).or_insert(f64::INFINITY);
            if *entry > v {
                *entry = v;
            }
        }
        // 2) Drop entries that are already dominated by `best[k]`.
        let mut filtered: Vec<(u32, f64)> = Vec::with_capacity(dedup.len());
        for (k, v) in dedup {
            if let Some(&cur) = self.best.get(&k) {
                if cur <= v {
                    continue;
                }
            }
            self.best.insert(k, v);
            filtered.push((k, v));
        }
        if filtered.is_empty() {
            return;
        }

        if filtered.len() <= self.m {
            let upper = filtered
                .iter()
                .map(|x| x.1)
                .fold(f64::NEG_INFINITY, f64::max);
            self.d0.insert(
                0,
                Block {
                    items: filtered,
                    upper,
                },
            );
            return;
        }

        // Split into chunks of ⌈m/2⌉ following the paper.
        filtered.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));
        let chunk = self.m.div_ceil(2).max(1);
        let mut new_blocks: Vec<Block> = Vec::with_capacity(filtered.len() / chunk + 1);
        for slice in filtered.chunks(chunk) {
            let items = slice.to_vec();
            let upper = items.last().unwrap().1;
            new_blocks.push(Block { items, upper });
        }
        // Prepend in order (block 0 of new_blocks has the smallest values).
        let mut combined = new_blocks;
        combined.append(&mut self.d0);
        self.d0 = combined;
    }

    /// Return up to `M` keys whose values are smallest, and a separator
    /// `x ≤ B` with `max(returned) < x ≤ min(remaining)`. If the data
    /// structure becomes empty, returns `(B, ...)`.
    pub fn pull(&mut self) -> (f64, Vec<u32>) {
        // Following Lemma 3.3: scan prefix blocks of D0 and D1 **separately**
        // until each has at least M valid items (or is exhausted). The block
        // sort invariant guarantees that the M globally-smallest values are
        // among the candidates we collect this way.
        let mut s0: Vec<(u32, f64, usize, usize)> = Vec::new();
        let mut s1: Vec<(u32, f64, usize, usize)> = Vec::new();
        let mut consumed_d0 = 0usize;
        let mut consumed_d1 = 0usize;

        while consumed_d0 < self.d0.len() && s0.len() < self.m {
            let block_idx = consumed_d0;
            for (item_idx, &(k, v)) in self.d0[block_idx].items.iter().enumerate() {
                if self.best.get(&k) == Some(&v) {
                    s0.push((k, v, block_idx, item_idx));
                }
            }
            consumed_d0 += 1;
        }
        while consumed_d1 < self.d1.len() && s1.len() < self.m {
            let block_idx = consumed_d1;
            for (item_idx, &(k, v)) in self.d1[block_idx].items.iter().enumerate() {
                if self.best.get(&k) == Some(&v) {
                    s1.push((k, v, block_idx, item_idx));
                }
            }
            consumed_d1 += 1;
        }

        // 0 = came from D0, 1 = came from D1.
        let mut combined: Vec<(u32, f64, u8, usize, usize)> =
            Vec::with_capacity(s0.len() + s1.len());
        for (k, v, b, i) in s0 {
            combined.push((k, v, 0, b, i));
        }
        for (k, v, b, i) in s1 {
            combined.push((k, v, 1, b, i));
        }

        if combined.len() <= self.m {
            // We can take everything we found. Drain all consumed blocks.
            for &(k, _, _, _, _) in &combined {
                self.best.remove(&k);
            }
            let keys: Vec<u32> = combined.iter().map(|x| x.0).collect();
            if consumed_d0 > 0 {
                self.d0.drain(0..consumed_d0);
            }
            if consumed_d1 > 0 {
                self.d1.drain(0..consumed_d1);
            }
            let separator = self.smallest_remaining_value().unwrap_or(self.b);
            return (separator, keys);
        }

        // Select the M smallest values.
        combined.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));
        let selected: Vec<(u32, f64, u8, usize, usize)> = combined.drain(0..self.m).collect();

        // Remove the selected items from their original blocks (swap-remove
        // keeps blocks intact; per-block within-block order doesn't matter).
        let mut per_block_removes_d0: Vec<Vec<usize>> =
            (0..consumed_d0).map(|_| Vec::new()).collect();
        let mut per_block_removes_d1: Vec<Vec<usize>> =
            (0..consumed_d1).map(|_| Vec::new()).collect();
        for &(k, _, src, b, i) in &selected {
            self.best.remove(&k);
            if src == 0 {
                per_block_removes_d0[b].push(i);
            } else {
                per_block_removes_d1[b].push(i);
            }
        }
        let keys: Vec<u32> = selected.iter().map(|x| x.0).collect();
        for (b, mut removes) in per_block_removes_d0.into_iter().enumerate() {
            removes.sort_unstable();
            for &i in removes.iter().rev() {
                self.d0[b].items.swap_remove(i);
            }
        }
        for (b, mut removes) in per_block_removes_d1.into_iter().enumerate() {
            removes.sort_unstable();
            for &i in removes.iter().rev() {
                self.d1[b].items.swap_remove(i);
            }
        }

        // Separator: the smallest live value still in D. Note this may be in
        // an unscanned tail block (which can hold values smaller than items
        // we put into `leftover` if the cross-list ordering is not strict).
        let separator = self.smallest_remaining_value().unwrap_or(self.b);

        (separator, keys)
    }

    /// Smallest non-stale value currently in `D`, or `None` if `D` is empty.
    ///
    /// Each list (`d0` and `d1`) is internally sorted across blocks, so its
    /// own min lives in its first block that has any non-stale entry. The
    /// cross-list ordering is **not** guaranteed (batch-prepend and insert
    /// can interleave values), so we must check both lists and take the
    /// smaller min.
    fn smallest_remaining_value(&self) -> Option<f64> {
        let mut min_overall = f64::INFINITY;
        for block in &self.d0 {
            let mut block_min = f64::INFINITY;
            for &(k, v) in &block.items {
                if self.best.get(&k) == Some(&v) && v < block_min {
                    block_min = v;
                }
            }
            if block_min.is_finite() {
                if block_min < min_overall {
                    min_overall = block_min;
                }
                break;
            }
        }
        for block in &self.d1 {
            let mut block_min = f64::INFINITY;
            for &(k, v) in &block.items {
                if self.best.get(&k) == Some(&v) && v < block_min {
                    block_min = v;
                }
            }
            if block_min.is_finite() {
                if block_min < min_overall {
                    min_overall = block_min;
                }
                break;
            }
        }
        if min_overall.is_finite() {
            Some(min_overall)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_pull_order() {
        let mut d = DStruct::new(2, 100.0);
        d.insert(1, 5.0);
        d.insert(2, 1.0);
        d.insert(3, 9.0);
        d.insert(4, 3.0);
        let (sep, keys) = d.pull();
        assert_eq!(keys.len(), 2);
        // Two smallest values are 1.0 (key=2) and 3.0 (key=4)
        let mut keys_sorted = keys.clone();
        keys_sorted.sort();
        assert_eq!(keys_sorted, vec![2, 4]);
        assert!(sep > 3.0 && sep <= 5.0);
    }

    #[test]
    fn batch_prepend_pulled_first() {
        let mut d = DStruct::new(2, 100.0);
        d.insert(10, 50.0);
        d.insert(11, 60.0);
        d.batch_prepend(vec![(20, 1.0), (21, 2.0), (22, 3.0)]);
        let (_sep, keys) = d.pull();
        let mut sorted = keys.clone();
        sorted.sort();
        // Two smallest globally are 1.0 (20) and 2.0 (21).
        assert_eq!(sorted, vec![20, 21]);
    }

    #[test]
    fn dedup_keeps_smallest() {
        let mut d = DStruct::new(4, 100.0);
        d.insert(7, 10.0);
        d.insert(7, 3.0);
        d.insert(7, 20.0);
        let (_sep, keys) = d.pull();
        assert_eq!(keys, vec![7]);
        assert!(d.is_empty());
    }

    #[test]
    fn pull_until_empty() {
        let mut d = DStruct::new(3, 100.0);
        for k in 0u32..10 {
            d.insert(k, k as f64);
        }
        let mut all_keys = Vec::new();
        while !d.is_empty() {
            let (_sep, keys) = d.pull();
            all_keys.extend(keys);
        }
        all_keys.sort();
        assert_eq!(all_keys, (0u32..10).collect::<Vec<_>>());
    }
}
