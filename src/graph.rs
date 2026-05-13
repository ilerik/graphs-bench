//! Directed graph in compressed-sparse-row (CSR) format with `f64` weights.

#[derive(Clone, Debug)]
pub struct Graph {
    pub n: usize,
    pub m: usize,
    /// `head[u] .. head[u+1]` gives the slice of edges originating at `u`.
    pub head: Vec<u32>,
    pub edge_to: Vec<u32>,
    pub edge_w: Vec<f64>,
}

impl Graph {
    pub fn from_edges(n: usize, edges: &[(u32, u32, f64)]) -> Self {
        let m = edges.len();
        let mut head = vec![0u32; n + 1];
        for &(u, _, _) in edges {
            head[u as usize + 1] += 1;
        }
        for i in 1..=n {
            head[i] += head[i - 1];
        }
        let mut edge_to = vec![0u32; m];
        let mut edge_w = vec![0.0f64; m];
        let mut cursor = head.clone();
        for &(u, v, w) in edges {
            let idx = cursor[u as usize] as usize;
            edge_to[idx] = v;
            edge_w[idx] = w;
            cursor[u as usize] += 1;
        }
        Graph {
            n,
            m,
            head,
            edge_to,
            edge_w,
        }
    }

    #[inline]
    pub fn out_edges(&self, u: usize) -> impl Iterator<Item = (u32, f64)> + '_ {
        let s = self.head[u] as usize;
        let e = self.head[u + 1] as usize;
        (s..e).map(move |i| (self.edge_to[i], self.edge_w[i]))
    }

    #[inline]
    pub fn out_degree(&self, u: usize) -> usize {
        (self.head[u + 1] - self.head[u]) as usize
    }
}
