# Moore graphs of diameter two: the Hoffman–Singleton theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A *Moore graph of diameter two* is a `k`-regular graph of diameter at most two and girth at least
five. All statements are in the namespace `HoffmanSingleton` and apply to finite graphs on a
nonempty vertex type:

1. `card_le`, the **Moore bound**. A `k`-regular graph of diameter at most two has at most
   `k² + 1` vertices.
2. `card_eq`. If the graph also has girth at least five, it has exactly `k² + 1` vertices.
3. `isSRGWith`. Such a graph is strongly regular with parameters `(k² + 1, k, 0, 1)`, in the sense
   of Mathlib's `IsSRGWith`.
4. `hoffman_singleton`, the **Hoffman–Singleton theorem (1960)**. If `k ≥ 2`, then
   `k ∈ {2, 3, 7, 57}`.

Examples exist for `k = 2` (the 5-cycle), `k = 3` (the Petersen graph) and `k = 7` (the
Hoffman–Singleton graph). Whether a Moore graph with `k = 57` exists is a famous open problem.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`MooreLib/`](MooreLib): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Moore bound.** Every vertex lies within distance two of a fixed vertex `v`. So the vertex set
  is `{v}`, together with the `k` neighbours of `v` and at most `k − 1` further neighbours of each
  of them.
* **Equality and strong regularity.** With girth at least five there are no triangles and no
  4-cycles. Then the pieces in the count above are disjoint, and two non-adjacent vertices have
  exactly one common neighbour.
* **Hoffman–Singleton.**
  1. From Mathlib's `IsSRGWith.matrix_eq`, the adjacency matrix satisfies `A² + A − (k − 1)I = J`.
     By the spectral theorem, every eigenvalue is `k` or a root of `x² + x − (k − 1)`.
  2. The traces `tr A = 0` and `tr A² = nk` show that the eigenvalue `k` is simple.
  3. If `4k − 3` is not a perfect square, the two roots `(−1 ± √(4k − 3))/2` must have equal
     multiplicities, which forces `k = 2`.
  4. Otherwise `√(4k − 3)` divides `15`, which gives `k ∈ {3, 7, 57}`.

## Sources

* A. J. Hoffman, R. R. Singleton, *On Moore graphs with diameters 2 and 3*, IBM J. Res. Dev. 4
  (1960) 497–504, doi:10.1147/rd.45.0497.

## Authorship and use of AI

The author chose the results. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
