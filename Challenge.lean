/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Moore graphs of diameter two: the Hoffman–Singleton theorem

A *Moore graph of diameter two* is a `k`-regular graph of diameter at most two and girth at least
five. For a finite graph on a nonempty vertex type:

* `HoffmanSingleton.card_le`: **Moore bound.** A `k`-regular graph of diameter at most two (Mathlib's
  `SimpleGraph.ediam`) has at most `k ^ 2 + 1` vertices.
* `HoffmanSingleton.card_eq`: a `k`-regular graph of diameter at most two and girth at least five
  (Mathlib's `SimpleGraph.egirth`) has exactly `k ^ 2 + 1` vertices.
* `HoffmanSingleton.isSRGWith`: such a graph is strongly regular with parameters
  `(k ^ 2 + 1, k, 0, 1)` (Mathlib's `SimpleGraph.IsSRGWith`).
* `HoffmanSingleton.hoffman_singleton`: **Hoffman–Singleton (1960).** If moreover `k ≥ 2`, then
  `k ∈ {2, 3, 7, 57}`.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open Finset SimpleGraph

namespace HoffmanSingleton

variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

/-- **Moore bound.** A finite `k`-regular graph of diameter at most two has at most `k ^ 2 + 1`
vertices. -/
theorem card_le {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2) :
    Fintype.card V ≤ k ^ 2 + 1 := by
  sorry

/-- A finite `k`-regular graph of diameter at most two and girth at least five has exactly
`k ^ 2 + 1` vertices. -/
theorem card_eq {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : Fintype.card V = k ^ 2 + 1 := by
  sorry

/-- A finite `k`-regular graph of diameter at most two and girth at least five is strongly
regular with parameters `(k ^ 2 + 1, k, 0, 1)`. -/
theorem isSRGWith {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : G.IsSRGWith (k ^ 2 + 1) k 0 1 := by
  sorry

/-- **Hoffman–Singleton theorem (1960).** If a finite `k`-regular graph with `k ≥ 2` has diameter
at most two and girth at least five (a Moore graph of diameter two), then
`k ∈ {2, 3, 7, 57}`. -/
theorem hoffman_singleton {k : ℕ} (hk : 2 ≤ k) (hreg : G.IsRegularOfDegree k)
    (hdiam : G.ediam ≤ 2) (hgirth : 5 ≤ G.egirth) : k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  sorry

end HoffmanSingleton
