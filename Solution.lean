/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import MooreLib.MooreGraphs

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `MooreLib/MooreGraphs.lean` and `MooreLib/MooreGraphsAux.lean`
(namespace `MooreGraphs`): the Moore bound by counting the ball of radius two around a vertex; the
equality and strong regularity from the absence of triangles and 4-cycles; and the Hoffman–Singleton
theorem from Mathlib's `IsSRGWith.matrix_eq` (giving A² + A − (k−1)I = J) and the spectral theorem:
trace identities show that the eigenvalue k is simple, and integrality of the multiplicities of
(−1 ± √(4k−3))/2 forces k = 2 or √(4k−3) ∣ 15.
-/

@[expose] public section

open Finset SimpleGraph

namespace HoffmanSingleton

variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

/-- **Moore bound.** A finite `k`-regular graph of diameter at most two has at most `k ^ 2 + 1`
vertices. -/
theorem card_le {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2) :
    Fintype.card V ≤ k ^ 2 + 1 :=
  MooreGraphs.card_le G hreg hdiam

/-- A finite `k`-regular graph of diameter at most two and girth at least five has exactly
`k ^ 2 + 1` vertices. -/
theorem card_eq {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : Fintype.card V = k ^ 2 + 1 :=
  MooreGraphs.card_eq G hreg hdiam hgirth

/-- A finite `k`-regular graph of diameter at most two and girth at least five is strongly
regular with parameters `(k ^ 2 + 1, k, 0, 1)`. -/
theorem isSRGWith {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : G.IsSRGWith (k ^ 2 + 1) k 0 1 :=
  MooreGraphs.isSRGWith G hreg hdiam hgirth

/-- **Hoffman–Singleton theorem (1960).** If a finite `k`-regular graph with `k ≥ 2` has diameter
at most two and girth at least five (a Moore graph of diameter two), then
`k ∈ {2, 3, 7, 57}`. -/
theorem hoffman_singleton {k : ℕ} (hk : 2 ≤ k) (hreg : G.IsRegularOfDegree k)
    (hdiam : G.ediam ≤ 2) (hgirth : 5 ≤ G.egirth) : k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 :=
  MooreGraphs.hoffman_singleton G hk hreg hdiam hgirth

end HoffmanSingleton
