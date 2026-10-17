/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import MooreLib.MooreGraphsAux

/-!
# Moore graphs of diameter two: the Hoffman–Singleton theorem

A *Moore graph of diameter two* is a `k`-regular graph of diameter at most two and girth at least
five. For a finite graph on a nonempty vertex type:

* `MooreGraphs.card_le`: **Moore bound.** A `k`-regular graph of diameter at most two (Mathlib's
  `SimpleGraph.ediam`) has at most `k ^ 2 + 1` vertices.
* `MooreGraphs.card_eq`: a `k`-regular graph of diameter at most two and girth at least five
  (Mathlib's `SimpleGraph.egirth`) has exactly `k ^ 2 + 1` vertices.
* `MooreGraphs.isSRGWith`: such a graph is strongly regular with parameters
  `(k ^ 2 + 1, k, 0, 1)` (Mathlib's `SimpleGraph.IsSRGWith`).
* `MooreGraphs.hoffman_singleton`: **Hoffman–Singleton (1960).** If moreover `k ≥ 2`, then
  `k ∈ {2, 3, 7, 57}`.
-/

@[expose] public section

open Finset SimpleGraph

namespace MooreGraphs

variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

/-- **Moore bound.** A finite `k`-regular graph of diameter at most two has at most `k ^ 2 + 1`
vertices. -/
theorem card_le {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2) :
    Fintype.card V ≤ k ^ 2 + 1 := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [← card_univ, ← ball2_eq_univ G hdiam v]
  exact card_ball2_le G hreg v

/-- A finite `k`-regular graph of diameter at most two and girth at least five has exactly
`k ^ 2 + 1` vertices. -/
theorem card_eq {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : Fintype.card V = k ^ 2 + 1 := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [← card_univ, ← ball2_eq_univ G hdiam v]
  exact card_ball2_eq G hreg hgirth v

/-- A finite `k`-regular graph of diameter at most two and girth at least five is strongly
regular with parameters `(k ^ 2 + 1, k, 0, 1)`. -/
theorem isSRGWith {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : G.IsSRGWith (k ^ 2 + 1) k 0 1 := by
  refine ⟨card_eq G hreg hdiam hgirth, hreg, fun v w h => ?_, fun v w hvw h => ?_⟩
  · rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    rw [mem_commonNeighbors] at hx
    exact no_triangle G hgirth h hx.2 hx.1.symm
  · rw [Fintype.card_eq_one_iff]
    obtain ⟨x, hvx, hxw⟩ := exists_common_of_ediam G hdiam hvw h
    refine ⟨⟨x, (G.mem_commonNeighbors).2 ⟨hvx, hxw.symm⟩⟩, fun ⟨y, hy⟩ => ?_⟩
    rw [mem_commonNeighbors] at hy
    by_contra hne
    have hxy : y ≠ x := fun e => hne (Subtype.ext e)
    exact no_square G hgirth hvx hxw hy.2 hy.1.symm hvw hxy.symm

/-- **Hoffman–Singleton theorem (1960).** If a finite `k`-regular graph with `k ≥ 2` has diameter
at most two and girth at least five (a Moore graph of diameter two), then
`k ∈ {2, 3, 7, 57}`. -/
theorem hoffman_singleton {k : ℕ} (hk : 2 ≤ k) (hreg : G.IsRegularOfDegree k)
    (hdiam : G.ediam ≤ 2) (hgirth : 5 ≤ G.egirth) : k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  classical
  have hsrg := isSRGWith G hreg hdiam hgirth
  have hA : (adjMatrix ℝ G).IsHermitian := isHermitian_adjMatrix (R := ℝ) G
  set ev := hA.eigenvalues
  have hcard : (Fintype.card V : ℝ) = k ^ 2 + 1 := by exact_mod_cast hsrg.card
  have hcub : ∀ i, (ev i ^ 2 + ev i - (k - 1)) * (ev i - k) = 0 := fun i =>
    eigen_cubic G hsrg (x := (hA.eigenvectorBasis i).ofLp)
      ((WithLp.ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i)
      (hA.mulVec_eigenvectorBasis i)
  have htr1 : ∑ i, ev i = 0 := by
    have := hA.trace_eq_sum_eigenvalues
    rw [trace_adjMatrix] at this
    simpa using this.symm
  have htr2 : ∑ i, ev i ^ 2 = (k ^ 2 + 1) * k := by
    rw [← trace_sq_eq_sum hA, pow_two, Matrix.trace]
    simp only [Matrix.diag_apply, adjMatrix_mul_self_apply_self, hreg.degree_eq]
    simp [hcard]
  set g : V → ℝ := fun i => if ev i = k then 1 else 0
  have hf : ∀ i, ev i ^ 2 + ev i - (k - 1) = (k ^ 2 + 1) * g i := by
    intro i
    by_cases h : ev i = k
    · simp only [g, h, ite_true]; ring
    · simp only [g, h, ite_false, mul_zero]
      exact (mul_eq_zero.1 (hcub i)).resolve_right (sub_ne_zero.2 h)
  have hg : ∑ i, g i = 1 := by
    have h1 : ∑ i, (ev i ^ 2 + ev i - (k - 1)) = (k ^ 2 + 1) * ∑ i, g i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hf i
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, htr1, htr2, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hcard] at h1
    have hpos : (k : ℝ) ^ 2 + 1 ≠ 0 := by positivity
    exact mul_left_cancel₀ hpos (h1.symm.trans (by ring : _ = ((k : ℝ) ^ 2 + 1) * 1))
  set s := √(4 * (k : ℝ) - 3)
  have hs : s ^ 2 = 4 * k - 3 := Real.sq_sqrt (by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith)
  set ε : V → ℤ := fun i => if ev i = k then 0 else if 2 * ev i + 1 = s then 1 else -1
  have hε : ∀ i, 2 * ev i + 1 = ε i * s + (2 * k + 1) * g i := by
    intro i
    by_cases h : ev i = k
    · simp [ε, g, h]
    · have hq : ev i ^ 2 + ev i - (k - 1) = 0 :=
        (mul_eq_zero.1 (hcub i)).resolve_right (sub_ne_zero.2 h)
      have hsq : (2 * ev i + 1) ^ 2 = s ^ 2 := by rw [hs]; linear_combination 4 * hq
      by_cases h' : 2 * ev i + 1 = s
      · simp [ε, g, h, h']
      · have : 2 * ev i + 1 = -s := ((sq_eq_sq_iff_eq_or_eq_neg).1 hsq).resolve_left h'
        simp [ε, g, h, this]
  have hsum : ∑ i, (2 * ev i + 1) = ((∑ i, ε i : ℤ) : ℝ) * s + (2 * k + 1) := by
    rw [Finset.sum_congr rfl fun i _ => hε i, Finset.sum_add_distrib, ← Finset.mul_sum, hg,
      ← Finset.sum_mul]
    push_cast; ring
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, htr1, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hcard] at hsum
  exact final_arith hk (∑ i, ε i) (by linear_combination -hsum)

end MooreGraphs
