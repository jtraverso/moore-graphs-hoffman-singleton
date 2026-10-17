/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Auxiliary lemmas for Moore graphs of diameter two

Helper results used in `MooreLib.MooreGraphs`: local structure forced by diameter at most two and girth
at least five, the radius-two ball count, the eigenvalue equation of the adjacency matrix of a
strongly regular graph with parameters `(n, k, 0, 1)`, and the final arithmetic step of the
Hoffman–Singleton argument.
-/

@[expose] public section

open Finset SimpleGraph Matrix

namespace MooreGraphs

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
theorem exists_common_of_ediam {u v : V} (hdiam : G.ediam ≤ 2) (huv : u ≠ v)
    (hadj : ¬G.Adj u v) : ∃ w, G.Adj u w ∧ G.Adj w v := by
  by_contra h
  have hempty : G.commonNeighbors u v = ∅ := by
    ext w
    simp only [mem_commonNeighbors, Set.mem_empty_iff_false, iff_false]
    exact fun ⟨h1, h2⟩ => h ⟨w, h1, h2.symm⟩
  have := (two_lt_edist_iff (G := G)).2 ⟨huv, hadj, hempty⟩
  exact absurd (edist_le_ediam.trans hdiam) (not_le.2 this)

omit [Fintype V] [DecidableRel G.Adj] in
theorem no_triangle (hgirth : 5 ≤ G.egirth) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) : False := by
  have hc : (Walk.cons hab (Walk.cons hbc (Walk.cons hca Walk.nil))).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    simp [Walk.cons_isPath_iff, hab.ne, hbc.ne, hca.ne, hab.ne.symm, hca.ne.symm]
  have := le_egirth.1 hgirth a _ hc
  simp at this
  norm_num at this

omit [Fintype V] [DecidableRel G.Adj] in
theorem no_square (hgirth : 5 ≤ G.egirth) {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have hc : (Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    simp [Walk.cons_isPath_iff, hab.ne, hbc.ne, hcd.ne, hda.ne, hab.ne.symm, hda.ne.symm, hac,
      hbd, hac.symm]
  have := le_egirth.1 hgirth a _ hc
  simp at this
  norm_num at this

theorem moore_count (k : ℕ) : 1 + (k + k * (k - 1)) = k ^ 2 + 1 := by
  cases k with
  | zero => rfl
  | succ k => simp; ring

/-- The ball of radius two around `v`, written as `{v} ∪ N(v) ∪ ⋃_{u ∈ N(v)} (N(u) \ {v})`. -/
noncomputable def ball2 [DecidableEq V] (v : V) : Finset V :=
  insert v (G.neighborFinset v ∪ (G.neighborFinset v).biUnion fun u => (G.neighborFinset u).erase v)

theorem ball2_eq_univ [DecidableEq V] (hdiam : G.ediam ≤ 2) (v : V) : ball2 G v = univ := by
  refine eq_univ_of_forall fun w => ?_
  simp only [ball2, mem_insert, mem_union, mem_neighborFinset, mem_biUnion, mem_erase]
  by_cases hwv : w = v
  · exact Or.inl hwv
  by_cases hadj : G.Adj v w
  · exact Or.inr (Or.inl hadj)
  obtain ⟨u, hvu, huw⟩ := exists_common_of_ediam G hdiam (Ne.symm hwv) hadj
  exact Or.inr (Or.inr ⟨u, hvu, hwv, huw⟩)

theorem card_ball2_le [DecidableEq V] {k : ℕ} (hreg : G.IsRegularOfDegree k) (v : V) :
    (ball2 G v).card ≤ k ^ 2 + 1 := by
  rw [← moore_count]
  refine (card_insert_le _ _).trans ?_
  rw [add_comm 1]
  refine Nat.add_le_add_right ((card_union_le _ _).trans ?_) 1
  refine Nat.add_le_add ?_ ((card_biUnion_le).trans ?_)
  · rw [card_neighborFinset_eq_degree, hreg v]
  · refine le_of_eq ?_
    calc ∑ u ∈ G.neighborFinset v, ((G.neighborFinset u).erase v).card
        = ∑ u ∈ G.neighborFinset v, (k - 1) := by
          refine sum_congr rfl fun u hu => ?_
          rw [card_erase_of_mem (by simpa [mem_neighborFinset] using
            (G.mem_neighborFinset v u).1 hu |>.symm), card_neighborFinset_eq_degree, hreg u]
      _ = k * (k - 1) := by rw [sum_const, card_neighborFinset_eq_degree, hreg v, smul_eq_mul]

theorem card_ball2_eq [DecidableEq V] {k : ℕ} (hreg : G.IsRegularOfDegree k)
    (hgirth : 5 ≤ G.egirth) (v : V) : (ball2 G v).card = k ^ 2 + 1 := by
  rw [← moore_count, ball2, card_insert_of_notMem, add_comm 1, card_union_of_disjoint,
    card_biUnion]
  · rw [card_neighborFinset_eq_degree, hreg v]
    congr 2
    calc ∑ u ∈ G.neighborFinset v, ((G.neighborFinset u).erase v).card
        = ∑ u ∈ G.neighborFinset v, (k - 1) := by
          refine sum_congr rfl fun u hu => ?_
          rw [card_erase_of_mem (by simpa [mem_neighborFinset] using
            (G.mem_neighborFinset v u).1 hu |>.symm), card_neighborFinset_eq_degree, hreg u]
      _ = k * (k - 1) := by rw [sum_const, card_neighborFinset_eq_degree, hreg v, smul_eq_mul]
  · intro u hu u' hu' huu'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [coe_neighborFinset, mem_neighborSet, mem_erase,
      mem_neighborFinset] at hu hu' hw hw'
    exact no_square G hgirth hu hw.2 hw'.2.symm hu'.symm hw.1.symm huu'
  · rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [mem_biUnion, mem_erase, mem_neighborFinset] at hw hw'
    obtain ⟨u, hu, -, huw⟩ := hw'
    exact no_triangle G hgirth hu huw hw.symm
  · simp only [mem_union, mem_biUnion, mem_erase, mem_neighborFinset, not_or, not_exists,
      not_and]
    exact ⟨G.loopless.irrefl v, fun u _ h => (h rfl).elim⟩

theorem final_arith {k : ℕ} (hk : 2 ≤ k) (d : ℤ) (h : (d : ℝ) * √(4 * k - 3) = k ^ 2 - 2 * k) :
    k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  rcases eq_or_ne d 0 with rfl | hd
  · left
    have h0 : ((k : ℝ) - 2) * k = 0 := by simp at h; linarith
    have hk' : (k : ℝ) ≠ 0 := by positivity
    have := (mul_eq_zero.1 h0).resolve_right hk'
    exact_mod_cast (by linarith : (k : ℝ) = 2)
  · right
    have hcast : ((4 * k - 3 : ℕ) : ℝ) = 4 * k - 3 := by
      push_cast [show 3 ≤ 4 * k by omega]; ring
    have hrat : ¬ Irrational √((4 * k - 3 : ℕ) : ℝ) := by
      rw [hcast]
      intro hirr
      have : √(4 * (k : ℝ) - 3) = ((((k : ℚ) ^ 2 - 2 * k) / d : ℚ) : ℝ) := by
        push_cast
        rw [eq_div_iff (by exact_mod_cast hd)]
        linarith
      exact hirr ⟨_, this.symm⟩
    rw [irrational_sqrt_natCast_iff, not_not] at hrat
    obtain ⟨t, ht⟩ := hrat
    rw [← hcast, ht] at h
    push_cast at h
    rw [Real.sqrt_mul_self (by positivity)] at h
    have hz : d * t = (k : ℤ) ^ 2 - 2 * k := by exact_mod_cast h
    have h4 : (4 * k : ℤ) = t * t + 3 := by omega
    have hdvd : (t : ℤ) ∣ 15 :=
      ⟨t ^ 3 - 2 * t - 16 * d, by linear_combination 16 * hz + (4 * k + t ^ 2 - 5) * h4⟩
    have hdvd' : t ∈ Nat.divisors 15 := Nat.mem_divisors.2 ⟨by exact_mod_cast hdvd, by norm_num⟩
    have h15 : Nat.divisors 15 = {1, 3, 5, 15} := by decide
    rw [h15] at hdvd'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdvd'
    rcases hdvd' with rfl | rfl | rfl | rfl <;> omega

theorem adjMatrix_sq_add_eq [DecidableEq V] {n k : ℕ} (hsrg : G.IsSRGWith n k 0 1) :
    adjMatrix ℝ G ^ 2 + adjMatrix ℝ G - ((k : ℝ) - 1) • (1 : Matrix V V ℝ) =
      Matrix.of fun _ _ => 1 := by
  rw [hsrg.matrix_eq]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.natCast_apply]
  · by_cases h : G.Adj i j <;> simp [hij, h, Matrix.one_apply_ne hij, Matrix.natCast_apply]

theorem eigen_cubic {n k : ℕ} (hsrg : G.IsSRGWith n k 0 1) {μ : ℝ}
    {x : V → ℝ} (hx0 : x ≠ 0) (hx : adjMatrix ℝ G *ᵥ x = μ • x) :
    (μ ^ 2 + μ - (k - 1)) * (μ - k) = 0 := by
  classical
  set A := adjMatrix ℝ G
  set c := μ ^ 2 + μ - (k - 1)
  have hB : (A ^ 2 + A - ((k : ℝ) - 1) • (1 : Matrix V V ℝ)) *ᵥ x = c • x := by
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, pow_two, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_smul, hx, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp [c, Pi.smul_apply]; ring
  rw [adjMatrix_sq_add_eq G hsrg] at hB
  have hconst : c • x = Function.const V (∑ j, x j) := by
    rw [← hB]; ext i; simp [Matrix.mulVec, dotProduct]
  have hAc : A *ᵥ (c • x) = (k : ℝ) • (c • x) := by
    rw [hconst]; ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact adjMatrix_mulVec_const_apply_of_regular hsrg.regular
  rw [Matrix.mulVec_smul, hx, smul_smul, smul_smul, ← sub_eq_zero, ← sub_smul] at hAc
  have := (smul_eq_zero.1 hAc).resolve_right hx0
  linear_combination this

omit [Fintype V] [DecidableRel G.Adj] in
theorem trace_sq_eq_sum {W : Type*} [Fintype W] [DecidableEq W] {A : Matrix W W ℝ}
    (hA : A.IsHermitian) : (A ^ 2).trace = ∑ i, hA.eigenvalues i ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp

end MooreGraphs
