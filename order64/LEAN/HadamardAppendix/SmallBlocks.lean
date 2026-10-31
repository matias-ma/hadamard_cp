import HadamardAppendix.Schur

/-! # Small-block steps appearing before the two contradiction arguments -/
set_option maxHeartbeats 1600000

namespace HadamardAppendix
open Finset Matrix

/-- An even sign prefix starting with +1 is a column of the normalized B. -/
lemma even_prefix_column (a b c : ℝ) (ha : Sign a) (hb : Sign b) (hc : Sign c)
    (heven : a * b * c = 1) : ∃ k : Fin 4, ![1, a, b, c] = fun j => B j k := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    norm_num at heven
  · refine ⟨0, ?_⟩; ext j; fin_cases j <;> rfl
  · refine ⟨2, ?_⟩; ext j; fin_cases j <;> rfl
  · refine ⟨1, ?_⟩; ext j; fin_cases j <;> rfl
  · refine ⟨3, ?_⟩; ext j; fin_cases j <;> rfl

/-- Two odd prefixes cannot give a fifth pivot of magnitude 2. This is
the parity argument allowing transposition in Case 1. -/
lemma odd_prefixes_not_two (a b c d e f ε : ℝ)
    (ha : Sign a) (hb : Sign b) (hc : Sign c) (hd : Sign d) (he : Sign e) (hf : Sign f)
    (hε : Sign ε) (hr : a * b * c = -1) (hc' : d * e * f = -1) :
    |ε - (![1, a, b, c] ⬝ᵥ (BInv *ᵥ ![1, d, e, f]))| ≠ 2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    norm_num at hr hc'
  all_goals rcases hε with rfl | rfl <;>
    norm_num [BInv, B, mulVec, dotProduct, Fin.sum_univ_succ, abs_le]

/-- The equality-in-Cauchy--Schwarz step in Case 2. The vector is B⁻¹c
and its squared norm is 1. The pivot identity forces every entry to be 1/2. -/
theorem case_two_equality (v : Fin 4 → ℝ)
    (hnorm : ∑ t, (v t) ^ 2 = 1)
    (hpivot : |(-1 : ℝ) - ∑ t, v t| = 3) : ∀ t, v t = 1 / 2 := by
  have hn : (v 0)^2 + (v 1)^2 + (v 2)^2 + (v 3)^2 = 1 := by
    simpa [Fin.sum_univ_four] using hnorm
  have hp : |(-1 : ℝ) - (v 0 + v 1 + v 2 + v 3)| = 3 := by
    simpa [Fin.sum_univ_four] using hpivot
  have hc : (v 0 + v 1 + v 2 + v 3)^2 ≤ 4 := by
    nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0 - v 2), sq_nonneg (v 0 - v 3),
      sq_nonneg (v 1 - v 2), sq_nonneg (v 1 - v 3), sq_nonneg (v 2 - v 3)]
  have hs : v 0 + v 1 + v 2 + v 3 = 2 := by
    rcases le_total 0 (-1 - (v 0 + v 1 + v 2 + v 3)) with h | h
    · rw [abs_of_nonneg h] at hp
      nlinarith
    · rw [abs_of_nonpos h] at hp
      linarith
  intro t
  have total : ∑ t, (v t - 1/2)^2 = 0 := by
    calc
      _ = (∑ t, (v t)^2) - (∑ t, v t) + 1 := by
        simp only [Fin.sum_univ_four]
        ring
      _ = 0 := by rw [hnorm]; simp only [Fin.sum_univ_four, hs]; norm_num
  have hsq : (v t - 1/2)^2 = 0 := by
    exact (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i - 1/2))).mp total t (mem_univ t)
  have hz := (sq_eq_zero_iff).mp hsq
  linarith

end HadamardAppendix
