import HadamardAppendix.Basic

namespace HadamardAppendix
open Finset Matrix

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Expand an inner product of two sums of rows. -/
lemma sum_rows_product (v : ι → κ → ℝ) (S T : Finset ι) :
    (∑ j, (∑ i ∈ S, v i j) * (∑ k ∈ T, v k j)) =
      ∑ i ∈ S, ∑ k ∈ T, ∑ j, v i j * v k j := by
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]

lemma sum_rows_energy (v : ι → κ → ℝ) (N : ℝ)
    (ho : ∀ i k, (∑ j, v i j * v k j) = if i = k then N else 0)
    (S : Finset ι) :
    ∑ j, (∑ i ∈ S, v i j) ^ 2 = S.card * N := by
  simp_rw [pow_two]
  rw [sum_rows_product]
  simp [ho]

lemma disjoint_rows_orthogonal (v : ι → κ → ℝ) (N : ℝ)
    (ho : ∀ i k, (∑ j, v i j * v k j) = if i = k then N else 0)
    (S T : Finset ι) (h : Disjoint S T) :
    ∑ j, (∑ i ∈ S, v i j) * (∑ k ∈ T, v k j) = 0 := by
  rw [sum_rows_product]
  apply sum_eq_zero
  intro i hi
  apply sum_eq_zero
  intro k hk
  rw [ho, if_neg]
  intro heq
  subst k
  exact disjoint_left.mp h hi hk

lemma row_orthogonal_sum (x : κ → ℝ) (v : ι → κ → ℝ) (S : Finset ι)
    (h : ∀ i ∈ S, ∑ j, x j * v i j = 0) :
    ∑ j, x j * (∑ i ∈ S, v i j) = 0 := by
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_eq_zero h

/-- Summing sign entries is equivalent to counting their minus positions. -/
lemma sum_signs (v : ι → ℝ) (hv : ∀ i, Sign (v i)) (S : Finset ι) :
    ∑ i ∈ S, v i = (S.card : ℝ) - 2 * (S.filter (fun i => v i = -1)).card := by
  have hp (i : ι) : v i = 1 - 2 * (if v i = -1 then (1 : ℝ) else 0) := by
    rcases hv i with h | h <;> norm_num [h]
  calc
    (∑ i ∈ S, v i) = ∑ i ∈ S, (1 - 2 * (if v i = -1 then (1 : ℝ) else 0)) :=
      sum_congr rfl (fun i _ => hp i)
    _ = _ := by
      simp only [sum_sub_distrib, ← mul_sum]
      rw [← sum_filter]
      simp

end
end HadamardAppendix
