import HadamardAppendix.Stage
import HadamardAppendix.NormalizedCaseTwo

namespace HadamardAppendix
open Finset Matrix

lemma sign_neg {a : ℝ} (ha : Sign a) : Sign (-a) := by
  rcases ha with rfl | rfl <;> norm_num [Sign]

/-- An odd-length sign sum has magnitude at least one. -/
lemma five_sign_sum (v : Fin 5 → ℝ) (hv : ∀ t, Sign (v t)) :
    1 ≤ |∑ t, v t| := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;>
    simp only [Fin.sum_univ_succ] <;>
    change 1 ≤ |v 0 + (v 1 + (v 2 + (v 3 + (v 4 + 0))))| <;>
    norm_num [h0, h1, h2, h3, h4]

noncomputable def majoritySign (s : ℝ) : ℝ := if s < 0 then -1 else 1
lemma majoritySign_sign (s : ℝ) : Sign (majoritySign s) := by
  unfold majoritySign
  split_ifs <;> norm_num [Sign]
lemma majoritySign_mul (s : ℝ) : majoritySign s * s = |s| := by
  unfold majoritySign
  split_ifs with h
  · simp [abs_of_neg h]
  · simp [abs_of_nonneg (le_of_not_gt h)]

noncomputable def residualFive {n : ℕ} (H : Hadamard n) (r c : Fin 5 ↪ Fin n)
    (i j : Fin n) : ℝ :=
  H.entry i j - ∑ t, ((∑ u, H.entry i (c u)) / 6 - H.entry i (c t) / 2) * H.entry (r t) j

/-- Negate only the remaining rows and columns to give each prefix at
most two minuses. The leading `J₅ - 2I₅` block stays fixed. -/
theorem case_two_from_F {n : ℕ} (H : Hadamard n) (r c : Fin 5 ↪ Fin n)
    (hF : ∀ t u, H.entry (r t) (c u) = if t = u then -1 else 1)
    (hbound : ∀ i j, |residualFive H r c i j| ≤ 2) : False := by
  let a := fun i => majoritySign (∑ t, H.entry i (c t))
  let b := fun j => majoritySign (∑ t, H.entry (r t) j)
  have hr (t : Fin 5) : (∑ u, H.entry (r t) (c u)) = 3 := by
    simp_rw [hF]
    have ht (u : Fin 5) : (if t = u then (-1 : ℝ) else 1) = 1 - 2 * (if t = u then 1 else 0) := by
      split_ifs <;> norm_num
    simp_rw [ht]
    norm_num [sum_sub_distrib, ← mul_sum]
  have hc (u : Fin 5) : (∑ t, H.entry (r t) (c u)) = 3 := by
    simp_rw [hF]
    have ht (t : Fin 5) : (if t = u then (-1 : ℝ) else 1) = 1 - 2 * (if t = u then 1 else 0) := by
      split_ifs <;> norm_num
    simp_rw [ht]
    norm_num [sum_sub_distrib, ← mul_sum]
  have har (t : Fin 5) : a (r t) = 1 := by simp [a, hr, majoritySign]
  have hbc (t : Fin 5) : b (c t) = 1 := by simp [b, hc, majoritySign]
  let K := H.signed a b (fun i => majoritySign_sign _) (fun j => majoritySign_sign _)
  have hrow (i : Fin n) : (∑ t, K.entry i (c t)) = a i * ∑ t, H.entry i (c t) := by
    simp only [K, Hadamard.signed, hbc, mul_one, mul_sum]
  have hcol (j : Fin n) : (∑ t, K.entry (r t) j) = b j * ∑ t, H.entry (r t) j := by
    simp only [K, Hadamard.signed, har, one_mul, ← sum_mul]
    ring
  have hs (i j : Fin n) : residualFive K r c i j = a i * b j * residualFive H r c i j := by
    simp only [residualFive, hrow, K, Hadamard.signed, har, hbc, mul_one, one_mul]
    simp only [mul_sub, mul_sum, mul_div_assoc, mul_assoc]
    congr 1
    · ring
    · apply sum_congr rfl
      intro t _
      rw [← mul_sum]
      ring
  let N : CaseTwoNormalForm n := {
    H := K, r := r, c := c,
    block := fun t u => by simp only [K, Hadamard.signed, har, hbc, one_mul, mul_one, hF],
    rowMajority := fun i => by
      rw [hrow, show a i = majoritySign (∑ t, H.entry i (c t)) from rfl, majoritySign_mul]
      exact five_sign_sum _ (fun t => H.signs _ _),
    colMajority := fun j => by
      rw [hcol, show b j = majoritySign (∑ t, H.entry (r t) j) from rfl, majoritySign_mul]
      exact five_sign_sum _ (fun t => H.signs _ _),
    schur := fun i j => by
      change |residualFive K r c i j| ≤ 2
      rw [hs, abs_mul, abs_mul, sign_abs (majoritySign_sign _), sign_abs (majoritySign_sign _)]
      simpa using hbound i j }
  exact N.impossible

end HadamardAppendix
