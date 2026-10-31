import HadamardAppendix.SmallBlocks
import HadamardAppendix.Orthogonality

namespace HadamardAppendix
open Finset Matrix

/-- Equality at the fifth pivot forces the normalized four-by-four block
to have all row and column sums equal to two. -/
theorem regular_four (M : Hadamard 4)
    (hp : |(-1 : ℝ) - (∑ a, ∑ b, M.entry a b) / 4| = 3) :
    (∀ b, ∑ a, M.entry a b = 2) ∧ (∀ a, ∑ b, M.entry a b = 2) := by
  let v := fun b => (∑ a, M.entry a b) / 4
  have henergy := sum_rows_energy M.entry 4 M.rows univ
  norm_num only [card_univ, Fintype.card_fin, Nat.cast_ofNat] at henergy
  have hvnorm : ∑ b, (v b)^2 = 1 := by
    simp only [v, div_pow, ← sum_div]
    norm_num
    nlinarith [henergy]
  have hvpivot : |(-1 : ℝ) - ∑ b, v b| = 3 := by
    simp only [v, ← sum_div]
    rw [sum_comm]
    exact hp
  have hv := case_two_equality v hvnorm hvpivot
  have hc (b : Fin 4) : ∑ a, M.entry a b = 2 := by
    have h := hv b
    change (∑ a, M.entry a b) / 4 = 1/2 at h
    linarith
  refine ⟨hc, ?_⟩
  intro a
  have h : (∑ k, ∑ b, M.entry a b * M.entry k b) = 4 := by
    simp [M.rows]
  rw [sum_comm] at h
  simp only [← mul_sum, hc, ← sum_mul] at h
  linarith

/-- Put the unique minus in each row on the diagonal. -/
theorem regular_four_permutation (M : Hadamard 4) (hr : ∀ a, ∑ b, M.entry a b = 2) :
    ∃ e : Equiv.Perm (Fin 4), ∀ a b, M.entry a (e b) = if a = b then -1 else 1 := by
  classical
  let S := fun a => univ.filter (fun b => M.entry a b = -1)
  have hcard (a : Fin 4) : (S a).card = 1 := by
    have h := sum_signs (M.entry a) (M.signs a) univ
    rw [hr a] at h
    norm_num only [card_univ, Fintype.card_fin, Nat.cast_ofNat] at h
    have heq : ((S a).card : ℝ) = 1 := by change (2 : ℝ) = 4 - 2 * (S a).card at h; linarith
    exact_mod_cast heq
  choose f hf using (fun a => card_eq_one.mp (hcard a))
  have hentry (a b : Fin 4) : M.entry a b = if b = f a then -1 else 1 := by
    by_cases h : b = f a
    · have hm : b ∈ S a := by rw [hf a]; simp [h]
      simpa only [if_pos h] using (mem_filter.mp hm).2
    · have hm : b ∉ S a := by rw [hf a]; simpa using h
      have hn : M.entry a b ≠ -1 := by simpa only [S, mem_filter, mem_univ, true_and] using hm
      rw [if_neg h]
      exact (M.signs a b).resolve_right hn
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have heq : M.entry a = M.entry b := by
      funext j
      rw [hentry, hentry, hab]
    have h := M.rows a b
    rw [← heq, M.rows, if_pos rfl, if_neg hne] at h
    norm_num at h
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨e, ?_⟩
  intro a b
  change M.entry a (f b) = _
  rw [hentry]
  simp only [hinj.eq_iff, eq_comm]

end HadamardAppendix
