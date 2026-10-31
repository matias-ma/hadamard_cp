import HadamardAppendix.Basic

/-! # Case 2: the polynomial certificate and the counting contradiction -/
namespace HadamardAppendix
open Finset Matrix

/-- The expanded expression for `Pⱼ` in the appendix. -/
noncomputable def certificate (x y a b : ℝ) : ℝ :=
  x * y + (x + y) * (a - b) - a ^ 2 + 2 * a * b + (b ^ 2 + 1) / 2

lemma certificate_factorization (x y a b : ℝ) :
    certificate x y a b =
      (x + a - b) * (y + a - b) - 2 * a ^ 2 + 4 * a * b - (b ^ 2 - 1) / 2 := by
  unfold certificate
  ring

/-- The six columns of the table in Case 2. -/
def AllowedSums (a b : ℝ) : Prop :=
  (a = 2 ∧ b = 3) ∨ (a = 0 ∧ b = 3) ∨ (a = 2 ∧ b = 1) ∨
  (a = -2 ∧ b = 3) ∨ (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = -1)

/-- All entries of the table, including the restrictions imposed by the
Schur bound, are verified by ordinary kernel-checked arithmetic. -/
theorem certificate_nonnegative {x y a b : ℝ}
    (hx : Sign x) (hy : Sign y) (hab : AllowedSums a b)
    (hxb : |x - (2 * a - b) / 3| ≤ 2)
    (hyb : |y - (2 * a - b) / 3| ≤ 2) :
    0 ≤ certificate x y a b := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [certificate, abs_le] at *

lemma certificate_first_pair : certificate (-1) (-1) 0 3 = 12 := by
  norm_num [certificate]
lemma certificate_first_complement : certificate 1 1 2 1 = 4 := by
  norm_num [certificate]
lemma certificate_all_positive {x y : ℝ} (hx : Sign x) (hy : Sign y) :
    12 ≤ certificate x y 2 3 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [certificate]

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cancellation identity `∑ Pⱼ = xyᵀ`. -/
theorem sum_certificate (x y a b : ι → ℝ)
    (hcross : ∑ j, (x j + y j) * (a j - b j) = 0)
    (hab : ∑ j, a j * b j = 0)
    (ha : ∑ j, a j ^ 2 = 2 * (Fintype.card ι : ℝ))
    (hb : ∑ j, b j ^ 2 = 3 * (Fintype.card ι : ℝ)) :
    ∑ j, certificate (x j) (y j) (a j) (b j) = ∑ j, x j * y j := by
  simp only [certificate, mul_assoc, sum_add_distrib, sum_sub_distrib,
    ← sum_div, ← mul_sum, sum_const, card_univ, nsmul_eq_mul,
    hcross, hab, ha, hb]
  ring

/-- The two special columns contribute `24`, the other three contribute
`12`, and all remaining columns contribute nonnegatively. -/
theorem certificate_sum_ge_36 (P : ι → ℝ) (A B : Finset ι)
    (hAB : Disjoint A B) (hA : A.card = 2) (hB : B.card = 3)
    (hpA : ∀ j ∈ A, P j = 12) (hpB : ∀ j ∈ B, P j = 4)
    (hp : ∀ j, j ∉ A ∪ B → 0 ≤ P j) :
    36 ≤ ∑ j, P j := by
  have hsumA : ∑ j ∈ A, P j = 24 := by
    rw [sum_congr rfl hpA]
    norm_num [hA]
  have hsumB : ∑ j ∈ B, P j = 12 := by
    rw [sum_congr rfl hpB]
    norm_num [hB]
  have hle : (∑ j ∈ A ∪ B, P j) ≤ ∑ j, P j := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro j _ hj
    exact hp j hj
  rw [sum_union hAB, hsumA, hsumB] at hle
  norm_num at hle
  exact hle

/-- Orthogonality plus the certificate forces the two rows to coincide,
and their common squared norm is at least 36. -/
theorem equal_rows_and_order {n : ℕ} (H : Hadamard n) (i k : Fin n)
    (hlower : 36 ≤ ∑ j, H.entry i j * H.entry k j) : i = k ∧ 36 ≤ n := by
  have heq : i = k := by
    by_contra h
    rw [H.rows, if_neg h] at hlower
    linarith
  constructor
  · exact heq
  · rw [H.rows, if_pos heq] at hlower
    exact_mod_cast hlower

/-- The moment equations for the number of rows with zero, one and two
minus signs. -/
theorem count_moments (t : ι → Fin 3)
    (henergy : ∑ i, (5 - 2 * (t i).val : ℝ) ^ 2 = 5 * (Fintype.card ι : ℝ)) :
    let N₀ := (univ.filter (fun i => t i = 0)).card
    let N₂ := (univ.filter (fun i => t i = 2)).card
    (N₂ : ℝ) = (Fintype.card ι : ℝ) / 2 + 2 * N₀ := by
  dsimp only
  have hp (i : ι) :
      (5 - 2 * (t i).val : ℝ) ^ 2 =
        9 + 16 * (if t i = 0 then (1 : ℝ) else 0) -
          8 * (if t i = 2 then (1 : ℝ) else 0) := by
    generalize t i = q
    fin_cases q <;> norm_num [Fin.ext_iff]
  simp_rw [hp] at henergy
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const,
    card_univ, nsmul_eq_mul] at henergy
  simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one] at henergy
  linarith

end

/-- There are ten possible pairs of minus positions. -/
lemma number_of_pairs : ((univ : Finset (Fin 5)).powersetCard 2).card = 10 := by
  decide

/-- The final counting contradiction in Case 2. The injection hypothesis
is supplied by `equal_rows_and_order` applied to the polynomial certificate. -/
theorem case_two_counting {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → Fin 3) (pair : ι → Finset (Fin 5))
    (hn : 0 < Fintype.card ι)
    (henergy : ∑ i, (5 - 2 * (t i).val : ℝ) ^ 2 = 5 * (Fintype.card ι : ℝ))
    (hcard : ∀ i, t i = 2 → (pair i).card = 2)
    (hinj : ∀ i k, t i = 2 → t k = 2 → pair i = pair k → i = k)
    (hlarge : ∀ i, t i = 2 → 36 ≤ Fintype.card ι) : False := by
  let S := univ.filter (fun i => t i = 2)
  have hS : S.card ≤ 10 := by
    calc
      S.card ≤ ((univ : Finset (Fin 5)).powersetCard 2).card := by
        apply card_le_card_of_injOn pair
        · intro i hi
          exact mem_powersetCard.mpr ⟨subset_univ _, hcard i (mem_filter.mp hi).2⟩
        · intro i hi k hk he
          exact hinj i k (mem_filter.mp hi).2 (mem_filter.mp hk).2 he
      _ = 10 := number_of_pairs
  have hm := count_moments t henergy
  change (S.card : ℝ) = _ at hm
  have hnreal : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hN₀ : (0 : ℝ) ≤ (univ.filter (fun i => t i = 0)).card := by positivity
  have hpos : 0 < S.card := by
    have : (0 : ℝ) < S.card := by linarith
    exact_mod_cast this
  obtain ⟨i, hi⟩ := card_pos.mp hpos
  have hbig := hlarge i (mem_filter.mp hi).2
  have hbigreal : (36 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hbig
  have hsmallreal : (S.card : ℝ) ≤ 10 := by exact_mod_cast hS
  linarith

end HadamardAppendix
