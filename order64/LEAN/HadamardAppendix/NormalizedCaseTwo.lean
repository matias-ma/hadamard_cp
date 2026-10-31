import HadamardAppendix.CaseTwo
import HadamardAppendix.Orthogonality
import Mathlib.Tactic.IntervalCases

namespace HadamardAppendix
open Finset Matrix

/-- The matrix situation after the sign changes in Case 2. `schur` uses
exactly the displayed inverse `(1/6)J - (1/2)I`. Bounds include the leading
zero rows and columns, so no index subtraction is needed. -/
structure CaseTwoNormalForm (n : ℕ) where
  H : Hadamard n
  r : Fin 5 ↪ Fin n
  c : Fin 5 ↪ Fin n
  block : ∀ t u, H.entry (r t) (c u) = if t = u then -1 else 1
  rowMajority : ∀ i, 1 ≤ ∑ t, H.entry i (c t)
  colMajority : ∀ j, 1 ≤ ∑ t, H.entry (r t) j
  schur : ∀ i j,
    |H.entry i j - ∑ t, ((∑ u, H.entry i (c u)) / 6 - H.entry i (c t) / 2) *
      H.entry (r t) j| ≤ 2

namespace CaseTwoNormalForm
variable {n : ℕ} (D : CaseTwoNormalForm n)

noncomputable def minus (i : Fin n) : Finset (Fin 5) :=
  univ.filter (fun t => D.H.entry i (D.c t) = -1)

lemma minus_sum (i : Fin n) :
    ∑ t, D.H.entry i (D.c t) = 5 - 2 * (D.minus i).card := by
  simpa [minus] using sum_signs (fun t => D.H.entry i (D.c t))
    (fun t => D.H.signs i (D.c t)) univ

lemma minus_le_two (i : Fin n) : (D.minus i).card ≤ 2 := by
  have h := D.rowMajority i
  rw [D.minus_sum] at h
  have : ((D.minus i).card : ℝ) < 3 := by linarith
  have hlt : (D.minus i).card < 3 := by exact_mod_cast this
  omega

lemma entry_of_minus (i : Fin n) (t : Fin 5) :
    D.H.entry i (D.c t) = if t ∈ D.minus i then -1 else 1 := by
  rcases D.H.signs i (D.c t) with h | h <;> norm_num [minus, h]

lemma leading_minus (t : Fin 5) : D.minus (D.r t) = {t} := by
  ext u
  simp only [minus, mem_filter, mem_univ, true_and, mem_singleton]
  rw [D.block]
  by_cases h : t = u
  · simp [h]
  · norm_num [h, Ne.symm h]

lemma two_minus_not_leading (i : Fin n) (hi : (D.minus i).card = 2)
    (t : Fin 5) : i ≠ D.r t := by
  intro h
  rw [h, D.leading_minus, card_singleton] at hi
  omega

noncomputable def a (A : Finset (Fin 5)) (j : Fin n) : ℝ := ∑ t ∈ A, D.H.entry (D.r t) j
noncomputable def b (A : Finset (Fin 5)) (j : Fin n) : ℝ := ∑ t ∈ Aᶜ, D.H.entry (D.r t) j

lemma a_add_b (A : Finset (Fin 5)) (j : Fin n) :
    D.a A j + D.b A j = ∑ t, D.H.entry (D.r t) j := by
  exact sum_add_sum_compl A _

lemma allowed (A : Finset (Fin 5)) (hA : A.card = 2) (j : Fin n) :
    AllowedSums (D.a A j) (D.b A j) := by
  have hB : Aᶜ.card = 3 := by simp [card_compl, hA]
  have ha := sum_signs (fun t => D.H.entry (D.r t) j)
    (fun t => D.H.signs (D.r t) j) A
  have hb := sum_signs (fun t => D.H.entry (D.r t) j)
    (fun t => D.H.signs (D.r t) j) Aᶜ
  change D.a A j = _ at ha
  change D.b A j = _ at hb
  rw [hA] at ha
  rw [hB] at hb
  have hma : (A.filter (fun t => D.H.entry (D.r t) j = -1)).card ≤ 2 :=
    le_trans (card_filter_le _ _) (le_of_eq hA)
  have hmb : (Aᶜ.filter (fun t => D.H.entry (D.r t) j = -1)).card ≤ 3 :=
    le_trans (card_filter_le _ _) (le_of_eq hB)
  have htotal : 1 ≤ D.a A j + D.b A j := by rw [D.a_add_b]; exact D.colMajority j
  generalize (A.filter (fun t => D.H.entry (D.r t) j = -1)).card = ma at *
  generalize (Aᶜ.filter (fun t => D.H.entry (D.r t) j = -1)).card = mb at *
  interval_cases ma <;> interval_cases mb <;>
    norm_num at ha hb <;> simp_all [AllowedSums] <;> linarith

lemma projection (i : Fin n) (hi : (D.minus i).card = 2) (j : Fin n) :
    (∑ t, ((∑ u, D.H.entry i (D.c u)) / 6 - D.H.entry i (D.c t) / 2) *
      D.H.entry (D.r t) j) = (2 * D.a (D.minus i) j - D.b (D.minus i) j) / 3 := by
  have hs : ∑ u, D.H.entry i (D.c u) = 1 := by rw [D.minus_sum, hi]; norm_num
  rw [hs, ← sum_add_sum_compl (D.minus i)]
  have hp : ∀ t ∈ D.minus i,
      (1 / 6 - D.H.entry i (D.c t) / 2) * D.H.entry (D.r t) j =
        (2 / 3 : ℝ) * D.H.entry (D.r t) j := by
    intro t ht
    rw [D.entry_of_minus, if_pos ht]
    ring
  have hq : ∀ t ∈ (D.minus i)ᶜ,
      (1 / 6 - D.H.entry i (D.c t) / 2) * D.H.entry (D.r t) j =
        -(1 / 3 : ℝ) * D.H.entry (D.r t) j := by
    intro t ht
    rw [D.entry_of_minus, if_neg (mem_compl.mp ht)]
    ring
  rw [sum_congr rfl hp, sum_congr rfl hq, ← mul_sum, ← mul_sum]
  change (2 / 3 : ℝ) * D.a (D.minus i) j + -(1 / 3 : ℝ) * D.b (D.minus i) j = _
  ring

lemma row_orth (i : Fin n) (hi : (D.minus i).card = 2) (t : Fin 5) :
    ∑ j, D.H.entry i j * D.H.entry (D.r t) j = 0 := by
  rw [D.H.rows, if_neg (D.two_minus_not_leading i hi t)]

lemma family_orth (t u : Fin 5) :
    (∑ j, D.H.entry (D.r t) j * D.H.entry (D.r u) j) = if t = u then (n : ℝ) else 0 := by
  rw [D.H.rows]
  simp only [EmbeddingLike.apply_eq_iff_eq]

lemma sum_cert (i k : Fin n) (hi : (D.minus i).card = 2) (hk : (D.minus k).card = 2)
    (A : Finset (Fin 5)) (hA : A.card = 2) :
    (∑ j, certificate (D.H.entry i j) (D.H.entry k j) (D.a A j) (D.b A j)) =
      ∑ j, D.H.entry i j * D.H.entry k j := by
  have hB : Aᶜ.card = 3 := by simp [card_compl, hA]
  have hiA := row_orthogonal_sum (D.H.entry i) (fun t => D.H.entry (D.r t)) A
    (fun t _ => D.row_orth i hi t)
  have hiB := row_orthogonal_sum (D.H.entry i) (fun t => D.H.entry (D.r t)) Aᶜ
    (fun t _ => D.row_orth i hi t)
  have hkA := row_orthogonal_sum (D.H.entry k) (fun t => D.H.entry (D.r t)) A
    (fun t _ => D.row_orth k hk t)
  have hkB := row_orthogonal_sum (D.H.entry k) (fun t => D.H.entry (D.r t)) Aᶜ
    (fun t _ => D.row_orth k hk t)
  apply sum_certificate
  · simp only [add_mul, mul_sub, sum_add_distrib, sum_sub_distrib, a, b] at *
    linarith
  · exact disjoint_rows_orthogonal _ n D.family_orth A Aᶜ (disjoint_compl_right)
  · simpa [hA] using sum_rows_energy _ n D.family_orth A
  · simpa [hB] using sum_rows_energy _ n D.family_orth Aᶜ

lemma a_leading (A : Finset (Fin 5)) (hA : A.card = 2) (u : Fin 5) :
    D.a A (D.c u) = if u ∈ A then 0 else 2 := by
  unfold a
  simp_rw [D.block]
  have hentry (t : Fin 5) : (if t = u then (-1 : ℝ) else 1) = 1 - 2 * (if t = u then 1 else 0) := by
    split_ifs <;> norm_num
  simp_rw [hentry]
  by_cases h : u ∈ A <;> norm_num [sum_sub_distrib, ← mul_sum, hA, h]

lemma b_leading (A : Finset (Fin 5)) (hA : A.card = 2) (u : Fin 5) :
    D.b A (D.c u) = if u ∈ A then 3 else 1 := by
  have hB : Aᶜ.card = 3 := by simp [card_compl, hA]
  unfold b
  simp_rw [D.block]
  have hentry (t : Fin 5) : (if t = u then (-1 : ℝ) else 1) = 1 - 2 * (if t = u then 1 else 0) := by
    split_ifs <;> norm_num
  simp_rw [hentry]
  simp only [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one, hB]
  by_cases h : u ∈ A <;> norm_num [h]

lemma same_pair_lower (i k : Fin n) (hi : (D.minus i).card = 2)
    (heq : D.minus i = D.minus k) :
    36 ≤ ∑ j, D.H.entry i j * D.H.entry k j := by
  have hk : (D.minus k).card = 2 := by rw [← heq]; exact hi
  let A := D.minus i
  let P := fun j => certificate (D.H.entry i j) (D.H.entry k j) (D.a A j) (D.b A j)
  have hp : ∀ j, 0 ≤ P j := by
    intro j
    apply certificate_nonnegative (D.H.signs i j) (D.H.signs k j) (D.allowed A hi j)
    · simpa [D.projection i hi j] using D.schur i j
    · simpa [D.projection k hk j, ← heq] using D.schur k j
  have hA : (A.map D.c).card = 2 := by simpa [A] using hi
  have hB : (Aᶜ.map D.c).card = 3 := by simp [card_compl, A, hi]
  have hd : Disjoint (A.map D.c) (Aᶜ.map D.c) := by
    exact (disjoint_map D.c).mpr disjoint_compl_right
  have hPA : ∀ j ∈ A.map D.c, P j = 12 := by
    intro j hj
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hj
    simp only [P, D.entry_of_minus, ← heq, if_pos hu,
      D.a_leading A hi, D.b_leading A hi]
    simpa only [show u ∈ D.minus i from hu, if_true] using certificate_first_pair
  have hPB : ∀ j ∈ Aᶜ.map D.c, P j = 4 := by
    intro j hj
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hj
    have hnot : u ∉ A := mem_compl.mp hu
    simp only [P, D.entry_of_minus, ← heq, if_neg hnot,
      D.a_leading A hi, D.b_leading A hi]
    simpa only [show u ∉ D.minus i from hnot, if_false] using certificate_first_complement
  have h := certificate_sum_ge_36 P _ _ hd hA hB hPA hPB (fun j _ => hp j)
  rw [D.sum_cert i k hi hk A hi] at h
  exact h

/-- Case 2 in normalized matrix form: no such matrix can have `p₆ ≤ 2`. -/
theorem impossible (D : CaseTwoNormalForm n) : False := by
  let t : Fin n → Fin 3 := fun i => ⟨(D.minus i).card, by have := D.minus_le_two i; omega⟩
  have hn : 0 < n := by
    have := (D.r 0).isLt
    omega
  apply case_two_counting t D.minus (by simpa using hn)
  · have hc (u v : Fin 5) :
        (∑ i, D.H.entry i (D.c u) * D.H.entry i (D.c v)) =
          if u = v then (n : ℝ) else 0 := by
      rw [D.H.cols]
      simp only [EmbeddingLike.apply_eq_iff_eq]
    have he := sum_rows_energy (fun u i => D.H.entry i (D.c u)) n hc univ
    simp only [card_univ, Fintype.card_fin, Nat.cast_ofNat] at he
    simpa only [t, D.minus_sum, Fintype.card_fin] using he
  · intro i hi
    have := congrArg Fin.val hi
    simpa [t] using this
  · intro i k hi hk he
    have hic : (D.minus i).card = 2 := by simpa [t] using congrArg Fin.val hi
    exact (equal_rows_and_order D.H i k (D.same_pair_lower i k hic he)).1
  · intro i hi
    have hic : (D.minus i).card = 2 := by simpa [t] using congrArg Fin.val hi
    simpa using (equal_rows_and_order D.H i i (D.same_pair_lower i i hic rfl)).2

end CaseTwoNormalForm
end HadamardAppendix
