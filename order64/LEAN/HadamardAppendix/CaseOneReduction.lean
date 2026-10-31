import HadamardAppendix.CanonicalFour
import HadamardAppendix.NormalizedCaseOne

namespace HadamardAppendix
open Finset Matrix

/-- The column permutation induced by multiplying by column `t` of B. -/
def columnTranslation : Fin 4 → Equiv.Perm (Fin 4) := ![
  ⟨![0, 1, 2, 3], ![0, 1, 2, 3], by decide, by decide⟩,
  ⟨![1, 0, 3, 2], ![1, 0, 3, 2], by decide, by decide⟩,
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩,
  ⟨![3, 2, 1, 0], ![3, 2, 1, 0], by decide, by decide⟩]

lemma columnTranslation_zero (t : Fin 4) : columnTranslation t 0 = t := by
  fin_cases t <;> rfl

lemma columnTranslation_B (t a b : Fin 4) :
    B a t * B a (columnTranslation t b) = B a b := by
  fin_cases t <;> fin_cases a <;> fin_cases b <;> norm_num [columnTranslation, B, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

lemma schurFour_standard {n : ℕ} (H : Hadamard n) (r c : Fin 4 ↪ Fin n)
    (hB : ∀ t u, H.entry (r t) (c u) = B t u) (hc : ∀ i, H.entry i (c 0) = 1)
    (i j : Fin n) : schurFour H r c i j = residualFour H r c i j := by
  simp only [schurFour, Fin.sum_univ_four, hB, hc, residualFour]
  simp [B, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  <;> ring

namespace FourStage
variable {n : ℕ} {p₆ : ℝ}

/-- Complete Case 1 when the fifth column prefix is even. -/
theorem case_one_even (D : FourStage n 2 p₆)
    (hB : ∀ a b, D.H.entry (D.r a) (D.c b) = B a b)
    (t : Fin 4) (hct : ∀ a, D.H.entry (D.r a) D.q = B a t) (hp : p₆ ≤ 3) : False := by
  let E := (D.signed (fun i => D.H.entry i (D.c t)) (fun _ => 1)
    (fun i => D.H.signs i (D.c t)) (fun _ => Or.inl rfl)).reindexCols (columnTranslation t)
  have hBE : ∀ a b, E.H.entry (E.r a) (E.c b) = B a b := by
    intro a b
    change D.H.entry (D.r a) (D.c t) * D.H.entry (D.r a) (D.c (columnTranslation t b)) * 1 = _
    rw [hB, hB, mul_one]
    exact columnTranslation_B t a b
  have hcol : ∀ i, E.H.entry i (E.c 0) = 1 := by
    intro i
    change D.H.entry i (D.c t) * D.H.entry i (D.c (columnTranslation t 0)) * 1 = 1
    rw [columnTranslation_zero, sign_mul_self (D.H.signs _ _), mul_one]
  have hfifth : ∀ a, E.H.entry (E.r a) E.q = 1 := by
    intro a
    change D.H.entry (D.r a) (D.c t) * D.H.entry (D.r a) D.q * 1 = 1
    rw [hB, hct]
    have hsign : Sign (B a t) := by rw [← hB]; exact D.H.signs _ _
    rw [sign_mul_self hsign, mul_one]
  have hres := schurFour_standard E.H E.r E.c hBE hcol
  have hq (i : Fin n) : schurFour E.H E.r E.c i E.q = E.H.entry i E.q - 1 := by
    rw [hres]
    simp only [residualFour, hfifth]
    ring
  have hzq : E.H.entry E.z E.q = -1 := by
    have h := E.pivot
    rw [hq] at h
    rcases E.H.signs E.z E.q with hsign | hsign
    · norm_num [hsign] at h
    · exact hsign
  let N : CaseOneNormalForm n := {
    H := E.H, r := E.r, c := E.c, z := E.z, q := E.q,
    block := hBE, firstColumn := hcol, fifthColumn := hfifth,
    qOutside := E.qOutside, pivot := hzq,
    schur4 := fun i _ j => by simpa only [hres] using E.bound4 i j,
    schur5 := fun i _ _ j => by
      have h := le_trans (E.bound5 i j) hp
      simpa only [schurFive, hres] using h }
  exact N.impossible

/-- The parity/transposition reduction of Case 1. -/
theorem case_one_canonical (D : FourStage n 2 p₆)
    (hB : ∀ a b, D.H.entry (D.r a) (D.c b) = B a b)
    (hr : ∀ j, D.H.entry (D.r 0) j = 1)
    (hc : ∀ i, D.H.entry i (D.c 0) = 1) (hp : p₆ ≤ 3) : False := by
  let rv := fun t : Fin 4 => D.H.entry D.z (D.c t)
  let cv := fun t : Fin 4 => D.H.entry (D.r t) D.q
  have hprodR : Sign (rv 1 * rv 2 * rv 3) :=
    sign_product (sign_product (D.H.signs _ _) (D.H.signs _ _)) (D.H.signs _ _)
  have hprodC : Sign (cv 1 * cv 2 * cv 3) :=
    sign_product (sign_product (D.H.signs _ _) (D.H.signs _ _)) (D.H.signs _ _)
  have not_odd : ¬ (rv 1 * rv 2 * rv 3 = -1 ∧ cv 1 * cv 2 * cv 3 = -1) := by
    rintro ⟨hR, hC⟩
    apply odd_prefixes_not_two (rv 1) (rv 2) (rv 3) (cv 1) (cv 2) (cv 3) (D.H.entry D.z D.q)
      (D.H.signs _ _) (D.H.signs _ _) (D.H.signs _ _)
      (D.H.signs _ _) (D.H.signs _ _) (D.H.signs _ _) (D.H.signs _ _) hR hC
    convert D.pivot using 2
    simp only [schurFour, Fin.sum_univ_four, hB, hr, hc]
    simp [rv, cv, BInv, B, dotProduct, mulVec, Fin.sum_univ_four, hr, hc]
    <;> ring
  have even_column (hC : cv 1 * cv 2 * cv 3 = 1) : ∃ t, ∀ a, cv a = B a t := by
    obtain ⟨t, ht⟩ := even_prefix_column (cv 1) (cv 2) (cv 3)
      (D.H.signs _ _) (D.H.signs _ _) (D.H.signs _ _) hC
    refine ⟨t, ?_⟩
    intro a
    have hh := congrFun ht a
    fin_cases a <;> simpa [cv, hr] using hh
  rcases hprodC with hC | hC
  · obtain ⟨t, ht⟩ := even_column hC
    exact D.case_one_even hB t ht hp
  · have hR : rv 1 * rv 2 * rv 3 = 1 := hprodR.resolve_right (fun h => not_odd ⟨h, hC⟩)
    obtain ⟨t, ht⟩ := even_prefix_column (rv 1) (rv 2) (rv 3)
      (D.H.signs _ _) (D.H.signs _ _) (D.H.signs _ _) hR
    apply D.transpose.case_one_even
      (fun a b => by change D.H.entry (D.r b) (D.c a) = B a b; rw [hB]; exact congrFun (congrFun B_symmetric a) b)
      t _ hp
    intro a
    change rv a = B a t
    have hh := congrFun ht a
    fin_cases a <;> simpa [rv, hc] using hh

/-- The complete first exclusion, with no normal-form hypothesis. -/
theorem case_one (D : FourStage n 2 p₆) : 3 < p₆ := by
  by_contra! hp
  obtain ⟨E, hB, hr, hc⟩ := D.exists_canonical
  exact E.case_one_canonical hB hr hc hp

end FourStage
end HadamardAppendix
