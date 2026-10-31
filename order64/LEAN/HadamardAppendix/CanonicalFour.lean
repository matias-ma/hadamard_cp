import HadamardAppendix.Stage
import HadamardAppendix.SmallBlocks

namespace HadamardAppendix
open Finset Matrix

lemma balanced_three (a b c : ℝ) (ha : Sign a) (hb : Sign b) (hc : Sign c)
    (hs : 1 + a + b + c = 0) :
    (a = -1 ∧ b = 1 ∧ c = -1) ∨ (a = 1 ∧ b = -1 ∧ c = -1) ∨
      (a = -1 ∧ b = -1 ∧ c = 1) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    norm_num at *

/-- The normalization of the leading four-by-four Hadamard matrix. -/
theorem canonical_four (H : Hadamard 4)
    (hr : ∀ j, H.entry 0 j = 1) (hc : ∀ i, H.entry i 0 = 1) :
    ∃ e : Equiv.Perm (Fin 4), e 0 = 0 ∧ ∀ i j, H.entry (e i) j = B i j := by
  have opts (i : Fin 4) (hi : i ≠ 0) :=
    balanced_three (H.entry i 1) (H.entry i 2) (H.entry i 3)
      (H.signs i 1) (H.signs i 2) (H.signs i 3) (by
        have h := H.rows i 0
        simpa [Fin.sum_univ_four, hr, hc, hi] using h)
  have h12 : (∑ j, H.entry 1 j * H.entry 2 j) = 0 := by simpa only [if_neg (by decide : (1 : Fin 4) ≠ 2)] using H.rows 1 2
  have h13 : (∑ j, H.entry 1 j * H.entry 3 j) = 0 := by simpa only [if_neg (by decide : (1 : Fin 4) ≠ 3)] using H.rows 1 3
  have h23 : (∑ j, H.entry 2 j * H.entry 3 j) = 0 := by simpa only [if_neg (by decide : (2 : Fin 4) ≠ 3)] using H.rows 2 3
  rcases opts 1 (by decide) with ⟨h11, h12', h13'⟩ | ⟨h11, h12', h13'⟩ | ⟨h11, h12', h13'⟩ <;>
    rcases opts 2 (by decide) with ⟨h21, h22, h23'⟩ | ⟨h21, h22, h23'⟩ | ⟨h21, h22, h23'⟩ <;>
    rcases opts 3 (by decide) with ⟨h31, h32, h33⟩ | ⟨h31, h32, h33⟩ | ⟨h31, h32, h33⟩ <;>
    norm_num [Fin.sum_univ_four, hc, h11, h12', h13', h21, h22, h23', h31, h32, h33,
      Fin.ext_iff] at h12 h13 h23
  · let e : Equiv.Perm (Fin 4) :=
      ⟨![0, 1, 2, 3], ![0, 1, 2, 3], by decide, by decide⟩
    refine ⟨e, rfl, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e, B, hr, hc, h11, h12', h13', h21, h22, h23', h31, h32, h33] <;> assumption
  · let e : Equiv.Perm (Fin 4) :=
      ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩
    refine ⟨e, rfl, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e, B, hr, hc, h11, h12', h13', h21, h22, h23', h31, h32, h33] <;> assumption
  · let e : Equiv.Perm (Fin 4) :=
      ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩
    refine ⟨e, rfl, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e, B, hr, hc, h11, h12', h13', h21, h22, h23', h31, h32, h33] <;> assumption
  · let e : Equiv.Perm (Fin 4) :=
      ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩
    refine ⟨e, rfl, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e, B, hr, hc, h11, h12', h13', h21, h22, h23', h31, h32, h33] <;> assumption
  · let e : Equiv.Perm (Fin 4) :=
      ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩
    refine ⟨e, rfl, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e, B, hr, hc, h11, h12', h13', h21, h22, h23', h31, h32, h33] <;> assumption
  · let e : Equiv.Perm (Fin 4) :=
      ⟨![0, 3, 2, 1], ![0, 3, 2, 1], by decide, by decide⟩
    refine ⟨e, rfl, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e, B, hr, hc, h11, h12', h13', h21, h22, h23', h31, h32, h33] <;> assumption

namespace FourStage
variable {n : ℕ} {p₅ p₆ : ℝ}

/-- The first normalization used by the appendix, retaining all Schur bounds. -/
theorem exists_canonical (D : FourStage n p₅ p₆) :
    ∃ E : FourStage n p₅ p₆,
      (∀ i j, E.H.entry (E.r i) (E.c j) = B i j) ∧
      (∀ j, E.H.entry (E.r 0) j = 1) ∧ (∀ i, E.H.entry i (E.c 0) = 1) := by
  let P := D.positive
  obtain ⟨e, he0, he⟩ := canonical_four P.leading
    (fun j => by rw [P.leading_eq]; exact D.positive_row _)
    (fun i => by rw [P.leading_eq]; exact D.positive_column _)
  refine ⟨P.reindexRows e, ?_, ?_, ?_⟩
  · intro i j
    change P.H.entry (P.r (e i)) (P.c j) = B i j
    rw [← P.leading_eq]
    exact he i j
  · intro j
    change P.H.entry (P.r (e 0)) j = 1
    rw [he0]
    exact D.positive_row j
  · exact D.positive_column

end FourStage
end HadamardAppendix
