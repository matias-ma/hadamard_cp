import HadamardAppendix.GaussianElimination
import HadamardAppendix.DeterminantFour

/-! # From the GE definition to the local setup used in the appendix -/
namespace HadamardAppendix
open Finset Matrix

/-- The actual leading four-by-four submatrix, in the chosen pivot order. -/
noncomputable def leadingFour {n : ℕ} (H : Hadamard n) (hn : 4 ≤ n) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j => H.entry (Fin.castLE hn i) (Fin.castLE hn j)

/-- The usual block-Schur identity at step four, proved from the scalar
GE recurrence and the orthogonality of the leading block. -/
theorem eliminate_four_eq_schur {n : ℕ} (H : Hadamard n) (hn : 4 ≤ n)
    (hCP : CompletelyPivoted H.entry) (L : Hadamard 4)
    (hL : ∀ t u, L.entry t u = H.entry (Fin.castLE hn t) (Fin.castLE hn u)) (i j : Fin n) :
    eliminate H.entry 4 i j = schurFour H (Fin.castLEEmb hn) (Fin.castLEEmb hn) i j := by
  obtain ⟨a, ha⟩ := eliminate_row_combination H.entry 4 hn i
  have hprefix (u : Fin 4) : H.entry i (Fin.castLE hn u) = ∑ t, a t * L.entry t u := by
    have hz := eliminate_retired_zero H.entry hCP 4 hn i (Fin.castLE hn u) (Or.inr u.isLt)
    rw [ha] at hz
    simp_rw [← hL] at hz
    linarith
  have hcoeff (t : Fin 4) : a t = (∑ u, H.entry i (Fin.castLE hn u) * L.entry t u) / 4 := by
    have he : (∑ u, H.entry i (Fin.castLE hn u) * L.entry t u) = 4 * a t := by
      simp_rw [hprefix, sum_mul, mul_assoc]
      rw [sum_comm]
      simp_rw [← mul_sum, L.rows]
      simp [mul_ite, mul_comm]
    linarith
  rw [ha]
  unfold schurFour
  congr 1
  simp only [hcoeff, div_mul_eq_mul_div, ← sum_div, sum_mul, hL, Fin.coe_castLEEmb]

/-- A CP run produces all fields of FourStage. The only extra mathematical
input is the leading determinant value quoted in the appendix. -/
theorem fourStage_of_completePivoting {n : ℕ} (H : Hadamard n) (hn : 8 ≤ n)
    (hCP : CompletelyPivoted H.entry)
    (hdet : |(leadingFour H (by omega)).det| = 16) :
    Nonempty (FourStage n (pivotMagnitude H.entry ⟨4, by omega⟩)
      (pivotMagnitude H.entry ⟨5, by omega⟩)) := by
  have h4 : 4 ≤ n := by omega
  let r := Fin.castLEEmb h4
  let z : Fin n := ⟨4, by omega⟩
  let w : Fin n := ⟨5, by omega⟩
  obtain ⟨L, hL⟩ := hadamard_of_abs_det_four (leadingFour H h4)
    (fun i j => H.signs _ _) hdet
  have heq4 := eliminate_four_eq_schur H h4 hCP L hL
  have heq5 (i j : Fin n) :
      eliminate H.entry 5 i j = schurFive H r r z z i j := by
    rw [show 5 = 4+1 from rfl, eliminate_succ H.entry (by omega)]
    simp only [heq4, schurFive]
    rfl
  refine ⟨{
    H := H, r := r, c := r, z := z, q := z,
    zOutside := ?_, qOutside := ?_, leading := L, leading_eq := hL,
    pivot := ?_, bound4 := ?_, bound5 := ?_ }⟩
  · intro t h
    have hval := congrArg Fin.val h
    have ht := t.isLt
    change 4 = t.val at hval
    omega
  · intro t h
    have hval := congrArg Fin.val h
    have ht := t.isLt
    change 4 = t.val at hval
    omega
  · rw [← heq4]
    rfl
  · intro i j
    rw [← heq4]
    exact hCP.bound z i j
  · intro i j
    rw [← heq5]
    exact hCP.bound w i j

end HadamardAppendix
