import HadamardAppendix.Stage
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace HadamardAppendix
open Finset Matrix

noncomputable def normalizedFour (a b c d e f g h i : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1,1,1; 1,a,b,c; 1,d,e,f; 1,g,h,i]

lemma normalizedFour_det (a b c d e f g h i : ℝ) :
    (normalizedFour a b c d e f g h i).det =
      (a-1)*((e-1)*(i-1)-(f-1)*(h-1)) -
      (b-1)*((d-1)*(i-1)-(f-1)*(g-1)) +
      (c-1)*((d-1)*(h-1)-(e-1)*(g-1)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  norm_num [normalizedFour, Fin.succAbove, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Fin.lt_def, Fin.ext_iff,
    show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl]
  <;> ring

/-- The order-four equality case of the Hadamard bound. After normalizing
its first row and column there are only nine independent signs. Ordinary
kernel-checked arithmetic leaves precisely the six normalized Hadamard
matrices; no native computation or unproved certificate is used. -/
lemma normalizedFour_maximal (a b c d e f g h i : ℝ)
    (ha : Sign a) (hb : Sign b) (hc : Sign c) (hd : Sign d) (he : Sign e)
    (hf : Sign f) (hg : Sign g) (hh : Sign h) (hi : Sign i)
    (hdet : |(normalizedFour a b c d e f g h i).det| = 16) :
    let N := normalizedFour a b c d e f g h i
    (∀ r s, (∑ j, N r j * N s j) = if r = s then (4 : ℝ) else 0) ∧
    (∀ r s, (∑ j, N j r * N j s) = if r = s then (4 : ℝ) else 0) := by
  rw [normalizedFour_det] at hdet
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;> rcases hi with rfl | rfl <;>
    norm_num at hdet
  all_goals constructor <;> intro r s <;> fin_cases r <;> fin_cases s <;>
    norm_num [normalizedFour, Fin.sum_univ_succ, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

/-- Every real four-by-four sign matrix attaining determinant magnitude
16 is Hadamard. This supplies the leading block, rather than assuming it. -/
theorem hadamard_of_abs_det_four (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, Sign (M i j)) (hdet : |M.det| = 16) :
    ∃ L : Hadamard 4, ∀ i j, L.entry i j = M i j := by
  let a := fun i => M i 0
  let b := fun j => M 0 0 * M 0 j
  have ha (i) : Sign (a i) := hM i 0
  have hb (j) : Sign (b j) := sign_product (hM 0 0) (hM 0 j)
  let N : Matrix (Fin 4) (Fin 4) ℝ := fun i j => a i * M i j * b j
  have hN (i j) : Sign (N i j) := sign_product (sign_product (ha i) (hM i j)) (hb j)
  have hr (j : Fin 4) : N 0 j = 1 := by
    dsimp [N, a, b]
    rcases hM 0 0 with h | h <;> rcases hM 0 j with h' | h' <;> rw [h, h'] <;> norm_num
  have hc (i : Fin 4) : N i 0 = 1 := by
    dsimp [N, a, b]
    rcases hM 0 0 with h | h <;> rcases hM i 0 with h' | h' <;> rw [h, h'] <;> norm_num
  have hdetN : |N.det| = 16 := by
    have he : N = Matrix.of (fun i j => a i * (Matrix.of (fun i j => b j * M i j)) i j) := by
      ext i j
      dsimp [N]
      ring
    rw [he, Matrix.det_mul_column, Matrix.det_mul_row, abs_mul, abs_mul]
    have hpa : |∏ i, a i| = 1 := by
      rw [Fin.prod_univ_four]
      simp only [abs_mul, sign_abs (ha _), mul_one]
    have hpb : |∏ j, b j| = 1 := by
      rw [Fin.prod_univ_four]
      simp only [abs_mul, sign_abs (hb _), mul_one]
    rw [hpa, hpb, hdet]
    norm_num
  have heq : N = normalizedFour (N 1 1) (N 1 2) (N 1 3) (N 2 1) (N 2 2)
      (N 2 3) (N 3 1) (N 3 2) (N 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [normalizedFour, hr, hc, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.vecHead, Matrix.vecTail] <;> rfl
  have ho := normalizedFour_maximal (N 1 1) (N 1 2) (N 1 3) (N 2 1) (N 2 2)
    (N 2 3) (N 3 1) (N 3 2) (N 3 3)
    (hN _ _) (hN _ _) (hN _ _) (hN _ _) (hN _ _) (hN _ _) (hN _ _) (hN _ _) (hN _ _)
    (by rw [← heq]; exact hdetN)
  change (∀ r s, _) ∧ (∀ r s, _) at ho
  rw [← heq] at ho
  let K : Hadamard 4 := ⟨N, hN, ho.1, ho.2⟩
  refine ⟨K.signed a b ha hb, ?_⟩
  intro i j
  change a i * (a i * M i j * b j) * b j = M i j
  rcases ha i with h | h <;> rcases hb j with h' | h' <;> rw [h, h'] <;> ring

end HadamardAppendix
