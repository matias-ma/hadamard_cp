import HadamardAppendix.Basic
import Mathlib.Data.Matrix.Notation

/-! # The displayed small matrices and the eliminated-row identities -/
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace HadamardAppendix
open Finset Matrix

/-- The normalized leading Hadamard block in Case 1. -/
def B : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]

noncomputable def BInv : Matrix (Fin 4) (Fin 4) ℝ := (1 / 4 : ℝ) • B

lemma B_symmetric : B.transpose = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma B_inverse : BInv * B = 1 ∧ B * BInv = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [BInv, B, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- The normalized leading five-by-five block of Case 2. -/
def F : Matrix (Fin 5) (Fin 5) ℝ := fun i j => if i = j then -1 else 1
noncomputable def FInv : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => 1 / 6 - if i = j then 1 / 2 else 0

lemma F_inverse : FInv * F = 1 ∧ F * FInv = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [FInv, F, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    norm_num [Fin.ext_iff]

section
variable {ι κ : Type*} {k : ℕ}

/-- Eliminate the leading block, using a specified inverse `G`. -/
noncomputable def eliminatedRow (H : ι → κ → ℝ) (r : Fin k → ι) (c : Fin k → κ)
    (G : Matrix (Fin k) (Fin k) ℝ) (i : ι) (j : κ) : ℝ :=
  H i j - (((fun t => H i (c t)) ᵥ* G) ᵥ* (fun t j => H (r t) j)) j

/-- Observation 2: the first `k` entries of an eliminated row vanish. -/
lemma eliminatedRow_zero (H : ι → κ → ℝ) (r : Fin k → ι) (c : Fin k → κ)
    (G : Matrix (Fin k) (Fin k) ℝ)
    (hG : (G * Matrix.of (fun t u => H (r t) (c u))) = 1) (i : ι) (u : Fin k) :
    eliminatedRow H r c G i (c u) = 0 := by
  unfold eliminatedRow
  have he : (((fun t => H i (c t)) ᵥ* G) ᵥ* (fun t u => H (r t) (c u))) u = H i (c u) := by
    rw [vecMul_vecMul]
    change ((fun t => H i (c t)) ᵥ* (G * Matrix.of (fun t u => H (r t) (c u)))) u = _
    rw [hG, vecMul_one]
  change H i (c u) - (((fun t => H i (c t)) ᵥ* G) ᵥ* (fun t u => H (r t) (c u))) u = 0
  rw [he, sub_self]

/-- The next elimination step in Observation 2. -/
noncomputable def nextRow (u z : κ → ℝ) (pivotColumn : κ) (j : κ) : ℝ :=
  u j - u pivotColumn / z pivotColumn * z j

lemma nextRow_zero (u z : κ → ℝ) (q : κ) (hq : z q ≠ 0) :
    nextRow u z q q = 0 := by
  simp [nextRow, div_mul_cancel₀ _ hq]

lemma nextRow_previous_zero (u z : κ → ℝ) (q j : κ) (hu : u j = 0) (hz : z j = 0) :
    nextRow u z q j = 0 := by simp [nextRow, hu, hz]

lemma nextRow_equal_pivot (u z : κ → ℝ) (q : κ) (hq : z q ≠ 0) (heq : u q = z q) :
    nextRow u z q = u - z := by
  ext j
  simp [nextRow, heq, hq]

/-- The absolute-value part of Observation 1: independent sign changes of
rows and columns preserve every Schur-complement entry bound. -/
lemma sign_bound_iff (x a b M : ℝ) (ha : Sign a) (hb : Sign b) :
    |a * x * b| ≤ M ↔ |x| ≤ M := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

end
end HadamardAppendix
