import HadamardAppendix.Stage

/-!
# Gaussian elimination and complete pivoting

`eliminate A k` stores the Schur matrix after k steps, padded with zeros
in the retired rows and columns. The recurrence is the usual scalar
Gaussian-elimination update. No Hadamard or leading-block property is
built into this definition.
-/
namespace HadamardAppendix
open Finset Matrix

noncomputable def eliminate {n : ℕ} (A : Fin n → Fin n → ℝ) : ℕ → Fin n → Fin n → ℝ
  | 0 => A
  | k + 1 => if hk : k < n then
      fun i j => eliminate A k i j -
        eliminate A k i ⟨k, hk⟩ / eliminate A k ⟨k, hk⟩ ⟨k, hk⟩ * eliminate A k ⟨k, hk⟩ j
    else eliminate A k

@[simp] lemma eliminate_zero {n : ℕ} (A : Fin n → Fin n → ℝ) : eliminate A 0 = A := rfl

lemma eliminate_succ {n k : ℕ} (A : Fin n → Fin n → ℝ) (hk : k < n) (i j : Fin n) :
    eliminate A (k+1) i j = eliminate A k i j -
      eliminate A k i ⟨k,hk⟩ / eliminate A k ⟨k,hk⟩ ⟨k,hk⟩ * eliminate A k ⟨k,hk⟩ j := by
  simp only [eliminate, dif_pos hk]

/-- Nonzero pivots and maximal absolute value in the active matrix, with
ties allowed. Rows and columns are already in the chosen pivot order. -/
def CompletelyPivoted {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ k : Fin n, eliminate A k.val k k ≠ 0 ∧
    ∀ i j : Fin n, k.val ≤ i.val → k.val ≤ j.val →
      |eliminate A k.val i j| ≤ |eliminate A k.val k k|

noncomputable def pivotMagnitude {n : ℕ} (A : Fin n → Fin n → ℝ) (k : Fin n) : ℝ :=
  |eliminate A k.val k k|

/-- The padded rows and columns really vanish after their elimination. -/
theorem eliminate_retired_zero {n : ℕ} (A : Fin n → Fin n → ℝ) (hCP : CompletelyPivoted A)
    (k : ℕ) (hk : k ≤ n) (i j : Fin n) (hij : i.val < k ∨ j.val < k) :
    eliminate A k i j = 0 := by
  induction k generalizing i j with
  | zero => omega
  | succ k ih =>
    have hkn : k < n := by omega
    let q : Fin n := ⟨k, hkn⟩
    have hq : eliminate A k q q ≠ 0 := (hCP q).1
    rw [eliminate_succ A hkn]
    by_cases hi : i.val < k
    · rw [ih (by omega) i j (Or.inl hi), ih (by omega) i q (Or.inl hi)]
      simp
    by_cases hj : j.val < k
    · rw [ih (by omega) i j (Or.inr hj), ih (by omega) q j (Or.inr hj)]
      simp
    have he : i = q ∨ j = q := by
      rcases hij with h | h
      · exact Or.inl (Fin.ext (by dsimp [q]; omega))
      · exact Or.inr (Fin.ext (by dsimp [q]; omega))
    rcases he with rfl | rfl
    · simp [show (⟨k, hkn⟩ : Fin n) = q from rfl, hq]
    · simp [show (⟨k, hkn⟩ : Fin n) = q from rfl, div_mul_cancel₀ _ hq]

/-- Extend the active CP bound to the padded matrix. -/
theorem CompletelyPivoted.bound {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hCP : CompletelyPivoted A) (k i j : Fin n) :
    |eliminate A k.val i j| ≤ pivotMagnitude A k := by
  by_cases hi : k.val ≤ i.val
  · by_cases hj : k.val ≤ j.val
    · exact (hCP k).2 i j hi hj
    · rw [eliminate_retired_zero A hCP k.val (Nat.le_of_lt k.isLt) i j (Or.inr (by omega))]
      exact le_trans (by norm_num) (abs_nonneg _)
  · rw [eliminate_retired_zero A hCP k.val (Nat.le_of_lt k.isLt) i j (Or.inl (by omega))]
    exact le_trans (by norm_num) (abs_nonneg _)

/-- Every eliminated row is the original row minus a combination of the
first k original rows. This is proved from the scalar recurrence. -/
theorem eliminate_row_combination {n : ℕ} (A : Fin n → Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (i : Fin n) :
    ∃ a : Fin k → ℝ, ∀ j,
      eliminate A k i j = A i j - ∑ t, a t * A (Fin.castLE hk t) j := by
  induction k generalizing i with
  | zero =>
    exact ⟨fun t => Fin.elim0 t, fun j => by simp⟩
  | succ k ih =>
    have hkn : k < n := by omega
    have hkle : k ≤ n := by omega
    let q : Fin n := ⟨k, hkn⟩
    obtain ⟨a, ha⟩ := ih hkle i
    obtain ⟨b, hb⟩ := ih hkle q
    let f := eliminate A k i q / eliminate A k q q
    refine ⟨Fin.lastCases f (fun t => a t - f * b t), ?_⟩
    intro j
    rw [eliminate_succ A hkn]
    change eliminate A k i j - f * eliminate A k q j = _
    rw [ha j, hb j, Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
    have he (t : Fin k) : Fin.castLE hk t.castSucc = Fin.castLE hkle t := rfl
    have hlast : Fin.castLE hk (Fin.last k) = q := rfl
    simp only [he, hlast, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
    ring

end HadamardAppendix
