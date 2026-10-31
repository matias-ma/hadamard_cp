import HadamardAppendix.Transformations

/-! # Schur bounds before choosing a normal form -/
namespace HadamardAppendix
open Finset Matrix

/-- Schur residual after a Hadamard block of order four. The inverse is
its transpose divided by four, expanded as a double sum. -/
noncomputable def schurFour {n : ℕ} (H : Hadamard n) (r c : Fin 4 ↪ Fin n)
    (i j : Fin n) : ℝ :=
  H.entry i j - (∑ a, ∑ b, H.entry i (c b) * H.entry (r a) (c b) * H.entry (r a) j) / 4

noncomputable def schurFive {n : ℕ} (H : Hadamard n) (r c : Fin 4 ↪ Fin n)
    (z q i j : Fin n) : ℝ :=
  schurFour H r c i j - schurFour H r c i q / schurFour H r c z q * schurFour H r c z j

/-- The Schur-complement transformation law behind Observation 1. -/
lemma schurFour_signed {n : ℕ} (H : Hadamard n) (r c : Fin 4 ↪ Fin n)
    (a b : Fin n → ℝ) (ha : ∀ i, Sign (a i)) (hb : ∀ j, Sign (b j)) (i j : Fin n) :
    schurFour (H.signed a b ha hb) r c i j = a i * b j * schurFour H r c i j := by
  have ht (s t : Fin 4) :
      (a i * H.entry i (c t) * b (c t)) * (a (r s) * H.entry (r s) (c t) * b (c t)) *
        (a (r s) * H.entry (r s) j * b j) =
      a i * b j * (H.entry i (c t) * H.entry (r s) (c t) * H.entry (r s) j) := by
    rcases ha (r s) with h | h <;> rcases hb (c t) with h' | h' <;> rw [h, h'] <;> ring
  simp only [schurFour, Hadamard.signed, ht, ← mul_sum]
  ring

lemma schurFive_signed {n : ℕ} (H : Hadamard n) (r c : Fin 4 ↪ Fin n)
    (a b : Fin n → ℝ) (ha : ∀ i, Sign (a i)) (hb : ∀ j, Sign (b j)) (z q i j : Fin n) :
    schurFive (H.signed a b ha hb) r c z q i j = a i * b j * schurFive H r c z q i j := by
  simp only [schurFive, schurFour_signed]
  rcases ha z with h | h <;> rcases hb q with h' | h' <;>
    rw [h, h'] <;> simp [div_eq_mul_inv] <;> ring

/-- Permuting the first four selected rows leaves their projection fixed. -/
lemma schurFour_reindex_rows {n : ℕ} (H : Hadamard n) (r c : Fin 4 ↪ Fin n)
    (e : Equiv.Perm (Fin 4)) (i j : Fin n) :
    schurFour H (e.toEmbedding.trans r) c i j = schurFour H r c i j := by
  have he := Equiv.sum_comp e (fun a => ∑ b, H.entry i (c b) * H.entry (r a) (c b) * H.entry (r a) j)
  exact congrArg (fun v : ℝ => H.entry i j - v / 4) he

/-- Permuting the first four selected columns also leaves it fixed. -/
lemma schurFour_reindex_cols {n : ℕ} (H : Hadamard n) (r c : Fin 4 ↪ Fin n)
    (e : Equiv.Perm (Fin 4)) (i j : Fin n) :
    schurFour H r (e.toEmbedding.trans c) i j = schurFour H r c i j := by
  have he : (∑ a, ∑ b, H.entry i (c (e b)) * H.entry (r a) (c (e b)) * H.entry (r a) j) =
      ∑ a, ∑ b, H.entry i (c b) * H.entry (r a) (c b) * H.entry (r a) j := by
    apply sum_congr rfl
    intro a _
    exact Equiv.sum_comp e (fun b => H.entry i (c b) * H.entry (r a) (c b) * H.entry (r a) j)
  exact congrArg (fun v : ℝ => H.entry i j - v / 4) he

/-- Transposing interchanges the Schur-complement indices. -/
lemma schurFour_transpose {n : ℕ} (H : Hadamard n) (r c : Fin 4 ↪ Fin n) (i j : Fin n) :
    schurFour H.transpose c r j i = schurFour H r c i j := by
  unfold schurFour Hadamard.transpose
  congr 2
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

lemma schurFive_transpose {n : ℕ} (H : Hadamard n) (r c : Fin 4 ↪ Fin n)
    (z q i j : Fin n) :
    schurFive H.transpose c r q z j i = schurFive H r c z q i j := by
  simp only [schurFive, schurFour_transpose]
  ring

end HadamardAppendix

namespace HadamardAppendix
open Finset Matrix

lemma sign_abs {a : ℝ} (ha : Sign a) : |a| = 1 := by
  rcases ha with rfl | rfl <;> norm_num

/-- The inputs used by the appendix once the cited first-four-pivot
result and equality in the determinant bound have been applied. -/
structure FourStage (n : ℕ) (p₅ p₆ : ℝ) where
  H : Hadamard n
  r : Fin 4 ↪ Fin n
  c : Fin 4 ↪ Fin n
  z : Fin n
  q : Fin n
  zOutside : ∀ t, z ≠ r t
  qOutside : ∀ t, q ≠ c t
  leading : Hadamard 4
  leading_eq : ∀ t u, leading.entry t u = H.entry (r t) (c u)
  pivot : |schurFour H r c z q| = p₅
  bound4 : ∀ i j, |schurFour H r c i j| ≤ p₅
  bound5 : ∀ i j, |schurFive H r c z q i j| ≤ p₆

namespace FourStage
variable {n : ℕ} {p₅ p₆ : ℝ} (D : FourStage n p₅ p₆)

noncomputable def signed (a b : Fin n → ℝ) (ha : ∀ i, Sign (a i)) (hb : ∀ j, Sign (b j)) :
    FourStage n p₅ p₆ where
  H := D.H.signed a b ha hb
  r := D.r
  c := D.c
  z := D.z
  q := D.q
  zOutside := D.zOutside
  qOutside := D.qOutside
  leading := D.leading.signed (fun t => a (D.r t)) (fun t => b (D.c t))
    (fun t => ha (D.r t)) (fun t => hb (D.c t))
  leading_eq t u := by simp only [Hadamard.signed, D.leading_eq]
  pivot := by
    rw [schurFour_signed, abs_mul, abs_mul, sign_abs (ha _), sign_abs (hb _)]
    simpa using D.pivot
  bound4 i j := by
    rw [schurFour_signed, abs_mul, abs_mul, sign_abs (ha _), sign_abs (hb _)]
    simpa using D.bound4 i j
  bound5 i j := by
    rw [schurFive_signed, abs_mul, abs_mul, sign_abs (ha _), sign_abs (hb _)]
    simpa using D.bound5 i j

noncomputable def transpose : FourStage n p₅ p₆ where
  H := D.H.transpose
  r := D.c
  c := D.r
  z := D.q
  q := D.z
  zOutside := D.qOutside
  qOutside := D.zOutside
  leading := D.leading.transpose
  leading_eq t u := D.leading_eq u t
  pivot := by simpa only [schurFour_transpose] using D.pivot
  bound4 i j := by simpa only [schurFour_transpose] using D.bound4 j i
  bound5 i j := by simpa only [schurFive_transpose] using D.bound5 j i

noncomputable def reindexRows (e : Equiv.Perm (Fin 4)) : FourStage n p₅ p₆ where
  H := D.H
  r := e.toEmbedding.trans D.r
  c := D.c
  z := D.z
  q := D.q
  zOutside t := D.zOutside (e t)
  qOutside := D.qOutside
  leading := D.leading.reindex e (Equiv.refl _)
  leading_eq t u := D.leading_eq (e t) u
  pivot := by simpa only [schurFour_reindex_rows] using D.pivot
  bound4 i j := by simpa only [schurFour_reindex_rows] using D.bound4 i j
  bound5 i j := by simpa only [schurFive, schurFour_reindex_rows] using D.bound5 i j

noncomputable def reindexCols (e : Equiv.Perm (Fin 4)) : FourStage n p₅ p₆ where
  H := D.H
  r := D.r
  c := e.toEmbedding.trans D.c
  z := D.z
  q := D.q
  zOutside := D.zOutside
  qOutside t := D.qOutside (e t)
  leading := D.leading.reindex (Equiv.refl _) e
  leading_eq t u := D.leading_eq t (e u)
  pivot := by simpa only [schurFour_reindex_cols] using D.pivot
  bound4 i j := by simpa only [schurFour_reindex_cols] using D.bound4 i j
  bound5 i j := by simpa only [schurFive, schurFour_reindex_cols] using D.bound5 i j

/-- Make the selected first row and first column positive. -/
noncomputable def positive : FourStage n p₅ p₆ :=
  D.signed (fun i => D.H.entry i (D.c 0))
    (fun j => D.H.entry (D.r 0) j * D.H.entry (D.r 0) (D.c 0))
    (fun i => D.H.signs i (D.c 0))
    (fun j => sign_product (D.H.signs (D.r 0) j) (D.H.signs (D.r 0) (D.c 0)))

lemma positive_row (j : Fin n) : D.positive.H.entry (D.positive.r 0) j = 1 := by
  dsimp [positive, signed, Hadamard.signed]
  rcases D.H.signs (D.r 0) j with h | h <;>
    rcases D.H.signs (D.r 0) (D.c 0) with h' | h' <;> rw [h, h'] <;> norm_num

lemma positive_column (i : Fin n) : D.positive.H.entry i (D.positive.c 0) = 1 := by
  dsimp [positive, signed, Hadamard.signed]
  rcases D.H.signs i (D.c 0) with h | h <;>
    rcases D.H.signs (D.r 0) (D.c 0) with h' | h' <;> rw [h, h'] <;> norm_num

end FourStage
end HadamardAppendix
