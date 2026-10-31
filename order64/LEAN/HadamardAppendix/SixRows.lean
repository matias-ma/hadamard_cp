import HadamardAppendix.CaseOne
import HadamardAppendix.Schur

namespace HadamardAppendix
open Finset Matrix

lemma sign_product {a b : ℝ} (ha : Sign a) (hb : Sign b) : Sign (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [Sign]

/-- Six distinct rows used in Case 1, with a common positive column.
The first four are the leading rows; rows 4 and 5 are `x` and `z`. -/
structure SixRows (ι : Type*) [Fintype ι] where
  row : Fin 6 → ι → ℝ
  sign : ∀ i j, Sign (row i j)
  orth : ∀ i k, i ≠ k → row i ⬝ᵥ row k = 0
  column : ι
  positive : ∀ i, row i column = 1

namespace SixRows
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (D : SixRows ι)

/-- Signed-column normalization used in the distance-three branch. -/
noncomputable def switch (k : Fin 6) : SixRows ι where
  row i j := D.row i j * D.row k j
  sign i j := sign_product (D.sign i j) (D.sign k j)
  orth i l hil := by
    change (∑ j, (D.row i j * D.row k j) * (D.row l j * D.row k j)) = 0
    calc
      _ = ∑ j, D.row i j * D.row l j := by
        apply sum_congr rfl
        intro j _
        calc
          _ = D.row i j * D.row l j * (D.row k j * D.row k j) := by ring
          _ = _ := by rw [sign_mul_self (D.sign k j), mul_one]
      _ = 0 := D.orth i l hil
  column := D.column
  positive i := by simp [D.positive]

lemma switch_base (k : Fin 6) (j : ι) : (D.switch k).row k j = 1 :=
  sign_mul_self (D.sign k j)

/-- A permutation of the six selected rows. -/
noncomputable def reindex (e : Fin 6 ↪ Fin 6) : SixRows ι where
  row i := D.row (e i)
  sign i j := D.sign (e i) j
  orth i k h := D.orth _ _ (fun he => h (e.injective he))
  column := D.column
  positive i := D.positive _

lemma signed_orth (i k : Fin 6) (h : i ≠ k) (a b : ℝ) :
    (fun j => a * D.row i j) ⬝ᵥ (fun j => b * D.row k j) = 0 := by
  change (∑ j, (a * D.row i j) * (b * D.row k j)) = 0
  calc
    _ = a * b * (D.row i ⬝ᵥ D.row k) := by
      simp only [dotProduct, mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [D.orth i k h]; ring

/-- Distance two, with the two nonzero coefficients of the transformed
prefix supplied explicitly. -/
theorem distance_two (k l : Fin 6) (α β : ℝ)
    (hα : Sign α) (hβ : Sign β) (hs : α + β = 0)
    (hk4 : (4 : Fin 6) ≠ k) (hk5 : (5 : Fin 6) ≠ k)
    (hl4 : (4 : Fin 6) ≠ l) (hl5 : (5 : Fin 6) ≠ l) (hkl : k ≠ l)
    (hbound : ∀ j, |D.row 4 j - D.row 5 j - α * D.row k j - β * D.row l j| ≤ 3) :
    False := by
  apply case_one_distance_two (D.row 4) (D.row 5)
    (fun j => α * D.row k j) (fun j => β * D.row l j) D.column
    (D.sign 4) (D.sign 5)
    (fun j => sign_product hα (D.sign k j)) (fun j => sign_product hβ (D.sign l j))
  · exact D.orth 4 5 (by decide)
  · simpa using D.signed_orth 4 k hk4 1 α
  · simpa using D.signed_orth 4 l hl4 1 β
  · simpa using D.signed_orth 5 k hk5 1 α
  · simpa using D.signed_orth 5 l hl5 1 β
  · exact D.signed_orth k l hkl α β
  · simp only [D.positive, mul_one]
    linarith
  · exact hbound

/-- Distance three before switching columns. Row 0 is the row matching
the even prefix, and rows 1, 2, 3 are the other leading rows. -/
theorem distance_three
    (h₄ : ∀ j, |D.row 4 j + (D.row 0 j - (D.row 1 j + D.row 2 j + D.row 3 j)) / 2| ≤ 2)
    (h₅ : ∀ j, |(D.row 4 j + (D.row 0 j - (D.row 1 j + D.row 2 j + D.row 3 j)) / 2) -
        (D.row 5 j - D.row 0 j)| ≤ 3) : False := by
  let E := D.switch 0
  have hones (i : Fin 6) (hi : i ≠ 0) : ∑ j, E.row i j = 0 := by
    exact D.orth i 0 hi
  have horth (i : Fin 6) (hi : i ≠ 4) : ∑ j, E.row i j * E.row 4 j = 0 :=
    E.orth i 4 hi
  have h₄' : ∀ j, |E.row 4 j + (1 - (E.row 1 j + E.row 2 j + E.row 3 j)) / 2| ≤ 2 := by
    intro j
    have he : E.row 4 j + (1 - (E.row 1 j + E.row 2 j + E.row 3 j)) / 2 =
        (D.row 4 j + (D.row 0 j - (D.row 1 j + D.row 2 j + D.row 3 j)) / 2) * D.row 0 j := by
      dsimp [E, switch]
      nlinarith [sign_sq (D.sign 0 j)]
    rw [he, abs_mul]
    rcases D.sign 0 j with h | h <;> simpa [h] using h₄ j
  have h₅' : ∀ j, |(E.row 4 j + (1 - (E.row 1 j + E.row 2 j + E.row 3 j)) / 2) -
      (E.row 5 j - 1)| ≤ 3 := by
    intro j
    have he : (E.row 4 j + (1 - (E.row 1 j + E.row 2 j + E.row 3 j)) / 2) - (E.row 5 j - 1) =
        ((D.row 4 j + (D.row 0 j - (D.row 1 j + D.row 2 j + D.row 3 j)) / 2) -
          (D.row 5 j - D.row 0 j)) * D.row 0 j := by
      dsimp [E, switch]
      nlinarith [sign_sq (D.sign 0 j)]
    rw [he, abs_mul]
    rcases D.sign 0 j with h | h <;> simpa [h] using h₅ j
  apply case_one_distance_three (E.row 4) (E.row 5) (E.row 1) (E.row 2) (E.row 3) E.column
    (E.sign 4) (E.sign 5) (E.sign 1) (E.sign 2) (E.sign 3)
  · simp only [sum_add_distrib, hones 1 (by decide), hones 2 (by decide),
      hones 3 (by decide), hones 5 (by decide)]
    norm_num
  · simp only [add_mul, sum_add_distrib, horth 1 (by decide), horth 2 (by decide),
      horth 3 (by decide), horth 5 (by decide)]
    norm_num
  · simp [E.positive]
  · exact h₄'
  · exact h₅'

end SixRows
end HadamardAppendix
