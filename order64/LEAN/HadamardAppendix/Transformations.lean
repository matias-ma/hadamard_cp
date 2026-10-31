import HadamardAppendix.SixRows

namespace HadamardAppendix
open Finset Matrix
namespace Hadamard
variable {n : ℕ} (H : Hadamard n)

/-- Observation 1: transpose preserves the Hadamard property. -/
def transpose : Hadamard n where
  entry i j := H.entry j i
  signs i j := H.signs j i
  rows := H.cols
  cols := H.rows

/-- Observation 1: independently negate full rows and columns. -/
noncomputable def signed (a b : Fin n → ℝ) (ha : ∀ i, Sign (a i)) (hb : ∀ j, Sign (b j)) :
    Hadamard n where
  entry i j := a i * H.entry i j * b j
  signs i j := sign_product (sign_product (ha i) (H.signs i j)) (hb j)
  rows i k := by
    calc
      (∑ j, (a i * H.entry i j * b j) * (a k * H.entry k j * b j)) =
          (a i * a k) * (∑ j, H.entry i j * H.entry k j) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        calc
          _ = (a i * a k) * (H.entry i j * H.entry k j) * (b j * b j) := by ring
          _ = _ := by rw [sign_mul_self (hb j), mul_one]
      _ = _ := by
        rw [H.rows]
        split_ifs with h
        · subst k
          rw [sign_mul_self (ha i), one_mul]
        · ring
  cols j k := by
    calc
      (∑ i, (a i * H.entry i j * b j) * (a i * H.entry i k * b k)) =
          (b j * b k) * (∑ i, H.entry i j * H.entry i k) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        calc
          _ = (b j * b k) * (H.entry i j * H.entry i k) * (a i * a i) := by ring
          _ = _ := by rw [sign_mul_self (ha i), mul_one]
      _ = _ := by
        rw [H.cols]
        split_ifs with h
        · subst k
          rw [sign_mul_self (hb j), one_mul]
        · ring

/-- A full row/column permutation also preserves orthogonality. -/
def reindex (r c : Equiv.Perm (Fin n)) : Hadamard n where
  entry i j := H.entry (r i) (c j)
  signs i j := H.signs _ _
  rows i k := by
    rw [Equiv.sum_comp c (fun j => H.entry (r i) j * H.entry (r k) j), H.rows]
    simp only [Equiv.apply_eq_iff_eq]
  cols j k := by
    rw [Equiv.sum_comp r (fun i => H.entry i (c j) * H.entry i (c k)), H.cols]
    simp only [Equiv.apply_eq_iff_eq]

end Hadamard
end HadamardAppendix
