import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Common ingredients of Appendix A of `main.tex`

Indices in Lean start at zero. `Sign x` means that `x` is a real sign.
All sums and all inequalities below are over the reals; there is no
floating-point computation and no use of `native_decide`.
-/

namespace HadamardAppendix
open Finset Matrix

abbrev Sign (x : ℝ) : Prop := x = 1 ∨ x = -1

lemma sign_sq {x : ℝ} (hx : Sign x) : x ^ 2 = 1 := by
  rcases hx with rfl | rfl <;> norm_num

lemma sign_mul_self {x : ℝ} (hx : Sign x) : x * x = 1 := by
  nlinarith [sign_sq hx]

/-- A real sign matrix with orthogonal rows and columns.
The two orthogonality fields avoid selecting an orientation of `HHᵀ = nI`.
-/
structure Hadamard (n : ℕ) where
  entry : Fin n → Fin n → ℝ
  signs : ∀ i j, Sign (entry i j)
  rows : ∀ i k, (∑ j, entry i j * entry k j) = if i = k then (n : ℝ) else 0
  cols : ∀ j k, (∑ i, entry i j * entry i k) = if j = k then (n : ℝ) else 0

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Observation 3: splitting an orthogonality sum by signs. -/
theorem sum_half (w s : ι → ℝ) (hs : ∀ j, Sign (s j))
    (h₁ : ∑ j, w j = 0) (h₂ : ∑ j, w j * s j = 0) :
    (∑ j ∈ univ.filter (fun j => s j = 1), w j) = 0 ∧
    (∑ j ∈ univ.filter (fun j => s j = -1), w j) = 0 := by
  have hp : ∀ j, (if s j = 1 then w j else 0) = (w j + w j * s j) / 2 := by
    intro j
    rcases hs j with h | h <;> norm_num [h]
  have hm : ∀ j, (if s j = -1 then w j else 0) = (w j - w j * s j) / 2 := by
    intro j
    rcases hs j with h | h <;> norm_num [h]
  constructor
  · simp only [sum_filter, hp, ← sum_div, sum_add_distrib, h₁, h₂]
    norm_num
  · simp only [sum_filter, hm, ← sum_div, sum_sub_distrib, h₁, h₂]
    norm_num

/-- A nonnegative sum which contains a positive term cannot vanish. -/
theorem positive_sum {s : Finset ι} {f : ι → ℝ} {j : ι}
    (hj : j ∈ s) (hn : ∀ i ∈ s, 0 ≤ f i) (hp : 0 < f j) :
    0 < ∑ i ∈ s, f i := by
  exact lt_of_lt_of_le hp (single_le_sum hn hj)

/-- If a zero sum has a positive summand, it has a negative summand. -/
theorem exists_negative_of_sum_zero {s : Finset ι} {f : ι → ℝ} {j : ι}
    (hj : j ∈ s) (hp : 0 < f j) (hz : ∑ i ∈ s, f i = 0) :
    ∃ i ∈ s, f i < 0 := by
  by_contra! h
  have := positive_sum hj h hp
  linarith

/-- The energy argument used in the `d = 2` branch. A single zero entry
already suffices; the appendix uses the first five zero entries. -/
theorem energy_contradiction (v : ι → ℝ) (j₀ : ι)
    (hzero : v j₀ = 0) (hbound : ∀ j, (v j) ^ 2 ≤ 4)
    (henergy : ∑ j, (v j) ^ 2 = 4 * (Fintype.card ι : ℝ)) : False := by
  have hlt : (∑ j, (v j) ^ 2) < ∑ _j : ι, (4 : ℝ) := by
    apply sum_lt_sum (fun j _ => hbound j)
    exact ⟨j₀, mem_univ _, by rw [hzero]; norm_num⟩
  simp only [sum_const, card_univ, nsmul_eq_mul] at hlt
  nlinarith

end Finite

/-- The candidate table quoted at the beginning of the appendix. This is
an explicit input, not an axiom asserting the published result in Lean. -/
def PivotCandidates (p₅ p₆ : ℝ) : Prop :=
  (p₅ = 2 ∧ (p₆ = 2 ∨ p₆ = 3 ∨ p₆ = 4)) ∨
  (p₅ = 3 ∧ (p₆ = 4 / 3 ∨ p₆ = 2 ∨ p₆ = 8 / 3 ∨ p₆ = 10 / 3))

/-- Derive the displayed candidate table from the determinant values and
upper bound quoted immediately before the appendix's proposition. -/
theorem pivot_candidates_of_determinants {A₅ A₆ p₅ p₆ : ℝ}
    (hA₅ : A₅ = 32 ∨ A₅ = 48)
    (hA₆ : A₆ = 64 ∨ A₆ = 96 ∨ A₆ = 128 ∨ A₆ = 160)
    (h₅ : p₅ = A₅ / 16) (h₆ : p₆ = A₆ / A₅) (hbound : p₆ ≤ 4) :
    PivotCandidates p₅ p₆ := by
  rcases hA₅ with rfl | rfl <;>
    rcases hA₆ with rfl | rfl | rfl | rfl <;>
    norm_num [PivotCandidates] at * <;> simp_all <;> norm_num at *

/-- The final elimination of candidates, once the two strict bounds have
been established. -/
theorem pivot_pairs_of_exclusions {p₅ p₆ : ℝ}
    (hc : PivotCandidates p₅ p₆)
    (h₂ : p₅ = 2 → 3 < p₆) (h₃ : p₅ = 3 → 2 < p₆) :
    (p₅ = 2 ∧ p₆ = 4) ∨
    (p₅ = 3 ∧ p₆ = 8 / 3) ∨ (p₅ = 3 ∧ p₆ = 10 / 3) := by
  rcases hc with ⟨rfl, h | h | h⟩ | ⟨rfl, h | h | h | h⟩
  all_goals first | (exfalso; have := h₂ rfl; linarith) |
    (exfalso; have := h₃ rfl; linarith) | (simp_all)

end HadamardAppendix
