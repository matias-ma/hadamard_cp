import HadamardAppendix.CaseOneReduction
import HadamardAppendix.CaseTwoReduction
import HadamardAppendix.CPBridge

/-!
# The sixth-pivot theorem for completely pivoted Hadamard matrices

`sixth_pivot` is the public theorem. Its matrix hypothesis is the direct
GE definition `CompletelyPivoted`, and its pivot magnitudes are computed
by that recurrence. `FourStage` is now constructed inside the proof.

The only external mathematical input is `CitedPivotFacts`: the published
leading determinant value A(4) = 16 and the preliminary candidate table.
It is an explicit theorem parameter, not a declared axiom. The equality
case for the leading block, the GE/Schur bridge, and both exclusion
arguments are all proved here.
-/

namespace HadamardAppendix

/-- Appendix A's conclusion, conditional on the explicit local setup and
candidate table stated at the beginning of its proof. -/
theorem sixth_pivot_of_fourStage {n : ℕ} {p₅ p₆ : ℝ}
    (D : FourStage n p₅ p₆) (candidates : PivotCandidates p₅ p₆) :
    (p₅ = 2 ∧ p₆ = 4) ∨
      (p₅ = 3 ∧ p₆ = 8 / 3) ∨ (p₅ = 3 ∧ p₆ = 10 / 3) := by
  apply pivot_pairs_of_exclusions candidates
  · intro h
    subst p₅
    exact D.case_one
  · intro h
    subst p₅
    exact D.case_two

/-- A version taking exactly the quoted determinant values and pivot
ratio formulas, rather than the already simplified candidate table. -/
theorem sixth_pivot_of_fourStage_determinants {n : ℕ} {p₅ p₆ A₅ A₆ : ℝ}
    (D : FourStage n p₅ p₆)
    (hA₅ : A₅ = 32 ∨ A₅ = 48)
    (hA₆ : A₆ = 64 ∨ A₆ = 96 ∨ A₆ = 128 ∨ A₆ = 160)
    (h₅ : p₅ = A₅ / 16) (h₆ : p₆ = A₆ / A₅) (hbound : p₆ ≤ 4) :
    (p₅ = 2 ∧ p₆ = 4) ∨
      (p₅ = 3 ∧ p₆ = 8 / 3) ∨ (p₅ = 3 ∧ p₆ = 10 / 3) :=
  sixth_pivot_of_fourStage D (pivot_candidates_of_determinants hA₅ hA₆ h₅ h₆ hbound)

/-- The two strict inequalities proved in the appendix, without using
the literature's candidate table. -/
theorem sixth_pivot_exclusions_of_fourStage {n : ℕ} {p₅ p₆ : ℝ} (D : FourStage n p₅ p₆) :
    (p₅ = 2 → 3 < p₆) ∧ (p₅ = 3 → 2 < p₆) := by
  constructor
  · intro h
    subst p₅
    exact D.case_one
  · intro h
    subst p₅
    exact D.case_two

/-- The two preliminary facts quoted from the literature at the start of
Appendix A (Day--Peterson and Kravvaritis--Mitrouli). This definition says
exactly what remains imported from those papers; it contains no local
Schur assumptions, no normal-form assumption, and no desired conclusion.
No axiom or inhabitant of this proposition is declared in this project. -/
def CitedPivotFacts : Prop :=
  ∀ (n : ℕ) (H : Hadamard n) (hn : 8 ≤ n), CompletelyPivoted H.entry →
    |(leadingFour H (by omega)).det| = 16 ∧
    PivotCandidates (pivotMagnitude H.entry ⟨4, by omega⟩)
      (pivotMagnitude H.entry ⟨5, by omega⟩)

/-- For every real CP Hadamard matrix of order at least eight, its actual
fifth and sixth GE pivot magnitudes form one of the three stated pairs.
The cited preliminary classification is the sole external input. -/
theorem sixth_pivot (cited : CitedPivotFacts)
    {n : ℕ} (H : Hadamard n) (hn : 8 ≤ n) (hCP : CompletelyPivoted H.entry) :
    let p₅ := pivotMagnitude H.entry ⟨4, by omega⟩
    let p₆ := pivotMagnitude H.entry ⟨5, by omega⟩
    (p₅ = 2 ∧ p₆ = 4) ∨
      (p₅ = 3 ∧ p₆ = 8 / 3) ∨ (p₅ = 3 ∧ p₆ = 10 / 3) := by
  obtain ⟨hdet, candidates⟩ := cited n H hn hCP
  obtain ⟨D⟩ := fourStage_of_completePivoting H hn hCP hdet
  exact sixth_pivot_of_fourStage D candidates

/-- The two new exclusions for a CP Hadamard matrix, using only the cited
leading determinant value, independently of the candidate classification. -/
theorem sixth_pivot_exclusions {n : ℕ} (H : Hadamard n) (hn : 8 ≤ n)
    (hCP : CompletelyPivoted H.entry)
    (hdet : |(leadingFour H (by omega)).det| = 16) :
    let p₅ := pivotMagnitude H.entry ⟨4, by omega⟩
    let p₆ := pivotMagnitude H.entry ⟨5, by omega⟩
    (p₅ = 2 → 3 < p₆) ∧ (p₅ = 3 → 2 < p₆) := by
  obtain ⟨D⟩ := fourStage_of_completePivoting H hn hCP hdet
  exact sixth_pivot_exclusions_of_fourStage D

/-- Arbitrary row and column orders: every order satisfying the maximal
pivot rule has the same three possibilities. No tie-breaking rule is
imposed. The permutations record the chosen pivot order. -/
theorem sixth_pivot_any_order (cited : CitedPivotFacts)
    {n : ℕ} (H : Hadamard n) (hn : 8 ≤ n) (rows cols : Equiv.Perm (Fin n))
    (hCP : CompletelyPivoted (H.reindex rows cols).entry) :
    let A := H.reindex rows cols
    let p₅ := pivotMagnitude A.entry ⟨4, by omega⟩
    let p₆ := pivotMagnitude A.entry ⟨5, by omega⟩
    (p₅ = 2 ∧ p₆ = 4) ∨
      (p₅ = 3 ∧ p₆ = 8 / 3) ∨ (p₅ = 3 ∧ p₆ = 10 / 3) :=
  sixth_pivot cited (H.reindex rows cols) hn hCP

end HadamardAppendix
