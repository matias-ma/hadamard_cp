import HadamardAppendix.CaseOnePatterns

set_option maxRecDepth 2048

namespace HadamardAppendix
open Finset Matrix

/-- The explicit `h₁:₄ B⁻¹ H₁:₄,:` residual for the displayed `B`, when
the first column is positive. -/
noncomputable def residualFour {n : ℕ} (H : Hadamard n)
    (r c : Fin 4 ↪ Fin n) (i j : Fin n) : ℝ :=
  let a := H.entry i (c 1)
  let b := H.entry i (c 2)
  let d := H.entry i (c 3)
  H.entry i j - ((1+a+b+d)/4 * H.entry (r 0) j + (1-a+b-d)/4 * H.entry (r 1) j +
    (1+a-b-d)/4 * H.entry (r 2) j + (1-a-b+d)/4 * H.entry (r 3) j)

/-- Case 1 after making `c = 1`, as in the appendix. The two Schur bounds
are stated on whole eliminated rows, including their leading zero entries. -/
structure CaseOneNormalForm (n : ℕ) where
  H : Hadamard n
  r : Fin 4 ↪ Fin n
  c : Fin 4 ↪ Fin n
  z : Fin n
  q : Fin n
  block : ∀ t u, H.entry (r t) (c u) = B t u
  firstColumn : ∀ i, H.entry i (c 0) = 1
  fifthColumn : ∀ t, H.entry (r t) q = 1
  qOutside : ∀ t, q ≠ c t
  pivot : H.entry z q = -1
  schur4 : ∀ i, (∀ t, i ≠ r t) → ∀ j, |residualFour H r c i j| ≤ 2
  schur5 : ∀ i, (∀ t, i ≠ r t) → i ≠ z → ∀ j,
    |residualFour H r c i j - residualFour H r c i q / residualFour H r c z q *
      residualFour H r c z j| ≤ 3

namespace CaseOneNormalForm
variable {n : ℕ} (D : CaseOneNormalForm n)

lemma outside (i : Fin n) (hi : D.H.entry i D.q = -1) (t : Fin 4) : i ≠ D.r t := by
  intro h
  rw [h, D.fifthColumn] at hi
  norm_num at hi

lemma residual_at_pivot (i : Fin n) :
    residualFour D.H D.r D.c i D.q = D.H.entry i D.q - 1 := by
  simp only [residualFour, D.fifthColumn]
  ring

lemma witness : ∃ x : Fin n, D.H.entry x D.q = -1 ∧ x ≠ D.z ∧
    D.H.entry x (D.c 1) * D.H.entry D.z (D.c 1) +
    D.H.entry x (D.c 2) * D.H.entry D.z (D.c 2) +
    D.H.entry x (D.c 3) * D.H.entry D.z (D.c 3) < 0 := by
  let R := univ.filter (fun i => D.H.entry i D.q = -1)
  have hs (t : Fin 4) (ht : t ≠ 0) : ∑ i ∈ R, D.H.entry i (D.c t) = 0 := by
    apply (sum_half (fun i => D.H.entry i (D.c t)) (fun i => D.H.entry i D.q)
      (fun i => D.H.signs i D.q) _ _).2
    · have h := D.H.cols (D.c t) (D.c 0)
      simpa only [D.firstColumn, mul_one, if_neg (fun h => ht (D.c.injective h))] using h
    · rw [D.H.cols, if_neg (Ne.symm (D.qOutside t))]
  let f := fun i => D.H.entry i (D.c 1) * D.H.entry D.z (D.c 1) +
    D.H.entry i (D.c 2) * D.H.entry D.z (D.c 2) +
    D.H.entry i (D.c 3) * D.H.entry D.z (D.c 3)
  have hsum : ∑ i ∈ R, f i = 0 := by
    simp only [f, sum_add_distrib, ← sum_mul, hs 1 (by decide), hs 2 (by decide),
      hs 3 (by decide), zero_mul, zero_add]
  have hfz : f D.z = 3 := by
    simp only [f, sign_mul_self (D.H.signs _ _)]
    norm_num
  have hz : D.z ∈ R := by simp [R, D.pivot]
  obtain ⟨x, hxR, hx⟩ := exists_negative_of_sum_zero hz (by linarith : 0 < f D.z) hsum
  refine ⟨x, (mem_filter.mp hxR).2, ?_, hx⟩
  intro he
  rw [he, hfz] at hx
  norm_num at hx

/-- The selected six rows, in the order used in the two distance arguments. -/
noncomputable def six (x : Fin n) (hx : ∀ t, x ≠ D.r t) (hxz : x ≠ D.z) : SixRows (Fin n) where
  row := ![D.H.entry (D.r 0), D.H.entry (D.r 1), D.H.entry (D.r 2),
    D.H.entry (D.r 3), D.H.entry x, D.H.entry D.z]
  sign i j := by fin_cases i <;> exact D.H.signs _ _
  orth i k hik := by
    have hz := D.outside D.z D.pivot
    fin_cases i <;> fin_cases k <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Fin.reduceFinMk] at *
    all_goals first | exact (hik rfl).elim | skip
    all_goals rw [show (fun j => _) ⬝ᵥ (fun j => _) = _ from D.H.rows _ _]
    all_goals simp_all [D.r.injective.eq_iff, ne_comm]
  column := D.c 0
  positive i := by fin_cases i <;> exact D.firstColumn _

/-- Case 1 in normalized matrix form: the bound `p₆ ≤ 3` is impossible. -/
theorem impossible (D : CaseOneNormalForm n) : False := by
  obtain ⟨x, hxq, hxz, hneg⟩ := D.witness
  have hx := D.outside x hxq
  have hz := D.outside D.z D.pivot
  let E := D.six x hx hxz
  apply E.pattern_contradiction
    (D.H.entry x (D.c 1)) (D.H.entry x (D.c 2)) (D.H.entry x (D.c 3))
    (D.H.entry D.z (D.c 1)) (D.H.entry D.z (D.c 2)) (D.H.entry D.z (D.c 3))
    (D.H.signs _ _) (D.H.signs _ _) (D.H.signs _ _)
    (D.H.signs _ _) (D.H.signs _ _) (D.H.signs _ _) hneg
  · simpa [E, six, SixRows.residual, residualFour] using D.schur4 x hx
  · simpa [E, six, SixRows.residual, residualFour] using D.schur4 D.z hz
  · intro j
    have h := D.schur5 x hx hxz j
    rw [D.residual_at_pivot, D.residual_at_pivot, hxq, D.pivot] at h
    norm_num at h
    simpa [E, six, SixRows.residual, residualFour] using h

end CaseOneNormalForm
end HadamardAppendix
