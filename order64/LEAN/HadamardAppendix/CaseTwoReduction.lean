import HadamardAppendix.FiveNormalization
import HadamardAppendix.RegularFour

namespace HadamardAppendix
open Finset Matrix

/-- Extend the four selected indices by the fifth index. -/
def extendIndices {n : ℕ} (e : Fin 4 ↪ Fin n) (z : Fin n) (hz : ∀ t, z ≠ e t) : Fin 5 ↪ Fin n where
  toFun := Fin.lastCases z e
  inj' := by
    intro a b h
    cases a using Fin.lastCases <;> cases b using Fin.lastCases
    all_goals simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
    · rfl
    · exact (hz _ h).elim
    · exact (hz _ h.symm).elim
    · exact congrArg Fin.castSucc (e.injective h)

@[simp] lemma extendIndices_last {n : ℕ} (e : Fin 4 ↪ Fin n) (z : Fin n) (hz : ∀ t, z ≠ e t) :
    extendIndices e z hz (Fin.last 4) = z := by simp only [extendIndices, Function.Embedding.coeFn_mk, Fin.lastCases_last]
@[simp] lemma extendIndices_castSucc {n : ℕ} (e : Fin 4 ↪ Fin n) (z : Fin n) (hz : ∀ t, z ≠ e t)
    (t : Fin 4) : extendIndices e z hz t.castSucc = e t := by simp only [extendIndices, Function.Embedding.coeFn_mk, Fin.lastCases_castSucc]

lemma schurFour_regular {n : ℕ} (H : Hadamard n) (r c : Fin 4 ↪ Fin n)
    (hB : ∀ a b, H.entry (r a) (c b) = if a = b then -1 else 1) (i j : Fin n) :
    schurFour H r c i j = H.entry i j -
      (∑ b, H.entry i (c b)) * (∑ a, H.entry (r a) j) / 4 +
      (∑ a, H.entry i (c a) * H.entry (r a) j) / 2 := by
  have hs (a : Fin 4) : (∑ b, H.entry i (c b) * (if a = b then (-1 : ℝ) else 1)) =
      (∑ b, H.entry i (c b)) - 2 * H.entry i (c a) := by
    calc
      _ = ∑ b, (H.entry i (c b) - if a = b then 2 * H.entry i (c b) else 0) := by
        apply sum_congr rfl
        intro b _
        split_ifs <;> ring
      _ = _ := by simp [sum_sub_distrib]
  have hinner (a : Fin 4) :
      (∑ b, H.entry i (c b) * H.entry (r a) (c b) * H.entry (r a) j) =
        ((∑ b, H.entry i (c b)) - 2 * H.entry i (c a)) * H.entry (r a) j := by
    rw [← sum_mul]
    simp_rw [hB]
    rw [hs]
  unfold schurFour
  rw [show (∑ a, ∑ b, H.entry i (c b) * H.entry (r a) (c b) * H.entry (r a) j) =
      ∑ a, ((∑ b, H.entry i (c b)) - 2 * H.entry i (c a)) * H.entry (r a) j from
      sum_congr rfl (fun a _ => hinner a)]
  simp only [sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
  ring

namespace FourStage
variable {n : ℕ} {p₆ : ℝ}

/-- Make `r = c = 1` and `ε = -1`, using only allowed sign changes. -/
theorem exists_case_two_border (D : FourStage n 3 p₆) :
    ∃ E : FourStage n 3 p₆,
      (∀ t, E.H.entry (E.r t) E.q = 1) ∧
      (∀ t, E.H.entry E.z (E.c t) = 1) ∧ E.H.entry E.z E.q = -1 := by
  let a := fun i => if i = D.z then (1 : ℝ) else -D.H.entry D.z D.q * D.H.entry i D.q
  let b := fun j => if j = D.q then -D.H.entry D.z D.q else D.H.entry D.z j
  have ha (i) : Sign (a i) := by
    dsimp [a]
    split_ifs
    · exact Or.inl rfl
    · exact sign_product (sign_neg (D.H.signs _ _)) (D.H.signs _ _)
  have hb (j) : Sign (b j) := by
    dsimp [b]
    split_ifs
    · exact sign_neg (D.H.signs _ _)
    · exact D.H.signs _ _
  let E := D.signed a b ha hb
  refine ⟨E, ?_, ?_, ?_⟩
  · intro t
    change a (D.r t) * D.H.entry (D.r t) D.q * b D.q = 1
    simp only [a, b, if_neg (Ne.symm (D.zOutside t)), if_pos rfl]
    rcases D.H.signs D.z D.q with h | h <;> rcases D.H.signs (D.r t) D.q with h' | h' <;>
      rw [h, h'] <;> norm_num
  · intro t
    change a D.z * D.H.entry D.z (D.c t) * b (D.c t) = 1
    simp only [a, b, if_pos rfl, if_neg (Ne.symm (D.qOutside t)), one_mul]
    exact sign_mul_self (D.H.signs _ _)
  · change a D.z * D.H.entry D.z D.q * b D.q = -1
    simp only [a, b, if_pos rfl, one_mul]
    rcases D.H.signs D.z D.q with h | h <;> rw [h] <;> norm_num

/-- At fifth pivot 3 the leading five-by-five block can be put in the form
`J₅ - 2I₅`. -/
theorem exists_case_two_regular (D : FourStage n 3 p₆) :
    ∃ E : FourStage n 3 p₆,
      (∀ a b, E.H.entry (E.r a) (E.c b) = if a = b then -1 else 1) ∧
      (∀ t, E.H.entry (E.r t) E.q = 1) ∧
      (∀ t, E.H.entry E.z (E.c t) = 1) ∧ E.H.entry E.z E.q = -1 := by
  obtain ⟨P, hc, hr, hε⟩ := D.exists_case_two_border
  have hp : |(-1 : ℝ) - (∑ a, ∑ b, P.leading.entry a b) / 4| = 3 := by
    have h := P.pivot
    simpa only [schurFour, hr, hc, hε, one_mul, mul_one, ← P.leading_eq] using h
  obtain ⟨e, he⟩ := regular_four_permutation P.leading (regular_four P.leading hp).2
  refine ⟨P.reindexCols e, ?_, hc, ?_, hε⟩
  · intro a b
    change P.H.entry (P.r a) (P.c (e b)) = _
    rw [← P.leading_eq]
    exact he a b
  · intro t
    exact hr (e t)

/-- The complete second exclusion, before candidate-table selection. -/
theorem case_two (D : FourStage n 3 p₆) : 2 < p₆ := by
  by_contra! hp
  obtain ⟨E, hB, hc, hr, hε⟩ := D.exists_case_two_regular
  let r := extendIndices E.r E.z E.zOutside
  let c := extendIndices E.c E.q E.qOutside
  have hF : ∀ t u, E.H.entry (r t) (c u) = if t = u then -1 else 1 := by
    intro t u
    cases t using Fin.lastCases <;> cases u using Fin.lastCases <;>
      simp only [r, c, extendIndices_last, extendIndices_castSucc, hB, hc, hr, hε,
        Ne.symm (Fin.castSucc_ne_last _), Fin.castSucc_ne_last, Fin.castSucc_inj, ↓reduceIte]
  apply case_two_from_F E.H r c hF
  intro i j
  have heq : residualFive E.H r c i j = schurFive E.H E.r E.c E.z E.q i j := by
    simp only [residualFive, Fin.sum_univ_castSucc (n := 4), r, c,
      extendIndices_last, extendIndices_castSucc, schurFive,
      schurFour_regular E.H E.r E.c hB, hr, hc, hε, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, one_mul, mul_one]
    simp only [sub_mul, sum_sub_distrib, ← mul_sum, ← sum_div, ← sum_mul, mul_assoc]
    ring_nf
    simp only [← sum_mul]
  rw [heq]
  exact le_trans (E.bound5 i j) hp

end FourStage
end HadamardAppendix
