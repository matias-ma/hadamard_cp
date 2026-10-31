import HadamardAppendix.Basic

/-! # Case 1: the two distance branches for `p₅ = 2` -/
namespace HadamardAppendix
open Finset Matrix

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The discrete step in the four-row energy argument. -/
lemma four_sign_bound {x z a b : ℝ}
    (hx : Sign x) (hz : Sign z) (ha : Sign a) (hb : Sign b)
    (hv : |x - z - a - b| ≤ 3) : (x - z - a - b) ^ 2 ≤ 4 := by
  rcases hx with rfl | rfl <;> rcases hz with rfl | rfl <;>
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num at *

/-- Four distinct orthogonal sign rows have energy `4n` in this combination.
The signs `α, β` in the appendix can be absorbed into `a, b`. -/
theorem four_row_energy (x z a b : ι → ℝ)
    (hx : ∀ j, Sign (x j)) (hz : ∀ j, Sign (z j))
    (ha : ∀ j, Sign (a j)) (hb : ∀ j, Sign (b j))
    (hxz : x ⬝ᵥ z = 0) (hxa : x ⬝ᵥ a = 0) (hxb : x ⬝ᵥ b = 0)
    (hza : z ⬝ᵥ a = 0) (hzb : z ⬝ᵥ b = 0) (hab : a ⬝ᵥ b = 0) :
    ∑ j, (x j - z j - a j - b j) ^ 2 = 4 * (Fintype.card ι : ℝ) := by
  have self (v : ι → ℝ) (hv : ∀ j, Sign (v j)) :
      v ⬝ᵥ v = (Fintype.card ι : ℝ) := by
    simp [dotProduct, sign_mul_self (hv _)]
  have hzx : z ⬝ᵥ x = 0 := by rw [dotProduct_comm, hxz]
  have hax : a ⬝ᵥ x = 0 := by rw [dotProduct_comm, hxa]
  have hbx : b ⬝ᵥ x = 0 := by rw [dotProduct_comm, hxb]
  have haz : a ⬝ᵥ z = 0 := by rw [dotProduct_comm, hza]
  have hbz : b ⬝ᵥ z = 0 := by rw [dotProduct_comm, hzb]
  have hba : b ⬝ᵥ a = 0 := by rw [dotProduct_comm, hab]
  simp only [pow_two]
  change (x - z - a - b) ⬝ᵥ (x - z - a - b) = _
  simp only [sub_dotProduct, dotProduct_sub, hxz, hxa, hxb, hza, hzb, hab,
    hzx, hax, hbx, haz, hbz, hba, self x hx, self z hz, self a ha, self b hb]
  ring

/-- Case 1, `d = 2`: the bound by 3 contradicts orthogonality and a zero
entry of the eliminated row. -/
theorem case_one_distance_two (x z a b : ι → ℝ) (j₀ : ι)
    (hx : ∀ j, Sign (x j)) (hz : ∀ j, Sign (z j))
    (ha : ∀ j, Sign (a j)) (hb : ∀ j, Sign (b j))
    (hxz : x ⬝ᵥ z = 0) (hxa : x ⬝ᵥ a = 0) (hxb : x ⬝ᵥ b = 0)
    (hza : z ⬝ᵥ a = 0) (hzb : z ⬝ᵥ b = 0) (hab : a ⬝ᵥ b = 0)
    (hzero : x j₀ - z j₀ - a j₀ - b j₀ = 0)
    (hbound : ∀ j, |x j - z j - a j - b j| ≤ 3) : False := by
  exact energy_contradiction _ j₀ hzero
    (fun j => four_sign_bound (hx j) (hz j) (ha j) (hb j) (hbound j))
    (four_row_energy x z a b hx hz ha hb hxz hxa hxb hza hzb hab)

/-- The parity step of the `d = 3` branch, checked on the sixteen possible
sign patterns. This is the appendix's averaging argument followed by parity. -/
lemma distance_three_nonnegative {a b c z : ℝ}
    (ha : Sign a) (hb : Sign b) (hc : Sign c) (hz : Sign z)
    (h₄ : |1 + (1 - (a + b + c)) / 2| ≤ 2)
    (h₅ : |(1 + (1 - (a + b + c)) / 2) - (z - 1)| ≤ 3) :
    0 ≤ a + b + c + z := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hz with rfl | rfl <;> norm_num at *

/-- Case 1, `d = 3`, after the column signs and first-four-row permutation
used in the appendix. The four orthogonality equations are collected into
one for `L + z`, since splitting the sum is linear. -/
theorem case_one_distance_three (x z a b c : ι → ℝ) (j₀ : ι)
    (hx : ∀ j, Sign (x j)) (hz : ∀ j, Sign (z j))
    (ha : ∀ j, Sign (a j)) (hb : ∀ j, Sign (b j)) (hc : ∀ j, Sign (c j))
    (hones : ∑ j, (a j + b j + c j + z j) = 0)
    (horth : ∑ j, (a j + b j + c j + z j) * x j = 0)
    (hcol : x j₀ = 1 ∧ a j₀ = 1 ∧ b j₀ = 1 ∧ c j₀ = 1 ∧ z j₀ = 1)
    (h₄ : ∀ j, |x j + (1 - (a j + b j + c j)) / 2| ≤ 2)
    (h₅ : ∀ j, |(x j + (1 - (a j + b j + c j)) / 2) - (z j - 1)| ≤ 3) :
    False := by
  have hsplit := (sum_half (fun j => a j + b j + c j + z j) x hx hones horth).1
  have hn : ∀ j ∈ univ.filter (fun j => x j = 1), 0 ≤ a j + b j + c j + z j := by
    intro j hj
    have h := (mem_filter.mp hj).2
    exact distance_three_nonnegative (ha j) (hb j) (hc j) (hz j)
      (by simpa [h] using h₄ j) (by simpa [h] using h₅ j)
  have hj : j₀ ∈ univ.filter (fun j => x j = 1) := by simp [hcol.1]
  have hp : 0 < a j₀ + b j₀ + c j₀ + z j₀ := by
    rcases hcol with ⟨_, h₁, h₂, h₃, h₄⟩
    norm_num [h₁, h₂, h₃, h₄]
  have := positive_sum hj hn hp
  linarith

end
end HadamardAppendix
