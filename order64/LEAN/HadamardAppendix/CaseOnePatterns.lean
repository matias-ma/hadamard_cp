import HadamardAppendix.SixRows

/-!
The small finite calculation in Case 1. The 32 surviving sign patterns
are split into the appendix's distance-two and distance-three branches.
The finite expansion is deliberately explicit; every branch invokes one
of the two analytic arguments, not an assumed exclusion theorem.
-/
namespace HadamardAppendix
open Matrix
namespace SixRows
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplication of the prefix `(1,a,b,c)` by `B⁻¹ = B/4`. -/
noncomputable def residual (D : SixRows ι) (i : Fin 6) (a b c : ℝ) (j : ι) : ℝ :=
  D.row i j - ((1+a+b+c)/4 * D.row 0 j + (1-a+b-c)/4 * D.row 1 j +
    (1+a-b-c)/4 * D.row 2 j + (1-a-b+c)/4 * D.row 3 j)

/-- Negative prefix correlation forces distance two or three, and both
are incompatible with the Schur bounds. -/
theorem pattern_contradiction (D : SixRows ι) (a b c d e f : ℝ)
    (ha : Sign a) (hb : Sign b) (hc : Sign c) (hd : Sign d) (he : Sign e) (hf : Sign f)
    (hneg : a*d + b*e + c*f < 0)
    (hx : ∀ j, |D.residual 4 a b c j| ≤ 2)
    (hz : ∀ j, |D.residual 5 d e f j| ≤ 2)
    (hbound : ∀ j, |D.residual 4 a b c j - D.residual 5 d e f j| ≤ 3) : False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    norm_num at hneg
  -- Prefixes (1, 1, 1) and (1, -1, -1): distance 2.
  · apply D.distance_two 0 2 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, 1, 1) and (-1, 1, -1): distance 2.
  · apply D.distance_two 0 1 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, 1, 1) and (-1, -1, 1): distance 2.
  · apply D.distance_two 0 3 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, 1, 1) and (-1, -1, -1): distance 3.
  · let E := D.reindex ⟨![0, 1, 2, 3, 5, 4], by decide⟩
    apply E.distance_three
    · intro j
      convert hz j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
    · intro j
      have h := hbound j
      rw [abs_sub_comm] at h
      convert h using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
  -- Prefixes (1, 1, -1) and (1, -1, 1): distance 2.
  · apply D.distance_two 1 3 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, 1, -1) and (-1, 1, 1): distance 2.
  · apply D.distance_two 2 3 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, 1, -1) and (-1, -1, 1): distance 3.
  · let E := D.reindex ⟨![3, 0, 1, 2, 4, 5], by decide⟩
    apply E.distance_three
    · intro j
      convert hx j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
    · intro j
      convert hbound j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
  -- Prefixes (1, 1, -1) and (-1, -1, -1): distance 2.
  · apply D.distance_two 0 3 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, -1, 1) and (1, 1, -1): distance 2.
  · apply D.distance_two 1 3 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, -1, 1) and (-1, 1, 1): distance 2.
  · apply D.distance_two 1 2 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, -1, 1) and (-1, 1, -1): distance 3.
  · let E := D.reindex ⟨![1, 0, 2, 3, 4, 5], by decide⟩
    apply E.distance_three
    · intro j
      convert hx j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
    · intro j
      convert hbound j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
  -- Prefixes (1, -1, 1) and (-1, -1, -1): distance 2.
  · apply D.distance_two 0 1 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, -1, -1) and (1, 1, 1): distance 2.
  · apply D.distance_two 0 2 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, -1, -1) and (-1, 1, 1): distance 3.
  · let E := D.reindex ⟨![2, 0, 1, 3, 5, 4], by decide⟩
    apply E.distance_three
    · intro j
      convert hz j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
    · intro j
      have h := hbound j
      rw [abs_sub_comm] at h
      convert h using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
  -- Prefixes (1, -1, -1) and (-1, 1, -1): distance 2.
  · apply D.distance_two 1 2 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (1, -1, -1) and (-1, -1, 1): distance 2.
  · apply D.distance_two 2 3 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, 1, 1) and (1, 1, -1): distance 2.
  · apply D.distance_two 2 3 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, 1, 1) and (1, -1, 1): distance 2.
  · apply D.distance_two 1 2 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, 1, 1) and (1, -1, -1): distance 3.
  · let E := D.reindex ⟨![2, 0, 1, 3, 4, 5], by decide⟩
    apply E.distance_three
    · intro j
      convert hx j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
    · intro j
      convert hbound j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
  -- Prefixes (-1, 1, 1) and (-1, -1, -1): distance 2.
  · apply D.distance_two 0 2 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, 1, -1) and (1, 1, 1): distance 2.
  · apply D.distance_two 0 1 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, 1, -1) and (1, -1, 1): distance 3.
  · let E := D.reindex ⟨![1, 0, 2, 3, 5, 4], by decide⟩
    apply E.distance_three
    · intro j
      convert hz j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
    · intro j
      have h := hbound j
      rw [abs_sub_comm] at h
      convert h using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
  -- Prefixes (-1, 1, -1) and (1, -1, -1): distance 2.
  · apply D.distance_two 1 2 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, 1, -1) and (-1, -1, 1): distance 2.
  · apply D.distance_two 1 3 1 (-1) (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, -1, 1) and (1, 1, 1): distance 2.
  · apply D.distance_two 0 3 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, -1, 1) and (1, 1, -1): distance 3.
  · let E := D.reindex ⟨![3, 0, 1, 2, 5, 4], by decide⟩
    apply E.distance_three
    · intro j
      convert hz j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
    · intro j
      have h := hbound j
      rw [abs_sub_comm] at h
      convert h using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
  -- Prefixes (-1, -1, 1) and (1, -1, -1): distance 2.
  · apply D.distance_two 2 3 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, -1, 1) and (-1, 1, -1): distance 2.
  · apply D.distance_two 1 3 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, -1, -1) and (1, 1, 1): distance 3.
  · let E := D.reindex ⟨![0, 1, 2, 3, 4, 5], by decide⟩
    apply E.distance_three
    · intro j
      convert hx j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
    · intro j
      convert hbound j using 1 <;> congr 1 <;>
        dsimp [E, reindex, residual] <;> ring
  -- Prefixes (-1, -1, -1) and (1, 1, -1): distance 2.
  · apply D.distance_two 0 3 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, -1, -1) and (1, -1, 1): distance 2.
  · apply D.distance_two 0 1 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring
  -- Prefixes (-1, -1, -1) and (-1, 1, 1): distance 2.
  · apply D.distance_two 0 2 (-1) 1 (by norm_num [Sign]) (by norm_num [Sign])
      (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
    intro j
    convert hbound j using 1 <;> congr 1 <;> dsimp [residual] <;> ring

end SixRows
end HadamardAppendix
