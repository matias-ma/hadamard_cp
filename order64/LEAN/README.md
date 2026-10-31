# Sixth-pivot appendix in Lean

This project follows the proof in Appendix A of `../main.tex`: the three
observations, the `p₅ = 2` case with its distance-two and distance-three
branches, and the `p₅ = 3` case with the polynomial certificate and counting
contradiction. The manuscript itself is unchanged.

## Exact scope

The public theorem is `HadamardAppendix.sixth_pivot` in
[`HadamardAppendix/Main.lean`](HadamardAppendix/Main.lean). It now starts
with an **arbitrary real Hadamard matrix** `H`, an order bound `8 ≤ n`,
and the direct hypothesis `CompletelyPivoted H.entry`. Its conclusion is

```text
(p₅ = 2 ∧ p₆ = 4) ∨ (p₅ = 3 ∧ p₆ = 8/3) ∨ (p₅ = 3 ∧ p₆ = 10/3),
```

where `p₅` and `p₆` are bound by `let` to the actual fifth and sixth pivot
magnitudes of the recursive GE computation. They are not arbitrary
numbers supplied by the caller. Lean uses zero-based indices, so their
pivot indices are 4 and 5.

The one external mathematical input, `cited : CitedPivotFacts`, states
exactly the two preliminary results used from the cited literature
(Day–Peterson and Kravvaritis–Mitrouli) for every CP Hadamard matrix of
order at least eight:

1. The actual leading four-by-four submatrix has determinant magnitude 16.
2. The actual fifth and sixth pivots belong to the preliminary seven-pair
   candidate table.

These published results are **explicit hypotheses**, not declared axioms.
No proof of `CitedPivotFacts` is supplied. Its definition contains neither
`FourStage` nor either exclusion nor the final three-pair conclusion.
The `#print axioms` audit does not remove this explicit hypothesis.

Everything connecting those published facts to the conclusion is now
proved in this project:

- `eliminate` defines GE by the scalar Schur update, retaining zeros in
  the retired rows and columns. `CompletelyPivoted` requires a nonzero
  pivot and maximal absolute value among the active entries at each step.
  The inequality is non-strict, so every choice among maximizing ties is
  allowed. No leading-block property is built into this definition.
- The retired entries are proved zero, and each eliminated row is proved
  to be the original row minus a combination of earlier original rows.
- A four-by-four sign matrix with determinant magnitude 16 is proved
  Hadamard. This order-four equality case is checked after normalizing
  the first row and column, by a finite calculation on the remaining
  nine signs.
- The fourth block-Schur formula is derived from the scalar GE recurrence
  and leading-block orthogonality. The fifth formula follows from the
  next GE update.
- These identities and the CP bounds construct `FourStage` internally.
- Both exclusion arguments and all their normalizations are proved as
  before. The original local conclusion remains available as the
  lower-level theorem `sixth_pivot_of_fourStage`.

`sixth_pivot_any_order` allows arbitrary full row and column permutations
and applies to every resulting order that satisfies complete pivoting.
Thus no particular pivot order or tie-breaking rule is assumed.

`sixth_pivot_exclusions` proves the two strict inequalities for the actual
GE pivots from CP and the leading determinant value, without using the
candidate table. The separate sharpness remark citing order-16 examples
is not formalized.

## Build and audit

The project pins Lean **4.20.0**, mathlib **v4.20.0**, and transitive
revisions in `lake-manifest.json`.

```sh
cd LEAN
lake exe cache get
lake build
lake env lean Audit.lean
```

`Audit.lean` prints the main theorems' axiom dependencies. They should be
only Lean/mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry` proofs, project-specific axioms, `native_decide`,
floating-point certificates, or external theorem-prover calls.

## Correspondence with the appendix

| Appendix step | Lean source |
|---|---|
| Scalar GE recurrence, actual pivots, and complete pivoting | `GaussianElimination.lean` |
| Leading determinant equality implies the block is Hadamard | `DeterminantFour.lean` |
| Derive the Schur identities and construct `FourStage` from CP | `CPBridge.lean` |
| Signs, orthogonality, candidate table and final selection | `Basic.lean` |
| Observation 1: allowed transformations and Schur invariance | `Transformations.lean`, `Stage.lean` |
| Observation 2: eliminated rows and zero entries; displayed inverses | `Schur.lean` |
| Observation 3: splitting a sum by signs | `Basic.lean` (`sum_half`) |
| Normalize the leading block to the displayed `B` | `CanonicalFour.lean` |
| Even/odd prefix argument and equality in Cauchy–Schwarz | `SmallBlocks.lean` |
| Case 1: select a negatively correlated row using column orthogonality | `NormalizedCaseOne.lean` (`witness`) |
| Case 1: distance two, energy `4n`, and contradiction | `CaseOne.lean`, `SixRows.lean` |
| Case 1: distance three, column switching, and the half-sum contradiction | `CaseOne.lean`, `SixRows.lean` |
| Small finite prefix calculation splitting the two distances | `CaseOnePatterns.lean` |
| Case 1: parity, transpose, and `c = 1` reductions | `CaseOneReduction.lean` |
| Case 2: row/column sums two; move the unique minuses to the diagonal | `RegularFour.lean`, `CaseTwoReduction.lean` |
| Case 2: normalize remaining prefixes to at most two minuses | `FiveNormalization.lean` |
| Orthogonality identities for sums of selected rows | `Orthogonality.lean` |
| Polynomial `Pⱼ`, table, lower bound 36, and moment/counting equations | `CaseTwo.lean` |
| Derive every certificate/counting input from the normalized matrix | `NormalizedCaseTwo.lean` |
| Full Case 2 reduction and exclusion | `CaseTwoReduction.lean` |
| Public theorem for every CP Hadamard matrix; cited facts and final selection | `Main.lean` |

All source files in the table are under `HadamardAppendix/`. Lean indices
start at zero. Selected indices use embeddings so that permutations can
be represented without repeatedly relabeling an entire matrix. The
distance-two argument uses one of the five zero entries to obtain a
strict energy contradiction; this is the same argument with a slightly
weaker sufficient bound. Small sign-pattern case splits use ordinary
kernel-checked arithmetic; they do not replace the analytic arguments.
