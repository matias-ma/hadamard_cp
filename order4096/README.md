# Order 4096 verification package

The supplied matrix is a row and column permutation of the Sylvester Hadamard
matrix of order 4096. Its diagonal elimination path is completely pivoted,
with growth **4608 = (9/8)4096** and exactly one overshoot, **+4608 at step 4089**.
The proof, including the lifting lemma and 124 explicit pivot choices, is in
[main.pdf](main.pdf). The seven-page manuscript contains two black-and-white
figures. The displayed 8 by 8 residual uses the working row
and column order of Appendix A; the stored matrix has already been permuted
to put the same oversized entry on the active diagonal.

## Run the checks

From the repository root, using Python 3.10 or newer:

```sh
python3 order4096/verify_construction.py
python3 order4096/verify_package.py
```

Both commands use only the Python standard library. The constructor checks
124 local pivot choices in exact rational arithmetic and expands four W4
lifts. It checks every stored matrix entry against the reconstructed Sylvester
permutation, certifying orthogonality by the Sylvester identity. The lifting
lemma in the PDF justifies the intervening pivot choices.

The package checker additionally verifies SHA-256 checksums, the JSON
certificate, every row of the exported pivot table, and byte-identical matrix
regeneration. It also runs the preserved extended constructor and compares
both permutations and all signed pivots. It compares the recorded matrix-only
dense history with all 4096 construction pivots and active maxima. Checksums
detect accidental changes; they are not mathematical proofs or signatures.

For a separate dense calculation that reads only the matrix:

```sh
python3 -m venv /tmp/hadamard-verify-env
/tmp/hadamard-verify-env/bin/python -m pip install 'numpy>=2.0'
/tmp/hadamard-verify-env/bin/python order4096/verify_dense.py --seconds 1800
```

All checks remain enabled under `python -O`. The dense verifier reads only the
matrix during the calculation. It checks orthogonality using integer Hamming
distances between every pair of packed sign rows, then performs all 4096
complete-pivot comparisons and Schur updates using scaled int64 numerators
and Python integer denominators. Explicit bounds prevent overflow and every
GCD division is checked for exactness. It enforces growth exactly 4608, exactly
one overshoot (+4608 at step 4089), prefix maximum 1024, and the signed-pivot
digest below. It reports progress, numerator/denominator maxima, and runtime.
Allow several minutes and roughly 1 GB of available memory. `--seconds` is
optional; its deadline is checked between operations, so a running NumPy
operation can finish after the deadline. Timeout or interruption is incomplete
verification and never produces a success report. `--matrix FILE` selects a
matrix; the default resolves next to the script, regardless of working directory.
`--output FILE.json` saves all signed pivots and whole-active maxima.

For independent small-minor corroboration and verifier negative controls:

```sh
/tmp/hadamard-verify-env/bin/python order4096/check_complementary_minors.py \
  --compare-pivots order4096/pivots.csv
/tmp/hadamard-verify-env/bin/python -O -B -m unittest discover \
  -s order4096 -p test_verify_dense.py -v
```

The minor checker uses Python integer Bareiss determinants and cofactors to
recover the final fourteen signed pivots. It verifies det(D8) = 512,
det(D7) = 576, and the unique positive inverse maximum 9/8 at (0,0).
This independently corroborates the critical pivot; it relies on a separately
verified Hadamard matrix and legal prefix, rather than proving reachability.

## Data and reproducibility

- `main.pdf`: the manuscript; TeX, bibliography, and figure build inputs are
  not distributed in this repository.
- `matrix.npy`: 4096 by 4096 signed-int8 array, NPY 1.0, row-major order.
- `verify_construction.py`: the exact rational constructor, unchanged.
- `verify_dense.py`: strengthened matrix-only verifier adapted from the supplied
  independent audit; requires NumPy >= 2.0.
- `check_complementary_minors.py`: adapted independent complementary-minor check.
- `test_verify_dense.py`: malformed-input, corrupt-matrix, illegal-order and
  timeout negative controls, including execution under optimization.
- `pivot_certificate.json`: the 124 choices as ordinary integer pairs, with
  stage dimensions and ordering conventions; checked against the constructor.
- `pivots.csv`: all 4096 signed pivots and the complete row/column permutations.
  Steps are one-based; Sylvester row/column labels are zero-based. The last
  column is the whole-active maximum certified by the construction and lemma.
- `verify_package.py`: portable integrity and consistency checks.
- `verify_extended.py`: the previous published constructor, retained for its
  additional exact W2/W4 panel, quarter-state inverse, binary-rank, signed
  determinant, and final-core checks. Its provenance is recorded in `audit/`.
- `SHA256SUMS`: current hashes for all release files in this directory except
  itself (ignoring local bytecode caches and `.DS_Store`).
- `audit/`: fresh execution logs, full dense pivot history, and provenance.
  `audit/external/` holds the original supplied report and its source hashes;
  these describe the earlier attachment set, not this repaired release.
- `verification.txt`, `construction_verification_recheck.txt`: unchanged
  historical logs from earlier, more extensive versions of the verifiers.
  Their script hashes and some claims/output options do not describe the
  current scripts. Use `audit/` for the current execution record.

To regenerate the matrix and pivot table without replacing the supplied data:

```sh
python3 order4096/verify_construction.py --write-matrix \
  --matrix /tmp/hadamard-regenerated.npy --pivots /tmp/hadamard-pivots.csv
```

Matrix SHA-256:
`3bde6b6832b314cbb8d0c92cf0e8ee651ef4e7a657caf4e3a4de051a97b3d99d`.
Signed-pivot SHA-256 (one exact fraction per line, including final newline):
`a761528e59bee03cd387a0b6b50e3d44efce44fc5d734fe8a326b684f9bfbec0`.

This is computational verification of the stated counterexample, not a claim
of external peer review, a formal proof assistant certification, or minimality
of order 4096. The asymptotic conjecture in the paper is separate from the
verified construction.
