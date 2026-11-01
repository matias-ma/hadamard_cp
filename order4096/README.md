# Order 4096 verification package

The supplied matrix is a row and column permutation of the Sylvester Hadamard
matrix of order 4096. Its diagonal elimination path is completely pivoted,
with growth **4608 = (9/8)4096** and first overshoot **+4608 at step 4089**.
The proof, including the lifting lemma and 124 explicit pivot choices, is in
[main.pdf](main.pdf). This directory is self-contained for verifying the
construction. The PDF is the only manuscript artifact included.

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
both permutations and all signed pivots. Checksums detect accidental changes;
they are not mathematical
proofs or signatures.

For a separate dense calculation that reads only the matrix:

```sh
python3 -m venv /tmp/hadamard-verify-env
/tmp/hadamard-verify-env/bin/python -m pip install numpy
cd order4096
/tmp/hadamard-verify-env/bin/python verify_dense.py
```

Keep Python assertions enabled: do not use `-O`, `-OO`, or `PYTHONOPTIMIZE`.
The dense script uses assertions for its verification checks. It checks all
row inner products with binary64 matrix multiplication (the sums of 4096
products of signs are exactly representable), then performs all 4096 complete
pivot comparisons and Schur updates using scaled int64 numerators and Python
integer denominators. An explicit bound prevents int64 overflow. GCD reduction
divides the numerators and denominator exactly. Allow several minutes and
roughly 1 GB of available memory. The current script has no timeout option,
progress reporting, or signed-pivot digest output; its success line reports
the growth. An interrupted run is incomplete.

## Data and reproducibility

- `matrix.npy`: 4096 by 4096 signed-int8 array, NPY 1.0, row-major order.
- `verify_construction.py`, `verify_dense.py`: the original current verifiers,
  preserved byte for byte from the research workspace.
- `pivot_certificate.json`: the 124 choices as ordinary integer pairs, with
  stage dimensions and ordering conventions; checked against the constructor.
- `pivots.csv`: all 4096 signed pivots and the complete row/column permutations.
  Steps are one-based; Sylvester row/column labels are zero-based. The last
  column is the whole-active maximum certified by the construction and lemma.
- `verify_package.py`: portable integrity and consistency checks.
- `verify_extended.py`: the previous published constructor, retained for its
  additional exact W2/W4 panel, quarter-state inverse, binary-rank, signed
  determinant, and final-core checks. Its provenance is recorded in `audit/`.
- `SHA256SUMS`: current hashes for all files in this directory except itself.
- `audit/`: fresh results and the scope of this completeness audit.
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
