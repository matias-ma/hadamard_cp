# Order-4096 verification records

This release repairs the issues in the user-supplied
`hadamard_counterexample_audit.zip`. Changes apply only to order 4096.
The matrix, all 124 local choices, the constructor, and both full
permutations remain unchanged. The signed-pivot digest remains
`a761528e59bee03cd387a0b6b50e3d44efce44fc5d734fe8a326b684f9bfbec0`.

## Current executions

Python 3.13.5, NumPy 2.5.4. Commands run from the repository root:

- `python3 -B order4096/verify_construction.py` → `construction.txt`.
- `python3 -B order4096/verify_extended.py` → `extended.txt`.
- `python -O order4096/verify_dense.py --seconds 1800 --output
  order4096/audit/dense_pivots.json` → `dense.txt`. The full run deliberately
  uses optimization to demonstrate that verification checks cannot disappear.
- `python order4096/check_complementary_minors.py --compare-pivots
  order4096/pivots.csv` → `complementary_minors.txt`.
- `python -O -B -m unittest discover -s order4096 -p test_verify_dense.py -v`
  → `negative_controls.txt`.
- `python3 -B order4096/verify_package.py` verifies manifest coverage and every
  checksum, JSON choices, CSV permutations/pivots, both constructors, byte-for-byte
  matrix regeneration, and all 4096 dense pivots and active maxima. Comparing a
  saved history is a consistency check; rerun the dense command to reproduce it.

The dense verifier was adapted from `independent_dense_audit.py` in the supplied
ZIP. Its integer packed-bit orthogonality check and exact Schur calculation
read only the matrix. Expected growth, overshoot, prefix maximum, and digest
are enforced after the calculation. The complementary-minor checker was
adapted from the ZIP's `check_complementary_minors.py`, with a portable default
path and explicit unique-maximum/critical-determinant checks.

## Manuscript and historical records

The PDF was rebuilt from `hadamard4096/main.tex` in the adjacent research
workspace using pdfLaTeX (TeX Live 2026). The sole text change adds “in the
working row and column order of Appendix A” immediately before the displayed
8 by 8 residual. Extracted text was compared against the previous PDF;
all seven rendered pages were visually checked. The supplied ZIP's
`audit_package_consistency.py --input order4096` was also run with PyMuPDF 2.0,
Pillow 13.0.0, NumPy 2.5.4 and Poppler `pdftotext`. Its manuscript results are
saved in `pdf_consistency.json` (the pre-freeze manifest section is omitted).
All 124 appendix pairs, all 6,300 Figure 1 vector cells, all 16,777,216 Figure 2
pixels, and the displayed residual match exactly. No numerical data changed.
The repository continues to distribute only the manuscript PDF, not a LaTeX
build kit; no source or figure build is promised by its reproduction instructions.

`verify_extended.py` is an unchanged copy of the published constructor from
commit `53c1796f1f315f035f4d6b5985f69850b7ddcd0f`. It retains additional
W2/W4 panel identities, quarter-state inverse identities, binary ranks, signed
determinant product, and final-core checks.

The top-level `verification.txt` and `construction_verification_recheck.txt`
are preserved historical logs. They are not output of the current verifiers.
The preceding release's simpler dense verifier can be recovered from Git
commit `3d4d6cc`; `dense.txt` now records the strengthened verifier above.

`external/AUDIT_REPORT.txt` and `external/SOURCE_SHA256SUMS` are unmodified
excerpts from the supplied ZIP. That report describes an earlier attachment
set, uses its old filenames, and records missing sources and stale checksums.
It is preserved as provenance, not as a current release manifest or as a claim
of external peer review. The release manifest is `../SHA256SUMS`.

No verification here establishes minimality of order 4096 or settles the
separate asymptotic conjecture in the paper.
