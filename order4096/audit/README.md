# Verification audit, 31 October 2026

The research workspace `hadamard4096` was compared with `hadamard_cp_repo/order4096`
and the published repository at commit
`53c1796f1f315f035f4d6b5985f69850b7ddcd0f`.

The six files already in the local order4096 directory matched the research
workspace byte for byte: `main.pdf`, `matrix.npy`, both current verifiers, and
the two historical verification logs. The local PDF and constructor were newer
than the published versions; this update includes those local versions.

Added the existing JSON pivot certificate and generated the full pivot CSV,
current checksums, reproduction guide, package checker, and fresh logs.
`verify_extended.py` is an unchanged copy of `order4096/verify_construction.py`
from the published commit above, preserving its additional verification checks
alongside the simpler current constructor. No original verification source or
matrix data was edited.

## Executed checks

- `construction.txt`: current rational constructor; all 124 choices, lifted
  pivot sequence, and all 16,777,216 matrix entries pass.
- `extended.txt`: preserved extended constructor; panel identities, five
  quarter-state inverse identities and binary ranks, signed determinant
  product, and the final-core pivot sequence pass.
- `dense.txt`: independent original dense verifier, with assertions enabled;
  all Gram entries and 4096 diagonal complete-pivot comparisons pass, and the
  exact resulting growth is 4608. Runtime and dependency versions are recorded.
- `verify_package.py`: both constructors agree on all permutations and signed
  pivots; the CSV and JSON agree; matrix regeneration is byte-identical;
  current package checksums pass.
- All 124 JSON choices were also compared with the six lists in the research
  manuscript appendix and agree. The illustrative pair examples before the
  lists were excluded from that comparison.

The signed-pivot digest matches the historical record:
`a761528e59bee03cd387a0b6b50e3d44efce44fc5d734fe8a326b684f9bfbec0`.
The fresh dense script reports growth only; it does not compute this digest.

## Completeness boundary

All mathematical verification inputs in the research workspace are included:
the explicit matrix, construction and dense verifiers, portable pivot choices,
and manuscript PDF containing the proof. The derived full pivot/permutation
table and additional published checks are included for convenience and audit.

At the author's request, no TeX, bibliography, figure assets, figure-generation
script, paper archive, or other paper build artifacts are included. The old
workspace README and checksum file were superseded rather than copied because
they refer to obsolete filenames and verifier versions. Operating-system
metadata and PR-submission administrative files are not mathematical
verification inputs and were excluded. The two original verification logs are
retained as historical records, not presented as output of the current scripts.

These checks verify this explicit counterexample and support the lifting
construction proved in the PDF; they do not settle the separate asymptotic
conjecture or establish that 4096 is the minimum possible order.
