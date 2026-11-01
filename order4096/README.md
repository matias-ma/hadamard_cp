# A Hadamard matrix with growth factor greater than its order

The [paper](main.pdf) by Matias Andia is now uploaded to
[Zenodo](https://zenodo.org/records/23871097).

We construct a row and column permutation of the Sylvester Hadamard matrix
of order 4096 that is completely pivoted and has growth factor

$$g(H)=p_{4089}=4608=\frac{9}{8}4096>4096,$$

where $p_k$ denotes the magnitude of the $k$-th pivot. This disproves the
long-standing conjecture that every completely pivoted Hadamard matrix has
growth factor equal to its order. The construction extends to every order
$n=2^d$ with $d\ge12$, giving growth factor $9n/8$.

The proof combines a tensor-product lifting lemma with 124 explicit pivot
choices checked in exact rational arithmetic. This directory contains the
[matrix](matrix.npy), [pivot table](pivots.csv), and verification code.
To check the construction, run from the repository root (Python standard
library only):

```sh
python3 order4096/verify_construction.py
```
