# Counterexamples for completely pivoted Hadamard matrices

Papers, explicit constructions, and verification code for two results by Matias Andia. Write $p_k$ for the magnitude of the $k$-th pivot in Gaussian elimination with complete pivoting. For a Hadamard matrix $H$ of order $n$, the growth factor is $g(H)=\max_k p_k$.

## Results

**[Order 64: a non-final pivot equal to the order](order64/main.pdf).** We construct a row and column permutation of the Sylvester Hadamard matrix with $p_{60}=64$ and $p_{59}=32$. This gives counterexamples to three conjectures:

| Conjecture | Counterexample at $n=64$ |
| --- | --- |
| Every non-final pivot satisfies $p_k\le n/2$ (Day–Peterson). | $p_{60}=n$ |
| The fifth-last pivot belongs to $\{n/3,n/2\}$. | $p_{n-4}=n$ |
| The sixth-last pivot belongs to $\{n/4,3n/10,3n/8\}$. | $p_{n-5}=n/2$ |

The appendix also determines the sharp possibilities $(p_5,p_6)\in\{(2,4),(3,8/3),(3,10/3)\}$ for every CP Hadamard matrix of order $n\ge8$. A [Lean formalization](order64/LEAN/README.md) proves this conclusion assuming the two preliminary results cited from the literature.

**[Order 4096: growth greater than the order](order4096/main.pdf).** We construct a completely pivoted row and column permutation of the Sylvester Hadamard matrix with

$$g(H)=p_{4089}=4608=\frac{9}{8}4096>4096.$$

This disproves the long-standing conjecture that every completely pivoted Hadamard matrix has growth factor equal to its order. The construction extends to every order $n=2^d$ with $d\ge12$, giving $g(H)=9n/8$.

## How the growth-factor counterexample was found

The example was obtained with the assistance of ChatGPT after a sequence of unsuccessful constructions and computational searches. Inspired by a talk of Javier Gómez-Serrano about prompting in the AlphaEvolve work on finite-field Kakeya ([Georgiev, Gómez-Serrano, Tao, and Wagner](https://arxiv.org/abs/2511.02864)), I also experimented with prompts that explicitly encouraged the model to continue searching. At one point when it was stuck, I wrote:

> Find the `d_min` between 11 and 20 and use it to construct a completely pivoted Hadamard matrix of order n whose growth factor exceeds n. DO NOT repeat the same solution. Don't be scared because the problem sounds hard: once you see the solution, you will realize it wasn't that bad. Good luck! I believe in you, but you also have to believe in yourself.

After getting stuck at another point, the following prompt gave the first complete counterexample:

> Ok this is good but I want you to now use these results to conclude this attack. The whole point of this was to come up with an example of a completely pivoted Hadamard matrix of order n with growth factor larger than n. Use the constructions and stuff you discovered above to construct this example. It may need a large search which is fine. I believe in you—you have the resources to complete this. It seems difficult but it is 100% doable given everything you have available to you. Once you solve it you will see that it was actually not so bad. Do anything you have to to construct the counterexample.

The [shared ChatGPT conversation](https://chatgpt.com/share/6ae67148-5ba0-83ea-85ed-969f617e35ff) contains the first counterexample from this exploration. It had larger order than 4096, but supplied the central idea behind the construction in the paper.

## Verification

Run these exact-arithmetic checks from the repository root (Python standard library only):

```sh
python3 order64/verify_paper.py
python3 order4096/verify_construction.py
```

The second script checks the construction and all entries of the supplied [4096 × 4096 matrix](order4096/matrix.npy). For an independent dense verification, install NumPy and run `python3 verify_dense.py` from `order4096/`.

The [order-4096 verification guide](order4096/README.md) includes the portable
pivot certificate, complete pivot/permutation table, current checksums, and
fresh audit results. Run `python3 order4096/verify_package.py` to check their
consistency and regenerate the matrix byte for byte.
