#!/usr/bin/env python3
"""Verify the order-64 counterexample exactly. Run: python3 verify_hadamard.py

Python 3.10+, standard library only. '+' and '-' below mean +1 and -1.
Permutation and swap indices are zero-based; pivot numbers are one-based.
GECP breaks ties by the first maximum in row-major order.
"""

from fractions import Fraction
from math import prod
from pathlib import Path
import re

N = 64
H_SIGNS = """
+-+-++++++-++++-++++++++---+-++-+-----++-+-+-------++----+--+---
--++-+-+-++++---+-+-++--++++++----+-+-+--+--+-+++-+--+--++--+-+-
++++++--++------++---++--+-++--++-++----+-+-+---+++++-+-++--++--
-++--++--++--++-+--+-+-++-++--++---++--++-++--++-+---++--+--+++-
++-+-+++----+-+---++-++-+--++--++--++----+-+---+++-+---++-+++-++
+++----+-+--++-+-+-+++--+++-+-+-+--+-++---++--+---+-+-+++--++-+-
+-+++-+----++--++--++-+--+-++-+--+++---+-+----++-+--++++--+-+++-
+----+-----+-+------++++++-+-++-+-+-+-+++-+-+--+--++--++--++++++
-++-++-+---+--++-+-+--+++++-+-+-+-----+--++-++-+++---+-+-+--++-+
++++-++++-++-+-+------------------+-+-++-+++-++--++++--+++--++++
--+---+++-------++++-------+-++-+--+-+++----++++++++-++-+--+++++
+-+++--+--+--++-+-+---++++++++----+++++----+-+---+--+-+----+++-+
+-+--+--+-+-+-++--+++--+-+--++++---++---+---+++-+--++-++-+--+-++
-+++----+--++++-++--+--+-+-++--++-+--+--++++-+++---+-+-----++-++
---+++-++---++-+-++--+-++--++-+--+--++-++++--+-++---+-+-+---+++-
---+-+-+++---++++--++-+--++--+-++--++--+-++-++------++--+-+++++-
+-++--+--+-+--++-++--+-++-+--+-++-+--+-+++--+-+-++--+--+---++++-
--+-+-++++--+-+-----+++++++-+--+-+----+++----++--+++----+-+-++++
-++++---++-+-+----++-++-+-+--++--+++-----++++++-+--+--+---+-+-++
+++-+--+-----++++-+---++---+-+-+-+----+-+-+++-+++-+-++-++-+-+-+-
+--++--++--++--++--+-+-+-++--+-++---++-+--++--+++++---+--++-+--+
+---++---+-++++-++++------+-+--+-+++++++--+-----+-++-+-+----++++
++-+++++-+------++--+--+-++--++--+--++--++-++----+-+-++++---+-++
---++++-+-++--+--+-+++----++++--------+-+-++--+-+---+++++-++++-+
+-++---+-++-++---+-+++--------+++++-+-+-+--+++-+++--++----+-++-+
--+-+---++++-+-+--++-++--+--++++----++--++-+---+-+++-+-++--+++--
-+-+--++---++++-++---++--++--++--+-++---+----++++-+++--+-+-+++--
+--+--+-+++-++---+-+--++--++++-----+-++-+++-++-+-++----+-++-+-+-
----------------++++++++--+-+--+-++-+-++-+++++++-+-++-++++-++---
++-----+++++--+--++-+-+--+++--++--+--+-+---+-+-++-----+++++-+++-
+----+++--+-+-++--++-++--+++----+++--+--+++++++---++-++-----++--
--+++++-----++-+-++-+-+-+-+--+-++-++---++--+-+-+--+--+++++--+--+
-+-+------+----+++++++++++---------+-+++++-+----+-++++---++-++++
-+--+++-+--+--++-+-+++--++-+-+-+-++++++----+++-+-++-+-------+-+-
+-+--++++--+-+----------+++-+--+-+-+-+++++-++--++--++++--++++---
----+-++-+++-+-+--+++--+-+++----++++----+-+----+++-++---++-++-++
+---++++-++----+++--+--++---++++--++-----+++-++++-++------++++--
-++--+-+-+-++--++-+-++-----+-+-+-+-+-++-+++--+---+----++-+++++-+
--+-----+-++++++++--+--++-++----++-++----+-++---++++--+++-+-++--
-++-+++---+-++---++-+-+--+--++--++--++-+--+++-+-++-------++++++-
++--+--++-+++---+--+-+-++---++--++++---++--+++-------+-+++-++++-
-+-++----++-+-++----------++++++++----++-+-++--+--+++-+--+-+++++
--++-++--+---++++--+-+-+-+-++-+--++--+-+---+++--+-+----++++++--+
+--+---+++-+--++-++-+-+-+--++-+--+-++--++-+++-+--++--+---+-++--+
++----+-++--++-+-+-+--++++-+-+-+-++-+-+--+----+-+----++-++-+++-+
+--++-+-+-+--++-+-+-++--++----++++----+--++--+--+++--+++-+-++-+-
-+-++-++-+-+-+----+++--++--++--++---++------+++---++++++-++-++--
------++--++++++++---++-+---++++--+--+----+-+----+-++++-+++-+-++
+++-+-+---+++---+--++-+-+-++--++----++-++++-++--+-+-+---+--++--+
+++---+--+++--+--++--+-+-+--++--++-++--+-++--+-+--+-+++-+-+-+--+
-++++-+++++-+-++----++++----------++++++--+-+--++--+-+++---++---
+-+-++--+++----+++---++-+-++----++--++-------+++---+++-+-++++-++
-+---++-++-++--++-+---++--+-+-+-+-+-+-+-+--+-+--+++-+++---+++-+-
---+-++-+++++---+-+---++++----++++-+-++---+++-++----+--++---++-+
-+--++-++-+-++---++--+-+-+++--++--++---+-+--+-+--++-++-+--+++--+
++--+-+-+----++++-+-++----+-+-+-+-+++++-++--+-++--------+++-++-+
-+++--+++-+----+++++----+++++++++++-+-+++-+--------+---+--+-+---
++-+-+----++-+-+----++++--++++++++-+-+++-----++-++-+-+--+---+---
----+----+--+-+---------++-+-++-+-++++++++++-++-++-+++-++++-+---
++-+++---+++++++++++----++------------+++---++++-+-+--+-+-+++---
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
-+---+-++++--++-+--++-+-+---++--+++--+-+++----+++++-+-++----+--+
--++++-+--++--+--+-+--++------+++++++++-++----+---+---+-+++++-+-
++++-+--+---+-+---+++--++-+--++--++--+----+----+-+++++--++++++--
"""

ROW_ORDER = (
    56, 45, 43, 62, 59, 50, 14, 40, 58, 47, 48, 37, 60, 35, 22, 57,
    33, 31, 12, 29, 49, 7, 20, 61, 10, 52, 28, 53, 15, 38, 3, 41,
    55, 5, 23, 11, 44, 21, 27, 17, 9, 24, 6, 30, 13, 26, 51, 36,
    54, 25, 39, 19, 42, 18, 46, 34, 8, 16, 32, 63, 0, 1, 2, 4,
)

COL_ORDER = (
    43, 34, 49, 33, 29, 40, 55, 52, 50, 30, 36, 45, 27, 46, 24, 39,
    54, 53, 51, 48, 42, 47, 44, 41, 18, 23, 35, 7, 38, 2, 1, 37,
    4, 32, 16, 13, 21, 8, 5, 6, 20, 28, 19, 31, 63, 15, 12, 58,
    14, 10, 56, 3, 26, 11, 60, 22, 9, 25, 17, 57, 0, 59, 61, 62,
)

# Explicit successive transpositions, applied from left to right to W_6.
# All indices in Python data are ZERO-BASED. ROW_ORDER[i] is the original
# row placed at position i (and analogously for columns).
ROW_SWAPS = (
    (0, 56), (1, 45), (2, 43), (3, 62), (4, 59), (5, 50),
    (6, 14), (7, 40), (8, 58), (9, 47), (10, 48), (11, 37),
    (12, 60), (13, 35), (14, 22), (15, 57), (16, 33), (17, 31),
    (18, 60), (19, 29), (20, 49), (21, 40), (22, 49), (23, 61),
    (24, 48), (25, 52), (26, 28), (27, 53), (28, 57), (29, 38),
    (30, 62), (31, 41), (32, 55), (33, 50), (34, 61), (35, 37),
    (36, 44), (37, 40), (38, 53), (39, 41), (40, 47), (41, 48),
    (42, 49), (43, 62), (44, 47), (45, 57), (46, 51), (48, 54),
    (49, 52), (50, 54), (51, 53), (53, 60), (54, 60), (55, 61),
    (56, 58), (57, 60), (58, 61), (59, 63), (60, 61),
)

COL_SWAPS = (
    (0, 43), (1, 34), (2, 49), (3, 33), (4, 29), (5, 40),
    (6, 55), (7, 52), (8, 50), (9, 30), (10, 36), (11, 45),
    (12, 27), (13, 46), (14, 24), (15, 39), (16, 54), (17, 53),
    (18, 51), (19, 48), (20, 42), (21, 47), (22, 44), (23, 41),
    (24, 51), (25, 41), (26, 35), (27, 52), (28, 38), (29, 49),
    (30, 34), (31, 37), (32, 49), (33, 49), (34, 54), (35, 46),
    (36, 47), (37, 50), (38, 40), (39, 55), (40, 42), (41, 42),
    (42, 48), (43, 50), (44, 63), (45, 55), (46, 52), (47, 58),
    (48, 51), (49, 58), (50, 56), (51, 58), (53, 55), (54, 60),
    (55, 63), (56, 60), (57, 58), (58, 63), (59, 63), (61, 63),
    (62, 63),
)

# The 8-by-8 block K in the construction, copied independently.
K = [
    [-1, -1,  1, -1,  1,  1,  1, -1],
    [ 1, -1, -1, -1,  1,  1,  1, -1],
    [ 1,  1,  1, -1, -1, -1, -1,  1],
    [ 1, -1,  1,  1, -1, -1, -1,  1],
    [ 1, -1,  1, -1,  1,  1,  1,  1],
    [-1,  1, -1,  1,  1, -1, -1,  1],
    [-1,  1, -1,  1,  1, -1,  1, -1],
    [-1,  1, -1,  1,  1,  1, -1, -1],
]

def check(condition, message):
    # Unlike assert, this remains active when Python is run with -O.
    if not condition:
        raise ValueError(message)


def sign_matrix(text):
    rows = text.split()
    check(len(rows) == N and all(len(r) == N and set(r) <= {'+', '-'} for r in rows),
          'Expected 64 rows of 64 signs')
    return [[1 if x == '+' else -1 for x in row] for row in rows]


def hadamard(A):
    n = len(A)
    check(all(len(row) == n and all(x in (-1, 1) for x in row) for row in A),
          'Not a square sign matrix')
    for vectors in (A, list(zip(*A))):  # Check rows and columns independently.
        check(all(sum(x*y for x, y in zip(u, v)) == n*(i == j)
                  for i, u in enumerate(vectors) for j, v in enumerate(vectors)),
              'Hadamard orthogonality failed')


def apply_swaps(A, row_swaps, col_swaps):
    A = [row[:] for row in A]
    for i, j in row_swaps:
        A[i], A[j] = A[j], A[i]
    for i, j in col_swaps:
        for row in A:
            row[i], row[j] = row[j], row[i]
    return A


def ge(A):
    """Ordinary GE with no pivot search; save each active Schur complement."""
    U = [[Fraction(x) for x in row] for row in A]
    states = []
    for k in range(len(A)):
        states.append([row[k:] for row in U[k:]])
        check(U[k][k] != 0, f'GE: zero pivot at step {k+1}')
        for i in range(k+1, len(A)):
            multiplier = U[i][k] / U[k][k]
            for j in range(k+1, len(A)):
                U[i][j] -= multiplier * U[k][j]
            U[i][k] = 0
    return states


def gecp(A):
    """Independent GECP implementation using shrinking Schur complements."""
    S = [[Fraction(x) for x in row] for row in A]
    states, swaps = [], []
    while S:
        m = len(S)
        # max keeps the FIRST maximum: row-major ties favor the current pivot.
        i, j = max(((i, j) for i in range(m) for j in range(m)),
                   key=lambda ij: abs(S[ij[0]][ij[1]]))
        check(S[i][j] != 0, 'GECP: singular Schur complement')
        if i or j:
            swaps.append((len(states)+1, i, j))
        S[0], S[i] = S[i], S[0]
        for row in S:
            row[0], row[j] = row[j], row[0]
        states.append([row[:] for row in S])
        S = [[S[i][j] - S[i][0]*S[0][j]/S[0][0]
              for j in range(1, m)] for i in range(1, m)]
    return states, swaps


def main():
    H = sign_matrix(H_SIGNS)
    manuscript = Path(__file__).with_name('main.tex')
    if manuscript.exists():
        match = re.search(r'(?ms)^\\Hrows\{(.*?)^\}', manuscript.read_text())
        check(match is not None, 'Cannot find Figure 1 sign data in main.tex')
        check(H == sign_matrix(match.group(1).replace(',', ' ')),
              'Explicit matrix differs from Figure 1')
        print('OK: explicit signs agree with Figure 1.')

    # Build W_6 by Sylvester's block recursion.
    W = [[1]]
    for _ in range(6):
        W = [row+row for row in W] + [row+[-x for x in row] for row in W]
    check(sorted(ROW_ORDER) == sorted(COL_ORDER) == list(range(N)), 'Invalid permutations')
    check(H == [[W[i][j] for j in COL_ORDER] for i in ROW_ORDER],
          'Explicit matrix differs from permuted W_6')
    check(H == apply_swaps(W, ROW_SWAPS, COL_SWAPS), 'Explicit swaps do not give H')
    check(W == apply_swaps(H, reversed(ROW_SWAPS), reversed(COL_SWAPS)),
          'Reversing the swaps does not recover W_6')
    print('OK: explicit H = permuted W_6 = W_6 after the listed swaps.')

    hadamard(H)
    hadamard(W)
    print('OK: +/-1 entries and both Hadamard identities.')

    # A small control makes sure GECP actually swaps when it should.
    control, swaps = gecp([[0, 1], [2, 3]])
    check(swaps == [(1, 1, 1)] and [S[0][0] for S in control] == [3, Fraction(-2, 3)],
          'GECP swap control failed')
    ordinary = ge(H)
    complete, swaps = gecp(H)
    check(not swaps, 'GECP on H made interchanges')
    check(ordinary == complete, 'GE and GECP differ in an active entry')
    for k, S in enumerate(ordinary, 1):
        check(abs(S[0][0]) == max(abs(x) for row in S for x in row),
              f'The pivot at step {k} is not globally maximal')
    print('OK: GE and GECP agree entry-for-entry at all 64 steps; no interchanges.')

    # Compute every pivot, but prescribe only the final values used in the paper.
    pivots = [abs(S[0][0]) for S in ordinary]
    check(pivots[-8:] == [16, 32, 32, 64, 16, 32, 32, 64], 'Final eight pivots differ')
    check(max(pivots) == N, 'Growth factor is not 64')
    check(prod(pivots) == N**(N//2), 'Pivot product does not equal the Hadamard determinant magnitude')
    check(pivots[59] not in (Fraction(N, 3), Fraction(N, 2)), 'No counterexample to (iii)')
    check(pivots[58] not in (Fraction(N, 4), Fraction(3*N, 10), Fraction(3*N, 8)),
          'No counterexample to (iv)')
    check(pivots[59] > Fraction(N, 2), 'No counterexample to (v)')
    print('OK: p_59 = 32, p_60 = 64, g(H) = 64; assertions (iii)-(v) fail.')

    check(ordinary[56] == [[16*x for x in row] for row in K], 'S after 56 steps is not 16 K')
    hadamard([row[:4] for row in K[:4]])
    trailing, swaps = gecp(K)
    check(not swaps, 'K is not CP')
    check(ordinary[56:] == [[[16*x for x in row] for row in S] for S in trailing],
          'Scaled elimination of K does not match the final eight steps')
    print('OK: S_56 = 16 K, its leading sign block is Hadamard, and all trailing steps agree.')
    print('PASS: all checks succeeded in exact arithmetic.')


if __name__ == '__main__':
    main()
