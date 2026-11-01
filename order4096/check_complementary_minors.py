#!/usr/bin/env python3
"""Independent exact complementary-minor audit of the stored matrix.

This script derives the last fourteen signed pivots from matrix.npy alone,
using a locally implemented integer Bareiss determinant. It then optionally
compares them against a separately generated full pivot CSV. It does not
establish that the prefix is a legal complete-pivoting history; that is a
separate obligation checked by the full rooted/dense verifiers.
"""

import argparse
import csv
from fractions import Fraction
from pathlib import Path

import numpy as np


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def determinant(matrix):
    """Integer determinant by fraction-free Bareiss elimination.

    All arithmetic after copying is Python integer arithmetic. Row swaps
    handle zero pivots. Every Bareiss division is checked for zero remainder.
    The empty determinant is one, including cofactors of a 1x1 matrix.
    """
    a = [[int(x) for x in row] for row in matrix]
    n = len(a)
    require(all(len(row) == n for row in a), "Expected a square matrix")
    if n == 0:
        return 1
    sign, denominator = 1, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                value, remainder = divmod(numerator, denominator)
                require(remainder == 0, "Non-exact Bareiss division")
                a[i][j] = value
            a[i][k] = 0
        denominator = pivot
    return sign * a[-1][-1]


def cofactor_matrix(matrix):
    n = len(matrix)
    return [
        [
            (-1 if (i + j) % 2 else 1)
            * determinant([
                [matrix[r][c] for c in range(n) if c != j]
                for r in range(n) if r != i
            ])
            for j in range(n)
        ]
        for i in range(n)
    ]


def main():
    base = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path,
                        default=base / "matrix.npy")
    parser.add_argument("--compare-pivots", type=Path,
                        help="Optional independent construction pivot CSV")
    args = parser.parse_args()

    h = np.load(args.matrix, allow_pickle=False, mmap_mode="r")
    require(h.shape == (4096, 4096), "Expected matrix shape 4096x4096")
    n = len(h)
    tail = [[int(x) for x in row] for row in h[-14:, -14:]]
    require(all(x in (-1, 1) for row in tail for x in row),
            "Trailing block must be a sign matrix")

    # Compute all matrix-only results before opening the comparison CSV.
    dets = {0: 1}
    for m in range(1, 15):
        block = [row[-m:] for row in tail[-m:]]
        dets[m] = determinant(block)
        require(dets[m] != 0, f"D_{m} is singular")
    signed_tail = [Fraction(n * dets[m - 1], dets[m])
                   for m in range(14, 0, -1)]

    d8 = [row[-8:] for row in tail[-8:]]
    cofactors = cofactor_matrix(d8)
    adjugate = [list(row) for row in zip(*cofactors)]
    for i in range(8):
        for j in range(8):
            require(sum(d8[i][k] * adjugate[k][j] for k in range(8))
                    == (dets[8] if i == j else 0),
                    f"D8 adjugate identity fails at ({i},{j})")
    inverse8 = [[Fraction(x, dets[8]) for x in row] for row in adjugate]
    maximum_inverse = max(abs(x) for row in inverse8 for x in row)
    maximizers = [(i, j) for i in range(8) for j in range(8)
                  if abs(inverse8[i][j]) == maximum_inverse]
    require(maximum_inverse == Fraction(9, 8),
            "D8 inverse maximum is not 9/8")
    require(maximizers == [(0, 0)], "D8 inverse maximum is not unique")
    require(dets[8] == 512 and dets[7] == 576, "Unexpected critical minors")
    require(inverse8[0][0] == Fraction(9, 8),
            "D8 inverse leading entry is not +9/8")

    print("INDEPENDENT COMPLEMENTARY-MINOR AUDIT")
    print("Input: matrix.npy only until the final comparison section")
    print("D_m = trailing m-by-m block of the original stored H; det D_0 = 1")
    print("Signed pivots use S_m = 4096 D_m^(-T), conditional on the rooted prefix")
    print("m, step, signed_det_D_m, signed_pivot")
    for m, pivot in zip(range(14, 0, -1), signed_tail):
        print(f"{m}, {n - m + 1}, {dets[m]}, {pivot}")
    print("PASS: all fourteen Bareiss determinants are nonzero; every division is exact")
    print("All signed D8 cofactors, in row-column order:")
    for row in cofactors:
        print(" ".join(map(str, row)))
    print("PASS: D8 * adj(D8) = det(D8) I8 in exact integer arithmetic")
    print(f"max |D8^(-1)| = {maximum_inverse}; leading entry = {inverse8[0][0]}")
    print(f"Inverse maximizers (zero-based): {maximizers}")
    print(f"Selected step 4089 signed Schur pivot = {n * inverse8[0][0]}")

    if args.compare_pivots is not None:
        with args.compare_pivots.open(newline="") as stream:
            records = list(csv.DictReader(stream))
        require(len(records) == n, "Expected all 4096 pivot records")
        require([int(record["step"]) for record in records] == list(range(1, n + 1)),
                "CSV step sequence is not 1 through 4096")
        pivots = [Fraction(record["signed_pivot"]) for record in records]
        require(pivots[-14:] == signed_tail,
                "Matrix-only complementary pivots disagree with construction CSV")
        product = Fraction(1)
        for pivot in pivots:
            product *= pivot
        require(product.denominator == 1 and product.numerator == (1 << 24576),
                "Signed full pivot product is not +2^24576")
        print("PASS: all fourteen independently derived signed pivots match the construction CSV")
        print("PASS: product of all 4096 signed pivots = +2^24576 = +4096^2048")
    else:
        print("No CSV comparison requested")


if __name__ == "__main__":
    main()
