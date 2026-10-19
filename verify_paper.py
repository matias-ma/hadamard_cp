from fractions import Fraction

n = 64
rows = [int(x) for x in """
    56 45 43 62 59 50 14 40 58 47 48 37 60 35 22 57
    33 31 12 29 49  7 20 61 10 52 28 53 15 38  3 41
    55  5 23 11 44 21 27 17  9 24  6 30 13 26 51 36
    54 25 39 19 42 18 46 34  8 16 32 63  0  1  2  4
""".split()]
cols = [int(x) for x in """
    43 34 49 33 29 40 55 52 50 30 36 45 27 46 24 39
    54 53 51 48 42 47 44 41 18 23 35  7 38  2  1 37
     4 32 16 13 21  8  5  6 20 28 19 31 63 15 12 58
    14 10 56  3 26 11 60 22  9 25 17 57  0 59 61 62
""".split()]

# H is the Sylvester matrix W_6 with its rows and columns permuted.
assert sorted(rows) == sorted(cols) == list(range(n))
H = [[(-1) ** (x & y).bit_count() for y in cols] for x in rows]

# Gaussian elimination without interchanges, in exact arithmetic.
S = [[Fraction(h) for h in row] for row in H]
pivots = []
for k in range(n):
    pivot = S[0][0]
    assert abs(pivot) == max(abs(s) for row in S for s in row)  # complete pivoting
    pivots.append(abs(pivot))
    S = [[S[i][j] - S[i][0] * S[0][j] / pivot for j in range(1, len(S))]
         for i in range(1, len(S))]

assert pivots[-8:] == [16, 32, 32, 64, 16, 32, 32, 64]
print("H is CP, with p_59 = 32 and p_60 = 64")
