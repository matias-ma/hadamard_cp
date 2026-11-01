#!/usr/bin/env python3
"""Reproduce Appendix A using exact rational arithmetic (standard library only).

Run: python3 verify_construction.py
Optional: --matrix FILE, --write-matrix, --pivots FILE.csv.

Only the 124 listed choices need direct checking. The lifting lemma in the
paper certifies the other pivots. The reconstructed permutations are also
checked against every entry of matrix.npy.
"""
import argparse
import ast
import csv
import hashlib
import struct
from fractions import Fraction
from pathlib import Path


# Copied from Appendix A, in its six groups. Coordinates are zero-based in
# the CURRENT Schur complement. Delete the chosen row and column, preserving
# all other positions; do not swap with the first row and column.
PIVOT_CHOICES = (
    # Order 16: ten pivots, leaving a 6 x 6 matrix.
    (
        (14, 8), (12, 6), (10, 4), (9, 2), (7, 4),
        (6, 10), (8, 6), (7, 4), (5, 1), (3, 1),
    ),
    # Order 64: sixteen pivots, leaving an 8 x 8 matrix.
    (
        (19, 17), (15, 1), (11, 8), (3, 18), (18, 13), (6, 4), (16, 9), (15, 10),
        (0, 0), (3, 1), (0, 1), (1, 2), (8, 6), (8, 7), (6, 9), (5, 7),
    ),
    # Order 256: twenty-two pivots, leaving a 10 x 10 matrix.
    (
        (3, 1), (10, 8), (13, 15), (16, 26), (19, 18), (22, 11),
        (25, 20), (3, 5), (3, 3), (3, 4), (9, 14), (9, 19),
        (11, 10), (9, 10), (6, 8), (12, 6), (9, 13), (12, 7),
        (12, 10), (4, 8), (9, 4), (5, 10),
    ),
    # Order 1024: twenty-eight pivots, leaving a 12 x 12 matrix.
    (
        (3, 1), (6, 16), (9, 35), (16, 23), (19, 30), (22, 26), (25, 12),
        (32, 18), (28, 4), (9, 8), (9, 6), (9, 7), (11, 18), (11, 8),
        (8, 1), (7, 1), (16, 14), (21, 22), (16, 6), (2, 7), (12, 7),
        (1, 12), (17, 16), (11, 3), (14, 2), (8, 10), (12, 7), (8, 5),
    ),
    # Order 4096: thirty-four pivots, leaving a 14 x 14 matrix.
    (
        (3, 1), (6, 16), (9, 4), (16, 7), (23, 21), (26, 24),
        (12, 35), (32, 10), (35, 16), (38, 36), (18, 25), (24, 29),
        (24, 27), (24, 28), (17, 13), (16, 14), (19, 29), (3, 26),
        (29, 14), (4, 27), (18, 25), (21, 19), (6, 0), (2, 9),
        (18, 16), (13, 3), (4, 5), (1, 2), (19, 7), (16, 0),
        (8, 2), (15, 3), (10, 7), (7, 6),
    ),
    # The final fourteen pivots: continue without lifting.
    (
        (8, 4), (2, 6), (10, 11), (3, 8), (1, 5), (2, 5), (7, 2),
        (0, 1), (0, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    ),
)


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def sylvester_entry(row, column):
    """W_n[row, column] = (-1) ** (binary dot product of row and column)."""
    return 1 - 2 * ((row & column).bit_count() % 2)


def eliminate(matrix, row, column):
    """Take one Schur complement, preserving the remaining row/column order."""
    pivot = matrix[row][column]
    size = len(matrix)
    return [
        [matrix[i][j] - matrix[i][column] * matrix[row][j] / pivot
         for j in range(size) if j != column]
        for i in range(size) if i != row
    ]


def tensor_w4(matrix):
    """Form S tensor W_4 in the usual block order."""
    return [
        [value * sylvester_entry(a, b) for value in row for b in range(4)]
        for row in matrix for a in range(4)
    ]


def lift_labels(labels, order):
    """Keep the same Walsh labels as the supplied matrix.npy.

    Label (r, a) by r + order*a, so
    W_{4n}[r+n*a, c+n*b] = W_n[r,c] * W_4[a,b].
    This is a permutation of the usual tensor-product labels 4*r+a.
    """
    return [label + order * a for label in labels for a in range(4)]


def construct(verbose=True):
    """Return row/column permutations, signed pivots, figure panels and core.

    The last two outputs preserve the interface used by make_figures.py.
    """
    order = 16
    active_rows = list(range(order))
    active_columns = list(range(order))
    matrix = [[Fraction(sylvester_entry(i, j)) for j in active_columns]
              for i in active_rows]
    rows, columns, pivots, snapshots = [], [], [], []

    for stage, choices in enumerate(PIVOT_CHOICES):
        if 1 <= stage <= 4:
            # Two applications of the lifting lemma replace p by p,-2p,-2p,4p.
            matrix = tensor_w4(matrix)
            pivots = [p * factor for p in pivots for factor in (1, -2, -2, 4)]
            rows = lift_labels(rows, order)
            columns = lift_labels(columns, order)
            active_rows = lift_labels(active_rows, order)
            active_columns = lift_labels(active_columns, order)
            order *= 4

        if stage < 5:
            snapshots.append({'order': order, 'start': matrix})
        else:
            core_rows, core_columns = active_rows[:], active_columns[:]
            core_matrix = matrix

        for number, (row, column) in enumerate(choices, start=1):
            pivot = matrix[row][column]
            largest = max(abs(value) for line in matrix for value in line)
            check(pivot != 0 and abs(pivot) == largest,
                  f'Group {stage + 1}, choice {number}: not a complete pivot')
            rows.append(active_rows.pop(row))
            columns.append(active_columns.pop(column))
            pivots.append(pivot)
            matrix = eliminate(matrix, row, column)

        remaining = (6, 8, 10, 12, 14, 0)[stage]
        check(len(matrix) == remaining, f'Group {stage + 1}: wrong remaining size')
        if stage < 5:
            check(all(abs(value) == order // 4 for line in matrix for value in line),
                  f'Order {order}: expected entries of magnitude {order // 4}')
            snapshots[-1]['end'] = matrix
        if verbose:
            print(f'Group {stage + 1}: order {order}, {len(choices)} exact pivot checks,'
                  f' {remaining} rows remaining')

    check(len(pivots) == 4096 and not active_rows and not active_columns,
          'The elimination sequence is incomplete')
    check(sorted(rows) == sorted(columns) == list(range(4096)),
          'The row and column labels must be permutations')
    check(max(abs(p) for p in pivots[:-14]) == 1024, 'Incorrect prefix maximum')
    tail = [Fraction(p) for p in ('1', '2', '2', '2', '4', '4', '9/2', '10/9',
                                  '6/5', '4/3', '1', '2', '2', '4')]
    check([abs(p) for p in pivots[-14:]] == [1024 * p for p in tail],
          'The final fourteen magnitudes do not match equation (1)')
    check(max(abs(p) for p in pivots) == pivots[4088] == 4608,
          'Expected growth 4608 at pivot 4089')

    # Express the final 14 x 14 core in the completed diagonal pivot order.
    core = [[core_matrix[core_rows.index(r)][core_columns.index(c)]
             for c in columns[-14:]] for r in rows[-14:]]
    return rows, columns, pivots, snapshots, (rows[-14:], columns[-14:], core)


def matrix_rows(rows, columns):
    """Rows of P W_4096 Q as signed-int8 bytes (255 represents -1)."""
    for row in rows:
        yield bytes(sylvester_entry(row, column) % 256 for column in columns)


def write_matrix(path, rows, columns):
    """Write NumPy's NPY 1.0 format without requiring NumPy."""
    header = b"{'descr': '|i1', 'fortran_order': False, 'shape': (4096, 4096), }"
    header += b' ' * ((-10 - len(header) - 1) % 64) + b'\n'
    with path.open('wb') as stream:
        stream.write(b'\x93NUMPY\x01\x00' + struct.pack('<H', len(header)) + header)
        stream.writelines(matrix_rows(rows, columns))


def check_matrix(path, rows, columns):
    """Compare every stored entry with the reconstructed Sylvester permutation."""
    with path.open('rb') as stream:
        check(stream.read(8) == b'\x93NUMPY\x01\x00', 'Expected an NPY 1.0 file')
        header_size = struct.unpack('<H', stream.read(2))[0]
        header = ast.literal_eval(stream.read(header_size).decode('ascii').strip())
        check(header == {'descr': '|i1', 'fortran_order': False, 'shape': (4096, 4096)},
              'Expected a 4096 x 4096 signed-int8 matrix in row-major order')
        for row, expected in enumerate(matrix_rows(rows, columns)):
            check(stream.read(4096) == expected, f'Matrix differs in row {row}')
        check(not stream.read(1), 'Unexpected trailing matrix data')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--matrix', type=Path,
                        default=Path(__file__).resolve().with_name('matrix.npy'))
    parser.add_argument('--write-matrix', action='store_true')
    parser.add_argument('--pivots', type=Path, help='export the full signed pivot sequence')
    args = parser.parse_args()

    rows, columns, pivots, _, _ = construct()
    if args.write_matrix:
        write_matrix(args.matrix, rows, columns)
    check_matrix(args.matrix, rows, columns)
    if args.pivots:
        with args.pivots.open('w', newline='') as stream:
            writer = csv.writer(stream)
            writer.writerow(['step', 'row_label', 'column_label',
                             'signed_pivot', 'whole_active_maximum'])
            for step, (row, column, pivot) in enumerate(zip(rows, columns, pivots), 1):
                writer.writerow([step, row, column, str(pivot), str(abs(pivot))])

    signature = hashlib.sha256(('\n'.join(map(str, pivots)) + '\n').encode()).hexdigest()
    print('PASS: 124 exact local checks and four lifts certify all 4096 pivots.')
    print('PASS: all matrix entries match P W_4096 Q; hence H H^T = 4096 I.')
    print('Growth = 4608 = (9/8)*4096, attained at pivot 4089.')
    print('Signed pivot sequence SHA256:', signature)


if __name__ == '__main__':
    main()
