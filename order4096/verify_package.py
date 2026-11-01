#!/usr/bin/env python3
"""Check package integrity, the portable certificate, and all exported pivots.

Python 3.10+, standard library only. Run from any directory.
This supplements verify_construction.py; verify_dense.py is independent.
"""
import csv
import hashlib
import json
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
from verify_construction import PIVOT_CHOICES, check, check_matrix, construct, write_matrix
from verify_extended import construct as construct_extended

BASE = Path(__file__).resolve().parent


def main():
    entries = (BASE / 'SHA256SUMS').read_text().splitlines()
    for entry in entries:
        expected, name = entry.split('  ', 1)
        check(hashlib.sha256((BASE / name).read_bytes()).hexdigest() == expected,
              f'Checksum mismatch: {name}')
    check(len(entries) == len(set(entries)), 'Duplicate checksum entries')
    print(f'PASS: {len(entries)} file checksums.')

    certificate = json.loads((BASE / 'pivot_certificate.json').read_text())
    check(certificate['index_base'] == 0, 'Wrong certificate index base')
    stages = certificate['stages']
    check(len(stages) == len(PIVOT_CHOICES) == 6, 'Wrong stage count')
    for i, (stage, choices) in enumerate(zip(stages, PIVOT_CHOICES)):
        check(stage['pivots'] == [list(pair) for pair in choices],
              f'Certificate choices differ in stage {i + 1}')
        check(stage['ambient_order'] == (16, 64, 256, 1024, 4096, 4096)[i],
              'Wrong ambient order')
        check(stage['input_order'] == (16, 24, 32, 40, 48, 14)[i],
              'Wrong input order')
        check(stage['remaining_order'] == (6, 8, 10, 12, 14, 0)[i],
              'Wrong remaining order')
        check(stage['lift_before'] == (1 <= i <= 4), 'Wrong lifting flag')
    print('PASS: JSON certificate agrees with all 124 choices and stage dimensions.')

    rows, columns, pivots, _, _ = construct(verbose=False)
    extended = construct_extended(verbose=False)
    check((rows, columns, pivots) == extended[:3],
          'Current and extended constructions differ')
    print('PASS: extended identities and determinant checks; both constructions agree.')
    check_matrix(BASE / 'matrix.npy', rows, columns)
    with (BASE / 'pivots.csv').open(newline='') as stream:
        table = list(csv.reader(stream))
    expected = [['step', 'row_label', 'column_label', 'signed_pivot',
                 'whole_active_maximum']]
    expected += [[str(step), str(row), str(column), str(pivot), str(abs(pivot))]
                 for step, (row, column, pivot)
                 in enumerate(zip(rows, columns, pivots), 1)]
    check(table == expected, 'Exported permutations or pivots differ')
    print('PASS: all 4096 exported signed pivots and both permutations agree.')

    with tempfile.TemporaryDirectory(prefix='hadamard-regenerate-') as tmp:
        regenerated = Path(tmp) / 'matrix.npy'
        write_matrix(regenerated, rows, columns)
        check(regenerated.read_bytes() == (BASE / 'matrix.npy').read_bytes(),
              'Regenerated matrix is not byte-identical')
    print('PASS: matrix regeneration is byte-identical.')
    overshoots = [i + 1 for i, p in enumerate(pivots) if abs(p) > 4096]
    check(overshoots[0] == 4089 and pivots[4088] == 4608,
          'Unexpected first overshoot')
    print('PASS: growth 4608; first overshoot +4608 at step 4089.')


if __name__ == '__main__':
    main()
