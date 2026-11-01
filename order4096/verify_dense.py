#!/usr/bin/env python3
"""Matrix-only exact verification of the order-4096 counterexample.

Adapted from independent_dense_audit.py in the supplied counterexample audit.
Does not import the constructor or read the certificate. Requires NumPy >= 2.0.
"""
import argparse
import hashlib
import json
import math
import time
from fractions import Fraction
from pathlib import Path

import numpy as np

ORDER = 4096
PIVOT_SHA256 = 'a761528e59bee03cd387a0b6b50e3d44efce44fc5d734fe8a326b684f9bfbec0'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify(matrix, seconds=None):
    """Check signs, orthogonality and every pivot; return exact history.

    A/d represents the active Schur complement, with positive denominator d.
    Checks remain active under Python optimization. No reference history is
    consulted during elimination. The deadline is checked between operations.
    """
    start = time.monotonic()

    def deadline():
        if seconds is not None and time.monotonic() - start >= seconds:
            raise TimeoutError('Verification time limit exceeded; run is incomplete')

    H = np.load(matrix, allow_pickle=False)
    require(H.shape == (ORDER, ORDER), 'Expected matrix shape 4096x4096')
    require(np.all((H == 1) | (H == -1)), 'Matrix has a non-sign entry')
    # Every distinct row pair must differ in exactly n/2 positions. Sign
    # validation gives diagonal norms n. No floating-point Gram calculation.
    packed = np.ascontiguousarray(np.packbits(H < 0, axis=1)).view(np.uint64)
    for i in range(ORDER):
        deadline()
        distances = np.bitwise_count(packed[i + 1:] ^ packed[i]).sum(axis=1)
        require(np.all(distances == ORDER // 2), f'Nonorthogonal row pair at row {i}')
    print('PASS: all signs and row inner products (exact packed-bit arithmetic).', flush=True)
    del packed
    A, d = H.astype(np.int64), 1
    del H
    pivots, maxima, overshoots = [], [], []
    largest_numerator, largest_denominator = 0, 1
    i64max = int(np.iinfo(np.int64).max)
    for k in range(ORDER):
        deadline()
        p = int(A[0, 0])
        m = max(abs(int(A.min())), abs(int(A.max())))
        require(p != 0, f'Zero pivot at step {k + 1}')
        require(abs(p) == m, f'Illegal complete pivot at step {k + 1}')
        pivot, maximum = Fraction(p, d), Fraction(m, d)
        pivots.append(str(pivot))
        maxima.append(str(maximum))
        if maximum > ORDER:
            overshoots.append({'step': k + 1, 'signed_pivot': str(pivot)})
        largest_numerator = max(largest_numerator, m)
        largest_denominator = max(largest_denominator, d)
        if k + 1 == ORDER:
            break
        # Products are bounded by m^2, their difference by 2m^2. This
        # strict int64 bound also protects negation and the gcd reduction.
        require(2 * m * m <= i64max, f'Potential int64 overflow at step {k + 1}')
        B = p * A[1:, 1:] - A[1:, :1] * A[:1, 1:]
        if p < 0:
            B = -B
        new_denominator = d * abs(p)
        g = math.gcd(new_denominator, int(np.gcd.reduce(B.ravel())))
        require(g > 0 and new_denominator % g == 0, 'Invalid common divisor')
        require(np.all(B % g == 0), 'Inexact numerator division')
        A, d = B // g, new_denominator // g
        del B
        if (k + 1) % 256 == 0:
            print(f'{k + 1}/{ORDER} pivots checked; elapsed {time.monotonic() - start:.1f}s', flush=True)
    deadline()
    signature = hashlib.sha256(('\n'.join(pivots) + '\n').encode()).hexdigest()
    growth = max(map(Fraction, maxima))
    require(growth == 4608, f'Expected growth 4608, got {growth}')
    require(overshoots == [{'step': 4089, 'signed_pivot': '4608'}],
            f'Expected exactly one overshoot, +4608 at step 4089; got {overshoots}')
    require(max(map(Fraction, maxima[:-14])) == 1024, 'Unexpected prefix maximum')
    require(signature == PIVOT_SHA256, 'Signed-pivot digest differs')
    return {
        'order': ORDER,
        'matrix_sha256': hashlib.sha256(Path(matrix).read_bytes()).hexdigest(),
        'growth': str(growth),
        'overshoots': overshoots,
        'signed_pivot_sha256': signature,
        'maximum_numerator': largest_numerator,
        'maximum_denominator': largest_denominator,
        'elapsed_seconds': time.monotonic() - start,
        'signed_pivots': pivots,
        'whole_active_maxima': maxima,
    }


def positive_seconds(value):
    value = float(value)
    if not math.isfinite(value) or value <= 0:
        raise argparse.ArgumentTypeError('--seconds must be finite and positive')
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--matrix', type=Path,
                        default=Path(__file__).resolve().with_name('matrix.npy'))
    parser.add_argument('--seconds', type=positive_seconds,
                        help='time limit checked between operations; expiry is failure')
    parser.add_argument('--output', type=Path, help='write full exact pivot history as JSON')
    args = parser.parse_args()
    try:
        result = verify(args.matrix, args.seconds)
    except (ValueError, TimeoutError, OSError, OverflowError) as error:
        parser.exit(1, f'FAIL: {error}\n')
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: Hadamard, completely pivoted, growth = 4608')
    print('Exactly one overshoot: +4608 at step 4089.')
    print('Signed pivot sequence SHA256:', result['signed_pivot_sha256'])
    print('Maximum numerator:', result['maximum_numerator'])
    print('Maximum denominator:', result['maximum_denominator'])
    print(f"Elapsed seconds: {result['elapsed_seconds']:.3f}")


if __name__ == '__main__':
    main()
