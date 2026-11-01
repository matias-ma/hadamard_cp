"""Negative controls for the dense verifier; also run with python -O."""
import contextlib
import io
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import numpy as np
import verify_dense as vd


class DenseNegativeControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.matrix = Path(self.temp.name) / 'matrix.npy'
        # Small Sylvester matrix; use the same arithmetic and Gram checker.
        self.h = np.array([[1 - 2 * ((r & c).bit_count() % 2)
                            for c in range(64)] for r in range(64)], dtype=np.int8)

    def reject(self, matrix, message, seconds=None):
        np.save(self.matrix, matrix)
        with patch.object(vd, 'ORDER', 64), contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaisesRegex((ValueError, TimeoutError), message):
                vd.verify(self.matrix, seconds=seconds)

    def test_wrong_shape(self):
        self.reject(self.h[:-1], 'shape')

    def test_non_sign(self):
        self.h[0, 0] = 0
        self.reject(self.h, 'non-sign')

    def test_corrupted_sign(self):
        self.h[0, 0] *= -1
        self.reject(self.h, 'Nonorthogonal')

    def test_duplicate_row(self):
        self.h[1] = self.h[0]
        self.reject(self.h, 'Nonorthogonal')

    def test_illegal_diagonal_order(self):
        # Swapping remaining rows keeps orthogonality but makes the second
        # diagonal entry zero while another active entry has magnitude two.
        self.h[[1, 2]] = self.h[[2, 1]]
        self.reject(self.h, 'Zero pivot at step 2')

    def test_deadline(self):
        self.reject(self.h, 'incomplete', seconds=1e-12)


if __name__ == '__main__':
    unittest.main()
