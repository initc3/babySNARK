from finitefield.finitefield import FiniteField
from finitefield.polynomial import polynomialsOver
from finitefield.euclidean import extendedEuclideanAlgorithm
import os
import random
from finitefield.numbertype import typecheck, memoize, DomainElement

# This defines a representation for polynomials suitable for FFT

@memoize
def polynomialsEvalRep(field, omega, m):
    # Check that omega is a 2^m primitive root of unity
    assert type(omega) is field
    assert omega**(2**m) == 1
    _powers = set([omega**i for i in range(2**m)])
    assert len(_powers) == 2**m

    _poly_coeff = polynomialsOver(field)

    class PolynomialEvalRep(DomainElement):

        def __init__(self, xs, ys):
            # Each element of xs must be a power of omega.
            # There must be a corresponding y for every x.
            if type(xs) is not tuple:
                xs = tuple(xs)
            if type(ys) is not tuple:
                ys = tuple(ys)

            assert len(xs) <= m+1
            assert len(xs) == len(ys)
            for x in xs:
                assert x in _powers
            for y in ys:
                assert type(y) is field

            self.num_nonroots = len(xs)
            self.evalmap = dict(xs, ys)

        def to_coeffs(self):
            # To convert back to the coefficient form, we use polynomial interpolation.
            # The non-zero elements stored in self.evalmap, so we fill in the zero values
            # here.
            ys = [self.evalmap[x] if x in self.evalmap else field(0) for x in _powers]
            f = _poly_coeff.interpolate(xs, ys)
            return f
