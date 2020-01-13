from finitefield.finitefield import FiniteField
from finitefield.polynomial import polynomialsOver
from finitefield.euclidean import extendedEuclideanAlgorithm
import os
import random
from finitefield.numbertype import typecheck, memoize, DomainElement
from functools import reduce

# This defines a representation for polynomials suitable for FFT

@memoize
def polynomialsEvalRep(field, omega, n):
    assert n & n - 1 == 0, "n must be a power of 2"

    # Check that omega is an n'th primitive root of unity
    assert type(omega) is field
    omega = field(omega)
    assert omega**(n) == 1
    _powers = set([omega**i for i in range(n)])
    assert len(_powers) == n

    _poly_coeff = polynomialsOver(field)

    class PolynomialEvalRep(object):

        @classmethod
        def from_coeffs(cls, poly):
            assert type(poly) is _poly_coeff
            assert poly.degree()
            # TODO: use FFT evaluation
            xs = []
            ys = []
            for x in _powers:
                y = poly(x)
                if y != 0:
                    xs.append(x)
                    ys.append(y)
            return cls(xs, ys)

        def __init__(self, xs, ys):
            # Each element of xs must be a power of omega.
            # There must be a corresponding y for every x.
            if type(xs) is not tuple:
                xs = tuple(xs)
            if type(ys) is not tuple:
                ys = tuple(ys)

            assert len(xs) <= n+1
            assert len(xs) == len(ys)
            for x in xs:
                assert x in _powers
            for y in ys:
                assert type(y) is field

            self.evalmap = dict(zip(xs, ys))

        def to_coeffs(self):
            # To convert back to the coefficient form, we use polynomial interpolation.
            # The non-zero elements stored in self.evalmap, so we fill in the zero values
            # here.
            ys = [self.evalmap[x] if x in self.evalmap else field(0) for x in _powers]
            f = _poly_coeff.interpolate(_powers, ys)
            return f

        _lagrange_cache = {}
        def __call__(self, x):
            if type(x) is int:
                x = field(x)
            assert type(x) is field
            xs = _powers

            def lagrange(x, xi):
                # Let's cache lagrange values
                if (x,xi) in PolynomialEvalRep._lagrange_cache:
                    return PolynomialEvalRep._lagrange_cache[(x,xi)]

                mul = lambda a,b: a*b
                num = reduce(mul, [x  - xj for xj in xs if xj != xi], field(1))
                den = reduce(mul, [xi - xj for xj in xs if xj != xi], field(1))
                PolynomialEvalRep._lagrange_cache[(x,xi)] = num / den
                return PolynomialEvalRep._lagrange_cache[(x,xi)]

            y = field(0)
            for xi, yi in self.evalmap.items():
                y += yi * lagrange(x, xi)
            return y

        def __mul__(self, other):
            # Scale by integer
            if type(other) is int:
                other = field(other)
            if type(other) is field:
                return PolynomialEvalRep(self.evalmap.keys(),
                                         [other * y for y in self.evalmap.values()])

            # Multiply another polynomial in the same representation
            if type(other) is type(self):
                xs = []
                ys = []
                for x, y in self.evalmap.items():
                    if x in other.evalmap:
                        xs.append(x)
                        ys.append(y * other.evalmap[x])
                return PolynomialEvalRep(xs, ys)

        @typecheck
        def __iadd__(self, other):
            # Add another polynomial to this one in place.
            # This is especially efficient when the other polynomial is sparse,
            # since we only need to add the non-zero elements.
            for x, y in other.evalmap.items():
                if x not in self.evalmap:
                    self.evalmap[x] = y
                else:
                    self.evalmap[x] += y
            return self

        @typecheck
        def __add__(self, other):
            res = PolynomialEvalRep(self.evalmap.keys(), self.evalmap.values())
            res += other
            return res

        def __sub__(self, other): return self + (-other)
        def __neg__(self): return PolynomialEvalRep(self.evalmap.keys(),
                                                    [-y for y in self.evalmap.values()])

        def __truediv__(self, divisor):
            # Scale by integer
            if type(divisor) is int:
                other = field(divisor)
            if type(divisor) is field:
                return self * (1/divisor)
            if type(divisor) is type(self):
                res = PolynomialEvalRep((),())
                for x, y in self.evalmap.items():
                    assert x in divisor.evalmap
                    res.evalmap[x] = y / divisor.evalmap[x]
                return res
            return NotImplemented

        def __copy__(self):
            return PolynomialEvalRep(self.evalmap.keys(), self.evalmap.values())

        def __repr__(self):
            return f'PolyEvalRep[{hex(omega.n)[:15]}...,{n}]({len(self.evalmap)} elements)'

        @classmethod
        def divideWithCoset(cls, p, t, c=field(3)):
            """
              This assumes that p and t are polynomials in coefficient representation,
            and that p is divisible by t.
               This function is useful when t has roots at some or all of the powers of omega,
            in which case we cannot just convert to evalrep and use division above
            (since it would cause a divide by zero.
               Instead, we evaluate p(X) at powers of (c*omega) for some constant cofactor c.
            To do this efficiently, we create new polynomials, pc(X) = p(cX), tc(X) = t(cX),
            and evaluate these at powers of omega. This conversion can be done efficiently
            on the coefficient representation.
               See also: cosetFFT in libsnark / libfqfft.
               https://github.com/scipr-lab/libfqfft/blob/master/libfqfft/evaluation_domain/domains/extended_radix2_domain.tcc
            """
            assert type(p) is _poly_coeff
            assert type(t) is _poly_coeff
            # Compute p(cX), t(cX) by multiplying coefficients
            c_acc = field(1)
            pc = Poly(list(p.coefficients))  # make a copy
            for i in range(p.degree() + 1):
                pc.coefficients[-i-1] *= c_acc
                c_acc *= c
            c_acc = field(1)
            tc = Poly(list(t.coefficients))  # make a copy
            for i in range(t.degree() + 1):
                tc.coefficients[-i-1] *= c_acc
                c_acc *= c

            # Divide using evalrep
            pc_rep = cls.from_coeffs(pc)
            tc_rep = cls.from_coeffs(tc)
            hc_rep = pc_rep / tc_rep
            hc = hc_rep.to_coeffs()

            assert pc == tc * hc

            # Compute h(X) from h(cX) by dividing coefficients
            c_acc = field(1)
            h = Poly(list(hc.coefficients))  # make a copy
            for i in range(hc.degree() + 1):
                h.coefficients[-i-1] /= c_acc
                c_acc *= c

            # Correctness check
            assert p == t * h

            return h


    return PolynomialEvalRep

def get_omega(field, n, seed=None):
    """
    Given a field, this method returns an n^th root of unity.
    If the seed is not None then this method will return the
    same n'th root of unity for every run with the same seed

    This only makes sense if n is a power of 2.
    """
    rnd = random.Random(seed)
    assert n & n - 1 == 0, "n must be a power of 2"
    x = field(rnd.randint(0, field.p-1))
    y = pow(x, (field.p - 1) // n)
    if y == 1 or pow(y, n // 2) == 1:
        return get_omega(field, n)
    assert pow(y, n) == 1, "omega must be 2n'th root of unity"
    assert pow(y, n // 2) != 1, "omega must be primitive 2n'th root of unity"
    return y


# Examples
Fp = FiniteField(52435875175126190479447740508185965837690552500527637822603658699938581184513,1)  # (# noqa: E501)
Poly = polynomialsOver(Fp)

n = 8
omega = get_omega(Fp, n)
PolyEvalRep = polynomialsEvalRep(Fp, omega, n)

f = Poly([1,2,3,4,5])
xs = tuple([omega**i for i in range(n)])
ys = tuple(map(f, xs))
# print('xs:', xs)
# print('ys:', ys)

assert f == PolyEvalRep(xs, ys).to_coeffs()
