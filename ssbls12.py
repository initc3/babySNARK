from py_ecc import optimized_bls12_381 as bls12_381
from py_ecc.optimized_bls12_381 import FQ, FQ2, FQ12, G1, G2, add, neg, multiply, eq

import sys
from finitefield.finitefield import FiniteField
from finitefield.polynomial import polynomialsOver
from finitefield.euclidean import extendedEuclideanAlgorithm

from functools import reduce


# BLS12_381 group order
Fp = FiniteField(52435875175126190479447740508185965837690552500527637822603658699938581184513,1)  # (# noqa: E501)

Poly = polynomialsOver(Fp)
Fp.__repr__ = lambda self: hex(self.n)[:15] + "..."


# Evaluating a polynomial
def eval_poly(f, x):
    assert type(x) is Fp
    y = Fp(0)
    xx = Fp(1)
    for coeff in f.coefficients:
        y += coeff * xx
        xx *= x
    return y
Poly.__call__ = eval_poly


# Interpolating a polynomial
def interpolate(xs, ys):
    xs_hash = hash(tuple(xi.n for xi in xs))
    global _lagrange_cache
    if '_lagrange_cache' not in globals():
        _lagrange_cache = {}
        
    assert len(xs) == len(ys)

    X = Poly([Fp(0),Fp(1)]) # This is the polynomial f(X) = X
    ONE = Poly([Fp(1)]) # This is the polynomial f(X) = 1

    f = Poly([Fp(0)])
    def lagrange(xi):
        # Let's cache lagrange values
        if (xs_hash, xi.n) in _lagrange_cache:
            return _lagrange_cache[(xs_hash, xi.n)]
        
        mul = lambda a,b: a*b
        num = reduce(mul, [X  - xj  for xj in xs if xj != xi], ONE)
        den = reduce(mul, [xi - xj  for xj in xs if xj != xi], Fp(1))
        _lagrange_cache[(xs_hash, xi.n)] = num / den
        return _lagrange_cache[(xs_hash, xi.n)]

    for xi, yi in zip(xs, ys):
        f += yi * lagrange(xi)

    # # Sanity check
    # for xi, yi in zip(xs, ys):
    #     assert eval_poly(f, xi) == yi
    return f
Poly.interpolate = interpolate


def sqrt(self):
    """Square root.
    No attempt is made the to return the positive square root.
    """
    assert self.p % 2 == 1, "Modulus must be odd"
    assert pow(self, (self.p - 1) // 2) == 1

    assert self.p % 4 == 1

    # The case that self.modulus % 4 == 1
    # Cipolla’s Algorithm
    # http://people.math.gatech.edu/~mbaker/pdf/cipolla2011.pdf
    t = u = 0
    for i in range(1, self.p):
        u = i * i - self
        if pow(u, (self.p - 1) // 2) == self.p - 1:
            t = i
            break

    def cipolla_mult(a, b, w):
        return ((a[0] * b[0] + a[1] * b[1] * w), (a[0] * b[1] + a[1] * b[0]))

    exp = (self.p + 1) // 2
    exp_bin = bin(exp)[2:]
    x1 = (t, 1)
    x2 = cipolla_mult(x1, x1, u)
    for i in range(1, len(exp_bin)):
        if exp_bin[i] == "0":
            x2 = cipolla_mult(x2, x1, u)
            x1 = cipolla_mult(x1, x1, u)
        else:
            x1 = cipolla_mult(x1, x2, u)
            x2 = cipolla_mult(x2, x2, u)
    return x1[0]

Fp.sqrt = sqrt


class SS_BLS12_381():
    
    def __init__(self, m1, m2):
        self.m1 = m1
        self.m2 = m2

    def in_group(self):
        return (bls12_381.pairing(self.m2, bls12_381.G1) ==
                bls12_381.pairing(bls12_381.G2, self.m1))

    order = bls12_381.curve_order

    def __add__(self, other):
        assert type(other) is SS_BLS12_381
        return SS_BLS12_381(add(self.m1, other.m1),
                            add(self.m2, other.m2))

    def __mul__(self, x):
        assert type(x) in (int, Fp)
        if type(x) is Fp:
            x = x.n
        return SS_BLS12_381(multiply(self.m1, x),
                            multiply(self.m2, x))

    def __rmul__(self, x):
        return self.__mul__(x)

    def __eq__(self, other):
        return (eq(self.m1, other.m1) and
                eq(self.m2, other.m2))

    def pair(self, other):
        t1 = bls12_381.pairing(self.m2, other.m1)
        # t2 = bls12_381.pairing(other.m2, self.m1)
        # assert t1 == t2
        return t1

    def __repr__(self):
        return repr(self.m1)
    
SS_BLS12_381.G = SS_BLS12_381(bls12_381.G1, bls12_381.G2)
SS_BLS12_381.GT = SS_BLS12_381.G.pair(SS_BLS12_381.G)
Group = SS_BLS12_381
