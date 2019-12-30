import sys
from finitefield.finitefield import FiniteField
from finitefield.polynomial import polynomialsOver
from finitefield.euclidean import extendedEuclideanAlgorithm
import os
import random
from functools import reduce


"""
## Polynomials over an example finite field Fp(71)
"""

Fp = FiniteField(53,1) #
Poly = polynomialsOver(Fp)

p1 = Poly([1,2,3,4,5])
print(p1)
# 1 + 2 t + 3 t^2 + 4 t^3 + 5 t^5 

# Evaluating a polynomial (this should be added as __call__!)
def eval_poly(f, x):
    assert type(x) is f.field
    y = f.field(0)
    for (degree,coeff) in enumerate(f):
        y += coeff * (x ** degree)
    return y

"""
## Generate a random polynomial
"""

def random_poly_with_intercept(s, k, Poly=Poly):
    # Returns a degree-k polynomial f
    # such that f(0) = 
    coeffs = [None] * (k+1)
    coeffs[0] = Poly.field(s)
    for i in range(1,k+1):
        coeffs[i] = Poly.field(random.randint(0,Poly.field.p-1))
    return Poly(coeffs)



"""
## Compute the Lagrange coefficients  p[i](x)
   p[i](x) = product[over j != i] of (x - x[j])/(x[i] - x[j])
 
"""

def lagrange(S, i, n, Poly=Poly):
    # 
    # Assert S is a subset of range(0,self.l)
    assert type(S) is set
    S = sorted(S)

    x = Poly([0,1]) # This is the polynomial f(x) = x
    ONE = Poly([1]) # This is the polynomial f(x) = 1
    
    assert i in S
    mul = lambda a,b: a*b
    num = reduce(mul, [x - j  for j in S if j != i], ONE)
    den = reduce(mul, [i - j  for j in S if j != i], Fp(1))
    return num / den
