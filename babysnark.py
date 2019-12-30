# Baby SNARK (do do dodo dodo)

"""
A simple, complete for NP expressive, implementation of a SNARK.
"""
import sys
from finitefield.finitefield import FiniteField
from finitefield.polynomial import polynomialsOver
import os
import random
import numpy as np

from ssbls12 import Fp, Poly, Group

G = Group.G
GT = Group.GT

#### Polynomial tools

def vanishing_poly(S):
    """
    args: 
       S   (n vector)
    returns:
       p(X) = (X-S1)*(X-S2)*...*(X-Sn)
    """
    p = Poly([Fp(1)])
    for s in S:
        p *= Poly([-s, Fp(1)])
    return p


#### Matrix tools
def random_fp():
    return Fp(random.randint(0, Fp.p-1))

def random_matrix(m, n):
    return np.array([[random_fp() for _ in range(n)] for _ in range(m)])


#### Square Span Programs
""" 
Square Span Program definition:
   U   (m x n  matrices)

Witness definition:
   a         (n vector)

Statement definition:
   a_stmt    (l < n vector)

Predicate to prove:
    (Ua)^2 = 1
    prefix(a) = a_stmt
"""

def generate_solved_instance(m, n):
    """
    Generates a random circuit and satisfying witness
    U, (stmt, wit)
    """
    # Generate a, U
    a = np.array([random_fp() for _ in range(n)])
    U = random_matrix(m, n)

    # Fix a so that it works
    Ua2= U.dot(a) * U.dot(a)
    for i in range(m):
        U[i,:] /= Ua2[i].sqrt()

    assert((U.dot(a) * U.dot(a) == 1).all())
    return U, a

U, a = generate_solved_instance(10, 6)

# Create a matrix
U = random_matrix(5, 6)



############
# Baby Snark
############

# Setup
def babysnark_setup(U, n_stmt):
    (m, n) = U.shape
    assert n_stmt < n

    # Generate roots for each gate
    # TODO: these should be powers of omega
    rs = [Fp(1+i) for i in range(m)]
    
    # Generate polynomials u from columns of U
    Us = [Poly.interpolate(rs, U[:,k]) for k in range(n)]

    # Trapdoors
    global tau, beta, gamma
    tau   = random_fp()
    beta  = random_fp()
    gamma = random_fp()

    # CRS elements
    CRS = [G * (tau ** i) for i in range(m+1)] + \
          [G * gamma, G * (beta * gamma)] + \
          [G * (beta * Ui(tau)) for Ui in Us[n_stmt:]]
    return CRS

# Prover
def babysnark_prover(U, n_stmt, CRS, a):
    (m, n) = U.shape
    assert n == len(a)
    assert len(CRS) == (m + 1) + 2 + (n - n_stmt)

    taus = CRS[:m+1]
    bUis = CRS[-(n-n_stmt):]

    # Target polynomial is vanishing
    rs = [Fp(1+i) for i in range(m)]
    t = vanishing_poly(rs)
    
    # 1. Find the polynomial p
    Us = [Poly.interpolate(rs, U[:,k]) for k in range(n)]

    # First just the witness polynomial
    vw = Poly([0])
    for k in range(n_stmt, n):
        vw += a[k] * Us[k]

    # Then the rest of the v polynomial
    v = vw
    for k in range(n_stmt):
        v += a[k] * Us[k]

    # Next find p by squaring 
    p = v * v - 1

    # Finally find the polynomial h by dividing by t
    h = p / t
    assert p == t * h
    assert len(vw.coefficients) == m
    assert len(h.coefficients) <= m

    # 2. Compute the H term
    H = sum([taus[i] * h.coefficients[i] for i in
             range(len(h.coefficients))], G*0)

    # 3. Compute the Vw terms
    Vw = sum([taus[i] * vw.coefficients[i] for i in range(m)], G*0)
    # assert G * vw(tau) == Vw

    # 4. Compute the Bw terms
    Bw = sum([bUis[k-n_stmt] * a[k] for k in range(n_stmt, n)], G*0)
    # assert G * (beta * vw(tau)) == Bw

    # assert H.pair(T) * GT == V.pair(V)

    print('H:', H)
    print('Bw:', Bw)
    print('Vw:', Vw)
    return H, Bw, Vw



# Verifier
def babysnark_verifier(U, CRS, a_stmt, pi):
    (m, n) = U.shape
    (H, Bw, Vw) = pi

    # Parse the CRS
    taus = CRS[:m+1]
    gamma = CRS[m+1]
    gammabeta = CRS[m+2]
    bUis = CRS[-(n-n_stmt):]

    # Compute the target poly term
    rs = [Fp(1+i) for i in range(m)]
    t = vanishing_poly(rs)
    T = sum([taus[i] * t.coefficients[i] for i in range(m+1)], G*0)
    
    # Compute the polynomials from U
    Us = [Poly.interpolate(rs, U[:,k]) for k in range(n)]
    
    # Compute Vs and V = Vs + Vw
    vs = Poly([0])
    for k in range(n_stmt):
        vs += a[k] * Us[k]

    Vs = sum([taus[i] * vs.coefficients[i] for i in range(m)], Group.G*0)
    V = Vs + Vw

    # Check 1
    print('Checking (1)')
    assert Bw.pair(gamma) == Vw.pair(gammabeta)

    # Check 2
    print('Checking (2)')
    assert H.pair(T) * GT == V.pair(V)

    return True


# Sample a problem instance
print("Generating a Square Span Program instance")
n_stmt = 4
m,n = (10, 6)
U, a = generate_solved_instance(m, n)
a_stmt = a[:n_stmt]
print('U:', U)
print('a_stmt:', a_stmt)

# Setup
print("Computing Setup...")
CRS = babysnark_setup(U, n_stmt)
print("CRS length:", len(CRS))

# Prover
print("Proving...")
H, Bw, Vw = babysnark_prover(U, n_stmt, CRS, a)

# Verifier
print("Verifying...")
babysnark_verifier(U, CRS, a[:n_stmt], (H, Bw, Vw))
