#| # Baby SNARK (do do dodo dodo)
#| A simple but expressive SNARK.

#| ## Polynomial tools
#| We start with a library for polynomials over finite fields, represented
#| by coefficients. It includes:
#|  - Constructing a polynomial from a list of coefficients
#|  - Addition, scalar multiplication, multiplication of polynomials
#|  - Euclidean division of polynomials
#|  - Lagrange interpolation of polynomials
#|
#|


# Polynomials over finite fields
from finitefield.finitefield import FiniteField
from finitefield.polynomial import polynomialsOver

# Example: Fp(53)
Fp = FiniteField(53,1)
Poly = polynomialsOver(Fp)

def _polydemo():
    p1 = Poly([1,2,3,4,5])
    # print(p1)
    # 1 + 2 t + 3 t^2 + 4 t^3 + 5 t^5
_polydemo()

#| ## Choosing a field and pairing-friendly curve
#| Define concrete parameters and pairing-friendly group.
#| We need a symmetric group, but the most readily available, bls12-381,
#| See `py_ecc/` and `ssbls12.py` for details.
# pairing : G x G -> GT
from ssbls12 import Fp, Poly, Group

G = Group.G
GT = Group.GT

#| Define some canonical roots
# This is a global value.
# Initializing it to 1,2,...,128 is enough for small examples in this file.
# We'll overwrite it in `babysnark_setup` when a larger constraint system
# is needed. And in `babysnark_opt.py` we'll define a different policy for
# choosing roots that leads to FFT optimization.
ROOTS = [Fp(i) for i in range(128)]


#| Here we define the vanishing polynomial, that has
#| roots at the given points
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


#| ## Square Constraint Programs
#| We'll represent square constraint programs using matrix-vector
#| multiplication.
"""
Square Constraint Program definition:
  - U   (m x n  matrices)

Witness definition (includes statement):
   a         (n vector)

Statement definition:
   a_stmt    (l < n vector)

Predicate to prove:
    (Ua)^2 = 1
    a[:l] = a_stmt
"""

# Use numpy to provide element-wise operations and fancy indexing
import numpy as np
import random

# Generate random problem instances
def random_fp():
    return Fp(random.randint(0, Fp.p-1))

def random_matrix(m, n):
    return np.array([[random_fp() for _ in range(n)] for _ in range(m)])

def generate_solved_instance(m, n):
    """
    Generates a random circuit and satisfying witness
    U, (stmt, wit)
    """
    # Generate a, U
    a = np.array([random_fp() for _ in range(n)])
    U = random_matrix(m, n)

    # Normalize U to satisfy constraints
    Ua2 = U.dot(a) * U.dot(a)
    for i in range(m):
        U[i,:] /= Ua2[i].sqrt()

    assert((U.dot(a) * U.dot(a) == 1).all())
    return U, a

#-
# Example
U, a = generate_solved_instance(10, 12)
# print(U)


#| # Baby Snark
#|
#| Here we define the Setup, Prover, and Verifier

# Setup
def babysnark_setup(U, n_stmt):
    (m, n) = U.shape
    assert n_stmt < n

    # Generate roots for each gate
    global ROOTS
    if len(ROOTS) < m:
        ROOTS = tuple(range(m))

    # Generate polynomials u from columns of U
    Us = [Poly.interpolate(ROOTS[:m], U[:,k]) for k in range(n)]

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
    assert len(ROOTS) >= m

    # Parse the CRS
    taus = CRS[:m+1]
    bUis = CRS[-(n-n_stmt):]

    # Target is the vanishing polynomial
    t = vanishing_poly(ROOTS[:m])
    
    # Convert the basis polynomials Us to coefficient form by interpolating
    Us = [Poly.interpolate(ROOTS[:m], U[:,k]) for k in range(n)]

    # 1. Find the polynomial p(X)

    # First just the witness polynomial (we'll use it later)
    vw = Poly([])
    for k in range(n_stmt, n):
        vw += Us[k] * a[k]

    # Then the rest of the v polynomial
    v = Poly(vw)
    for k in range(n_stmt):
        v += Us[k] * a[k]

    # Finally p
    p = v * v - 1

    # 2. Compute the H term
    # Find the polynomial h by dividing p / t
    h = p / t

    H = sum([taus[i] * h.coefficients[i] for i in
             range(len(h.coefficients))], G*0)

    # 3. Compute the Vw terms
    Vw = sum([taus[i] * vw.coefficients[i] for i in range(m)], G*0)
    # assert G * vw(tau) == Vw

    # 4. Compute the Bw terms
    Bw = sum([bUis[k-n_stmt] * a[k] for k in range(n_stmt, n)], G*0)
    # assert G * (beta * vw(tau)) == Bw

    # T = G * t(tau)
    # V = G * vv(tau)
    # assert H.pair(T) * GT == V.pair(V)

    # print('H:', H)
    # print('Bw:', Bw)
    # print('Vw:', Vw)
    return H, Bw, Vw


# Verifier
def babysnark_verifier(U, CRS, a_stmt, pi):
    (m, n) = U.shape
    (H, Bw, Vw) = pi
    assert len(ROOTS) >= m
    n_stmt = len(a_stmt)

    # Parse the CRS
    taus = CRS[:m+1]
    gamma = CRS[m+1]
    gammabeta = CRS[m+2]
    bUis = CRS[-(n-n_stmt):]

    # Compute the target poly term
    t = vanishing_poly(ROOTS[:m])
    T = sum([taus[i] * t.coefficients[i] for i in range(m+1)], G*0)
    
    # Convert the basis polynomials Us to coefficient form by interpolating
    Us = [Poly.interpolate(ROOTS[:m], U[:,k]) for k in range(n)]
    
    # Compute Vs and V = Vs + Vw
    vs = Poly([0])
    for k in range(n_stmt):
        vs += a_stmt[k] * Us[k]

    Vs = sum([taus[i] * vs.coefficients[i] for i in range(m)], Group.G*0)
    V = Vs + Vw

    # Check 1
    print('Checking (1)')
    assert Bw.pair(gamma) == Vw.pair(gammabeta)

    # Check 2
    print('Checking (2)')
    #print('GT', GT)
    #print('H.pair(T) * GT:', H.pair(T) * GT)
    #print('V.pair(V):', V.pair(V))
    assert H.pair(T) * GT == V.pair(V)

    return True

#-
if __name__ == '__main__':
    # Sample a problem instance
    print("Generating a Square Span Program instance")
    n_stmt = 4
    m,n = (16, 6)
    U, a = generate_solved_instance(m, n)
    a_stmt = a[:n_stmt]
    print('U:', repr(U))
    print('a_stmt:', a_stmt)
    print('nonzero in U:', np.sum(U == Fp(0)))
    print('m x n:', m * n)

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
