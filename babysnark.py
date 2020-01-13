#| # Baby SNARK (do do dodo dodo)
#| A simple but expressive SNARK.

#| ## Polynomial tools
#| We have a library for polynomials over finite fields, represented
#| by coefficients. It includes:
#|  - Constructing a polynomial from a list of coefficients
#|  - Addition, scalar multiplication, multiplication of polynomials
#|  - Euclidean division of polynomials
#|  - Lagrange interpolation of polynomials
#|
#| We also have the following FFT-based tools for efficiently converting
#| between coefficient and evaluation representation, but will use these
#| later in babysnark_opt.py
#|  - Fast fourier transform for finite fields
#|  - Interpolation and evaluation using FFT
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

#| ## Pairing friendly elliptic curve
#| Define concrete parameters and pairing-friendly group.
#| We need a symmetric group, but the most readily available, bls12-381,
#| See `py_ecc/` and `ssbls12.py` for details.
# pairing : G x G -> GT
from ssbls12 import Fp, Poly, Group
from polynomial_extra import get_omega

G = Group.G
GT = Group.GT

#| Define some canonical roots of unity
omega_base = get_omega(Fp, 2**32, seed=0)

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
#| To be efficient when the constraints do not have many terms,
#| we'll use scipy sparse matrices.
"""
Square Constraint Program definition:
  - U   (m x n  matrices)

Witness definition:
   a         (n vector)

Statement definition:
   a_stmt    (l < n vector)

Predicate to prove:
    (Ua)^2 = 1
    prefix(a) = a_stmt
"""

# Use numpy to provide element-wise operations and fancy indexing
import numpy as np
import random

# Generate random (but sparse) problem instances
def random_fp():
    return Fp(random.randint(0, Fp.p-1))

# Matrix is m-by-n, but contains only avgPerN*n non-zero values in expectation.
# The first column is all non-zero.
def random_sparse_matrix(m, n, avgPerN=2):
    # # First column
    # mat = sparse.lil_matrix((m, n), dtype=np.object)
    # for i in range(m):
    #     mat[i,0] = random_fp()

    # # Randomize
    # for _ in range((avgPerN-1)*n):
    #     i = random.randint(0, m-1)
    #     j = random.randint(1, n-1)
    #     mat[i,j] = [random_fp()]
    return np.array([[random_fp() if col == 0 or random.random() < (avgPerN-1)/n else Fp(0)
                      for col in range(n)] for _ in range(m)])

def generate_solved_instance(m, n):
    """
    Generates a random circuit and satisfying witness
    U, (stmt, wit)
    """
    # Generate a, U
    a = np.array([random_fp() for _ in range(n)])
    U = random_sparse_matrix(m, n)

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
    omega = omega_base ** (2**32 // m)
    rs = [Fp(omega**i) for i in range(m)]

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

    # Choose roots consistent with the FFT version
    omega = omega_base ** (2**32 // m)
    rs = [Fp(omega**i) for i in range(m)]

    # Target is the vanishing polynomial
    t = vanishing_poly(rs)
    
    # 1. Find the polynomial p(X)
    Us = [Poly.interpolate(rs[:m], U[:,k]) for k in range(n)]

    # First just the witness polynomial
    vw = Poly([])
    for k in range(n_stmt, n):
        vw += Us[k] * a[k]

    # Then the rest of the v polynomial
    v = Poly(vw)
    for k in range(n_stmt):
        v += Us[k] * a[k]

    p = v * v - 1

    # Find the polynomial h by dividing p / t
    h = p / t

    # 2. Compute the H term
    H = sum([taus[i] * h.coefficients[i] for i in
             range(len(h.coefficients))], G*0)

    # 3. Compute the Vw terms
    Vw = sum([taus[i] * vw.coefficients[i] for i in range(m)], G*0)
    assert G * vw(tau) == Vw

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

    # Parse the CRS
    taus = CRS[:m+1]
    gamma = CRS[m+1]
    gammabeta = CRS[m+2]
    bUis = CRS[-(n-n_stmt):]

    # Compute the target poly term
    omega = omega_base ** (2**32 // m)
    rs = [Fp(omega**i) for i in range(m)]

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
