#| # Baby SNARK (do do dodo dodo)
#| _A simple but expressive SNARK._
#|
#| This is a self-contained development of SNARKs for NP. It is based on
#| [Square Span Program SNARKs](https://eprint.iacr.org/2014/718) by Danezis et al.,
#| which are expressive enough to encode boolean circuits.
#|
#| For detail about the algorithm, especially its security definition and soundness,
#| proof, see [the acompanying paper](TODO: overleaf/eprint link).
#|
#| This implementation in this file is optimized for readability and simplicity, not
#| performance. The result is that the proof is succinct, but the computation overhead
#| of `Setup` and `Prove` is quadratic in the circuit size, rather than quasilinear.
#| In `babysnark_opt.py` you can find a quasilinear implementation.

#| ## Polynomials library
#| We start with a library, `finite_field/`, for polynomials over finite fields,
#| represented by coefficients. The library includes:
#|  - Constructing a polynomial from a list of coefficients
#|  - Addition, scaling, multiplication of polynomials
#|  - Euclidean division of polynomials
#|  - Lagrange interpolation of polynomials
#|
#| The library is adapted from tutorials by Jeremy Kun.
#| See [A Programmer's Introudction to Mathematics](https://github.com/pim-book/programmers-introduction-to-mathematics)
#| and [Programming with Finite Fields](https://jeremykun.com/2014/03/13/programming-with-finite-fields/)
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

#| ## Choosing a field and pairing-friendly elliptic curve
#| We need to define a finite field to work with, that corresponds to the order
#| of a pairing-friendly curve.
#| To keep notation down to a minimum, BabySNARK is defined for a symmetric (Type-1)
#| elliptic curve group, that is $pair : G \times G \rightarrow G_T$.
#| However, since the most readily available curve, `bls12-381`, is asymmetric (Type-3),
#| we write an adaptor for it. See `py_ecc/` and `ssbls12.py` for details.
from ssbls12 import Fp, Poly, Group
G = Group.G
GT = Group.GT

#| ## Choosing the evaluation domain
#| Define some canonical roots $r_1,...,r_m$. These are public parameters
#| and can be set arbitrarily, and in particular they don't depend on the
#| circuit (though there must be enough of them to represent the problem
#| instance).
# This is a global value.
# Initializing it to 1,2,...,128 is enough for small examples in this file.
# We'll overwrite it in `babysnark_setup` when a larger constraint system
# is needed. And in `babysnark_opt.py` we'll define a different policy for
# choosing roots that leads to FFT optimization.
ROOTS = [Fp(i) for i in range(128)]


#| Here we define the vanishing polynomial, which is a degree-$m$ polynomial
#| that roots at the $m$ distinct locations given.
def vanishing_poly(S):
    """
    args: 
       S   (m vector)
    returns:
       p(X) = (X-S1)*(X-S2)*...*(X-Sm)
    """
    p = Poly([Fp(1)])
    for s in S:
        p *= Poly([-s, Fp(1)])
    return p


#| ## Square Constraint Systems
#| We'll represent square constraint systems using matrix-vector
#| multiplication.
#|
#| The constraint system itself is defined by:
#| - `U`$~~$  (an `m` $\times$ `n`  matrix)
#|
#| The witness (including the statement)
#| - `a`$~~$   (an `n` vector)
#|
#| The statement is:
#| - `a_stmt`    (an `n_stmt` size vector, where `n_stmt`<`n`)
#|
#| The predicate to prove is:
#| - $(\!$ `U` $\!\cdot\!$ `a` $\!)^2 = 1$
#| - `a[:n_stmt]`$ = $`a_stmt`
#|
#| The code below generates approximately random instances of Square
#| Constraint Systems with a known solution. We'll use these for
#| tests and examples, though in reality the problem instances would
#| be generated from a circuit.

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
#| Here we define the Setup, Prover, and Verifier. Follow along with
#| the pseudocode from the [accompanying writeup](TODO: eprint/overleaf link)

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

    # Precomputation
    # Note: This is not considered part of the trusted setup, since it
    # could be computed direcftly from the G * (tau **i) terms.

    # Compute the target poly term
    t = vanishing_poly(ROOTS[:m])
    T = G * t(tau)

    # Evaluate the Ui's corresponding to statement values
    Uis = [G * Ui(tau) for Ui in Us]
    precomp = Uis, T

    return CRS, precomp


# Prover
def babysnark_prover(U, n_stmt, CRS, precomp, a):
    (m, n) = U.shape
    assert n == len(a)
    assert len(CRS) == (m + 1) + 2 + (n - n_stmt)
    assert len(ROOTS) >= m

    # Parse the CRS
    taus = CRS[:m+1]
    bUis = CRS[-(n-n_stmt):]

    Uis, T = precomp

    # Target is the vanishing polynomial
    t = vanishing_poly(ROOTS[:m])
    
    # Convert the basis polynomials Us to coefficient form by interpolating
    Us = [Poly.interpolate(ROOTS[:m], U[:,k]) for k in range(n)]

    # 1. Find the polynomial p(X)

    # First compute v
    v = Poly([])
    for k in range(n):
        v += Us[k] * a[k]

    # Finally p
    p = v * v - 1

    # 2. Compute the H term
    # Find the polynomial h by dividing p / t
    h = p / t
    # assert p == h * t

    H = sum([taus[i] * h.coefficients[i] for i in
             range(len(h.coefficients))], G*0)

    # 3. Compute the Vw terms, using precomputed Uis
    Vw = sum([Uis[k] * a[k] for k in range(n_stmt, n)], G*0)
    # assert G * vw(tau) == Vw

    # 4. Compute the Bw terms
    Bw = sum([bUis[k-n_stmt] * a[k] for k in range(n_stmt, n)], G*0)
    # assert G * (beta * vw(tau)) == Bw

    # V = G * v(tau)
    # assert H.pair(T) * GT == V.pair(V)

    # print('H:', H)
    # print('Bw:', Bw)
    # print('Vw:', Vw)
    return H, Bw, Vw


# Verifier
def babysnark_verifier(U, CRS, precomp, a_stmt, pi):
    (m, n) = U.shape
    (H, Bw, Vw) = pi
    assert len(ROOTS) >= m
    n_stmt = len(a_stmt)

    # Parse the CRS
    taus = CRS[:m+1]
    gamma = CRS[m+1]
    gammabeta = CRS[m+2]
    bUis = CRS[-(n-n_stmt):]
    
    Uis, T = precomp
    
    # Compute Vs and V = Vs + Vw
    Vs = sum([Uis[k] * a_stmt[k] for k in range(n_stmt)], G * 0)
    V = Vs + Vw

    # Check 1
    print('Checking (1)')
    assert Bw.pair(gamma) == Vw.pair(gammabeta)

    # Check 2
    print('Checking (2)')
    # print('GT', GT)
    # print('V:', V)
    # print('H.pair(T) * GT:', H.pair(T) * GT)
    # print('V.pair(V):', V.pair(V))
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
    CRS, precomp = babysnark_setup(U, n_stmt)
    print("CRS length:", len(CRS))

    # Prover
    print("Proving...")
    H, Bw, Vw = babysnark_prover(U, n_stmt, CRS, precomp, a)

    # Verifier
    print("Verifying...")
    babysnark_verifier(U, CRS, precomp, a[:n_stmt], (H, Bw, Vw))
