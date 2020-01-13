#| # Baby SNARK with FFT optimizations
#| This is the same algorithm as BabySNARK, except optimized so that
#| the overhead is quasilinear rather than quadratic (in the number of
#| constraints).

from finitefield.finitefield import FiniteField
from finitefield.polynomial import polynomialsOver
from polynomial_extra import get_omega, polynomialsEvalRep
import numpy as np
import random
from babysnark import generate_solved_instance, omega_base, random_fp
from ssbls12 import Fp, Poly, Group
G = Group.G
GT = Group.GT

def vanishing_poly(omega, n):
    # For the special case of evaluating at all n powers of omega,
    # the vanishing poly has a special form.
    #  t(X) = (X-1)(X-omega)....(X-omega^(n-1)) = X^n - 1
    return Poly([Fp(-1)] + [Fp(0)]*(n-1) + [Fp(1)])

# Setup
def babysnarkopt_setup(U, n_stmt):
    (m, n) = U.shape
    assert n_stmt < n

    # Generate roots for each gate
    mpow2 = m
    assert mpow2 & mpow2 - 1 == 0, "mpow2 must be a power of 2"
    omega = omega_base ** (2**32 // mpow2)
    PolyEvalRep = polynomialsEvalRep(Fp, omega, mpow2)

    # Generate polynomials u from columns of U
    Us = []
    for k in range(n):
        xs = []
        ys = []
        for i in range(m):
            if U[i,k] != 0:
                xs.append(omega**i)
                ys.append(U[i,k])
        Us.append(PolyEvalRep(xs, ys))

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
def babysnarkopt_prover(U, n_stmt, CRS, a):
    (m, n) = U.shape
    assert n == len(a)
    assert len(CRS) == (m + 1) + 2 + (n - n_stmt)

    taus = CRS[:m+1]
    bUis = CRS[-(n-n_stmt):]

    # Target is the vanishing polynomial
    mpow2 = m
    assert mpow2 & mpow2 - 1 == 0, "mpow2 must be a power of 2"
    omega  = omega_base ** (2**32 // mpow2)
    omega2 = omega_base ** (2**32 // (2*mpow2))
    PolyEvalRep = polynomialsEvalRep(Fp, omega, mpow2)
    t = vanishing_poly(omega, mpow2)
    
    # 1. Find the polynomial p(X)
    Us = []
    for k in range(n):
        xs = []
        ys = []
        for i in range(m):
            if U[i,k] != 0:
                xs.append(omega**i)
                ys.append(U[i,k])
        Us.append(PolyEvalRep(xs, ys))

    # First just the witness polynomial
    vw = PolyEvalRep((),())
    for k in range(n_stmt, n):
        vw += Us[k] * a[k]

    # Then the rest of the v polynomial
    v = vw.__copy__()
    # v = Poly(vw)
    for k in range(n_stmt):
        v += Us[k] * a[k]

    # Now we need to convert between representations to multiply and divide
    PolyEvalRep2 = polynomialsEvalRep(Fp, omega2, 2*mpow2)
    rs2 = [omega2**i for i in range(2*mpow2)]
    ONE = PolyEvalRep2(rs2, [Fp(1) for _ in rs2])

    vv = v.to_coeffs()
    v2 = PolyEvalRep2.from_coeffs(v.to_coeffs())
    p2 = v2 * v2 - ONE
    p = p2.to_coeffs()

    # Find the polynomial h by dividing p / t
    h = PolyEvalRep2.divideWithCoset(p, t)
    # assert p == h * t

    # 2. Compute the H term
    H = sum([taus[i] * h.coefficients[i] for i in
             range(len(h.coefficients))], G*0)

    # 3. Compute the Vw terms
    vw = vw.to_coeffs()
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
def babysnarkopt_verifier(U, CRS, a_stmt, pi):
    (m, n) = U.shape
    (H, Bw, Vw) = pi

    # Parse the CRS
    taus = CRS[:m+1]
    gamma = CRS[m+1]
    gammabeta = CRS[m+2]
    bUis = CRS[-(n-n_stmt):]

    # Compute the target poly term
    assert m & m - 1 == 0, "m must be a power of 2"
    omega = omega_base ** (2**32 // m)
    PolyEvalRep = polynomialsEvalRep(Fp, omega, m)
    t = vanishing_poly(omega, m)
    T = sum([taus[i] * t.coefficients[i] for i in range(m+1)], G*0)
    
    # Compute the polynomials from U
    Us = []
    for k in range(n):
        xs = []
        ys = []
        for i in range(m):
            if U[i,k] != 0:
                xs.append(omega**i)
                ys.append(U[i,k])
        Us.append(PolyEvalRep(xs, ys))
    
    # Compute Vs and V = Vs + Vw
    vs = PolyEvalRep((),())
    for k in range(n_stmt):
        vs += Us[k] * a[k]
    vs = vs.to_coeffs()

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
    CRS = babysnarkopt_setup(U, n_stmt)
    print("CRS length:", len(CRS))

    # Prover
    print("Proving...")
    H, Bw, Vw = babysnarkopt_prover(U, n_stmt, CRS, a)

    # Verifier
    print("Verifying...")
    babysnarkopt_verifier(U, CRS, a[:n_stmt], (H, Bw, Vw))
