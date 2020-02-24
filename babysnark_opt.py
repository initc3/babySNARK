# | # Baby SNARK with FFT optimizations
# | This is the same algorithm as BabySNARK, except optimized so that
# | the overhead is quasilinear rather than quadratic (in the number of
# | constraints).
import sys
from babysnark import *

from finitefield.finitefield import FiniteField
from finitefield.polynomial import polynomialsOver
from ssbls12 import Fp, Poly, Group
from circuit import BooleanCircuit

G = Group.G
GT = Group.GT

# | # Choosing roots of unity
# | The BLS12-381 is chosen in part because it's FFT friendly. To use radix-2
# | FFT, we need to find m^th roots of unity, where m is a power of two, and
# | m is the degree bound of the polynomial we want to represent.
# |
# | In the BLS12-381, we can find primitive n^th roots of unity, for any
# | power of two n up to n <= 2^**32.
# | This follows because for the ssbls12-381 exponent field Fp, we have
# |    2^32 divides (p - 1).
from polynomial_evalrep import get_omega, polynomialsEvalRep, RowDictSparseMatrix

omega_base = get_omega(Fp, 2 ** 32, seed=0)

# These are globals. They're set to be large enough for small examples, and in
# babysnark_setup we'll change them for other sizes anyway.
mpow2 = 128  # nearest power of 2 greather than m, the number of constraints
omega = omega_base ** (2 ** 32 // mpow2)

# This overwrite a global parameter imported from babysnark.
ROOTS.clear()
ROOTS += [omega ** i for i in range(mpow2)]


def vanishing_poly(omega, n):
    # For the special case of evaluating at all n powers of omega,
    # the vanishing poly has a special form.
    #  t(X) = (X-1)(X-omega)....(X-omega^(n-1)) = X^n - 1
    return Poly([Fp(-1)] + [Fp(0)] * (n - 1) + [Fp(1)])


# | # Evaluation Representation of polynomials
# |
# | This representation is sparse - it only stores the non-zero values,
# | so if it has lots of roots among the powers of omega,
def _sparse_poly_demo():
    PolyEvalRep = polynomialsEvalRep(Fp, omega, mpow2)

    # Example polynomial that has roots at most of the powers of omega
    xs = [omega ** 1, omega ** 4, omega ** 5]
    ys = [Fp(3), Fp(5), Fp(1)]
    f_rep = PolyEvalRep(xs, ys)

    for i in [0, 2, 3, 6, 7]:
        assert f_rep(omega ** i) == Fp(0)
    for i, x in enumerate(xs):
        assert f_rep(x) == ys[i]

    # Convert to coeffs and back
    f = f_rep.to_coeffs()
    assert f_rep.to_coeffs() == PolyEvalRep.from_coeffs(f).to_coeffs()

    # Check f and f_rep are consistent
    tau = random_fp()
    assert f(tau) == f_rep(tau)

    # print('f_rep:', f_rep)
    # print('f:', f)


_sparse_poly_demo()

# | # Sparse representation of Square Constraint Systems
# |
# | In order to reach our goal of quasilinear overhead (in the number of gates),
# | we can't just use the dense numpy matrix U to represent our constraints.
# |
# | Suppose we use the construction from boolean circuits, and that the circuit
# | has an average fan-in of some constant (e.g., average fan-in of ~2). Then the
# | matrix U, will be sparse, with only O(m + n) non-zero values despite being
# | an (m * n) matrix.
# |

# Matrix is m-by-n, but contains only avgPerN*n non-zero values in expectation.
# The first column is all non-zero.
def random_sparse_matrix(m, n, avgPerN=2):
    U = RowDictSparseMatrix(m, n, Fp(0))

    # First fill the first column
    for row in range(m):
        U[row, 0] = random_fp()

    # Then pick randomly for the rest
    for _ in range(avgPerN * n - 1):
        row = random.randrange(m)
        col = random.randrange(n)
        U[row, col] = random_fp()

    return U


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
    for (i, j), val in U.items():
        U[i, j] /= Ua2[i].sqrt()

    assert (U.dot(a) * U.dot(a) == 1).all()
    Ud = U.to_dense()
    assert (Ud.dot(a) * Ud.dot(a) == 1).all()
    return U, a


# -
# Example
m, n = 10, 12
U = random_sparse_matrix(m, n)
U, a = generate_solved_instance(m, n)
print(U)
print(U.to_dense())

# | # Baby SNARK with quasilinear overhead

# Setup
def babysnarkopt_setup(U, n_stmt):
    (m, n) = U.shape
    assert n_stmt < n

    # Generate roots for each gate
    # TODO: Handle padding?
    global mpow2, omega
    mpow2 = m
    assert mpow2 & mpow2 - 1 == 0, "mpow2 must be a power of 2"
    omega = omega_base ** (2 ** 32 // mpow2)
    PolyEvalRep = polynomialsEvalRep(Fp, omega, mpow2)

    global ROOTS
    if len(ROOTS) != m:
        ROOTS.clear()
        ROOTS += [omega ** i for i in range(m)]

    # Generate polynomials u from columns of U
    Us = [PolyEvalRep((), ()) for _ in range(n)]
    for (i, k), y in U.items():
        x = ROOTS[i]
        Us[k] += PolyEvalRep([x], [y])

    # Trapdoors
    global tau, beta, gamma
    tau = random_fp()
    beta = random_fp()
    gamma = random_fp()

    # CRS elements
    CRS = (
        [G * (tau ** i) for i in range(m + 1)]
        + [G * gamma, G * (beta * gamma)]
        + [G * (beta * Ui(tau)) for Ui in Us[n_stmt:]]
    )

    # Precomputation
    # Note: This is not considered part of the trusted setup, since it
    # could be computed direcftly from the G * (tau **i) terms.

    # Compute the target poly term
    t = vanishing_poly(omega, m)
    T = G * t(tau)

    # Evaluate the Ui's corresponding to statement values
    Uis = [G * Ui(tau) for Ui in Us]
    precomp = Uis, T

    return CRS, precomp


# Prover
def babysnarkopt_prover(U, n_stmt, CRS, precomp, a):
    (m, n) = U.shape
    assert n == len(a)
    assert len(CRS) == (m + 1) + 2 + (n - n_stmt)

    taus = CRS[: m + 1]
    bUis = CRS[-(n - n_stmt) :]

    Uis, T = precomp

    # Target is the vanishing polynomial
    mpow2 = m
    assert mpow2 & mpow2 - 1 == 0, "mpow2 must be a power of 2"
    omega = omega_base ** (2 ** 32 // mpow2)
    omega2 = omega_base ** (2 ** 32 // (2 * mpow2))
    PolyEvalRep = polynomialsEvalRep(Fp, omega, mpow2)
    t = vanishing_poly(omega, mpow2)

    # 1. Find the polynomial p(X)

    # First compute v
    v = PolyEvalRep((), ())
    for (i, k), y in U.items():
        x = ROOTS[i]
        v += PolyEvalRep([x], [y]) * a[k]

    # Now we need to convert between representations to multiply and divide
    PolyEvalRep2 = polynomialsEvalRep(Fp, omega2, 2 * mpow2)
    roots2 = [omega2 ** i for i in range(2 * mpow2)]
    ONE = PolyEvalRep2(roots2, [Fp(1) for _ in roots2])

    vv = v.to_coeffs()
    v2 = PolyEvalRep2.from_coeffs(v.to_coeffs())
    p2 = v2 * v2 - ONE
    p = p2.to_coeffs()

    # Find the polynomial h by dividing p / t
    h = PolyEvalRep2.divideWithCoset(p, t)
    # assert p == h * t

    # 2. Compute the H term
    H = evaluate_in_exponent(taus, h)

    # 3. Compute the Vw terms, using precomputed Uis
    Vw = sum([Uis[k] * a[k] for k in range(n_stmt, n)], G * 0)
    # assert G * vw(tau) == Vw

    # 4. Compute the Bw terms
    Bw = sum([bUis[k - n_stmt] * a[k] for k in range(n_stmt, n)], G * 0)
    # assert G * (beta * vw(tau)) == Bw

    # V = G * vv(tau)
    # assert H.pair(T) * GT == V.pair(V)

    # print('H:', H)
    # print('Bw:', Bw)
    # print('Vw:', Vw)
    return H, Bw, Vw


# -
if __name__ == "__main__":
    # Sample a problem instance
    print("\n\n\n")
    if len(sys.argv) == 1:
        print(
            "No circuit file input provided. You can provide circuit(in bristol format) as follows"
        )
        print("python babysnark_opt.py <circuit_file>")
        print("Generating a Square Span Program instance")
        n_stmt = 4
        m, n = (16, 6)
        U, a = generate_solved_instance(m, n)
    else:
        filename = sys.argv[1]
        c = BooleanCircuit(file_name=filename)
        # Calculating the entire circuit using random inputs
        # Use the output as the statement, all other wires as witness
        inputs = c.get_random_inputs()
        n_stmt, a, U = c.compile_to_solved_ssp(inputs)

    print("\n\n\n")
    a_stmt = a[:n_stmt]
    print("U:", repr(U))
    print("a_stmt:", a_stmt)
    print("m x n:", m * n)

    # Setup
    print("Computing Setup (optimized)...")
    CRS, precomp = babysnarkopt_setup(U, n_stmt)
    print("CRS length:", len(CRS))

    # Prover
    print("Proving (optimized)...")
    H, Bw, Vw = babysnarkopt_prover(U, n_stmt, CRS, precomp, a)

    if 0:  # Uncomment this to cross-check the optimized with the reference
        # Alternate prover
        print("Proving (reference)...")
        H_, Bw_, Vw_ = babysnark_prover(U.to_dense(), n_stmt, CRS, precomp, a)
        assert (H_, Bw_, Vw_) == (H, Bw, Vw)

    # Verifier
    print("[opt] Verifying (optimized)...")
    babysnark_verifier(U, CRS, precomp, a[:n_stmt], (H, Bw, Vw))
