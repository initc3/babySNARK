import random
from ssbls12 import Fp, Poly


def isPowerOfTwo(n):
    # bit-arithmetic trick
    return n & (n-1) == 0


def nearestPowerOfTwo(n):
    if isPowerOfTwo(n): return n
    return 2 ** n.bit_length()

