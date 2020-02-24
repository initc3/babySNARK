from .euclidean import *
from .numbertype import *

# so all IntegersModP are instances of the same base class
class _Modular(FieldElement):
    pass


@memoize
def IntegersModP(p):
    # assume p is prime

    class IntegerModP(_Modular):
        def __init__(self, n):
            try:
                self.n = int(n) % IntegerModP.p
            except:
                raise TypeError(
                    "Can't cast type %s to %s in __init__"
                    % (type(n).__name__, type(self).__name__)
                )

            self.field = IntegerModP

        @typecheck
        def __add__(self, other):
            return IntegerModP(self.n + other.n)

        @typecheck
        def __sub__(self, other):
            return IntegerModP(self.n - other.n)

        @typecheck
        def __mul__(self, other):
            return IntegerModP(self.n * other.n)

        def __neg__(self):
            return IntegerModP(-self.n)

        @typecheck
        def __eq__(self, other):
            return isinstance(other, IntegerModP) and self.n == other.n

        @typecheck
        def __ne__(self, other):
            return isinstance(other, IntegerModP) is False or self.n != other.n

        @typecheck
        def __divmod__(self, divisor):
            q, r = divmod(self.n, divisor.n)
            return (IntegerModP(q), IntegerModP(r))

        def inverse(self):
            # need to use the division algorithm *as integers* because we're
            # doing it on the modulus itself (which would otherwise be zero)
            x, y, d = extendedEuclideanAlgorithm(self.n, self.p)

            if d != 1:
                raise Exception("Error: p is not prime in %s!" % (self.__name__))

            return IntegerModP(x)

        def __abs__(self):
            return abs(self.n)

        def __str__(self):
            return str(self.n)

        def __repr__(self):
            return "%d (mod %d)" % (self.n, self.p)

        def __int__(self):
            return self.n

        def __hash__(self):
         return hash((self.n, self.p))

        def sqrt(self):
         """Square root for integers mod p.
         No attempt is made the to return the positive square root.
         """
         assert self.p % 2 == 1, "Modulus must be odd"

         if self.p % 4 == 3:
            # TODO: this is the easy case, just need to fill it in
            raise NotImplementedError

         if self.p % 4 == 1:

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


    IntegerModP.p = p
    IntegerModP.__name__ = 'Z/%d' % (p)
    IntegerModP.englishName = 'IntegersMod%d' % (p)
    return IntegerModP


if __name__ == "__main__":
    mod7 = IntegersModP(7)
