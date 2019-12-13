
# An elliptic curve with generalized Weierstrass normal form
class GeneralizedEllipticCurve(object):
    def __init__(self, a1=0, a2=0, a3=0, a4=0, a6=0):
        #Coefficients are for y^2 + a1xy + a3y = x^3 + a2x^2 + a4x + a6
        self.a1 = a1
        self.a2 = a2
        self.a3 = a3
        self.a4 = a4
        self.a6 = a6

        b2 = self.a1**2 + 4*self.a2
        b4 = 2*self.a4 + self.a1*self.a3
        b6 = self.a3**2 + 4*self.a6
        b8 = (self.a1**2)*self.a6 + 4*self.a2*self.a6 - self.a1*self.a3*self.a4 + self.a2*(self.a3**2) - self.a4**2

        c4 = b2*b2 - 24*b4
        c6 = -b2*b2*b2 + 36*b2*b4 - 216*b6

        self.disc = -b2*b2*b8 - 8*b4*b4*b4 - 27*b6*b6 + 9*b2*b4*b6
        self.j = c4*c4*c4/self.disc


    def testPoint(self, x, y):
        return y*y + self.a1*x*y + self.a3*y - x*x*x - self.a2*(x*x) - self.a4*x - self.a6 == 0



class Point(object):
    def __init__ (self, curve, x, y):
        self.curve = curve # the curve containing this point
        self.x = x
        self.y = y

    def __str__(self):
        return "(%r, %r)" % (self.x, self.y)

    def __repr__(self):
        return str(self)


    def __neg__(self):
        return Point(self.curve, self.x, -self.y - self.curve.a1*self.x - self.curve.a3)

    def __add__(self, Q):
        if isinstance(Q, Ideal):
            return Point(self.curve, self.x, self.y)

        a1,a2,a3,a4,a6 = (self.curve.a1, self.curve.a2, self.curve.a3, self.curve.a4, self.curve.a6)

        if self.x == Q.x:
            x = self.x
            if self.y + Q.y + a1*x + a3 == 0:
                return Ideal(self.curve)
            else:
                c = ((3*x*x + 2*a2*x + a4 - a1*self.y) / (2*self.y + a1*x + a3))
                d = (-(x*x*x) + a4*x + 2*a6 - a3*self.y) / (2*self.y + a1*x + a3)
                Sum_x = c*c + a1*c - a2 - 2*self.x
                Sum_y = -(c + a1) * Sum_x - d - a3
                return Point(self.curve, Sum_x, Sum_y)
        else:
            c =  (Q.y - self.y) / (Q.x - self.x)
            d =  (self.y*Q.x - Q.y*self.x) / (Q.x - self.x)
            Sum_x = c*c + a1*c - a2 - self.x - Q.x
            Sum_y = -(c + a1)*Sum_x - d - a3
            return Point(self.curve, Sum_x, Sum_y)

    def __sub__(self, Q):
        return self + -Q


    def __mul__(self, n):
        if not (isinstance(n, int) or isinstance(n, long)):
            raise Exception("Can't scale a point by something which isn't an int!")
        else:
            if n < 0:
                return -self * -n
        if n == 0:
            return Ideal(self.curve)
        else:
            Q = self
            R = self if n & 1 == 1 else Ideal(self.curve)

            i = 2
            while i <= n:
                Q = Q + Q

                if n & i == i:
                    R = Q + R

                i = i << 1

            return R

    def __rmul__(self, n):
        return self * n

    def __list__(self):
        return [self.x, self.y]

    def __eq__(self, other):
        if isinstance(other, Ideal):
            return False
        return list(self) == list(other)

    def __ne__(self, other):
        return not self == other

    def __getitem__(self, index):
        return [self.x, self.y][index]

    # lexicographic ordering on points
    def __lt__(self, other):
        if isinstance(other, Ideal): return False
        return list(self) < list(other)
    def __gt__(self, other):
        return other.__lt__(self)
    def __ge__(self, other):
        return not self < other
    def __le__(self, other):
        return not other < self


class Ideal(Point):
    def __init__(self, curve):
        self.curve = curve

    def __neg__(self):
        return self

    def __repr__(self):
        return "Ideal"

    def __add__(self, Q):
        if self.curve != Q.curve:
            raise Exception("Can't add points on different curves!")
        return Q

    def __mul__(self, n):
        if not isinstance(n, int):
            raise Exception("Can't scale a point by something which isn't an int!")
        else:
            return self

    def __eq__(self, other):
        return isinstance(other, Ideal)

    def __lt__(self, other):
        return not isinstance(other, Ideal)

