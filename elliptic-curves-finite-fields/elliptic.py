
class EllipticCurve(object):
   def __init__(self, a, b):
      # assume we're already in the Weierstrass form
      self.a = a
      self.b = b

      self.discriminant = -16 * (4 * a*a*a + 27 * b * b)
      if not self.isSmooth():
         raise Exception("The curve %s is not smooth!" % self)


   def isSmooth(self):
      return self.discriminant != 0


   def testPoint(self, x, y):
      return y*y == x*x*x + self.a * x + self.b


   def __str__(self):
      return 'y^2 = x^3 + %sx + %s' % (self.a, self.b)


   def __repr__(self):
      return str(self)


   def __eq__(self, other):
      return (self.a, self.b) == (other.a, other.b)



class Point(object):
   def __init__(self, curve, x, y):
      self.curve = curve # the curve containing this point
      self.x = x
      self.y = y

      if not curve.testPoint(x,y):
         raise Exception("The point %s is not on the given curve %s!" % (self, curve))


   def __str__(self):
      return "(%r, %r)" % (self.x, self.y)


   def __repr__(self):
      return str(self)


   def __neg__(self):
      return Point(self.curve, self.x, -self.y)


   def __add__(self, Q):
      if self.curve != Q.curve:
         raise Exception("Can't add points on different curves!")
      if isinstance(Q, Ideal):
         return self

      x_1, y_1, x_2, y_2 = self.x, self.y, Q.x, Q.y

      if (x_1, y_1) == (x_2, y_2):
         if y_1 == 0:
            return Ideal(self.curve)

         # slope of the tangent line
         m = (3 * x_1 * x_1 + self.curve.a) / (2 * y_1)
      else:
         if x_1 == x_2:
            return Ideal(self.curve)

         # slope of the secant line
         m = (y_2 - y_1) / (x_2 - x_1)

      x_3 = m*m - x_2 - x_1
      y_3 = m*(x_3 - x_1) + y_1

      return Point(self.curve, x_3, -y_3)


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
      if type(other) is Ideal:
         return False

      return (self.x, self.y) == (other.x, other.y)

   def __ne__(self, other):
      return not self == other

   def __getitem__(self, index):
      return [self.x, self.y][index]


class Ideal(Point):
   def __init__(self, curve):
      self.curve = curve

   def __neg__(self):
      return self

   def __str__(self):
      return "Ideal"

   def __add__(self, Q):
      if self.curve != Q.curve:
         raise Exception("Can't add points on different curves!")
      return Q

   def __mul__(self, n):
      if not (isinstance(n, int) or isinstance(n, long)):
         raise Exception("Can't scale a point by something which isn't an int!")
      else:
         return self

   def __eq__(self, other):
      return type(other) is Ideal

