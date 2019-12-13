from elliptic import *
from fractions import Fraction as frac

from finitefield.finitefield import FiniteField

import itertools

def findPoints(curve, field):
   print('Finding all points over %s' % (curve))
   print('The ideal generator is %s' % (field.idealGenerator))

   degree = field.idealGenerator.degree()
   subfield = field.primeSubfield
   xs = [field(x) for x in itertools.product(range(subfield.p), repeat=degree)]
   ys = [field(x) for x in itertools.product(range(subfield.p), repeat=degree)]

   points = [Point(curve, x, y) for x in xs for y in ys if curve.testPoint(x,y)]
   return points



F25 = FiniteField(5, 2)
curve = EllipticCurve(a=F25(1), b=F25(1))
points = findPoints(curve, F25)

for point in points:
   print(point)



