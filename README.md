BabySNARK
====
_The simplest possible SNARK for NP. You know, for kids!_

This is a self-contained development of SNARKs for NP. It is based on
[Square Span Program SNARKs](https://eprint.iacr.org/2014/718) by Danezis et al.,
which are expressive enough to encode boolean circuits.

This code accompanies a tutorial on defining and analyzing the security
of a SNARK, focusing on the soundness proof.
[(writeup.)](https://github.com/initc3/babysnark/babysnark.pdf)

Recommended usage
--
This is for educational purposes only.
It's not efficient overall compared to state-of-the-art SNARK implementations, it doesn't come with a type system or any program analysis to rule out mistakes, and it doesn't support the zero-knowledge feature.
It does, however, demonstrate some important SNARK design concepts and algorithm optimizations. It's succinct: the proof is constant size, and verifying it depends only on the size of statement, not the circuit and witness.
It also achieves quasilinear overhead, through the use of FFT-based optimizations.

So, use it to study how SNARKs can be implemented, and to check your understanding of the [accompanying tutorial](https://github.com/initc3/babysnark/babysnark.pdf)
As a project, consider extending this library to implement additional optimizations or protocol variants.
This may also be useful in development for prototyping and reference implementations.

Components
--
 - [babysnark.py](babysnark.py): a succinct SNARK for square span programs
 - [babysnark_opt.py](babysnark_opt.py): improves on babysnark by using FFT optimizations,
     achieving quasilinear compute overhead
 - [finitefield/](finitefield/): a generic library for finite fields, and polynomials defined over them
     This library is adapted from posts by Jeremy Kun.
     See [A Programmer's Introudction to Mathematics](https://github.com/pim-book/programmers-introduction-to-mathematcs)
 and [Programming with Finite Fields](https://jeremykun.com/2014/03/13/programming-with-finite-fields/)
 - [polynomial_evalrep.py](polynomial_evalrep.py):
   -- an alternative polynomial abstraction, using evaluation at roots of unity, rather than coefficients.
 - `{babysnark,babysnark_opt,polynomial_evalrep}.ipynb`: the files are rendered in jupyter notebook form so they're more informative on github


Setting up
--
This uses Python3. There are a few python dependencies, mainly `numpy` and `py_ecc`, an implementation of pairing cryptography including bls12-381.
```
pip install -r requirements.txt
```
To run:
```
python babysnark.py
python babysnark_opt.py
```

To rebuild the jupyter notebooks:
```
py2nb babysnark.py
py2nb babysnark_opt.py
py2nb polynomial_evalrep.py
```