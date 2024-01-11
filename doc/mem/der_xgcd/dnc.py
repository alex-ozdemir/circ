#!/usr/bin/env python

from sage.misc.misc_c import prod
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_element import Polynomial
from dataclasses import dataclass

p = 31
F = GF(p)
R = PolynomialRing(F, "x")
x = R.gen(0)


@dataclass
class Bezout:
    f: Polynomial
    g: Polynomial
    gf: Polynomial
    fg: Polynomial

    def check(self):
        assert self.f * self.gf + self.g * self.fg == 1


def ea(f, g) -> Bezout:
    gcd, gf, fg = f.xgcd(g)
    assert gcd == 1
    return Bezout(f, g, gf, fg)


def mul0(b0: Bezout, b1: Bezout) -> Bezout:
    assert b0.f == b1.f
    return Bezout(b0.f, b0.g * b1.g, b0.gf + b0.g * b0.fg * b1.gf, b0.fg * b1.fg)


def v(*xs):
    if len(xs) == 1 and isinstance(xs, list):
        xs = xs[0]
    return prod([x - a for a in xs])


def dgcd(p):
    g, s, t = p.xgcd(p.derivative())
    return g, s, t, s.factor(), t.factor()


f = v(2, 5, 7)
g = v(1, 3, 8)
print("f", f)
print("g", g)
_, fg, gf = f.xgcd(g)
print("fg", fg)
print("gf", gf)
_, fF, Ff = f.xgcd(f.derivative())
print("fF", fF)
print("Ff", Ff)
_, gG, Gg = g.xgcd(g.derivative())
print("gG", gG)
print("Gg", Gg)
h = f * g
print("h", h)
print("h", h.factor())
print("H", h.derivative().factor())
_, hH, Hh = h.xgcd(h.derivative())
print("hH", hH)
print("Hh", Hh)
c = Hh.coefficients()[-1]
print()
a = v(1, 2, 7, 10)
b = v(3, 4, 8)
c = v(5, 6)
assert a.xgcd(b)[0] == 1
assert b.xgcd(c)[0] == 1
assert a.xgcd(c)[0] == 1
print("a", a)
print("b", b)
print("c", c)
_, ba, ab = a.xgcd(b)
_, ca, ac = a.xgcd(c)
print("(a,b)", a.xgcd(b))
print("(a,c)", a.xgcd(c))
print("(a,bc)", a.xgcd(b * c))
print("(a,bc)", (1, ca + c * ac * ba, ab * ac))
s = ca + c * ac * ba
t = ab * ac
print("s", s)
print("t", t)
print(s * a + t * b * c)
q, r = s.quo_rem(b * c)
print("q", q)
print("r", r)
print(r * a + b * c * (t + q * a))
print(t + q * a)

# ea(a, b).check()
# ea(a, c).check()
# mul0(ea(a, b), ea(a, c)).check()
# print(ea(a, b))
# print(ea(a, c))
# print(ea(a, b * c))
# print(mul0(ea(a, b), ea(a, c)))
# print(mul0(ea(a, b), ea(a, c)).fg.factor())
# print(mul0(ea(a, b), ea(a, c)).gf.factor())
