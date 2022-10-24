"""
Some help functions for special Picard curves
=============================================


"""

from sage.all import *
from mclf import SuperellipticCurve, BerkovichLine, BerkovichTree, RationalDomainOnBerkovichLine, SemistableModel, ReductionTree


def Q_invariant(f):
    """ Return the Q-invariant of f.

    We assume that f is a monic irreducible quartic polynomial over QQ.
    Let K be the splitting field of f and alpha_1,..,alpha_4 the roots
    of f. Then the *Q-invariant* of f is the minimal polynomial over QQ
    of J, where

           J = (t^2-t+1)^3/((t-1)*t))^2

    and

        t =  (alpha_3-alpha_1)/(alpha_2-alpha_1).

    We write Q(f) for this polynomial. It is easy to see that if f_1 and f_2
    are *PGL_2-equivalent*, i.e. there exists gamma in PGL_2(QQ) with
    f_2(x) = a*g^4*f_1(gamma(x)), then Q(f_1)=Q(f_2).

    """
    assert f.is_irreducible()
    K = f.splitting_field('theta')
    a = [alpha for alpha, m in f.roots(K)]
    t = (a[2]-a[0])/(a[1]-a[0])
    J = (t**2-t+1)**3/t**2/(t-1)**2
    return J.minpoly('x')


def f_standard(b,c):
    """ Return the polynomial

        f = x^4 + 6*b*x^2 + c*x - 3*b^2.

    """
    R = PolynomialRing(QQ, 'x')
    x = R.gen()
    return x**4 + 6*b*x**2 + c*x - 3*b**2


def normalize(f):
    """ Return the normalized form of f.

    Here f is any quartic polynomial. It is called *normalized*
    if f = x^4 + b*x^2 + c*x + d. We normalize f by a shift,
    f(x-e), and multiplication by a constant.

    """
    assert f.degree() == 4, "f must have degree 4"
    x = f.parent().gen()
    f = f.monic()
    return f(x-f[3]/4)


def shadow(f):
    """ Return the shadow of the special quartic f.

    Given a special quartic f over QQ and a root alpha of f. There is a
    unique automorphism group of PP^1 of order 3 which permutes the roots
    of f and fixes alpha. Let alpha' be the second fix point of that group.
    If f has roots a_1,..,a_4 then the *shadow* of f is the  polynomial

          f' := (x-a_1')(x-a_2')(x-a_3')(x-a_4').

    """
    assert f.degree() == 4, "f must have degree 4"
    assert f.gcd(f.derivative())==1, "f must be separable"
    R = f.parent()
    x = R.gen()
    F = f.factor()
    f_shadow = R.one()
    for f1, m in F:
        K = NumberField(f1, 'alpha')
        alpha = K.gens()[0]
        g = f((alpha*x+1)/(x+1)).numerator()
        if g[3] != 0:
            beta = -g[2]/3/g[3]
            if beta + 1 != 0:
                gamma = (alpha*beta+1)/(beta+1)
                f_shadow = f_shadow*gamma.minpoly()
    return f_shadow


def conductor_exponent(f, p, reduction_tree=False):
    r""" Return the conductor exponent of this special Picard curve at p.

    We assume that f is a special quartic over QQ. Let

        Y: y^4 = f(x)

    be the corresponding special Picard curve. We return the conductor exponent
    at p.

    """
    vp = QQ.valuation(p)
    if p > 2:
        Y = SuperellipticCurve(f, 4)
        return SemistableModel(Y, vp).conductor_exponent()
    else:
        # now p = 2
        Y = SuperellipticCurve(f, 4)
        F = Y.rational_function_field()
        g = F(shadow(f))
        f = F(f)
        h = f/g
        X = BerkovichLine(F, vp)
        T = BerkovichTree(X)
        T = T.adapt_to_function(h)
        T = T.permanent_completion()

        xi_list = [xi for xi in T.vertices() if xi.type()=="II"]
        values = [xi.v(h) for xi in xi_list]
        xi1 = xi_list[values.index(max(values))]
        xi2 = xi_list[values.index(min(values))]
        s1 = QQ(xi1.v(h))
        s2 = QQ(xi2.v(h))
        s = QQ(xi2.v(h)) + QQ(4)/QQ(3)
        p = QQ(p)
        U1 = RationalDomainOnBerkovichLine(X, p**(s.numerator())/h**(s.denominator()))
        U1.simplify()
        U1.simplify()
        T1 = U1._T

        U2 = RationalDomainOnBerkovichLine(X, p**s2.numerator()/h**s2.denominator())
        U2.simplify()
        U2.simplify()
        T2 = U2._T

        for xi in T2.vertices():
            if xi.type()=="II":
                T1, _ = T1.add_point(xi, True)

        RT = ReductionTree(Y, vp, T1)
        xi = X.point_from_discoid(g,Infinity)
        for Z in RT.inertial_components():
            Z._basepoint = xi
        if reduction_tree:
            return RT
        else:
            assert RT.is_semistable()
            return RT.reduction_conductor()

        return conductor_exponent
