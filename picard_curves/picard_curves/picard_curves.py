r"""
Creating and maintaining a database of Picard curves
===================================================

"""

from sage.misc.misc_c import prod
from sage.structure.sage_object import SageObject
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.parallel.decorate import fork
from sage.all import cartesian_product
from sage.all import magma
import mclf


# Most calculation have been outsourced to Magma. SageMath functions mainly as
# a window to MCLF and database manipulation.


class PicardCurve(SageObject):
    def __init__(self, f, special = False, dowild = True, calccond = True, givencond = [], givenreds = []):
        if not special:
            self.special = ""
            self.pol = f
            self.lwe = (magma.LongWeierstrassEquation(self.pol)).sage()
            self.swe = (magma.ShortWeierstrassEquation(self.pol)).sage()
            self.rwe = (magma.ReducedWeierstrassEquation(self.pol)).sage()
            self.invs_QQ = (magma.ArithmeticInvariants(self.pol)).sage()
            self.invs_geo = (magma.GeometricInvariants(self.pol)).sage()
            disc = (magma.MinimalDiscriminant(self.pol)).sage()
            self.disc = [ tup for tup in disc.factor() ]
            if calccond:
                self.calculate_cond(dowild = dowild)
            else:
                self.cond = []
                self.reds = []
                if givencond:
                    self.cond = givencond
                if givenreds:
                    self.reds = givenreds

        else:
            self.special = "special "
            self.pol = f
            self.lwe = (magma.SpecialLongWeierstrassEquation(self.pol)).sage()
            self.swe = (magma.SpecialShortWeierstrassEquation(self.pol)).sage()
            self.rwe = (magma.SpecialReducedWeierstrassEquation(self.pol)).sage()
            self.invs_QQ = [ ]
            self.invs_geo = [ 0, 0, 1 ]
            disc = (magma.SpecialMinimalDiscriminant(self.pol)).sage()
            self.disc = [ tup for tup in disc.factor() ]
            if calccond:
                self.calculate_cond_special(dowild = dowild)
            else:
                self.cond = []
                self.reds = []
                if givencond:
                    self.cond = givencond
                if givenreds:
                    self.reds = givenreds

    def __repr__(self):
        return "The {}Picard curve associated to the polynomial {}:\n\
    Reduced Weierstrass equation: {}\n\
    Short Weierstrass equation:   {}\n\
    Long Weierstrass equation:    {}\n\
    Invariants over QQ:           {}\n\
    Invariants over QQbar:        {}\n\
    Factored discriminant:        {}\n\
    Factored conductor:           {}\n\
    Reduction types:              {}\n".format(str(self.special), str(self.pol), str(self.rwe), str(self.swe), str(self.lwe), str(self.invs_QQ), str(self.invs_geo), str(self.disc), str(self.cond), str(self.reds))

    def calculate_cond(self, dowild = True):
        # A list of pairs, representing the prime factors and their exponents
        # in the conductor
        #print "Calculating the semistable reduction and the conductor exponents of", self.pol
        Y = mclf.curves.picard_curves.PicardCurve(self.pol)
        if dowild:
            bad_primes = [ p for p, e in self.disc ]
        else:
            bad_primes = [ p for p, e in self.disc if p != 3 ]
        self.cond = [ ]
        self.reds= [ ]
        #print "Bad primes:", bad_primes
        for p in bad_primes:
            #print "At prime", p, "..."
            vp = QQ.valuation(p)
            Yp = mclf.semistable_reduction.semistable_models.SemistableModel(Y, vp)
            assert Yp.is_semistable(), 'We failed to compute the semistable reduction of %s at %s'%(Y, p)
            # compute the reduction type; this is the sorted list of the positive genera of the components
            typ = [ ]
            for W in Yp.components_of_positive_genus():
                typ += [W.genus()]*W.field_of_constants_degree()
            typ.sort()
            # compute the conductor_exponent
            fp = Yp.conductor_exponent()
            if fp != 0:
                self.reds.append((p, typ))
                self.cond.append((p, fp))
            #print typ
            #print fp
            #print "done"

    def calculate_cond_special(self, dowild = True):
        # A list of pairs, representing the prime factors and their exponents
        # in the conductor
        if dowild:
            bad_primes = [ p for p, e in self.disc ]
        else:
            bad_primes = [ p for p, e in self.disc if p != 2 ]
        self.cond = [ ]
        self.reds= [ ]
        for p in bad_primes:
            #print "At prime", p, "..."
            fp = tools.conductor_exponent(self.pol, p)
            self.reds.append(())
            self.cond.append((p, fp))
            #print fp

    def is_isomorphic_QQ(self, Y):
        if Y.special != self.special:
            return False
        elif not Y.special:
            return self.invs_QQ == Y.invs_QQ
        else:
            return (magma.SpecialPicardIsIsomorphic(self.pol, Y.pol)).sage()

    def is_isomorphic_geo(self, Y):
        return self.invs_geo == Y.invs_geo


class PicardDatabase(SageObject):
    def __init__(self, Ys):
        self.curves = [ ]
        for Y in Ys:
            self.insert_curve(Y)

    def __repr__(self):
        return "A database of Picard curves with {} elements".format(str(len(self.curves)))

    def in_database_pol(self, f, special = False):
        Yf = PicardCurve(f, special = special, calccond = False)
        for Y in self.curves:
            if Y.is_isomorphic_QQ(Yf):
                return True, Y
        return False, 0

    def in_database_curve(self, Y0):
        for Y in self.curves:
            if Y.is_isomorphic_QQ(Y0):
                return True, Y
        return False, 0

    def twists_in_database_pol(self, f, special = False):
        Yf = PicardCurve(f, special = special, calccond = False)
        twists = [ ]
        for Y in self.curves:
            if Y.is_isomorphic_geo(Yf):
                twists.append(Y)
        return twists

    def twists_in_database_curve(self, Y0):
        twists = [ ]
        for Y in self.curves:
            if Y.is_isomorphic_geo(Y0):
                twists.append(Y)
        return twists

    def remove_pol(self, f, special = False):
        Yf = PicardCurve(f, special = special, calccond = False)
        for Y in self.curves:
            if Y.is_isomorphic_QQ(Yf):
                self.curves.remove(Y)

    def remove_curve(self, Y0):
        for Y in self.curves:
            if Y.is_isomorphic_QQ(Y0):
                self.curves.remove(Y)

    def override_pol(self, f, special = False, dowild = True, calccond = True, givencond = [], givenreds = []):
        Yf = PicardCurve(f, special = special, dowild = dowild, calccond = calccond, givencond = givencond, givenreds = givenreds)
        self.override_curve(Yf)

    def override_curve(self, Y0):
        self.remove_curve(Y0)
        self.curves.append(Y0)

    def insert_pol(self, f, special = False, dowild = True, calccond = True, givencond = [], givenreds = []):
        Yf = PicardCurve(f, special = special, dowild = dowild, calccond = calccond, givencond = givencond, givenreds = givenreds)
        self.insert_curve(Yf)

    def insert_curve(self, Y0):
        test, Y = self.in_database_curve(Y0)
        if not test:
            self.curves.append(Y0)
        else:
            test0 = (len(Y.cond) == 0) and (len(Y0.cond) != 0)
            if not Y.special:
                testspec = (not (3 in [ p for p, e in Y.cond ])) and (3 in [ p for p, e in Y0.cond ])
            else:
                testspec = (not (2 in [ p for p, e in Y.cond ])) and (2 in [ p for p, e in Y0.cond ])
            if test0 or testspec:
                self.override_curve(Y0)

    def sorted_by_discriminant(self):
        Ys = [ Y for Y in self.curves if Y.disc ]
        disc_prod = lambda Y : prod([ l[0]**l[1] for l in Y.disc ])
        return sorted(Ys, key = disc_prod)

    def sorted_by_conductor(self):
        def test(Y):
            if Y.special:
                return 2 in [ p for p, e in Y.cond ]
            return 3 in [ p for p, e in Y.cond ]
        Ys = [ Y for Y in self.curves if test(Y) ]
        cond_prod = lambda Y : prod([ l[0]**l[1] for l in Y.cond ])
        return sorted(Ys, key = cond_prod)

    @fork(timeout=600)
    def calculate_pol_fork(self, f, special = False, dowild = True, calccond = True):
        test, Y = self.in_database_pol(f, special = special)
        if not test:
            return PicardCurve(f, special = special, dowild = dowild, calccond = calccond)
        else:
            test0 = (len(Y.cond) == 0) and calccond
            if not Y.special:
                testspec = (not (3 in [ p for p, e in Y.cond ])) and dowild
            else:
                testspec = (not (2 in [ p for p, e in Y.cond ])) and dowild
            if test0 or testspec:
                return PicardCurve(f, special = special, dowild = dowild, calccond = calccond)
            return Y
