# Statistics
from picard_curves import PicardDatabase, PicardCurve


database = load('picard_database')
print ""
print "Number of elements in database:"
print len(database.curves)


print ""
print "Number of nonspecial elements:"
print len([ Y for Y in database.curves if not Y.special ])

curves_comp_part = [ Y for Y in database.curves if Y.cond and not Y.special ]
print ""
print "Number of nonspecial elements in database with conductor partially or completely computed:"
print len(curves_comp_part)

curves_comp_comp = [ ]
for Y in curves_comp_part:
    if 3 in [ p for p, e in Y.cond ]:
        curves_comp_comp.append(Y)

print ""
print "Number of nonspecial elements in database with conductor completely computed:"
print len(curves_comp_comp)


print ""
print "Number of special elements:"
print len([ Y for Y in database.curves if Y.special ])

curves_spec_comp_part = [ Y for Y in database.curves if Y.cond and Y.special ]
print ""
print "Number of special elements in database with conductor partially or completely computed:"
print len(curves_spec_comp_part)

curves_spec_comp_comp = [ ]
for Y in curves_spec_comp_part:
    if 2 in [ p for p, e in Y.cond ]:
        curves_spec_comp_comp.append(Y)

print ""
print "Number of special elements in database with conductor completely computed:"
print len(curves_spec_comp_comp)


curves_equal = [ ]
for Y in database.curves:
    disc = prod([ tup[0]^tup[1] for tup in Y.disc ])
    cond = prod([ tup[0]^tup[1] for tup in Y.cond ])
    for tup in Y.cond:
        cond_fac = tup[0]^tup[1]
        if disc % cond_fac != 0:
            print "ERROR: Curve with smaller discriminant exponent than conductor exponent!"
            print Y
    if disc == cond:
        curves_equal.append(Y)

print ""
print "Number of completely computed curves with conductor equal to discriminant:"
print len(curves_equal)


print ""
print "Curve with smallest discriminant:"
print database.sorted_by_discriminant()[0]

print ""
print "Curve with smallest computed conductor:"
print database.sorted_by_conductor()[0]


#R.<x> = PolynomialRing(QQ)
#f = x^4 + 2^3*x + 2^4
#
#print ""
#print "Polynomial:"
#print f
#print "In database?"
#print database.in_database_pol(f)
#print "Twists in database:"
#print database.twists_in_database_pol(f)
#
#Y = PicardCurve(x^4 - 6*x^2 - 3, special = True, calccond = False)
#Y = PicardCurve(x^4 - 162*x^2 - 2187, calccond = False)

R.<x> = PolynomialRing(QQ)
Y = PicardCurve(x^4 - 4806*x^2 + 181224*x - 1920915, calccond = False)
#Y = PicardCurve(x^3 + 1, special = True, calccond = False)

print ""
print "Looking up the curve:"
print Y
print "In database?"
print database.in_database_curve(Y)
#print "Twists in database:"
#print database.twists_in_database_curve(Y)

